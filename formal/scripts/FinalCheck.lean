import Lean
open Lean

/-!
# Out-of-band final check (trust audits of 2026-09-26; PLAN_FORMALIZATION.md §1, §4, §8 Q2–Q3)

Usage (from `formal/`, after `lake build EGCheck.Final`):

    lake env lean --run scripts/FinalCheck.lean [options]

This script is the statement/axiom half of the acceptance criterion. Unlike the in-band checks
of `EGCheck/Final.lean` (`type_of%`, `#guard_msgs` on `#print axioms`, `run_cmd`), it runs **no
code of the project or of any package**: `importModules` is called with `loadExts := false`, so
no imported elaborator, macro, delaborator, environment-extension import hook or `initialize`
runs. Every check below reads the `ConstantInfo`s stored in the `.olean` files and uses only code
of this script and of the pinned Lean toolchain. Every constant is looked up by a literal `Name`.

Checks (each prints `[PASS]`, `[WARN]` or `[FAIL]`; exit code 1 on any `[FAIL]`):

* `lean`      — the running Lean is the pinned commit (`EG-PIN lean-githash` in the pin file).
* `import`    — `importModules #[FormalConjectures.ErdosProblems.«184», EGCheck.Final, <policy
                roots>]` succeeds. A second declaration of an upstream name with a different type
                is an import clash; a same-type theorem copy is merged silently (see `origin`).
* `oleans`    — every imported module's `.olean` is the one of its package: project modules
                (`EG*`, `EGTest*`, `EGCheck*`) under `.lake/build/lib/lean`, every other module
                under the toolchain or `.lake/packages/<its package>/.lake/build/lib/lean`, with a
                git-tracked source file; each package used is at its `lake-manifest.json` rev with
                a clean worktree (`git status --porcelain --untracked-files=all`).
* `origin`    — `Erdos184.erdos_184` and `Erdos184.IsCycleOrEdge` come from
                `FormalConjectures.ErdosProblems.«184»`, `SimpleGraph.IsDecomposition` from
                `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition`, and
                `EGCheck.erdos_184` from `EGCheck.Final`, each declared by exactly one module.
                Duplicates and attribution (trust2.opus N4/N6): `importModules` silently merges two
                same-type theorems of the same name (the later module's `ConstantInfo` wins, while
                `const2ModIdx` keeps the first module), and it attributes every IR
                `extraConstNames` entry to its module with `insertIfNew`, so attribution
                (`getModuleIdxFor?`) is NOT a reliable "declared here". Hence this check FAILS on:
                a name declared by a project module and by any non-project module; a name declared
                by two project modules unless every copy is a theorem with the same type, universe
                parameters and `all` (the realized `eq_N`/`congr_simp` lemmas Lean generates in
                several modules; each copy is then replayed and axiom-walked separately); any
                duplicate of the four names above; a project module's `extraConstNames` entry that
                names a kernel constant the module does not itself declare; and any kernel
                constant whose `const2ModIdx` attribution involves a project module but is not one
                of its declaring modules.
* `kinds`     — both theorems are `.thmInfo`; both upstream definitions are `.defnInfo`.
* `statement` — `Expr.equal` (binder names and binder annotations included) of the two types,
                after renaming the universe parameters by position; equal counts. Computed on the
                `importModules` environment itself.
* `replay`    — every declaration of every project module, taken from that module's OWN stored
                `ConstantInfo` (all names in its `constNames`, with no attribution filter; every
                copy of a merged duplicate separately), is re-checked by the kernel
                (`Environment.replay`) on top of an environment made only of the package modules
                (trust level 0). Catches kernel bypasses (`debug.skipKernelTC`, `addDecl` from
                `#eval`/`elab`/`run_tac`, …). BY DESIGN `Environment.replay` skips `unsafe` and
                `partial` constants (not kernel-checkable); a replayed constant that refers to one
                fails with an unknown constant, so they are unusable by anything replayed. The
                honest tree has such constants only as `._unsafe_rec` compiler auxiliaries; the
                `policy` check forbids `unsafe`, `@[implemented_by]` and `@[extern]` (which
                `partial def` needs), and `scripts/lint.py` forbids the keyword `partial` in
                `EG`/`EGCheck`. Package `.olean`s are trusted here; `leanchecker --fresh
                EGCheck.Final` (for `EGCheck.Final`'s import closure) and comparator re-check those.
* `axioms`    — the axioms reachable from `EGCheck.erdos_184` (own traversal of the stored bodies
                in the `importModules` environment, following EVERY stored copy of a duplicated
                project theorem, so the result does not depend on which copy `importModules` kept)
                are exactly `propext, Classical.choice, Quot.sound`. `sorryAx` is reported
                separately and is a failure unless `--allow-sorry`. Lean's `collectAxioms` (which
                sees only the kept copy) is run as a cross-check. Only meaningful together with a
                passing `replay` (a FAIL of either fails the run).
* `policy`    — the policy of `scripts/Axioms.lean --no-sorry` on every constant of a project
                module: no axiom outside the three (`sorryAx` only with `--allow-sorry`), no
                `axiom` declaration, nothing `unsafe`, no `@[extern]`, `@[implemented_by]`,
                `@[init]`/`@[builtin_init]`; every copy of a duplicated theorem is checked.
* `meta`      — no constant of a project module has a type mentioning meta-level types
                (elaborators, macros, parsers, syntax, `IO`, environments, …): the project is pure
                mathematics, so such a constant can only be an elaborator/macro/initializer hook.
* `pin`       — SHA-256 of a canonical serialisation of the statement `Erdos184.erdos_184` and of
                its closure (types, definition bodies, inductive declarations) equals the pins
                `EG-PIN statement-sha256` / `EG-PIN closure-sha256` of the pin file (default
                `TRUST.md`). This pins the *meaning* of the upstream statement, including every
                Mathlib/Batteries/core definition it unfolds to, against tampered or stale
                `.olean`s and working trees. The hashes are computed by `sha256sum`.

Options:

    --allow-sorry            sorryAx is a warning instead of a failure (development only)
    --allow-unpinned         a missing pin is a warning instead of a failure (development only)
    --pin-file PATH          file with `EG-PIN <key> <value>` lines (default: TRUST.md)
    --expect-statement-sha256 HEX / --expect-closure-sha256 HEX   override the pin file
    --final-module M         module declaring the final theorem (default: EGCheck.Final)
    --policy-roots A,B|none  extra modules imported for the policy scan (default: EG,EGCheck)
    --no-replay              skip the kernel replay (fast development runs only)
    --dump-canon DIR         write the canonical statement/closure serialisations to DIR

The canonical serialisation between `BEGIN CANON` and `END CANON` must stay byte-identical with
the one in `scripts/Statement.lean` (`scripts/redteam.sh` checks this).

Role (TRUST.md §4): this script is DEFENCE IN DEPTH next to `leanchecker --fresh`; comparator is
the load-bearing check against a malicious build. What this script does NOT establish: that the
package `.olean`s were compiled from the pinned sources (use a fresh clone + from-source build of
formal-conjectures, `leanchecker --fresh`, comparator); that the build did not tamper with this
script, the pin file or the lock (run this script from a copy of `scripts/` and `TRUST.md` taken
from the approved commit, never from the commit under test); and it loads the untrusted project
`.olean`s into its own process, so the Lean v4.33.1 `.olean` loader on adversarial input is
trusted (as it is by `leanchecker` and by comparator's `lean4export`).
-/

namespace EGFinalCheck

/-! ## Fixed data: literal names, never resolved in an environment -/

def upstreamModule : Name := `FormalConjectures.ErdosProblems.«184»
def decompModule : Name := `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition
def upstreamThm : Name := `Erdos184.erdos_184
def cycleOrEdgeDef : Name := `Erdos184.IsCycleOrEdge
def isDecompDef : Name := `SimpleGraph.IsDecomposition
def finalThm : Name := `EGCheck.erdos_184
def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]
def sorryAxName : Name := `sorryAx

/-- Module-name roots of the project's own libraries (`lean_lib`s of `lakefile.toml`). -/
def projectRoots : Array Name := #[`EG, `EGTest, `EGCheck]

/-- Module-name root ↦ package directory under `.lake/packages` (`none`: the Lean toolchain). -/
def packageOfRoot : List (Name × Option String) :=
  [(`Init, none), (`Std, none), (`Lean, none), (`Lake, none),
   (`Mathlib, some "mathlib"), (`Batteries, some "batteries"), (`Aesop, some "aesop"),
   (`Qq, some "Qq"), (`ProofWidgets, some "proofwidgets"), (`Plausible, some "plausible"),
   (`ImportGraph, some "importGraph"), (`LeanSearchClient, some "LeanSearchClient"),
   (`Cli, some "Cli"), (`FormalConjectures, some "formal_conjectures"),
   (`FormalConjecturesForMathlib, some "formal_conjectures"),
   (`FormalConjecturesUtil, some "formal_conjectures")]

/-- Prefixes of constants that only meta-level code mentions in its type. -/
def metaHeads : Array Name :=
  #[`Lean.Elab, `Lean.Meta, `Lean.Macro, `Lean.MacroM, `Lean.Syntax, `Lean.TSyntax,
    `Lean.SyntaxNodeKind, `Lean.ParserDescr, `Lean.TrailingParserDescr, `Lean.Parser,
    `Lean.PrettyPrinter, `Lean.Environment, `Lean.Kernel, `Lean.Declaration,
    `Lean.ConstantInfo, `Lean.Expr, `Lean.Level, `Lean.Core, `Lean.CoreM, `Lean.Options,
    `Lean.KVMap, `Lean.MessageData, `Lean.AttributeImpl, `Lean.EnvExtension,
    `Lean.PersistentEnvExtension, `Lean.Widget, `Lean.Server, `Lean.Json, `Lean.ToExpr,
    `Lean.Compiler, `Lean.IR, `IO, `EIO, `BaseIO, `IO.RealWorld, `EStateM, `ST, `System.FilePath]

def isProjectModule (m : Name) : Bool := projectRoots.contains m.getRoot

/-! ## Report -/

structure Report where
  fails : Nat := 0
  warns : Nat := 0

abbrev M := StateRefT Report IO

def out (tag check msg : String) : M Unit := do
  IO.println s!"[{tag}] {check}: {msg}"
  (← IO.getStdout).flush

/-- Progress line on stderr (with elapsed seconds), for long runs. -/
def progress (msg : String) : IO Unit := do
  IO.eprintln s!"  … {msg} ({(← IO.monoMsNow) / 1000} s)"
  (← IO.getStderr).flush
def pass (check msg : String) : M Unit := out "PASS" check msg
def warn (check msg : String) : M Unit := do
  out "WARN" check msg; modify fun r => { r with warns := r.warns + 1 }
def fail (check msg : String) : M Unit := do
  out "FAIL" check msg; modify fun r => { r with fails := r.fails + 1 }

/-! ## Options -/

structure Opts where
  allowSorry : Bool := false
  allowUnpinned : Bool := false
  pinFile : String := "TRUST.md"
  expectStmt : Option String := none
  expectClosure : Option String := none
  expectLeanGithash : Option String := none
  finalModule : Name := `EGCheck.Final
  policyRoots : Array Name := #[`EG, `EGCheck]
  replay : Bool := true
  scanOnly : Bool := false
  solutionModule : Option Name := none
  restatedThm : Name := `Erdos184.erdos_184
  dumpCanon : Option String := none
  bad : Array String := #[]

partial def parseArgs : List String → Opts → Opts
  | "--allow-sorry" :: r, o => parseArgs r { o with allowSorry := true }
  | "--allow-unpinned" :: r, o => parseArgs r { o with allowUnpinned := true }
  | "--pin-file" :: p :: r, o => parseArgs r { o with pinFile := p }
  | "--expect-statement-sha256" :: h :: r, o => parseArgs r { o with expectStmt := some h }
  | "--expect-closure-sha256" :: h :: r, o => parseArgs r { o with expectClosure := some h }
  | "--expect-lean-githash" :: h :: r, o => parseArgs r { o with expectLeanGithash := some h }
  | "--final-module" :: m :: r, o => parseArgs r { o with finalModule := m.toName }
  | "--policy-roots" :: ms :: r, o =>
    let roots := if ms == "none" then #[] else
      (ms.splitOn ",").toArray.filter (· ≠ "") |>.map (·.toName)
    parseArgs r { o with policyRoots := roots }
  | "--no-replay" :: r, o => parseArgs r { o with replay := false }
  | "--scan-only" :: r, o => parseArgs r { o with scanOnly := true }
  | "--solution-module" :: m :: r, o => parseArgs r { o with solutionModule := some m.toName }
  | "--restated-thm" :: m :: r, o => parseArgs r { o with restatedThm := m.toName }
  | "--dump-canon" :: d :: r, o => parseArgs r { o with dumpCanon := some d }
  | a :: r, o => parseArgs r { o with bad := o.bad.push a }
  | [], o => o

/-! ## BEGIN CANON
Canonical, injective serialisation of kernel declarations (de Bruijn indices, length-prefixed
names and strings, explicit binder annotations). Independent of every pretty-printer and of
the environment. Keep byte-identical with `scripts/Statement.lean`. -/

namespace Canon

abbrev W := StateM String

def emit (s : String) : W Unit := modify (· ++ s)

def name : Name → W Unit
  | .anonymous => emit "_"
  | .str p s => do name p; emit s!".s{s.utf8ByteSize}:{s}"
  | .num p k => do name p; emit s!".n{k}"

def level : Level → W Unit
  | .zero => emit "0"
  | .succ l => do emit "(S "; level l; emit ")"
  | .max a b => do emit "(M "; level a; emit " "; level b; emit ")"
  | .imax a b => do emit "(I "; level a; emit " "; level b; emit ")"
  | .param n => do emit "(P "; name n; emit ")"
  | .mvar _ => emit "(?L)"

def levels (ls : List Level) : W Unit := do
  emit "["; for l in ls do level l; emit ","
  emit "]"

def names (ns : List Name) : W Unit := do
  emit "["; for n in ns do name n; emit ","
  emit "]"

def binfo : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

partial def expr : Expr → W Unit
  | .bvar i => emit s!"#{i}"
  | .fvar id => do emit "(F "; name id.name; emit ")"
  | .mvar id => do emit "(?E "; name id.name; emit ")"
  | .sort l => do emit "(T "; level l; emit ")"
  | .const n ls => do emit "(C "; name n; emit " "; levels ls; emit ")"
  | .app f a => do emit "(A "; expr f; emit " "; expr a; emit ")"
  | .lam n t b bi => do
    emit s!"(L{binfo bi} "; name n; emit " "; expr t; emit " "; expr b; emit ")"
  | .forallE n t b bi => do
    emit s!"(P{binfo bi} "; name n; emit " "; expr t; emit " "; expr b; emit ")"
  | .letE n t v b nd => do
    emit s!"(E{if nd then "n" else "d"} "; name n; emit " "; expr t; emit " "; expr v; emit " ";
    expr b; emit ")"
  | .lit (.natVal k) => emit s!"(N {k})"
  | .lit (.strVal s) => emit s!"(Z {s.utf8ByteSize}:{s})"
  | .mdata m e => do
    let s := toString m
    emit s!"(D {s.utf8ByteSize}:{s} "; expr e; emit ")"
  | .proj s i e => do emit "(J "; name s; emit s!" {i} "; expr e; emit ")"

def safety : DefinitionSafety → String
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

/-- One line per declaration. Theorem bodies are omitted (proof irrelevance): the line pins what
the declaration *says*, and for definitions what they unfold to. -/
def constInfo (ci : ConstantInfo) : W Unit := do
  let hdr (k : String) : W Unit := do
    emit k; emit " "; name ci.name; emit " "; names ci.levelParams; emit " "; expr ci.type
  match ci with
  | .axiomInfo v => do hdr "AX"; emit s!" unsafe={v.isUnsafe}"
  | .defnInfo v => do hdr "DEF"; emit s!" {safety v.safety} "; expr v.value
  | .thmInfo _ => hdr "THM"
  | .opaqueInfo v => do hdr "OPQ"; emit s!" unsafe={v.isUnsafe} "; expr v.value
  | .quotInfo v => do
    hdr "QUOT"
    emit s!" {match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"}"
  | .inductInfo v => do
    hdr "IND"
    emit s!" params={v.numParams} indices={v.numIndices} all="; names v.all
    emit " ctors="; names v.ctors
    emit s!" nested={v.numNested} rec={v.isRec} unsafe={v.isUnsafe} refl={v.isReflexive}"
  | .ctorInfo v => do
    hdr "CTOR"; emit " induct="; name v.induct
    emit s!" cidx={v.cidx} params={v.numParams} fields={v.numFields} unsafe={v.isUnsafe}"
  | .recInfo v => do
    hdr "REC"; emit " all="; names v.all
    emit s!" params={v.numParams} indices={v.numIndices} motives={v.numMotives} minors={v.numMinors} k={v.k} unsafe={v.isUnsafe} rules=["
    for r in v.rules do
      emit "("; name r.ctor; emit s!" {r.nfields} "; expr r.rhs; emit ")"
    emit "]"

def constLine (ci : ConstantInfo) : String := (constInfo ci).run "" |>.2

/-- Constants the meaning of `ci` depends on: its type; for definitions and opaques also the
body; for inductives the mutual block and the constructors; for constructors the inductive. -/
def deps (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => t.push v.induct
  | .recInfo v => t ++ v.all.toArray
  | _ => t

/-- The closure of `root` under `deps`, sorted by `Name.lt`; also the names that are missing. -/
def closure (env : Environment) (root : Name) : Array Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  let mut missing : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => missing := missing.push n
    | some ci => for d in deps ci do
        unless seen.contains d do todo := todo.push d
  let found := seen.toArray.filter fun n => !missing.contains n
  return (found.qsort Name.lt, missing.qsort Name.lt)

/-- The canonical text of the statement (the declaration of `root` alone) and of its closure. -/
def dumps (env : Environment) (root : Name) : Option (String × String) × Array Name := Id.run do
  let (ns, missing) := closure env root
  let some rootCi := env.find? root | return (none, missing)
  let mut all := ""
  for n in ns do
    if let some ci := env.find? n then
      all := all ++ constLine ci ++ "\n"
  return (some (constLine rootCi ++ "\n", all), missing)

end Canon

/-! ## END CANON -/

/-! ## Helpers -/

def sha256 (data : String) : IO String := do
  IO.FS.withTempFile fun h path => do
    h.putStr data
    h.flush
    let o ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
    if o.exitCode != 0 then throw <| IO.userError s!"sha256sum failed: {o.stderr}"
    return (o.stdout.splitOn " ").headD ""

def run (cmd : String) (args : Array String) (cwd : Option String := none) :
    IO (UInt32 × String) := do
  let o ← IO.Process.output { cmd, args, cwd := cwd.map (⟨·⟩) }
  return (o.exitCode, o.stdout ++ o.stderr)

/-- `EG-PIN <key> <value>` lines of the pin file (backticks and trailing colons ignored). -/
def readPins (path : String) : IO (Array (String × String)) := do
  unless ← System.FilePath.pathExists path do return #[]
  let txt ← IO.FS.readFile path
  let mut pins := #[]
  for line in txt.splitOn "\n" do
    let toks := (line.replace "`" " ").splitOn " " |>.filter (· ≠ "")
    let rec go : List String → Array (String × String) → Array (String × String)
      | "EG-PIN" :: k :: v :: rest, acc => go rest (acc.push ((k.dropEndWhile (· == ':')).toString, v))
      | _ :: rest, acc => go rest acc
      | [], acc => acc
    pins := go toks pins
  return pins

def pinValue (pins : Array (String × String)) (key : String) : Except String (Option String) :=
  let vs := (pins.filter (·.1 == key)).map (·.2)
  let vs := vs.foldl (fun acc v => if acc.contains v then acc else acc.push v) #[]
  if vs.size > 1 then .error s!"conflicting values for {key}: {vs}" else .ok vs[0]?

def isHex64 (s : String) : Bool := s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Axioms reachable from `root`, by an explicit-stack traversal of the stored declarations
(types; bodies of definitions, theorems and opaques; constructors of inductives). `look n` returns
EVERY stored `ConstantInfo` of `n` (several for a merged duplicate theorem, see `ProjDecls.look`),
and the traversal follows all of them. Also returns the referenced names that are missing and the
number of constants visited. -/
def reachableAxioms (look : Name → Array ConstantInfo) (root : Name) :
    Array Name × Array Name × Nat := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  let mut axs : Array Name := #[]
  let mut missing : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let cis := look n
    if cis.isEmpty then missing := missing.push n; continue
    for ci in cis do
      let mut ds := ci.type.getUsedConstants
      match ci with
      | .axiomInfo _ => unless axs.contains n do axs := axs.push n
      | .defnInfo v => ds := ds ++ v.value.getUsedConstants
      | .thmInfo v => ds := ds ++ v.value.getUsedConstants
      | .opaqueInfo v => ds := ds ++ v.value.getUsedConstants
      | .inductInfo v => ds := ds ++ v.ctors.toArray
      | _ => pure ()
      for d in ds do
        unless seen.contains d do todo := todo.push d
  return (axs.qsort Name.lt, missing.qsort Name.lt, seen.size)

/-- Representative of the node of `n` in the axiom-dependency graph: inductive blocks and their
constructors are collapsed into one node (their first inductive), so the graph is acyclic. -/
def rep (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) =>
    match env.find? v.induct with
    | some (.inductInfo iv) => iv.all.headD v.induct
    | _ => v.induct
  | some (.inductInfo v) => v.all.headD n
  | _ => n

/-- Successors of the node `n` (already a representative) and the axiom it is, if any. -/
def repDeps (env : Environment) (n : Name) : Option (Array Name × Option Name) := do
  let ci ← env.find? n
  let mut ds : Array Name := ci.type.getUsedConstants
  let mut ax : Option Name := none
  match ci with
  | .axiomInfo _ => ax := some n
  | .defnInfo v => ds := ds ++ v.value.getUsedConstants
  | .thmInfo v => ds := ds ++ v.value.getUsedConstants
  | .opaqueInfo v => ds := ds ++ v.value.getUsedConstants
  | .inductInfo v =>
    for m in v.all do
      if let some (.inductInfo mv) := env.find? m then
        ds := ds ++ mv.type.getUsedConstants
        for c in mv.ctors do
          if let some cci := env.find? c then ds := ds ++ cci.type.getUsedConstants
  | _ => pure ()
  let self := rep env n
  return (ds.map (rep env) |>.filter (· != self), ax)

/-- Exact axiom sets of all `roots`, as bit masks over the returned axiom names, by one
memoised explicit-stack post-order traversal (all state in local mutable variables, so the
interpreter updates the maps in place). Also returns missing names and back edges seen. -/
def axiomMasks (env : Environment) (roots : Array Name) :
    Std.HashMap Name Nat × Array Name × Array Name × Nat := Id.run do
  let mut memo : Std.HashMap Name Nat := {}
  let mut axNames : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut cycles := 0
  let mut inProg : Std.HashSet Name := {}
  -- frame: node, successors, next successor index, accumulated mask
  let mut stack : Array (Name × Array Name × Nat × Nat) := #[]
  for r0 in roots do
    let r := rep env r0
    if memo.contains r then continue
    stack := stack.push (r, #[], 0, 0)
    -- a frame with index 0 and no successors yet is expanded on first visit
    let mut fresh := true
    while h : stack.size > 0 do
      let (n, ds, i, m) := stack[stack.size - 1]
      if fresh then
        fresh := false
        match repDeps env n with
        | none =>
          missing := missing.push n
          memo := memo.insert n 0
          stack := stack.pop
          inProg := inProg.erase n
          continue
        | some (ds', ax) =>
          let mut m' := 0
          if let some a := ax then
            let idx := (axNames.idxOf? a).getD axNames.size
            if idx == axNames.size then axNames := axNames.push a
            m' := 1 <<< idx
          inProg := inProg.insert n
          stack := stack.set! (stack.size - 1) (n, ds', 0, m')
          continue
      if i < ds.size then
        let d := ds[i]!
        stack := stack.set! (stack.size - 1) (n, ds, i + 1, m)
        if let some dm := memo[d]? then
          stack := stack.set! (stack.size - 1) (n, ds, i + 1, m ||| dm)
        else if inProg.contains d then
          cycles := cycles + 1
        else
          stack := stack.push (d, #[], 0, 0)
          fresh := true
      else
        stack := stack.pop
        inProg := inProg.erase n
        memo := memo.insert n m
        if stack.size > 0 then
          let (pn, pds, pi, pm) := stack[stack.size - 1]!
          stack := stack.set! (stack.size - 1) (pn, pds, pi, pm ||| m)
  return (memo, axNames, missing, cycles)

def maskNames (axNames : Array Name) (m : Nat) : Array Name := Id.run do
  let mut r := #[]
  for h : i in [0:axNames.size] do
    if (m >>> i) % 2 == 1 then r := r.push axNames[i]
  return r.qsort Name.lt

/-! ## The checks -/

def checkOleans (env : Environment) (projDir : System.FilePath) : M Unit := do
  let sp ← searchPathRef.get
  let sysLib ← IO.FS.realPath ((← findSysroot) / "lib" / "lean")
  let projLib ← IO.FS.realPath (projDir / ".lake" / "build" / "lib" / "lean")
  let pkgsDir := projDir / ".lake" / "packages"
  let mut bad : Array String := #[]
  let mut pkgsUsed : Array String := #[]
  let mut tracked : Std.HashMap String (Std.HashSet String) := {}
  let mut nChecked := 0
  for m in env.header.moduleNames do
    let root := m.getRoot
    let some olean ← sp.findWithExt "olean" m | bad := bad.push s!"{m}: no .olean on LEAN_PATH"; continue
    unless ← olean.pathExists do bad := bad.push s!"{m}: {olean} does not exist"; continue
    let real ← IO.FS.realPath olean
    let rel := (modToFilePath "." m "olean").toString.drop 2 |>.toString
    nChecked := nChecked + 1
    if isProjectModule m then
      unless real.toString == (projLib / rel).toString do
        bad := bad.push s!"{m}: project module loaded from {real}"
      continue
    match packageOfRoot.lookup root with
    | none => bad := bad.push s!"{m}: module root {root} belongs to no pinned package"
    | some none =>
      unless real.toString == (sysLib / rel).toString do
        bad := bad.push s!"{m}: toolchain module loaded from {real}"
    | some (some pkg) =>
      let pkgReal ← IO.FS.realPath (pkgsDir / pkg)
      unless real.toString == (pkgReal / ".lake" / "build" / "lib" / "lean" / rel).toString do
        bad := bad.push s!"{m}: loaded from {real}, expected package {pkg}"
        continue
      unless pkgsUsed.contains pkg do
        pkgsUsed := pkgsUsed.push pkg
        let (rc, o) ← run "git" #["-C", pkgReal.toString, "ls-files"]
        if rc != 0 then bad := bad.push s!"package {pkg}: git ls-files failed: {o}"
        tracked := tracked.insert pkg (Std.HashSet.ofList (o.splitOn "\n"))
      let src := (modToFilePath "." m "lean").toString.drop 2 |>.toString
      unless (tracked[pkg]?.map (·.contains src)).getD false do
        bad := bad.push s!"{m}: source {src} is not tracked by git in package {pkg}"
  -- package revisions and clean worktrees
  let manifest ← IO.FS.readFile (projDir / "lake-manifest.json")
  let json ← IO.ofExcept (Json.parse manifest)
  let pkgs ← IO.ofExcept (json.getObjValAs? (Array Json) "packages")
  for pkg in pkgsUsed do
    let entry? := pkgs.find? fun p => (p.getObjValAs? String "name").toOption == some pkg
    let some entry := entry? | bad := bad.push s!"package {pkg} is not in lake-manifest.json"; continue
    let some rev := (entry.getObjValAs? String "rev").toOption | bad := bad.push s!"{pkg}: no rev"; continue
    let pkgReal ← IO.FS.realPath (pkgsDir / pkg)
    let (_, head) ← run "git" #["-C", pkgReal.toString, "rev-parse", "HEAD"]
    unless head.trimAscii.toString == rev do bad := bad.push s!"{pkg}: HEAD {head.trimAscii} ≠ manifest rev {rev}"
    let (rc, st) ← run "git" #["-C", pkgReal.toString, "status", "--porcelain", "--untracked-files=all"]
    unless rc == 0 && st.trimAscii.isEmpty do
      bad := bad.push s!"{pkg}: worktree not clean: {(st.splitOn "\n").take 5}"
  if bad.isEmpty then
    pass "oleans" s!"{nChecked} modules from their packages; packages {pkgsUsed} at manifest revs, clean"
  else
    for b in bad.toList.take 20 do fail "oleans" b
    if bad.size > 20 then fail "oleans" s!"… {bad.size - 20} more"

/-- Module of `n`; `mods` must be `env.header.moduleNames` (computed once: it is not cached). -/
def moduleOf (mods : Array Name) (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => mods[i.toNat]!

/-- The declarations of the in-scope (project) modules, each with the module's OWN stored
`ConstantInfo` (`constNames` zipped with `constants`), independent of `const2ModIdx` attribution
and of which copy `importModules` kept for a merged duplicate (trust2.opus N4, N6). -/
structure ProjDecls where
  /-- name ↦ every (module index, stored `ConstantInfo`) declaring it, in module order -/
  copies : Std.HashMap Name (Array (Nat × ConstantInfo)) := {}
  /-- all declared names, sorted, without repetition -/
  names : Array Name := #[]
  /-- per in-scope module index, the set of names it declares -/
  own : Std.HashMap Nat (Std.HashSet Name) := {}

def collectProjDecls (mods : Array Name) (env : Environment) (inScope : Name → Bool) : ProjDecls :=
  Id.run do
    let mut copies : Std.HashMap Name (Array (Nat × ConstantInfo)) := {}
    let mut own : Std.HashMap Nat (Std.HashSet Name) := {}
    for h : i in [0:env.header.moduleData.size] do
      unless inScope mods[i]! do continue
      let d := env.header.moduleData[i]
      let mut o : Std.HashSet Name := {}
      for h' : j in [0:d.constNames.size] do
        let n := d.constNames[j]
        let some ci := d.constants[j]? | continue
        copies := copies.insert n ((copies.getD n #[]).push (i, ci))
        o := o.insert n
      own := own.insert i o
    let names := copies.fold (init := #[]) fun acc n _ => acc.push n
    return { copies, own, names := names.qsort Name.lt }

/-- Every stored `ConstantInfo` of `n`: all project copies, else the environment's. -/
def ProjDecls.look (pd : ProjDecls) (env : Environment) (n : Name) : Array ConstantInfo :=
  match pd.copies[n]? with
  | some cs => cs.map (·.2)
  | none => (env.find? n).toArray

/-- May the copies of one name coexist? Only same-type theorems (what `importModules` merges and
Lean produces for realized `eq_N`/`congr_simp` lemmas); each copy is replayed separately. -/
def mergeableCopies (cs : Array (Nat × ConstantInfo)) : Bool :=
  match cs[0]?.map (·.2) with
  | some (ConstantInfo.thmInfo v0) => cs.all fun (_, ci) => match ci with
      | ConstantInfo.thmInfo v =>
        v.type == v0.type && v.levelParams == v0.levelParams && v.all == v0.all
      | _ => false
  | _ => false

/-- `fixed := false` (scan/solution modes) skips the four fixed provenance checks; `inScope` is the
predicate `pd` was collected with (the project modules, plus the Solution module in that mode). -/
def checkOrigins (mods : Array Name) (env : Environment) (o : Opts) (pd : ProjDecls)
    (fixed := true) (inScope : Name → Bool := isProjectModule) : M Unit := do
  let mut bad : Array String := #[]
  let fixedNames := if fixed then [(upstreamThm, upstreamModule), (cycleOrEdgeDef, upstreamModule),
                 (isDecompDef, decompModule), (finalThm, o.finalModule)] else []
  for (n, m) in fixedNames do
    unless moduleOf mods env n == some m do
      bad := bad.push s!"{n} comes from {moduleOf mods env n}, expected {m}"
  -- (1) no name is declared by a project module and by a non-project module
  let mut declaredElsewhere : Std.HashMap Name Name := {}
  for h : i in [0:env.header.moduleData.size] do
    if inScope mods[i]! then continue
    for n in env.header.moduleData[i].constNames do
      if pd.copies.contains n then declaredElsewhere := declaredElsewhere.insert n mods[i]!
  for (n, m') in declaredElsewhere.toList do
    bad := bad.push s!"project module(s) {(pd.copies.getD n #[]).map (mods[·.1]!)} re-declare {n}, \
      also declared by non-project module {m'}"
  -- (2) duplicates between project modules: only same-type theorems, never the four fixed names
  let mut dups : Array Name := #[]
  for n in pd.names do
    let cs := pd.copies.getD n #[]
    if cs.size < 2 then continue
    let where_ := cs.map (mods[·.1]!)
    if [upstreamThm, cycleOrEdgeDef, isDecompDef, finalThm].contains n then
      bad := bad.push s!"{n} is declared by several modules {where_}"
    else if mergeableCopies cs then dups := dups.push n
    else bad := bad.push s!"{n} is declared by several project modules {where_}, not all same-type theorems"
  -- (3) a project module's extraConstNames must not name a kernel constant it does not declare
  for h : i in [0:env.header.moduleData.size] do
    unless inScope mods[i]! do continue
    let own := pd.own.getD i {}
    for n in env.header.moduleData[i].extraConstNames do
      if env.constants.contains n && !own.contains n then
        bad := bad.push s!"{mods[i]!} lists kernel constant {n} in extraConstNames without declaring it"
  -- (4) attribution (const2ModIdx) must be a declaring module whenever a project module is involved
  for (n, idx) in env.const2ModIdx.toList do
    let i := idx.toNat
    let attrProj := inScope (mods[i]?.getD .anonymous)
    match pd.copies[n]? with
    | some cs =>
      unless cs.any (·.1 == i) do
        bad := bad.push s!"{n} (declared by {cs.map (mods[·.1]!)}) is attributed to {mods[i]?}"
    | none =>
      -- no project module declares `n`, yet it is attributed to one (e.g. a planted IR entry)
      if attrProj && env.constants.contains n then
        bad := bad.push s!"kernel constant {n} is attributed to project module {mods[i]!}, \
          which does not declare it"
  if bad.isEmpty then
    pass "origin" s!"{if fixed then s!"upstream names from the pinned modules; {finalThm} from {o.finalModule}; " else ""}\
      no package constant re-declared; attribution consistent; {dups.size} duplicate project \
      theorems (same type; every copy replayed): {dups.toList.take 8}"
  else
    for b in bad.toList.take 25 do fail "origin" b
    if bad.size > 25 then fail "origin" s!"… {bad.size - 25} more"

def checkKinds (env : Environment) : M Bool := do
  let mut ok := true
  for (n, k) in [(upstreamThm, "theorem"), (finalThm, "theorem"),
                 (cycleOrEdgeDef, "definition"), (isDecompDef, "definition")] do
    let good := match env.find? n, k with
      | some (.thmInfo _), "theorem" => true
      | some (.defnInfo _), "definition" => true
      | _, _ => false
    unless good do fail "kinds" s!"{n} is not a {k}"; ok := false
  if ok then pass "kinds" "both theorems are theorems, both upstream definitions are definitions"
  return ok

def checkStatement (env : Environment) : M Unit := do
  let (some a, some b) := (env.find? finalThm, env.find? upstreamThm)
    | fail "statement" "a theorem is missing"
  unless a.levelParams.length == b.levelParams.length do
    fail "statement" s!"universe parameter counts differ: {a.levelParams} vs {b.levelParams}"
    return
  let bty := b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param)
  if a.type.equal bty then
    pass "statement" s!"type of {finalThm} is Expr.equal to that of {upstreamThm} \
      (universes {a.levelParams} ↔ {b.levelParams})"
  else
    fail "statement" s!"type of {finalThm} differs from {upstreamThm} \
      (up to binder names/annotations: {if a.type == bty then "equal" else "different"})"

def checkAxioms (env : Environment) (pd : ProjDecls) (o : Opts) (root : Name) : M Unit := do
  let label := "importModules environment, every stored copy"
  let (axs, missing, visited) := reachableAxioms (pd.look env) root
  unless missing.isEmpty do fail "axioms" s!"{root} refers to missing constants {missing.toList.take 5}"
  let other := axs.filter (· != sorryAxName)
  let exact := other.size == allowedAxioms.size && allowedAxioms.all other.contains
  if exact then
    pass "axioms" s!"{root} ({label}; {visited} constants visited) depends on exactly {other}"
  else
    fail "axioms" s!"{root} ({label}) depends on {other}, expected exactly {allowedAxioms}"
  if axs.contains sorryAxName then
    if o.allowSorry then warn "axioms" s!"{root} depends on sorryAx (--allow-sorry)"
    else fail "axioms" s!"{root} depends on sorryAx"
  -- cross-check with Lean's own collectAxioms (it follows only the copy importModules kept)
  try
    let l ← (collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<finalcheck>", fileMap := default } { env }
    if l.qsort Name.lt == axs then pass "axioms" s!"Lean's collectAxioms agrees"
    else fail "axioms" s!"Lean's collectAxioms gives {l.qsort Name.lt}, own traversal gives {axs}"
  catch e => fail "axioms" s!"Lean's collectAxioms threw: {e}"

def checkPolicy (mods : Array Name) (env : Environment) (o : Opts) (pd : ProjDecls) : M Unit := do
  let consts := pd.names
  let (memo, axNames, missing, cycles) := axiomMasks env consts
  let mut bad : Array String := #[]
  let mut sorryUsers : Array Name := #[]
  -- the masks follow the copy importModules kept; every other stored copy of a duplicated
  -- theorem is walked here separately
  for n in consts do
    let cs := pd.copies.getD n #[]
    if cs.size < 2 then continue
    let (axs, _, _) := reachableAxioms (pd.look env) n
    for a in axs do
      unless allowedAxioms.contains a || (a == sorryAxName && o.allowSorry) do
        bad := bad.push s!"{n} (copies in {cs.map (mods[·.1]!)}): axiom {a}"
    for (i, ci) in cs do
      if ci.isUnsafe then bad := bad.push s!"{n} ({mods[i]!}): unsafe copy"
  for n in consts do
    let some ci := env.find? n | continue
    let axs := maskNames axNames (memo[rep env n]?.getD 0)
    let mut reasons : Array String := #[]
    for a in axs do
      unless allowedAxioms.contains a || a == sorryAxName do reasons := reasons.push s!"axiom {a}"
    if axs.contains sorryAxName then
      sorryUsers := sorryUsers.push n
      unless o.allowSorry do reasons := reasons.push "uses sorryAx"
    if (pd.look env n).any (· matches .axiomInfo _) then reasons := reasons.push "declares an axiom"
    if ci.isUnsafe then reasons := reasons.push "unsafe"
    if isExtern env n then reasons := reasons.push "@[extern]"
    if (Compiler.implementedByAttr.getParam? env n).isSome then reasons := reasons.push "@[implemented_by]"
    if hasInitAttr env n then reasons := reasons.push "@[init]"
    unless reasons.isEmpty do
      bad := bad.push s!"{n} ({(pd.copies.getD n #[]).map (mods[·.1]!)}): {", ".intercalate reasons.toList}"
  unless missing.isEmpty do
    fail "policy" s!"references to missing constants: {missing.toList.take 5}"
  if bad.isEmpty then
    pass "policy" s!"{consts.size} project constants: axioms ⊆ {allowedAxioms}\
      {if o.allowSorry then " + sorryAx" else ""}, no axiom/unsafe/extern/implemented_by/init"
  else
    for b in bad.toList.take 25 do fail "policy" b
    if bad.size > 25 then fail "policy" s!"… {bad.size - 25} more"
  unless sorryUsers.isEmpty do
    (if o.allowSorry then warn else fail) "policy"
      s!"{sorryUsers.size} project constants use sorryAx, e.g. {sorryUsers.toList.take 5}"
  if cycles > 0 then warn "policy" s!"{cycles} dependency cycles outside inductive blocks"

def checkMeta (mods : Array Name) (env : Environment) (pd : ProjDecls) : M Unit := do
  let consts := pd.names
  let mut hits : Array String := #[]
  for n in consts do
    for ci in pd.look env n do
      let used := ci.type.getUsedConstants.filter fun u => metaHeads.any (·.isPrefixOf u)
      unless used.isEmpty do
        hits := hits.push s!"{n} ({(pd.copies.getD n #[]).map (mods[·.1]!)}) : mentions {used.toList.take 3}"
  if hits.isEmpty then pass "meta" s!"no meta-level constant among {consts.size} project constants"
  else
    for h in hits.toList.take 25 do fail "meta" h
    if hits.size > 25 then fail "meta" s!"… {hits.size - 25} more"

/-- Prefix under which the project constants are replayed (see `checkReplay`). -/
def replayPrefix : Name := `_egFinalCheckReplay

/-- Rename every reference to a project constant (constants and structure projections). -/
partial def renameExpr (proj : Std.HashSet Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => if proj.contains n then some (.const (replayPrefix ++ n) ls) else none
    | .proj s i b =>
      if proj.contains s then some (.proj (replayPrefix ++ s) i (renameExpr proj b)) else none
    | _ => none

def renameConst (proj : Std.HashSet Name) (ci : ConstantInfo) : ConstantInfo :=
  let rn (n : Name) := if proj.contains n then replayPrefix ++ n else n
  let re := renameExpr proj
  match ci with
  | .axiomInfo v => .axiomInfo { v with name := rn v.name, type := re v.type }
  | .defnInfo v => .defnInfo { v with name := rn v.name, type := re v.type, value := re v.value,
                                       all := v.all.map rn }
  | .thmInfo v => .thmInfo { v with name := rn v.name, type := re v.type, value := re v.value,
                                     all := v.all.map rn }
  | .opaqueInfo v => .opaqueInfo { v with name := rn v.name, type := re v.type,
                                           value := re v.value, all := v.all.map rn }
  | .quotInfo v => .quotInfo { v with name := rn v.name, type := re v.type }
  | .inductInfo v => .inductInfo { v with name := rn v.name, type := re v.type,
                                           all := v.all.map rn, ctors := v.ctors.map rn }
  | .ctorInfo v => .ctorInfo { v with name := rn v.name, type := re v.type, induct := rn v.induct }
  | .recInfo v =>
    let rules := v.rules.map fun r => { r with ctor := rn r.ctor, rhs := re r.rhs }
    .recInfo { v with name := rn v.name, type := re v.type, all := v.all.map rn, rules := rules }

/-- Does a (renamed) declaration still refer to an original project constant? -/
def mentionsProject (proj : Std.HashSet Name) (ci : ConstantInfo) : Bool :=
  let bad (e : Expr) : Bool := (e.find? fun
      | .const n _ => proj.contains n
      | .proj s .. => proj.contains s
      | _ => false).isSome
  bad ci.type || match ci with
    | .defnInfo v => bad v.value || v.all.any proj.contains
    | .thmInfo v => bad v.value || v.all.any proj.contains
    | .opaqueInfo v => bad v.value || v.all.any proj.contains
    | .recInfo v => v.rules.any (fun r => bad r.rhs || proj.contains r.ctor) || v.all.any proj.contains
    | .inductInfo v => v.ctors.any proj.contains || v.all.any proj.contains
    | .ctorInfo v => proj.contains v.induct
    | _ => false

/-- Prefix under which the 2nd, 3rd, … stored copies of a duplicated project theorem are replayed
(`_egFinalCheckCopy.<k>.<name>`). Nothing refers to these names; they exist only so that every
copy is kernel-checked. -/
def copyPrefix : Name := `_egFinalCheckCopy

/-- Kernel replay of every declaration of every project module, from the module's OWN stored
`ConstantInfo` (trust2.opus N4: no `const2ModIdx` filter, so a name whose attribution was stolen
through `extraConstNames` is still replayed; N6: every copy of a merged duplicate theorem is
replayed). The constants are re-checked **renamed** (every reference to a project constant `n`
becomes `_egFinalCheckReplay.n`; the first copy in module order is that constant, further copies are
replayed as `_egFinalCheckCopy.<k>.n`) inside the imported environment, so the already imported,
unchecked originals can neither clash nor be used: a renamed declaration only refers to renamed
(hence replayed) constants and to package constants. This needs a single `importModules` (a second
import of the same `.olean`s cannot be memory-mapped again and would double the memory).

By design `Environment.replay` skips `unsafe` and `partial` constants (the kernel cannot check
them); a replayed constant referring to a skipped one fails with an unknown constant, so skipped
constants are unusable by anything replayed. -/
def checkReplay (env : Environment) (pd : ProjDecls) : M Bool := do
  let t0 ← IO.monoMsNow
  let proj : Std.HashSet Name := Std.HashSet.ofArray pd.names
  if env.constants.map₁.fold (init := false)
      (fun acc n _ => acc || replayPrefix.isPrefixOf n || copyPrefix.isPrefixOf n) then
    fail "replay" s!"the environment already contains names under {replayPrefix} or {copyPrefix}"
    return false
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut skipped : Array Name := #[]
  let mut leaks : Array Name := #[]
  let mut nCopies := 0
  for n in pd.names do
    let cs := pd.copies.getD n #[]
    for h : k in [0:cs.size] do
      let ci := cs[k].2
      let ci' := renameConst proj ci
      if mentionsProject proj ci' then leaks := leaks.push n
      let mut ci' := ci'
      if k > 0 then
        let .thmInfo v := ci'
          | fail "replay" s!"{n}: a non-theorem copy cannot be replayed"; return false
        let nm := (Name.mkNum copyPrefix k) ++ n
        nCopies := nCopies + 1
        ci' := .thmInfo { v with name := nm, all := [nm] }
      if newConsts.contains ci'.name then
        fail "replay" s!"two project declarations map to {ci'.name}"; return false
      newConsts := newConsts.insert ci'.name ci'
      if ci.isUnsafe || ci.isPartial then skipped := skipped.push n
  unless leaks.isEmpty do
    fail "replay" s!"renaming left references to original project constants in {leaks.toList.take 5}"
    return false
  try
    let _ ← env.replay newConsts
    let t1 ← IO.monoMsNow
    pass "replay" s!"kernel re-checked {newConsts.size - skipped.size} project declarations \
      ({nCopies} extra copies of duplicated theorems) from each declaring module's own \
      ConstantInfo, on top of the package modules ({(t1 - t0) / 1000} s); {skipped.size} \
      unsafe/partial constants skipped by design, hence unusable by any replayed constant: \
      {skipped.toList.take 5}"
    return true
  catch e =>
    fail "replay" s!"kernel rejected a project constant: {(toString e).take 700}"
    return false

def checkPin (env : Environment) (o : Opts) (root : Name := upstreamThm) : M Unit := do
  let (d?, missing) := Canon.dumps env root
  unless missing.isEmpty do fail "pin" s!"closure refers to missing constants {missing.toList.take 5}"
  let some (stmt, clos) := d? | fail "pin" s!"{root} not found"
  if let some dir := o.dumpCanon then
    IO.FS.createDirAll dir
    IO.FS.writeFile (System.FilePath.mk dir / "statement.canon") stmt
    IO.FS.writeFile (System.FilePath.mk dir / "closure.canon") clos
  let hs ← sha256 stmt
  let hc ← sha256 clos
  let nConsts := (clos.splitOn "\n").length - 1
  let pins ← readPins o.pinFile
  for (key, computed, override) in [("statement-sha256", hs, o.expectStmt),
                                     ("closure-sha256", hc, o.expectClosure)] do
    let expected ← match override with
      | some v => pure (some v)
      | none => match pinValue pins key with
        | .ok v => pure v
        | .error e => do fail "pin" e; pure none
    match expected with
    | none =>
      (if o.allowUnpinned then warn else fail) "pin"
        s!"no {key} pin (in {o.pinFile} or on the command line); computed {computed}"
    | some v =>
      if !isHex64 v then fail "pin" s!"{key} pin '{v}' is not a SHA-256"
      else if v == computed then pass "pin" s!"{key} = {computed}{if key == "closure-sha256" then s!" ({nConsts} constants)" else ""}"
      else fail "pin" s!"{key}: computed {computed}, pinned {v}"

def checkLean (o : Opts) : M Unit := do
  let pins ← readPins o.pinFile
  match (match o.expectLeanGithash with | some v => Except.ok (some v) | none => pinValue pins "lean-githash") with
  | .error e => fail "lean" e
  | .ok none =>
    (if o.allowUnpinned then warn else fail) "lean" s!"no lean-githash pin; running {Lean.githash}"
  | .ok (some v) =>
    if v == Lean.githash then pass "lean" s!"running Lean {Lean.versionString} ({Lean.githash})"
    else fail "lean" s!"running Lean {Lean.githash}, pinned {v}"

/-- Comparator Solution layout (coordinate via `formal/work/trust/bridge.md`): the Solution module
restates `Erdos184.erdos_184` (and `IsCycleOrEdge`) VERBATIM and does NOT import
`FormalConjectures.ErdosProblems.«184»`, so there is no upstream to `Expr.equal` against and no
import clash. Instead the restated statement is pinned by its canonical hash (which equals the
upstream `statement-sha256`/`closure-sha256`, since it restates the same Mathlib definitions), and
its axioms, replay, policy and meta are checked. Comparator itself does the Challenge-vs-Solution
comparison; this is the axiom/pin/replay half. UNTESTED until the Solution module exists. -/
def solutionM (o : Opts) (solMod : Name) : M Unit := do
  IO.println s!"FinalCheck --solution-module {solMod}: restated {o.restatedThm}"
  checkLean o
  initSearchPath (← findSysroot)
  let env ← try importModules #[{ module := solMod }] {} (trustLevel := 0)
    catch e => fail "import" s!"importModules #[{solMod}] failed: {e}"; return
  let mods := env.header.moduleNames
  pass "import" s!"#[{solMod}] ({mods.size} modules, no imported code run; upstream NOT imported)"
  -- the restated theorem must live in the Solution module and be a theorem
  match moduleOf mods env o.restatedThm with
  | some m => unless m == solMod do fail "origin" s!"{o.restatedThm} comes from {m}, expected {solMod}"
  | none => fail "origin" s!"{o.restatedThm} not found"
  unless (env.find? o.restatedThm matches some (.thmInfo _)) do
    fail "kinds" s!"{o.restatedThm} is not a theorem"
  -- in-scope constants: the Solution module itself plus the project modules it imports (EG*/EGCheck*)
  let inScope (m : Name) : Bool := m == solMod || isProjectModule m
  let pd := collectProjDecls mods env inScope
  progress "declarations"; checkOrigins mods env o pd (fixed := false) (inScope := inScope)
  progress "replay"
  let _ ← if o.replay then checkReplay env pd else do warn "replay" "skipped"; pure false
  progress "axioms"; checkAxioms env pd o o.restatedThm
  progress "policy"; checkPolicy mods env o pd
  progress "meta"; checkMeta mods env pd
  -- statement equality for the verbatim-restated Solution is comparator's job (eqv against the
  -- byte-identical Challenge); the binder-sensitive statement/closure pins do not apply here
  -- because a verbatim restatement gets different hygienic instance-binder names. Provenance of the
  -- Solution module (built from the byte-identical Challenge) is likewise comparator's job.
  IO.println "note: statement equality and Solution provenance for the comparator layout are checked \
by comparator (Challenge byte-identity + eqv + sandboxed build), not here"
  progress "done"

/-- Scan an arbitrary set of project modules (no final theorem, no upstream): kernel replay,
axiom/attribute policy and the meta-type check. Used by `scripts/redteam.sh` for the lint-evasion
fixtures. -/
def scanM (o : Opts) : M Unit := do
  IO.println s!"FinalCheck --scan-only: modules {o.policyRoots}"
  initSearchPath (← findSysroot)
  let env ← try
      importModules (o.policyRoots.map fun m => { module := m }) {} (trustLevel := 0)
    catch e => fail "import" s!"importModules {o.policyRoots} failed: {e}"; return
  let mods := env.header.moduleNames
  pass "import" s!"{o.policyRoots} ({mods.size} modules, no imported code run)"
  progress "oleans"
  checkOleans env "."
  progress "project declarations"
  let pd := collectProjDecls mods env isProjectModule
  checkOrigins mods env o pd (fixed := false)
  let _ ← if o.replay then checkReplay env pd else do warn "replay" "skipped"; pure false
  progress "policy"
  checkPolicy mods env o pd
  progress "meta"
  checkMeta mods env pd
  progress "done"

def mainM (o : Opts) : M Unit := do
  IO.println s!"FinalCheck (out-of-band): final theorem {finalThm} in {o.finalModule}; \
    upstream {upstreamThm} in {upstreamModule}"
  checkLean o
  initSearchPath (← findSysroot)
  let projDir : System.FilePath := "."
  let imports := #[upstreamModule, o.finalModule] ++ o.policyRoots
  let env ← try
      importModules (imports.map fun m => { module := m }) {} (trustLevel := 0)
    catch e =>
      fail "import" s!"importModules {imports} failed: {e}"
      return
  let mods := env.header.moduleNames
  pass "import" s!"{imports} ({mods.size} modules, no imported code run)"
  progress "oleans"
  checkOleans env projDir
  progress "project declarations / origins"
  -- every declaration of every project module, from the module's own ConstantInfo (N4)
  let pd := collectProjDecls mods env isProjectModule
  checkOrigins mods env o pd
  progress "replay"
  let _ ← if o.replay then checkReplay env pd else do
    warn "replay" "skipped (--no-replay)"; pure false
  -- statement and axioms on the importModules environment (every stored copy followed)
  progress "kinds/statement/axioms"
  if ← checkKinds env then
    checkStatement env
    checkAxioms env pd o finalThm
  progress "policy"
  checkPolicy mods env o pd
  progress "meta"
  checkMeta mods env pd
  progress "pin"
  checkPin env o
  progress "done"

end EGFinalCheck

open EGFinalCheck in
def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  unless o.bad.isEmpty do
    IO.eprintln s!"unknown arguments {o.bad}; see the header of scripts/FinalCheck.lean"
    return 2
  let (_, r) ← (match o.solutionModule, o.scanOnly with
    | some m, _ => solutionM o m
    | none, true => scanM o
    | none, false => mainM o).run {}
  IO.println s!"FINALCHECK: {if r.fails == 0 then "PASS" else "FAIL"} \
    ({r.fails} failures, {r.warns} warnings)"
  return (if r.fails == 0 then 0 else 1)
