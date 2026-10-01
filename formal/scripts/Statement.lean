import Lean
open Lean

/-!
# `scripts/Statement.lean` — generate `STATEMENT.md` (the statement a reader actually trusts)

Usage (from `formal/`):

    lake env lean --run scripts/Statement.lean [OUTPUT.md]     # default: STATEMENT.md

Imports **only** `FormalConjectures.ErdosProblems.«184»` (no project module), with
`loadExts := false`, so no imported elaborator, delaborator or initializer runs; the `pp.all`
output uses the delaborators built into the pinned Lean binary only.

`STATEMENT.md` contains, for `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge` and
`SimpleGraph.IsDecomposition`: the `pp.all` form, the constants used (grouped by module), the
closure of the statement grouped by package and module, and two SHA-256 pins (computed by
`sha256sum`):

* `statement-sha256`: canonical serialisation of the declaration `Erdos184.erdos_184`;
* `closure-sha256`: canonical serialisation of every declaration the statement depends on
  (types; bodies of definitions; inductive declarations and constructors; not theorem proofs).

The canonical serialisation between `BEGIN CANON` and `END CANON` is byte-identical with the one
in `scripts/FinalCheck.lean`, which recomputes both hashes and compares them with the
`EG-PIN statement-sha256` / `EG-PIN closure-sha256` lines of `TRUST.md` (`scripts/redteam.sh`
checks that the two blocks are identical). Also printed, for cross-reference with the trust audit
of 2026-09-26: the SHA-256 of `Expr.dbgToString` of the statement's type (no trailing newline).
-/

namespace EGStatement

def upstreamModule : Name := `FormalConjectures.ErdosProblems.«184»
def upstreamThm : Name := `Erdos184.erdos_184
def shown : Array Name := #[`Erdos184.erdos_184, `Erdos184.IsCycleOrEdge, `SimpleGraph.IsDecomposition]

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

def sha256 (data : String) : IO String := do
  IO.FS.withTempFile fun h path => do
    h.putStr data
    h.flush
    let o ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
    if o.exitCode != 0 then throw <| IO.userError s!"sha256sum failed: {o.stderr}"
    return (o.stdout.splitOn " ").headD ""

def manifestRev (pkg : String) : IO String := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let pkgs ← IO.ofExcept (json.getObjValAs? (Array Json) "packages")
  let some e := pkgs.find? fun p => (p.getObjValAs? String "name").toOption == some pkg
    | return "?"
  return (e.getObjValAs? String "rev").toOption.getD "?"

def ppAll (env : Environment) (e : Expr) : IO String := do
  let opts : Options := ({} : Options) |>.setBool `pp.all true |>.insert `format.width (.ofNat 100)
  try
    let (fmt, _, _) ← (PrettyPrinter.ppExpr e).toIO
      { fileName := "<statement>", fileMap := default, options := opts } { env }
    return fmt.pretty 100
  catch ex => return s!"(pretty-printer failed: {ex}; Expr.dbgToString follows)\n{e.dbgToString}"

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def main (args : List String) : IO UInt32 := do
  let outPath := args.headD "STATEMENT.md"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := upstreamModule }] {} (trustLevel := 0)
  let mods := env.header.moduleNames
  let modOf (n : Name) : Name := ((env.getModuleIdxFor? n).map fun i => mods[i.toNat]!).getD `«?»
  let (some (stmt, clos), missing) := Canon.dumps env upstreamThm
    | IO.eprintln s!"{upstreamThm} not found"; return 1
  unless missing.isEmpty do
    IO.eprintln s!"closure refers to missing constants {missing}"; return 1
  let (closNames, _) := Canon.closure env upstreamThm
  let hs ← sha256 stmt
  let hc ← sha256 clos
  let some stmtCi := env.find? upstreamThm | return 1
  let hd ← sha256 stmtCi.type.dbgToString
  let fc ← manifestRev "formal_conjectures"
  let ml ← manifestRev "mathlib"
  let mut md := ""
  md := md ++ s!"# STATEMENT.md — the elaborated target statement (GENERATED, do not edit)\n\n"
  md := md ++ "Generated by `lake env lean --run scripts/Statement.lean` from the pinned build: only " ++
    "`FormalConjectures.ErdosProblems.«184»` is imported (no project code; no imported elaborator, " ++
    "delaborator or initializer runs). This is the statement, and the definitions it unfolds to, " ++
    "that `scripts/FinalCheck.lean` pins. See `TRUST.md`.\n\n"
  md := md ++ s!"* Lean: `{Lean.versionString}`, commit `{Lean.githash}`\n"
  md := md ++ s!"* formal-conjectures (lake-manifest.json): `{fc}`\n"
  md := md ++ s!"* Mathlib (lake-manifest.json): `{ml}`\n\n"
  md := md ++ "## Pins\n\n"
  md := md ++ "Canonical serialisation (`BEGIN CANON` block of `scripts/Statement.lean` / " ++
    "`scripts/FinalCheck.lean`), hashed with `sha256sum`:\n\n"
  md := md ++ s!"    EG-PIN lean-githash {Lean.githash}\n"
  md := md ++ s!"    EG-PIN statement-sha256 {hs}\n"
  md := md ++ s!"    EG-PIN closure-sha256 {hc}\n\n"
  md := md ++ s!"* closure: {closNames.size} declarations (types of all; bodies of definitions; " ++
    "inductive declarations with their constructors; no theorem proofs)\n"
  md := md ++ s!"* SHA-256 of `Expr.dbgToString` of the type of `{upstreamThm}` (no trailing " ++
    s!"newline), for cross-reference with the trust audit of 2026-09-26: `{hd}`\n\n"
  md := md ++ "## `pp.all` forms\n\n"
  for n in shown do
    let some ci := env.find? n | md := md ++ s!"`{n}`: NOT FOUND\n\n"; continue
    md := md ++ s!"### `{n}` ({kindOf ci}, universe parameters {ci.levelParams}, module `{modOf n}`)\n\n"
    md := md ++ "Type:\n\n```\n" ++ (← ppAll env ci.type) ++ "\n```\n\n"
    if let .defnInfo v := ci then
      md := md ++ "Body:\n\n```\n" ++ (← ppAll env v.value) ++ "\n```\n\n"
    -- constants used by the shown declaration (type and, for definitions, body)
    let used := (ci.type.getUsedConstants ++ (match ci with
      | .defnInfo v => v.value.getUsedConstants | _ => #[])).foldl
        (fun acc c => if acc.contains c then acc else acc.push c) #[]
    let mut byMod : Std.HashMap Name (Array Name) := {}
    for c in used do byMod := byMod.insert (modOf c) ((byMod.getD (modOf c) #[]).push c)
    md := md ++ s!"Constants used ({used.size}), by module:\n\n"
    for (m, cs) in byMod.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
      md := md ++ s!"* `{m}`: " ++ ", ".intercalate ((cs.qsort fun a b => a.toString < b.toString).toList.map (s!"`{·}`")) ++ "\n"
    md := md ++ "\n"
  -- closure grouped by package root and module
  let mut byRoot : Std.HashMap Name Nat := {}
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for c in closNames do
    let m := modOf c
    byRoot := byRoot.insert m.getRoot (byRoot.getD m.getRoot 0 + 1)
    byMod := byMod.insert m ((byMod.getD m #[]).push c)
  md := md ++ s!"## Closure of the statement ({closNames.size} declarations)\n\n"
  md := md ++ "By package (module-name root):\n\n"
  for (r, k) in byRoot.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    md := md ++ s!"* `{r}`: {k}\n"
  md := md ++ "\nEvery declaration outside `Init`/`Std`/`Lean`/`Mathlib`, and its module:\n\n"
  for (m, cs) in byMod.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    unless [`Init, `Std, `Lean, `Mathlib].contains m.getRoot do
      md := md ++ s!"* `{m}`: " ++ ", ".intercalate ((cs.qsort fun a b => a.toString < b.toString).toList.map (s!"`{·}`")) ++ "\n"
  md := md ++ s!"\n<details><summary>All {closNames.size} declarations by module ({byMod.size} modules)</summary>\n\n"
  for (m, cs) in byMod.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    md := md ++ s!"* `{m}`: " ++ ", ".intercalate ((cs.qsort fun a b => a.toString < b.toString).toList.map (s!"`{·}`")) ++ "\n"
  md := md ++ "\n</details>\n"
  IO.FS.writeFile outPath md
  IO.println s!"wrote {outPath}: statement-sha256 {hs}, closure-sha256 {hc} ({closNames.size} declarations)"
  return 0

end EGStatement

def main (args : List String) : IO UInt32 := EGStatement.main args
