import Lean

/-!
# Axiom / trust scan (PLAN_FORMALIZATION.md §4 `axiomcheck`, §8 Q2)

Usage (from `formal/`, after `lake build` of the modules):

    lake env lean --run scripts/Axioms.lean [--prefix P]... [--no-sorry] [--json] [--cross-check] Module...

Imports `Module...` with `importModules` (no imported elaborator, macro, initializer or
environment-extension code runs: extensions are not loaded, `loadExts := false`) and inspects
every constant declared in a module whose name has one of the prefixes `P` (default: `EG`).

## Axiom policy (per inspected constant)

The axioms a constant depends on are computed by an independent walk over the kernel
`ConstantInfo`s of the loaded environment (types and values of every reachable constant; an
inductive type together with its constructors). The walk does not consult the per-module axiom
tables that `#print axioms` / `collectAxioms` read from `.olean` files (`exportedAxiomsExt`), so a
tampered table cannot hide an axiom. `--cross-check` additionally runs Lean's `collectAxioms`
and reports any axiom it finds that the walk missed (should never happen; slow).

A constant is a violation if it
* depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` (and `sorryAx`,
  which is only rejected with `--no-sorry`), or on a constant missing from the environment,
* is itself an `axiom`, is `unsafe`, or carries `@[extern]` / `@[implemented_by]` / `@[export]`.

## MetaScan (lint-independent; always on)

Code in an imported module can change what the in-band checks of `EGCheck/Final.lean` mean
(`@[command_elab]`/`@[term_elab]`/`@[macro]` overrides, `initialize`, kernel bypass via
`#eval`/`elab`; APPROVALS/reviews/trust.*.md). The proof needs none of this, so every such trace
left in an inspected module is a violation:
* a constant whose *type* (or, for a definition, whose *value*) mentions a meta-level type or
  namespace (`metaHeads` below: `Lean.Elab`, `Lean.Meta`, `Lean.Macro`, `Lean.Syntax`,
  `Lean.Parser`, `Lean.ParserDescr`, `IO`, `EIO`, `BaseIO`, `Lean.Environment`, `Lean.CoreM`,
  `Lean.Expr`, `Lean.Declaration`, `Lean.Kernel`, ...);
* a constant marked `meta` (module system) or registered as an initializer (`[init]`,
  `[builtin_init]`, i.e. `initialize` / `builtin_initialize`);
* a module whose `.olean` carries entries of a meta-level environment extension
  (`deniedExts` below: command/term/tactic elaborators, macros, parsers/`syntax`, delaborators,
  initializers, `[csimp]`, `[implemented_by]`, `[extern]`, `[export]`, simprocs, `meta`
  declarations, server/widget hooks). This also catches `attribute [...]` applied to constants
  declared elsewhere;
* a module with a `meta import` (other than the implicit `Init`), or an `EG*`/`EGTest*` module
  importing `FormalConjectures*` directly (only `EGCheck*` may);
* a constant declared in a namespace reserved for the upstream statement (`Erdos184`,
  `FormalConjectures*`, `SimpleGraph.IsDecomposition`), or with an `Erdos184` name component.

What this scan cannot see: effects of code that ran at build time and left nothing in the
environment (`#eval` writing files, `run_tac` + kernel bypass leaving an ill-typed but
meta-free constant). Those are caught by `lint.py` (hygiene) and, as the actual guarantee, by
kernel replay (`leanchecker`) and comparator; see TRUST.md.

Output: one line per constant that uses `sorryAx` (the sorry frontier), `VIOLATION ...` lines on
stderr, and a summary line. With `--json`, one JSON object per inspected constant instead
(`name`, `module`, `kind`, `sorry`, `axioms`, `violations`, `reasons`); module-level violations
still go to stderr. Exit code: 0 clean, 1 violations, 2 usage/internal error.
-/

open Lean

namespace EGAxioms

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- MetaScan: a constant whose type (or definition value) uses a constant with one of these
name prefixes (component-wise) is meta-level code. -/
def metaHeads : List Name :=
  [`Lean.Elab, `Lean.Meta, `Lean.Macro, `Lean.MacroM, `Lean.Syntax, `Lean.TSyntax,
   `Lean.Parser, `Lean.ParserDescr, `Lean.TrailingParserDescr, `Lean.PrettyPrinter,
   `IO, `EIO, `BaseIO, `ST, `EStateM, `unsafeIO, `unsafeBaseIO, `unsafeEIO,
   `Lean.Environment, `Lean.Kernel, `Lean.Core, `Lean.CoreM, `Lean.Expr, `Lean.Declaration,
   `Lean.ConstantInfo, `Lean.Options, `Lean.KVMap, `Lean.MessageData, `Lean.Exception,
   `Lean.EnvExtension, `Lean.PersistentEnvExtension, `Lean.SimplePersistentEnvExtension,
   `Lean.ScopedEnvExtension, `Lean.KeyedDeclsAttribute, `Lean.AttributeImpl, `Lean.AttrM,
   `Lean.ImportM, `Lean.Compiler, `Lean.IR, `Lean.Server, `Lean.Widget, `Lean.Linter]

/-- Environment extensions whose entries in an inspected module mean meta-level code or
compiler overrides. Each name must be registered in this toolchain (checked at start-up, so a
renamed extension fails closed instead of being silently skipped). -/
def deniedExts : List (Name × String) :=
  [(`Lean.Elab.Command.commandElabAttribute, "command elaborator (@[command_elab], elab)"),
   (`Lean.Elab.Term.termElabAttribute, "term elaborator (@[term_elab], elab)"),
   (`Lean.Elab.Tactic.tacticElabAttribute, "tactic elaborator (@[tactic], elab)"),
   (`Lean.Elab.macroAttribute, "macro (@[macro], macro, macro_rules, notation)"),
   (`Lean.Elab.Do.doElemElabAttribute, "do-element elaborator"),
   (`Lean.Elab.Do.controlInfoElemAttribute, "do-element elaborator"),
   (`Lean.Elab.Command.inductiveElabAttr, "inductive elaborator"),
   (`Lean.Elab.Term.Quotation.precheckAttribute, "quotation precheck hook"),
   (`Lean.Elab.Tactic.Grind.grindTacElabAttribute, "grind tactic elaborator"),
   (`Lean.Elab.Tactic.Grind.symSimprocElabAttribute, "grind simproc elaborator"),
   (`Lean.Elab.Tactic.Grind.symDischargerElabAttribute, "grind discharger elaborator"),
   (`Lean.Elab.Tactic.Grind.symDSimprocElabAttribute, "grind dsimproc elaborator"),
   (`Lean.Elab.Tactic.Try.tryTacticElabAttribute, "try? tactic elaborator"),
   (`Lean.Parser.parserExtension, "syntax / parser (syntax, notation, declare_syntax_cat)"),
   (`Lean.PrettyPrinter.Delaborator.delabAttribute, "delaborator (@[delab])"),
   (`Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute, "unexpander (@[app_unexpander])"),
   (`Lean.regularInitAttr, "initializer (@[init], initialize)"),
   (`Lean.builtinInitAttr, "initializer (@[builtin_init], builtin_initialize)"),
   (`Lean.Compiler.CSimp.ext, "@[csimp]"),
   (`Lean.Compiler.implementedByAttr, "@[implemented_by]"),
   (`Lean.externAttr, "@[extern]"),
   (`Lean.exportAttr, "@[export]"),
   (`Lean.Meta.Simp.simprocDeclExt, "simproc declaration"),
   (`Lean.Meta.Simp.simprocExtension, "simproc registration"),
   (`Lean.Meta.Simp.simprocSEvalExtension, "simproc registration"),
   (`Lean.Meta.Tactic.Cbv.cbvSimprocDeclExt, "cbv simproc declaration"),
   (`cbvSimprocExt, "cbv simproc registration"),
   (`Lean.Server.codeActionProviderExt, "code action provider"),
   (`Lean.CodeAction.holeCodeActionExt, "code action provider"),
   (`Lean.CodeAction.cmdCodeActionExt, "code action provider"),
   (`Lean.Server.userRpcProcedures, "RPC procedure")]

/-- Private extensions of the module system's `meta` marker (matched by the last name
component, since private names cannot be written down). -/
def deniedPrivateExtSuffixes : List (String × String) :=
  [("metaExt", "meta definition (module system)"),
   ("declMetaExt", "meta definition (module system)"),
   ("moduleRegistry", "widget module"),
   ("panelWidgetsExt", "widget panel")]

/-- Namespaces reserved for the upstream statement: a project constant there could shadow or
fake the target (trust review attack C). -/
def reservedNames : List Name :=
  [`Erdos184, `FormalConjectures, `FormalConjecturesForMathlib, `FormalConjecturesUtil,
   `SimpleGraph.IsDecomposition]

structure Opts where
  prefixes : Array Name := #[]
  noSorry : Bool := false
  json : Bool := false
  crossCheck : Bool := false
  modules : Array Name := #[]

partial def parseArgs : List String → Opts → Except String Opts
  | "--prefix" :: p :: rest, o => parseArgs rest { o with prefixes := o.prefixes.push p.toName }
  | "--no-sorry" :: rest, o => parseArgs rest { o with noSorry := true }
  | "--json" :: rest, o => parseArgs rest { o with json := true }
  | "--cross-check" :: rest, o => parseArgs rest { o with crossCheck := true }
  | m :: rest, o =>
    if m.startsWith "-" then .error s!"unknown option {m}"
    else parseArgs rest { o with modules := o.modules.push m.toName }
  | [], o => .ok o

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def jsonStr (s : String) : String := (Json.str s).compress

/-! ### Independent axiom walk -/

/-- Marker "axiom" recorded when a referenced constant is missing from the environment. -/
def missingMarker (n : Name) : Name := Name.mkStr (Name.mkSimple "«missing constant»") n.toString

/-- Constructors are merged with their inductive type, and the types of one mutual block with
each other, so the dependency graph is acyclic (the kernel adds every other constant only after
the constants it mentions). -/
def blockKey (env : Environment) (n : Name) : Name :=
  let rep (i : Name) : Name :=
    match env.find? i with
    | some (.inductInfo v) => v.all.head?.getD i
    | _ => i
  match env.find? n with
  | some (.ctorInfo v) => rep v.induct
  | some (.inductInfo v) => v.all.head?.getD n
  | _ => n

/-- Direct dependencies (block keys) of a block key, and whether the key is itself an axiom. -/
def directDeps (env : Environment) (k : Name) : Array Name × Bool := Id.run do
  let some ci := env.find? k | return (#[], false)
  let mut used : Array Name := #[]
  let mut isAx := false
  match ci with
  | .axiomInfo v => isAx := true; used := v.type.getUsedConstants
  | .defnInfo v => used := v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => used := v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => used := v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo v => used := v.type.getUsedConstants
  | .recInfo v => used := v.type.getUsedConstants
  | .ctorInfo v => used := v.type.getUsedConstants
  | .inductInfo v =>
    for i in v.all do
      if let some (.inductInfo w) := env.find? i then
        used := used ++ w.type.getUsedConstants
        for c in w.ctors do
          if let some cc := env.find? c then used := used ++ cc.type.getUsedConstants
  let mut out : Array Name := #[]
  let mut seen : NameSet := {}
  for u in used do
    let key := if (env.find? u).isSome then blockKey env u else missingMarker u
    if key != k && !seen.contains key then
      seen := seen.insert key
      out := out.push key
  return (out, isAx)

structure WalkState where
  cache : Std.HashMap Name NameSet := {}
  pending : Std.HashMap Name (Array Name) := {}

/-- Axioms (plus missing-constant markers) reachable from `root`; memoised across calls.
Iterative post-order DFS, so deep dependency chains cannot overflow the stack. Throws on a
dependency cycle (impossible for a kernel-checked environment; fail closed). -/
def walkAxioms (env : Environment) (root : Name) : StateT WalkState (Except String) NameSet := do
  let rootKey := if (env.find? root).isSome then blockKey env root else missingMarker root
  let mut stack : Array (Name × Bool) := #[(rootKey, false)]
  while h : stack.size > 0 do
    let (k, finish) := stack[stack.size - 1]
    stack := stack.pop
    let s ← get
    if s.cache.contains k then continue
    if (env.find? k).isNone then
      -- a missing constant: its marker is its own "axiom"
      modify fun s => { s with cache := s.cache.insert k (NameSet.empty.insert k) }
      continue
    if !finish then
      if s.pending.contains k then
        throw s!"dependency cycle through {k}"
      let (deps, _) := directDeps env k
      modify fun s => { s with pending := s.pending.insert k deps }
      stack := stack.push (k, true)
      for d in deps do
        unless s.cache.contains d do stack := stack.push (d, false)
    else
      let deps := s.pending.getD k #[]
      let isAx := match env.find? k with | some (.axiomInfo _) => true | _ => false
      let mut acc : NameSet := if isAx then NameSet.empty.insert k else {}
      for d in deps do
        match s.cache.get? d with
        | some axs => acc := axs.foldl (fun a x => a.insert x) acc
        | none => throw s!"dependency cycle through {k} → {d}"
      modify fun s => { s with cache := s.cache.insert k acc, pending := s.pending.erase k }
  let s ← get
  match s.cache.get? rootKey with
  | some axs => return axs
  | none => throw s!"internal: {root} not resolved"

/-! ### MetaScan helpers -/

def metaHits (e : Expr) : Array Name :=
  e.getUsedConstants.filter fun u => metaHeads.any (·.isPrefixOf u)

/-- Reserved: under a `reservedNames` prefix, or with an `Erdos184` component anywhere
(e.g. `EGCheck.Erdos184.erdos_184`, which would shadow the upstream name inside
`namespace EGCheck`; trust review attack B0/A2). -/
def isReserved (n : Name) : Bool :=
  let u := privateToUserName n
  reservedNames.any (·.isPrefixOf u) || u.components.contains `Erdos184

def isFCModule (m : Name) : Bool :=
  (m.getRoot.toString (escape := false)).startsWith "FormalConjectures"

end EGAxioms

open EGAxioms in
def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"Axioms.lean: {e}"; return 2
  let prefixes := if o.prefixes.isEmpty then #[`EG] else o.prefixes
  if o.modules.isEmpty then
    IO.eprintln "usage: lake env lean --run scripts/Axioms.lean [--prefix P]... [--no-sorry] [--json] [--cross-check] Module..."
    return 2
  -- Fail closed if an extension named in `deniedExts` does not exist in this toolchain.
  let registered := (← persistentEnvExtensionsRef.get).map (·.name)
  for (x, _) in deniedExts do
    unless registered.contains x do
      IO.eprintln s!"Axioms.lean: internal: environment extension {x} is not registered in this toolchain; update deniedExts"
      return 2
  let mut privDenied : Array (Name × String) := #[]
  for (suffix, label) in deniedPrivateExtSuffixes do
    let hits := registered.filter fun x => isPrivateName x &&
      (match x with | .str _ s => s == suffix | _ => false)
    if hits.isEmpty then
      IO.eprintln s!"Axioms.lean: internal: no private environment extension named *.{suffix}; update deniedPrivateExtSuffixes"
      return 2
    privDenied := privDenied ++ hits.map (·, label)
  let deniedAll : Std.HashMap Name String :=
    (deniedExts.toArray ++ privDenied).foldl (fun m (x, l) => m.insert x l) {}
  initSearchPath (← findSysroot)
  let env ← importModules (o.modules.map fun m => { module := m }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let inScope (mod : Name) : Bool := prefixes.any (·.isPrefixOf mod)
  let mut inspected := 0
  let mut sorryUsers : Array Name := #[]
  let mut violations : Array String := #[]
  let mut metaCount := 0
  -- Module-level MetaScan: imports and environment-extension entries.
  for h : i in [0:modNames.size] do
    let mod := modNames[i]
    unless inScope mod do continue
    let some md := env.header.moduleData[i]? | do
      violations := violations.push s!"module {mod}: no module data loaded"; continue
    for imp in md.imports do
      if imp.isMeta && imp.module != `Init then
        violations := violations.push s!"module {mod}: meta import {imp.module}"
        metaCount := metaCount + 1
      if isFCModule imp.module && !(`EGCheck).isPrefixOf mod then
        violations := violations.push s!"module {mod}: imports {imp.module} (only EGCheck* may import FormalConjectures)"
    for (ext, entries) in md.entries do
      if entries.size > 0 then
        if let some label := deniedAll.get? ext then
          violations := violations.push s!"module {mod}: {entries.size} {label} entr{if entries.size == 1 then "y" else "ies"} ({ext})"
          metaCount := metaCount + 1
  -- Deterministic order: sort the inspected names.
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if inScope modNames[idx.toNat]! then
        names := names.push n
  names := names.qsort Name.lt
  let mut walk : WalkState := {}
  for n in names do
    let some ci := env.find? n | continue
    let mod := modNames[(env.getModuleIdxFor? n).get!.toNat]!
    inspected := inspected + 1
    let axsSet ← match (walkAxioms env n).run walk with
      | .ok (axs, w) => walk := w; pure axs
      | .error e => IO.eprintln s!"Axioms.lean: internal: {e}"; return 2
    let axs := axsSet.toArray.qsort Name.lt
    let usesSorry := axs.contains ``sorryAx
    if usesSorry then sorryUsers := sorryUsers.push n
    let bad := axs.filter fun a => !(allowedAxioms.contains a) && a != ``sorryAx
    let mut reasons : Array String := bad.map (s!"axiom {·}")
    if o.crossCheck then
      let lean ← (collectAxioms n : CoreM (Array Name)).toIO'
        { fileName := "<axioms>", fileMap := default } { env }
      for a in lean do
        unless axs.contains a do reasons := reasons.push s!"cross-check: collectAxioms reports {a}, walk does not"
    if ci matches .axiomInfo _ then reasons := reasons.push "declares an axiom"
    if ci.isUnsafe then reasons := reasons.push "unsafe"
    if isExtern env n then reasons := reasons.push "@[extern]"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      reasons := reasons.push "@[implemented_by]"
    if (exportAttr.getParam? env n).isSome then reasons := reasons.push "@[export]"
    if o.noSorry && usesSorry then reasons := reasons.push "uses sorryAx"
    -- MetaScan (per constant)
    let mut metaR : Array String := #[]
    let tyHits := metaHits ci.type
    unless tyHits.isEmpty do metaR := metaR.push s!"meta-level type (mentions {tyHits.toList.take 3})"
    let value? : Option Expr := match ci with
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := value? then
      let vHits := metaHits val
      unless vHits.isEmpty do metaR := metaR.push s!"meta-level value (mentions {vHits.toList.take 3})"
    if isMarkedMeta env n then metaR := metaR.push "meta definition"
    if hasInitAttr env n then metaR := metaR.push "initializer ([init]/[builtin_init])"
    if isReserved n then metaR := metaR.push "declared in a namespace reserved for the upstream statement"
    unless metaR.isEmpty do metaCount := metaCount + 1
    reasons := reasons ++ metaR
    unless reasons.isEmpty do
      violations := violations.push s!"{n} ({mod}): {", ".intercalate reasons.toList}"
    if o.json then
      let axsJ := ",".intercalate (axs.toList.map fun a => jsonStr a.toString)
      let rsJ := ",".intercalate (reasons.toList.map jsonStr)
      IO.println s!"\{\"name\":{jsonStr n.toString},\"module\":{jsonStr mod.toString},\"kind\":{jsonStr (kindOf ci)},\"sorry\":{usesSorry},\"axioms\":[{axsJ}],\"violations\":{reasons.size},\"reasons\":[{rsJ}]}"
    else if usesSorry then
      IO.println s!"SORRY {n} ({mod})"
  for v in violations do
    IO.eprintln s!"VIOLATION {v}"
  let summary := s!"inspected {inspected} constants under {prefixes.toList}; \
    {sorryUsers.size} use sorryAx; {metaCount} meta-scan hits; {violations.size} violations"
  if o.json then IO.eprintln summary else IO.println summary
  return (if violations.isEmpty then 0 else 1)
