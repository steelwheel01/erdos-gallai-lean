import Lean

/-!
# Statement lock dump (PLAN_FORMALIZATION.md §4 "Lock")

Usage (from `formal/`, after `lake build`):

    lake env lean --run scripts/Lock.lean [--prefix P]... Module...

Imports `Module...` and prints one JSON object per constant declared in a module under one of
the prefixes `P` (default: `EG.Spec`, `EG.Defs`):

    {"name", "module", "kind", "levels", "type", "value", "deps"}

* `type` is the kernel type rendered with `Expr.dbgToString` (fully explicit, no notation);
* `value` is the body for definitions (their meaning matters) and `""` for theorems
  (only the statement is locked);
* `aux` marks auto-generated constants (recursors, `noConfusion`, matchers, …), which
  `scripts/lock.py` does not hash: they are determined by the inductive types they come from;
* `deps` lists the constants under the same prefixes that the type/value mention, so that
  `scripts/lock.py` can compute closure hashes.

`scripts/lock.py` hashes these records and compares them with `LOCK.json`.
-/

open Lean

namespace EGLock

def jsonStr (s : String) : String := (Json.str s).compress

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- The part of a constant whose meaning is locked, besides its type. -/
def lockedValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

end EGLock

open EGLock in
def main (args : List String) : IO UInt32 := do
  let mut prefixes : Array Name := #[]
  let mut modules : Array Name := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--prefix" :: p :: r => prefixes := prefixes.push p.toName; rest := r
    | m :: r => modules := modules.push m.toName; rest := r
    | [] => rest := []
  if prefixes.isEmpty then prefixes := #[`EG.Spec, `EG.Defs]
  if modules.isEmpty then
    IO.eprintln "usage: lake env lean --run scripts/Lock.lean [--prefix P]... Module..."
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun m => { module := m }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let inScope (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let mod := modNames[idx.toNat]!
    if prefixes.any (·.isPrefixOf mod) then some mod else none
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if (inScope n).isSome then names := names.push n
  names := names.qsort Name.lt
  for n in names do
    let some ci := env.find? n | continue
    let some mod := inScope n | continue
    let v? := lockedValue? ci
    let used := ci.type.getUsedConstants ++ (v?.map (·.getUsedConstants)).getD #[]
    let deps := (used.filter fun c => c != n && (inScope c).isSome).qsort Name.lt
    let deps := deps.toList.eraseDups
    let depsJ := ",".intercalate (deps.map fun d => jsonStr d.toString)
    let aux := n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n
      || (ci matches .recInfo _) || n.isInternal
    let lvls := ",".intercalate (ci.levelParams.map fun l => jsonStr l.toString)
    IO.println s!"\{\"name\":{jsonStr n.toString},\"module\":{jsonStr mod.toString},\
      \"kind\":{jsonStr (kindOf ci)},\"levels\":[{lvls}],\
      \"type\":{jsonStr ci.type.dbgToString},\
      \"value\":{jsonStr ((v?.map (·.dbgToString)).getD "")},\"deps\":[{depsJ}],\
      \"aux\":{aux}}"
  return 0
