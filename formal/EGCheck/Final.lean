import FormalConjectures.ErdosProblems.«184»
import EGCheck.Bridge

/-!
# Final check (PLAN_FORMALIZATION.md §1, §8 Q2–Q3, §13; TRUST.md "How to check")

PROTECTED FILE. This module is NOT part of the default `EGCheck` build: it is expected to fail
until phase P4, because the `#guard_msgs` below demands exactly the three standard axioms.
Build it with `lake build EGCheck.Final`.

**The checks in this file are ADVISORY** (a fast first line for developers). They run inside the
Lean elaborator, whose behaviour every imported module can change (elaborator/macro overrides, a
kernel bypass through `debug.skipKernelTC`, build-time IO; trust audits of 2026-09-26,
`APPROVALS/reviews/trust.{opus,fable}.md`). The acceptance criterion is out-of-band and listed in
TRUST.md §4: comparator (the load-bearing check), with `leanchecker --fresh EGCheck.Final` and
`scripts/FinalCheck.lean` as defence in depth.

Hardening against the audited attacks, for what an in-band check can do:
* the upstream module is imported **first and directly**, so a second declaration of
  `Erdos184.IsCycleOrEdge` or `SimpleGraph.IsDecomposition` (definitions), or of
  `Erdos184.erdos_184` **with a different type**, in the project is an import clash (attack C).
  A re-declaration of a theorem with the **same** type (and universe parameters) is NOT a clash:
  `importModules` silently merges the two copies (the later module's proof wins). This file cannot
  see that; the out-of-band `scripts/FinalCheck.lean` `origin` check rejects any name declared both
  by a project module and by another module, and its replay checks every stored copy;
* the statement is `type_of% @_root_.Erdos184.erdos_184.{u}`, so a constant
  `EGCheck.Erdos184.erdos_184` cannot shadow the upstream one (attack B0);
* the meta-check requires both theorems to be `theorem`s, the two upstream definitions to be
  definitions, and checks the module each upstream constant comes from.
-/

theorem EGCheck.erdos_184.{u} : type_of% @_root_.Erdos184.erdos_184.{u} :=
  EGCheck.Bridge.solution

/-- info: 'EGCheck.erdos_184' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EGCheck.erdos_184

/- Meta-check (advisory): `EGCheck.erdos_184` is a theorem declared in this module, whose statement
is syntactically identical (binder names and annotations included, `Expr.equal`) to that of the
theorem `Erdos184.erdos_184` of `FormalConjectures.ErdosProblems.«184»`, up to renaming universe
parameters; `Erdos184.IsCycleOrEdge` and `SimpleGraph.IsDecomposition` are the upstream
definitions. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let checkOrigin (n m : Name) : CommandElabM Unit := do
    unless modOf n == some m do
      throwError "{n} does not come from module {m} (it comes from {modOf n})"
  checkOrigin `Erdos184.erdos_184 `FormalConjectures.ErdosProblems.«184»
  checkOrigin `Erdos184.IsCycleOrEdge `FormalConjectures.ErdosProblems.«184»
  checkOrigin `SimpleGraph.IsDecomposition
    `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition
  unless (modOf `EGCheck.erdos_184).isNone do
    throwError "EGCheck.erdos_184 is not declared in this module"
  let some (.thmInfo a) := env.find? `EGCheck.erdos_184 | throwError "EGCheck.erdos_184 is not a theorem"
  let some (.thmInfo b) := env.find? `Erdos184.erdos_184 | throwError "Erdos184.erdos_184 is not a theorem"
  let some (.defnInfo _) := env.find? `Erdos184.IsCycleOrEdge |
    throwError "Erdos184.IsCycleOrEdge is not a definition"
  let some (.defnInfo _) := env.find? `SimpleGraph.IsDecomposition |
    throwError "SimpleGraph.IsDecomposition is not a definition"
  unless a.levelParams.length == b.levelParams.length do
    throwError "universe parameter counts differ"
  let bty := b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param)
  unless a.type.equal bty do
    throwError "EGCheck.erdos_184 and Erdos184.erdos_184 have different statements"
