# Clean-room review — group `bridge` — reviewer `fable`

Date: 2026-09-26. Model: Claude (Fable 5.1). Independent review from scratch. The earlier
review `APPROVALS/reviews/bridge.opus.md` was read only *after* every check below had been run
and every verdict formed; nothing here rests on it (a cross-check against it is in §9). This
review is the only file written in the repository. No git command that changes the repository
was run.

**Scope.** `EGCheck/Bridge.lean` (`EGCheck.Bridge.of_mainInternal`, `EGCheck.Bridge.solution`)
and `EGCheck/BridgeLemmas.lean` (helper definitions `toSub`, `chainEdges`, `lastOf`, `listWalk`,
`cycleWalk`, `objMap`; lemmas `exists_finset_of_isDecomp`, `isDecomp_comap_symm` and their
supporting lemmas). Hypothesis side: `EG/Spec/Main.lean` (`EG.Spec.MainInternal`) on top of
`EG/Defs/Objects.lean` (`EG.Obj`, `EG.Obj.edges`, `EG.Obj.WF`, `EG.cycleEdges`, `EG.IsDecomp`).
Target side: `.lake/packages/formal_conjectures/FormalConjectures/ErdosProblems/184.lean`
(`Erdos184.IsCycleOrEdge`, `Erdos184.erdos_184`) and
`.lake/packages/formal_conjectures/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`
(`SimpleGraph.IsDecomposition`). Also read: `EGCheck/Final.lean`, `EG/Proof/Main.lean`,
`EG/Lib/Found/FnumMain.lean` (for the strength judgement only), `scripts/Axioms.lean`,
`LOCK.json`, `TRUST.md`, `PLAN_FORMALIZATION.md` §1 and §3 (design decisions 1 and 8), manuscript
`proofs/manuscript/s1.tex` l. 66–84 (s1:thmMain), l. 321–352 (s1:convGraphs), l. 354–362
(s1:defObject) and `s7.tex` l. 1434–1461 (s7:thmMainProof).

**Method.** (1) Back-translated the upstream statement, `MainInternal` and the bridge theorem
into plain mathematics and compared them clause by clause with the quoted manuscript text.
(2) Ran a meta-program (scratch file `BridgeCheck.lean`, appendix A) that checks the *shape* of
`of_mainInternal`'s type — a single non-dependent arrow whose domain is literally the constant
`EG.Spec.MainInternal` and whose codomain is `Expr.equal` (binder names and binder info
included) to the upstream type after universe renaming — and prints axioms and the elaborated
proof term. (3) Ran the project axiom scan. (4) Elaborated `EGCheck/Final.lean` as it stands.
(5) Wrote non-vacuity probes on concrete small graphs (scratch file `BridgeNonvac.lean`,
appendix B; 0 errors). (6) Verified provenance: pinned upstream commit, upstream blob hashes
against `TRUST.md`, locked file hashes against `LOCK.json`, `.olean`s up to date.

**Verdict: APPROVE (all items), with non-blocking notes in §8.**

* The statement of `of_mainInternal` is exactly `EG.Spec.MainInternal → type_of%
  @Erdos184.erdos_184.{u}`; the conclusion is syntactically the upstream statement.
* The proof uses no hypothesis other than `MainInternal` and depends only on `propext`,
  `Classical.choice`, `Quot.sound`.
* The only `sorryAx` in `EGCheck.Bridge` enters through `EG.Proof.mainInternal`, via
  `solution := of_mainInternal EG.Proof.mainInternal`.
* `MainInternal` is at least as strong as needed (it implies the upstream statement in every
  universe — that is the theorem), and it is not stronger than the manuscript's Theorem
  s1:thmMain: it is that theorem's conclusion "f(G) ≤ c·n for every graph G on n vertices" with
  the constant existentially quantified over ℕ. The bridge is not vacuous.

---

## 1. Integrity of what was reviewed

* `lake build EGCheck.Bridge --no-build`: "All targets up-to-date (8931 jobs)", so the `.olean`
  files inspected by the meta-check and the axiom scan match the sources read.
* `formal_conjectures` checkout is at `2424bb480c590237ffbb2cc831ae4cb8977e045a`, the `rev` and
  `inputRev` pinned in `lake-manifest.json`.
* `git hash-object` of the two upstream files: `36cc140cb3d8e60b08a842f1691fe9b73602f92b`
  (`184.lean`) and `a4d3f066158b799e851dd8c6ac511ef2b6731111` (`Decomposition.lean`), equal to the
  blob ids recorded in `TRUST.md` l. 31–34.
* `sha256sum` of `EG/Spec/Main.lean`, `EG/Defs/Objects.lean`, `EGCheck/Final.lean` equal the
  `files` entries of `LOCK.json`. `git status` shows these files and the two bridge files
  unmodified (other agents' in-flight edits elsewhere in the tree do not touch the scope).
* `python3 scripts/lint.py`: 0 findings. A grep of both bridge files finds no `sorry`, `axiom`,
  `admit`, `native_decide`, `unsafe`, `opaque`, `implemented_by` (the word `sorry` occurs once, in
  the module docstring of `Bridge.lean`, describing `EG.Proof.mainInternal`).

## 2. The upstream target, back-translated

`Erdos184.erdos_184.{u}` is elaborated under `open scoped Classical in`:

```
∃ f : ℕ → ℝ, (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  ∃ (D : Finset G.Subgraph),
    (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)
```

with `IsCycleOrEdge H := (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1` and
`IsDecomposition G D := Set.PairwiseDisjoint (↑D) (fun H ↦ H.edgeSet) ∧ (⋃ H ∈ D, H.edgeSet) =
G.edgeSet`.

Plain mathematics: there is a real function f with f(n) = O(n) as n → ∞ such that every finite
simple graph G (on a vertex type of universe u, with a decidable equality) has a finite family D
of subgraphs whose members, each viewed as a graph on its own vertex set, are connected and
2-regular or have exactly one edge, whose edge sets are pairwise disjoint with union E(G), and
with |D| ≤ f(|V|).

Checks on the target itself (it is the fixed reference, not something this project chose, but
the bridge inherits its meaning):
* A finite connected 2-regular simple graph is a cycle of length ≥ 3 (`Connected` includes
  `Nonempty`; a simple graph has no loops or parallel edges). So the left disjunct is exactly
  "H is a cycle of length at least 3" (manuscript s1:defObject).
* A one-edge member may carry isolated vertices; that only makes the upstream *easier* and the
  bridge never produces such a member (`toSub` has vertices = ends of its edges).
* Members are never edgeless (both disjuncts force ≥ 1 edge), so |D| counts parts of a genuine
  partition of E(G), as in s1:defObject ("a partition of F into the edge sets of objects").
* `f =O[atTop] n` is an eventual bound with an arbitrary constant; `f` may take any value at
  small `n`. The bridge supplies `f n = c·n`, which is `O(n)` outright.
* The `Fintype H.verts` instance inside `IsCycleOrEdge H.coe` is, per the elaborated proof term
  (appendix A), `Subtype.fintype (Membership.mem H.verts)` with classical decidability. The
  bridge lemma `exists_finset_of_isDecomp` proves the property for **every** instance
  (`∀ inst : Fintype H.verts, …`), so the instance choice cannot matter.

## 3. `EG.Spec.MainInternal`, back-translated and compared with the manuscript

```
def MainInternal : Prop :=
  ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V
```

with, from `EG/Defs/Objects.lean`, `cycleEdges c = zipWith s(·,·) c (c.rotate 1)`,
`Obj.edges (edge e) = [e]`, `Obj.edges (cycle c) = cycleEdges c`, `WF (edge e) = ¬ e.IsDiag`,
`WF (cycle c) = c.Nodup ∧ 3 ≤ c.length`, and
`IsDecomp E D := (∀ o ∈ D, o.WF) ∧ (D.flatMap Obj.edges).Nodup ∧ ∀ e, e ∈ D.flatMap Obj.edges ↔ e ∈ E`.

Plain mathematics: there is a natural number c such that every finite simple graph G on a
vertex type V of universe 0 has a list D of objects — each a non-loop edge or a cyclic vertex list
with ≥ 3 distinct vertices — whose edge lists concatenate to a duplicate-free list containing
exactly the edges of G, and with |D| ≤ c·|V|.

Manuscript s1:defObject (quoted): "An *object* is a cycle (of length at least 3) or a single
edge. A *decomposition* of an edge set F is a partition of F into the edge sets of objects; a
decomposition of a graph H is a decomposition of E(H). f(F) is the least number of objects in a
decomposition of F (so f(∅) = 0); f(H) := f(E(H)); and f(n) := max{f(H) : |V(H)| = n}."

Manuscript s1:thmMain (quoted): "Then every graph G on n vertices satisfies f(G) ≤ c_EG n. In
particular f(n) = O(n)." s1:convGraphs(a): "Graphs are finite and simple … n := |V(G)|."
s7:thmMainProof, last lines: "Theorem s7:thmHI … therefore gives f(G) ≤ c_EG|V(G)| for every
graph G. In particular f(n) ≤ c_EG n for every n, so f(n) = O(n)."

Clause-by-clause comparison:
* **Object = cycle of length ≥ 3 or single edge.** A `cycle c` with `c.Nodup` and `3 ≤ c.length`
  has edges `c₀c₁, c₁c₂, …, c_{k−1}c₀`: k distinct non-loop edges forming a cycle of length k ≥ 3
  (probe: on `Fin 3`, `toSub ⊤ (cycle [0,1,2])` has edge set exactly `{s(0,1), s(1,2), s(2,0)}`,
  appendix B). An `edge e` is a single non-loop edge. Degenerate objects — 2-vertex "cycle",
  closed walk with a repeated vertex, loop edge — are rejected by `WF` (appendix B). Conversely
  every cycle of length ≥ 3 in a simple graph is `cycle` of its vertex sequence, and every edge is
  `edge`. So `Obj` + `WF` is exactly s1:defObject's "object".
* **Decomposition = partition of E(G) into edge sets of objects.** `(D.flatMap edges).Nodup`
  says each object's edges are distinct and distinct list entries have disjoint edge sets;
  `∀ e, e ∈ flatMap ↔ e ∈ G.edgeSet` says the union is exactly E(G) (both inclusions: no stray
  edge outside G, no edge of G missed). Every WF object has ≥ 1 edge, so `D` cannot contain the
  same object twice and `D.length` is exactly the number of parts. So `IsDecomp G.edgeSet D` is
  exactly "D is a decomposition of G", and `∃ D, IsDecomp … ∧ D.length ≤ k` is exactly
  "f(G) ≤ k" (this is `EG.fnum_edgeFinset_le_iff`, reviewed by the `objects-main-fnum` group;
  I rely only on the unfolded definitions above, not on that lemma).
* **Quantifiers / constant.** Manuscript: explicit real c_EG, bound for *every* graph and every
  n (s7:thmMainProof says "for every n" — small n are absorbed by the `N₀/2` term of c_EG).
  `MainInternal`: some `c : ℕ`, bound for every graph. Taking `c := ⌈c_EG⌉₊` the manuscript's
  conclusion implies `MainInternal`; the explicit formula is deliberately not carried (PLAN §3
  decision 4: galactic constants as eventualities). So `MainInternal` is **not stronger** than
  s1:thmMain.
* **Strict vs non-strict.** Both `≤`.
* **Arithmetic conventions.** Only `ℕ` multiplication `c * Fintype.card V`: no subtraction,
  division, logarithm, rounding or casts. `Fintype.card V` is instance-independent.
* **Finite and simple.** `[Fintype V]`, `SimpleGraph V`; `G.edgeSet` is loop-free, so
  `IsDecomp` on it never meets a loop (the `fnum`-ignores-loops caveat of `EG/Defs/Fnum.lean`
  is irrelevant here: `MainInternal` is stated with `IsDecomp`, not `fnum`).
* **Edge cases.** n = 0 or 1: E(G) = ∅, `D = []` satisfies `IsDecomp` (empty flatMap, both
  membership directions vacuous) with `0 ≤ c·n`. n = 2 with an edge: needs one `edge` object, so
  c ≥ 1 is forced — `MainInternal` is not satisfied by `c = 0`, i.e. it is not trivially true.
  It is not trivially false: it is the (open) conjecture at universe 0.
* **Implicit assumptions.** `[DecidableEq V]` is an extra hypothesis under a `∀`, so it weakens
  the obligation and is harmless; the bridge only ever instantiates `V := Fin n`, which has
  `instDecidableEqFin`. `V : Type` (universe 0) is a restriction relative to the universe-
  polymorphic target — that is precisely what the bridge repairs (§5), and it keeps
  `MainInternal : Prop` without universe parameters.
* **Deviation from PLAN §3 decision 8 text.** The PLAN writes `IsDecomp (edgeFinset G) D`;
  the frozen Spec uses `IsDecomp G.edgeSet D`. `IsDecomp` takes a `Set`, and `↑(edgeFinset G) =
  G.edgeSet`, so the meaning is identical; the `Set` form avoids a `Fintype G.edgeSet` instance
  in the statement. Not a defect (the Spec is the source of truth).

## 4. `of_mainInternal` and `solution`: exact statements

```
theorem of_mainInternal (h : EG.Spec.MainInternal) : type_of% @Erdos184.erdos_184.{u}
theorem solution : type_of% @Erdos184.erdos_184.{u} := of_mainInternal EG.Proof.mainInternal
```

Meta-check (appendix A), output verbatim:

```
of_mainInternal levelParams: [u], upstream: [u_1]
binder h (Lean.BinderInfo.default) : EG.Spec.MainInternal
OK: conclusion is syntactically the upstream statement (Expr.equal, binder names incl.)
OK: solution type is syntactically the upstream statement
```

So:
* `of_mainInternal`'s type is a `forallE` with domain the constant `EG.Spec.MainInternal`
  (compared with `==` against `mkConst ``EG.Spec.MainInternal`), the body has no loose bound
  variable (the conclusion does not depend on `h`), and the body is `Expr.equal` to the upstream
  type after instantiating the upstream universe parameter with `u`. `Expr.equal` is structural
  and compares binder names and binder info, which is the same test `EGCheck/Final.lean` uses.
* `Bridge.lean` declares `universe u` and no `variable`; the level parameters are exactly `[u]`,
  so there are no auto-bound implicits and **no hypothesis beyond `MainInternal`**.
* `solution`'s type is `Expr.equal` to the upstream type, with one universe parameter.
* The name `Erdos184.erdos_184` is fully qualified; the variants are the distinct constants
  `erdos_184.variants.*`, and the `#print`ed type shows `f =O[atTop] fun n ↦ ↑n` (linear, not
  `n log n` or `n log* n`).
* `type_of%` reads the constant's declared type; it does not re-elaborate the statement, so the
  `open scoped Classical` instances baked into the upstream statement are reproduced verbatim.
* `EGCheck/Final.lean` elaborated as it stands (`lake env lean EGCheck/Final.lean`): exactly one
  error, the expected `#guard_msgs` mismatch (`sorryAx` still present); its `run_cmd` syntactic
  meta-check passes silently, and the universe-parameter count check passes.

## 5. The proof, back-translated

Given `h`, obtain `c` and `hc`. Put `f n := (c : ℝ) * n`; `f =O n` by
`isBigO_refl.const_mul_left`. Given `V : Type u`, `[Fintype V] [DecidableEq V]`, `G`: let
`e := Fintype.equivFin V : V ≃ Fin (card V)` and apply `hc` to the copy `G.comap e.symm` on
`Fin (card V) : Type`, obtaining a list `D₀` with `IsDecomp (G.comap e.symm).edgeSet D₀` and
`D₀.length ≤ c * card (Fin (card V))`. Then

* `isDecomp_comap_symm e G hD₀ : IsDecomp G.edgeSet (D₀.map (objMap e.symm))`. Back-translation:
  mapping each object's vertices by the bijection `e.symm` preserves `WF` (injectivity keeps
  `Nodup` and non-loops), preserves `Nodup` of the concatenated edge list (`Sym2.map` of an
  injective map is injective), and turns "edge of the copy" into "edge of G" (`mem_edgeSet_comap`
  and `Sym2.map_map` with `e ∘ e.symm = id`). Correct; the only place injectivity is needed is
  supplied by an equivalence.
* `exists_finset_of_isDecomp : ∃ D' : Finset G.Subgraph, (∀ H ∈ D', ∀ inst, IsCycleOrEdge H.coe)
  ∧ G.IsDecomposition D' ∧ D'.card ≤ D.length`, with `D' := (D.map (toSub G)).toFinset`.
  * `toSub G o`: vertices = ends of the edges of `o`; `a ~ b ↔ s(a,b) ∈ o.edges ∧ G.Adj a b`. For
    an object of a decomposition of E(G) its edge set is exactly `o.edges` (`mem_edgeSet_toSub`;
    probe in appendix B).
  * Edge object: edge set `{e}`, so `H.coe.edgeFinset.card = 1` via
    `Subgraph.image_coe_edgeSet_coe` and `Set.ncard_singleton`, for any `Fintype` instance
    (`card_edgeFinset_eq_ncard`).
  * Cycle object `cycle (a :: l)`: `cycleWalk` is the closed walk `a, l₀, …, l_{k−2}, a`
    (`listWalk` along `l ++ [a]`); `cycleEdges_cons` shows its edge list is `EG.cycleEdges
    (a :: l)` (via `(a :: l).rotate 1 = l ++ [a]`); `isCycle_cycleWalk` gives `Walk.IsCycle`
    from duplicate-free edges, `Nodup` of `a :: l` (so `Nodup` of the tail `l ++ [a]` by
    `nodup_rotate`) and length ≥ 3 (non-nil); `toSub_cycle_eq` identifies `toSub` with
    `Walk.toSubgraph` (vertex sets agree because a non-nil walk's support is the set of ends of
    its edges). Mathlib then gives `Connected` (`toSubgraph_connected`) and degree 2 at every
    vertex (`IsCycle.ncard_neighborSet_toSubgraph_eq_two`), for any `Fintype` instance
    (`degree_eq_ncard`).
  * Pairwise disjointness: two distinct members come from objects `o₁, o₂ ∈ D`; a common edge
    would give `o₁ = o₂` by `eq_of_mem_of_nodup_flatMap` (the concatenation is `Nodup`), hence
    equal members, contradiction. Union = E(G): from the membership clause of `IsDecomp`.
    Card: `toFinset_card_le` and `length_map`.
* Final arithmetic: `D'.card ≤ (D₀.map _).length = D₀.length ≤ c * card (Fin (card V)) =
  c * card V`, cast to ℝ (`exact_mod_cast`). The `Fintype.card V` in the goal uses the bound
  instance, the same one `Fintype.equivFin V` uses, so no instance mismatch can arise.

The helper definitions are untrusted: they are kernel-checked and appear only inside the proof,
so a wrong helper could make the bridge fail to compile but could never change what
`Final.lean` asserts. I nevertheless confirmed that each means what its docstring says.

## 6. Axioms

`lake env lean --run scripts/Axioms.lean --prefix EGCheck EGCheck.Bridge`:

```
SORRY EGCheck.Bridge.solution (EGCheck.Bridge)
inspected 66 constants under [EGCheck]; 1 use sorryAx; 0 violations
```

`#print axioms` (appendix A):
* `EGCheck.Bridge.of_mainInternal`, `exists_finset_of_isDecomp`, `isDecomp_comap_symm`:
  `[propext, Classical.choice, Quot.sound]`.
* `EGCheck.Bridge.solution`, `EG.Proof.mainInternal`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.

Since `of_mainInternal` is `sorryAx`-free and `solution` is literally
`of_mainInternal EG.Proof.mainInternal`, the only `sorryAx` in `EGCheck.Bridge` enters through
`EG.Proof.mainInternal`. The upstream `erdos_184` is itself `sorry`, but only its *type* is used
(`type_of%`); the axiom lists confirm its value is not.

## 7. Strength of `MainInternal`; non-vacuity of the bridge

* **At least as strong as needed.** `MainInternal ⇒ Erdos184.erdos_184.{u}` for every `u` is the
  theorem `of_mainInternal`, kernel-checked with standard axioms. So once
  `EG.Proof.mainInternal` is proved, `Final.lean` states exactly the upstream conjecture.
* **Not vacuous, not degenerate.** `MainInternal` is not provable by a loophole: `IsDecomp`
  forces genuine objects (`WF`), exact coverage (both directions), and disjointness (`Nodup`);
  `c = 0` already fails on a single edge (§3). Probes in appendix B: `⊤` on `Fin 3` decomposes
  into `[cycle [0,1,2]]`; the path `0–1–2` into `[edge s(0,1), edge s(1,2)]`; the three
  degenerate objects are rejected. So the hypothesis of `exists_finset_of_isDecomp` is
  satisfiable on graphs with edges, and the bridge is exercised on non-empty instances.
* **Not too strong (so it can be proved from the manuscript).** s1:thmMain / s7:thmMainProof give
  `f(G) ≤ c_EG·|V(G)|` for *every* graph (small n included, via the `N₀/2` term), i.e. for every
  G a decomposition with at most `⌈c_EG⌉₊·n` objects. That is `MainInternal` with `c := ⌈c_EG⌉₊`
  (the project's `EG.mainInternal_iff_fmax` and `EG.Proof.Quot.HIMain` formalize exactly this
  step). On paper, the upstream statement at universe 0 also implies `MainInternal` (convert each
  member to an `Obj`; for `n < N` use the single-edge decomposition, `|E| ≤ n(n−1)/2 ≤ N·n`; take
  `c := max(⌈C⌉, N)`), so `MainInternal` is mathematically equivalent to the conjecture — the
  reverse direction is not formalized and is not needed.

## 8. Per-item verdicts and notes

| Item | Verdict |
|---|---|
| `EGCheck.Bridge.of_mainInternal` — type exactly `MainInternal → type_of% @Erdos184.erdos_184.{u}`, no other hypothesis, standard axioms | approve |
| `EGCheck.Bridge.solution` — type syntactically the upstream statement; `sorryAx` only via `EG.Proof.mainInternal` | approve |
| `EG.Spec.MainInternal` as the bridge's hypothesis — faithful to s1:defObject/s1:thmMain, neither vacuous nor too strong | approve |
| `BridgeLemmas` helper definitions `toSub`, `chainEdges`, `lastOf`, `listWalk`, `cycleWalk`, `objMap` | approve |
| `BridgeLemmas` lemmas `exists_finset_of_isDecomp`, `isDecomp_comap_symm` and supporting lemmas | approve |

Notes (none blocking):
* **N1.** `MainInternal`'s `[DecidableEq V]` binder is unused by the statement (`IsDecomp` is on a
  `Set`); it is harmless and matches the upstream binder list.
* **N2.** PLAN §3 decision 8 says `IsDecomp (edgeFinset G) D`; the frozen Spec says
  `IsDecomp G.edgeSet D`. Same meaning; the PLAN text could be aligned to the Spec.
* **N3.** `EGCheck/Bridge.lean` and `EGCheck/BridgeLemmas.lean` are not in `LOCK.json`. This is
  acceptable because the locked `EGCheck/Final.lean` re-checks the final type syntactically and
  demands exactly the three standard axioms, so no later edit of the bridge can change the final
  claim without `Final.lean` failing. If the bridge is nevertheless to be treated as "locked",
  `EGCheck.Bridge.of_mainInternal` should be added to `LOCK.json` so that `scripts/lock.py check`
  detects a change of its statement.
* **N4.** `EGCheck/Final.lean` uses `run_cmd`, which AGENTS.md rule 2 forbids in `EGCheck/`;
  `scripts/lint.py` whitelists exactly this file for exactly this token (`ALLOW`), so this is
  intentional and consistent. It also emits a cosmetic "more than one module docstring" linter
  warning.
* **N5 (stage α).** `MainInternal` is unconditional. Stage-α hypotheses (Lovász, Haxell, Euler),
  if used, must live on `EG.Proof.mainInternal`, not in `MainInternal`; adding them to the Spec
  would be a statement change requiring re-approval, and `Final.lean` would not compile without
  `sorry` until they are discharged.

## 9. Cross-check against `bridge.opus.md` (read last)

Independently reached the same verdicts, the same axiom lists, the same statement-shape check
and the same strength argument. The earlier review verified upstream files by SHA-256; this
one by git blob id — both agree with `TRUST.md`. No disagreement found.

---

## Appendix A — `BridgeCheck.lean` (scratch, compiles; the one "error" is the deliberate
`value?` probe on a theorem, which the module system does not expose)

```lean
import EGCheck.Bridge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some a := env.find? `EGCheck.Bridge.of_mainInternal | throwError "not found"
  let some b := env.find? `Erdos184.erdos_184 | throwError "upstream not found"
  logInfo m!"of_mainInternal levelParams: {a.levelParams}, upstream: {b.levelParams}"
  match a.type with
  | .forallE n dom body bi =>
    logInfo m!"binder {n} ({repr bi}) : {dom}"
    unless dom == mkConst ``EG.Spec.MainInternal do throwError "hypothesis is not exactly EG.Spec.MainInternal"
    if body.hasLooseBVars then throwError "conclusion depends on h"
    let bty := b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param)
    unless body.equal bty do throwError "conclusion differs from upstream statement"
    logInfo "OK: conclusion is syntactically the upstream statement (Expr.equal, binder names incl.)"
  | _ => throwError "not a forall"
  let some s := env.find? `EGCheck.Bridge.solution | throwError "solution not found"
  let sty := b.type.instantiateLevelParams b.levelParams (s.levelParams.map Level.param)
  unless s.type.equal sty do throwError "solution type differs"
  logInfo "OK: solution type is syntactically the upstream statement"

#print axioms EGCheck.Bridge.of_mainInternal
#print axioms EGCheck.Bridge.solution
#print axioms EGCheck.Bridge.exists_finset_of_isDecomp
#print axioms EGCheck.Bridge.isDecomp_comap_symm
#print axioms EG.Proof.mainInternal
#print EGCheck.Bridge.of_mainInternal
```

Output (abridged): the four `logInfo` lines quoted in §4; the axiom lines quoted in §6; and the
elaborated proof term, in which the `IsCycleOrEdge` obligation is discharged as
`hcyc H hH (Subtype.fintype (Membership.mem H.verts))`.

## Appendix B — `BridgeNonvac.lean` (scratch, 0 errors)

```lean
import EGCheck.BridgeLemmas
open SimpleGraph

example : EG.IsDecomp (⊤ : SimpleGraph (Fin 3)).edgeSet [EG.Obj.cycle [0, 1, 2]] := by
  refine ⟨?_, ?_, ?_⟩
  · intro o ho; simp only [List.mem_singleton] at ho; subst ho; exact ⟨by decide, by decide⟩
  · decide
  · intro e; induction e using Sym2.ind with
    | _ a b =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, EG.Obj.edges,
        EG.cycleEdges, mem_edgeSet, top_adj]
      fin_cases a <;> fin_cases b <;> decide

example : EG.IsDecomp (fromRel fun (i j : Fin 3) => i.val + 1 = j.val).edgeSet
    [EG.Obj.edge s(0, 1), EG.Obj.edge s(1, 2)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro o ho
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp [EG.Obj.WF]
  · decide
  · intro e; induction e using Sym2.ind with
    | _ a b =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, EG.Obj.edges,
        mem_edgeSet, fromRel_adj]
      fin_cases a <;> fin_cases b <;> decide

example : ¬ (EG.Obj.cycle [(0 : Fin 3), 1]).WF := by simp [EG.Obj.WF]
example : ¬ (EG.Obj.cycle [(0 : Fin 3), 1, 0]).WF := by simp [EG.Obj.WF]
example : ¬ (EG.Obj.edge s((0 : Fin 3), 0)).WF := by simp [EG.Obj.WF]

example : (EGCheck.Bridge.toSub (⊤ : SimpleGraph (Fin 3)) (EG.Obj.cycle [0, 1, 2])).edgeSet
    = {s(0, 1), s(1, 2), s(2, 0)} := by
  ext e; induction e using Sym2.ind with
  | _ a b =>
    simp only [EGCheck.Bridge.mem_edgeSet_toSub, EG.Obj.edges, EG.cycleEdges, mem_edgeSet,
      top_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases a <;> fin_cases b <;> decide
```
