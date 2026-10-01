# Clean-room review — group `objects-main-fnum` — reviewer `fable`

Date: 2026-09-26. Model: Claude (Fable 5.1). Independent review from scratch; earlier verdicts were
not consulted.

**Scope.** `EG/Defs/Objects.lean` (`EG.cycleEdges`, `EG.Obj`, `EG.Obj.edges`, `EG.Obj.WF`,
`EG.IsDecomp`), `EG/Defs/Fnum.lean` (`EG.fnum`, `EG.fmax`), `EG/Spec/Main.lean`
(`EG.Spec.MainInternal`). Manuscript: `s1:defObject`, `s1:factAdd`, `s1:thmMain`
(`proofs/manuscript/s1.tex` l. 66–80, 321–353, 354–362, 364–395) and the last step of
`s7:thmMainProof` (`s7.tex` l. 1434–1462). Also checked: that `MainInternal` is exactly
"f(n) = O(n) for finite simple graphs" (`EG/Lib/Found/FnumMain.lean`).

**Method.** Each definition was back-translated into plain mathematics, compared with the quoted
manuscript text, and probed with scratch Lean files (under the session scratchpad; reproduced in
the appendix). `#print` of every in-scope constant was inspected to make sure the reviewed text is
what Lean elaborated. `#print axioms` of the `FnumMain` theorems and of my scratch theorems shows
only `propext`, `Classical.choice`, `Quot.sound`. No repository file was edited; the only file
written is this review.

**Verdict: APPROVE (all eight items), with non-blocking notes in §5.**

---

## 1. `EG/Defs/Objects.lean`

### 1.1 `EG.cycleEdges (c : List V) : List (Sym2 V) := List.zipWith (fun a b => s(a, b)) c (c.rotate 1)`

*Back-translation.* For `c = [c₀, …, c_{k−1}]`, `c.rotate 1 = [c₁, …, c_{k−1}, c₀]` (Batteries
`rotate` uses `n % length`, so it is total), hence
`cycleEdges c = [s(c₀,c₁), s(c₁,c₂), …, s(c_{k−2},c_{k−1}), s(c_{k−1},c₀)]`: the `k` edges of the
closed walk `c₀ c₁ … c_{k−1} c₀`. Length is `k` (`length_cycleEdges`), and
`(cycleEdges c)[i] = s(c[i], c[(i+1) mod k])` (`getElem_cycleEdges`).

*Edge cases (checked by `decide`).* `cycleEdges [] = []`; `cycleEdges [7] = [s(7,7)]` (a loop);
`cycleEdges [0,1] = [s(0,1), s(1,0)]` (the same edge twice, so *not* `Nodup`);
`cycleEdges [0,1,2] = [s(0,1), s(1,2), s(2,0)]`; `cycleEdges [0,1,2,3] = [s(0,1), s(1,2), s(2,3), s(3,0)]`.
The degenerate cases `k ≤ 2` are exactly those excluded by `Obj.WF`; for `k ≥ 3` and `c.Nodup`
the edge list is duplicate free and loop free (`nodup_cycleEdges`, `not_isDiag_of_mem_cycleEdges`
in `EG/Lib/Found/Fnum.lean`, both proved).

*Verdict:* approve.

### 1.2 `EG.Obj V` — `edge (e : Sym2 V) | cycle (c : List V)`

*Manuscript* (s1:defObject): "An *object* is a cycle (of length at least 3) or a single edge."
The inductive type is a syntactic representation; whether a value is a genuine object is the job
of `WF`, and whether it lies in the graph is the job of `IsDecomp`. `Obj V : Type u` for
`V : Type u`; `deriving DecidableEq` needs `DecidableEq V` (an instance, not a hypothesis on the
mathematics). *Verdict:* approve.

### 1.3 `EG.Obj.edges` — `edge e ↦ [e]`, `cycle c ↦ cycleEdges c`

The edge list of the object: one edge, or the `k` cycle edges. *Verdict:* approve.

### 1.4 `EG.Obj.WF` — `edge e ↦ ¬ e.IsDiag`, `cycle c ↦ c.Nodup ∧ 3 ≤ c.length`

*Back-translation.* An edge object is a non-loop; a cycle object is a list of *pairwise distinct*
vertices of length at least 3. Then `cycleEdges c` is the edge set of the cycle graph `C_k` on the
vertices of `c` (k = |c| ≥ 3 distinct edges, no loops) — a genuine cycle of length ≥ 3 in the
manuscript's sense (Convention s1:convGraphs(a): graphs are finite and simple, so a cycle has
length ≥ 3 automatically; the manuscript's parenthetical "(of length at least 3)" is matched by
`3 ≤ c.length`, non-strict, as intended). Conversely every cycle of a simple graph (connected
2-regular subgraph) has a cyclic vertex ordering `[v₀, …, v_{k−1}]`, `k ≥ 3`, distinct, whose
`cycleEdges` is exactly its edge set; every single edge is `edge e`. So the family of "edge sets
of well-formed objects" coincides with the manuscript's family of object edge sets. (The direction
"every WF object is a genuine cycle or edge" is additionally machine-checked in
`EGCheck/BridgeLemmas.lean`, which builds the Mathlib closed walk and proves connectivity and
2-regularity for the upstream `IsCycleOrEdge`.)

*Negative tests (scratch, `decide`):* `cycle []`, `cycle [0,1]`, `cycle [0,1,0]`,
`cycle [0,1,2,1]`, `edge s(3,3)` are all `¬ WF`; `cycle [0,1,2]`, `cycle [0,1,2,3]`,
`edge s(3,4)` are `WF`.

*Verdict:* approve.

### 1.5 `EG.IsDecomp (E : Set (Sym2 V)) (D : List (Obj V)) : Prop`
`(∀ o ∈ D, o.WF) ∧ (D.flatMap Obj.edges).Nodup ∧ ∀ e, e ∈ D.flatMap Obj.edges ↔ e ∈ E`

*Back-translation.* `D` is a finite sequence of well-formed objects; the concatenation of their
edge lists has no repeated edge (so the objects' edge sets are pairwise disjoint, and each is
duplicate free — the latter is automatic for WF objects); and the union of the edge sets is exactly
`E` (both inclusions, from the `↔`).

*Manuscript:* "A *decomposition* of an edge set F is a partition of F into the edge sets of
objects; a decomposition of a graph H is a decomposition of E(H)." A partition = pairwise disjoint
nonempty parts covering F. Parts are nonempty because WF objects have ≥ 1 edge
(`WF.length_edges_pos`). Cover and containment: the `↔`. Disjointness: `Nodup`.

*Count fidelity.* The manuscript counts parts; Lean counts list entries `D.length`. These agree:
an object cannot occur twice in `D` (its nonempty edge list would repeat — scratch theorem
`¬ IsDecomp E [o, o]`), and two different lists describing the same cycle (rotation, reversal)
have the same edge set, so both cannot occur (scratch: `[cycle [0,1,2], cycle [1,2,0]]` is not a
decomposition of the triangle). Hence `D.length` = number of parts of the partition.

*Edge cases.* `IsDecomp ∅ []` holds and is the only decomposition of `∅` (`isDecomp_nil_iff`).
If `E` contains a loop, no `D` works (`IsDecomp.not_isDiag`; scratch check for `{s(0,0), s(0,1)}`).
`E : Set` may be infinite syntactically, but `IsDecomp E D` forces `E` finite (it equals the
range of a finite list) — harmless; the manuscript only uses finite edge sets. `V` in any universe.

*Non-vacuity (scratch):* triangle decomposed by `[cycle [0,1,2]]` and by `[cycle [2,1,0]]`;
the path `{s(0,1), s(1,2)}` is *not* decomposed by `[cycle [0,1,2]]` (extra edge `s(2,0)`);
`[cycle [0,1,2], edge s(0,1)]` fails (shared edge); `[edge s(0,1), edge s(2,3)]` is not a
decomposition of `{s(0,1)}` (edge outside E); `[cycle [0,1]]` is not a decomposition of `{s(0,1)}`
(WF). Existing tests `EGTest/Fnum.lean` also give f(K₄) = 3, a value strictly between the trivial
bounds.

*Verdict:* approve.

## 2. `EG/Defs/Fnum.lean`

### 2.1 `EG.fnum (F : Finset (Sym2 V)) : ℕ := sInf {k | ∃ D, IsDecomp (↑F \ Sym2.diagSet) D ∧ D.length = k}`

*Back-translation.* The least length of a list of objects decomposing the non-loop part of `F`.

*Manuscript:* "f(F) is the least number of objects in a decomposition of F (so f(∅) = 0)."

*Lean conventions checked.* `sInf` on `ℕ` returns `0` on the empty set, but the set is nonempty for
every `F` (the single non-loop edges; `exists_isDecomp_sdiff_diagSet`), so `sInf` is a genuine
attained minimum (`fnum_spec`), and `fnum_le_iff` / `le_fnum_iff` give the manuscript's
characterisation for loopless `F`: `fnum F ≤ k ↔ ∃ D, IsDecomp ↑F D ∧ D.length ≤ k`. For loopless
`F` (edge sets of simple graphs — the only case in the manuscript, since every `F` there is a
subset of some `E(H)`), `↑F \ diagSet = ↑F` (`coe_sdiff_diagSet_of_loopless`) and `fnum F` is
literally the manuscript's f(F). `f(∅) = 0`: `fnum_empty`, and re-derived in `EGTest/Fnum.lean`
straight from the definition.

*Loop convention (T0, PLAN §7).* The manuscript never takes f of a set with loops (its minimum
would be over the empty set). The formal choice "ignore loops" makes `fnum` total and agrees with
Mathlib's `fromEdgeSet`; I verified the docstring claim
`fnum (fromEdgeSet ↑F).edgeFinset = fnum F` in scratch. The caveat that `fnum F ≤ k` for a raw `F`
with loops does not assert that `F` decomposes is documented in the module docstring, in
`AGENTS.md`, and demonstrated in the tests (`fnum {s(0,0)} = 0`). This is a legitimate T0 encoding
choice and cannot change the meaning of any manuscript statement provided statement authors apply
`fnum` only to loopless sets (`FGraph.edges`, `edgeFinset`, or with `∀ e ∈ F, ¬ e.IsDiag`) — see
note 5.3.

*factAdd counterparts* (theorems in `EG/Lib/Found/Fnum.lean`, all proved; statements compared with
s1:factAdd): (a) `fnum_le_card : fnum F ≤ F.card` (no hypothesis needed — stronger than the
manuscript, which is fine for an upper bound); (b) `fnum_union_le (hd : Disjoint F₁ F₂) :
fnum (F₁ ∪ F₂) ≤ fnum F₁ + fnum F₂`; (c) `fnum_union_eq_of_vertexDisjoint` (no vertex incident to
an edge of both `F₁` and `F₂`, i.e. vertex-disjoint union; the graph form
`fnum_edgeFinset_sup_of_disjoint_support` uses `Disjoint H₁.support H₂.support`, equivalent since
isolated vertices are irrelevant to f); (d) `fnum_map (φ : V ↪ W) : fnum (F.map φ.sym2Map) = fnum F`,
`fnum_edgeFinset_induce_of_support_subset`, `fmax_mono : Monotone fmax`. All match the manuscript
text; (c) and (d) are stated in the edge-set language that the manuscript's proof itself uses
("f(H) depends only on E(H)").

*Verdict:* approve.

### 2.2 `EG.fmax (n : ℕ) : ℕ := Finset.univ.sup fun H : SimpleGraph (Fin n) => fnum H.edgeFinset` (classical)

*Back-translation.* The maximum of f(H) over all simple graphs on the labelled vertex set `Fin n`
(`Finset.sup` on `ℕ` with `⊥ = 0`; the index set is nonempty, so it is a true maximum).

*Manuscript:* "f(n) := max{f(H) : |V(H)| = n}" — over all graphs with exactly n vertices.
Every such graph is isomorphic to one on `Fin n` and f is invariant under relabelling
(`fnum_map`), so the two maxima agree: `fnum_le_fmax` (`Fintype.card V = n → fnum G.edgeFinset ≤ fmax n`,
any `V`) and `exists_fnum_eq_fmax` (attained on `Fin n`), both proved. Isolated vertices count
towards n (`Fin n` has exactly n elements), as in the manuscript. The `open Classical` only
provides `Fintype (SimpleGraph (Fin n))` and `Fintype H.edgeSet`; `edgeFinset` is
instance-independent, so `fmax` does not depend on the choice.

*Edge cases (scratch):* `fmax 0 = 0`, `fmax 1 = 0`; `fmax 2 = 1` (existing test);
`fmax n ≤ n²` (existing test and scratch). *Verdict:* approve.

## 3. `EG/Spec/Main.lean` — `EG.Spec.MainInternal`

```
∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V
```

*Back-translation.* There is one constant `c ∈ ℕ` such that every finite simple graph `G` (on any
finite vertex type in universe 0) has a decomposition of `E(G)` into cycles and single edges with at
most `c·|V(G)|` objects; equivalently (`fnum_edgeFinset_le_iff`) `f(G) ≤ c·|V(G)|` for every finite
simple graph.

*Manuscript* (s1:thmMain): "every graph G on n vertices satisfies f(G) ≤ c_EG n. In particular
f(n) = O(n)"; s7:thmMainProof: "f(G) ≤ c_EG |V(G)| for every graph G. In particular f(n) ≤ c_EG n
for every n, so f(n) = O(n)."

*Checks.*
* **Quantifier order.** `∃ c` precedes `∀ V G`: `c` is uniform, as in the manuscript. I verified in
  scratch that the swapped statement (`∀ V G, ∃ c, …`) is *trivially* provable (take
  `c = |E(G)|`), so the order is both essential and correct.
* **Non-strict `≤`,** as in the manuscript.
* **`c : ℕ` vs real `c_EG`.** Equivalent: an `ℕ` bound is a real bound, and a real bound `C` gives
  the `ℕ` bound `⌈C⌉`. Verified as part of the `IsBigO` equivalence below.
* **"For every n" vs "O(n)".** Scratch theorem `mainInternal_iff_isBigO :
  MainInternal ↔ (fun n => (fmax n : ℝ)) =O[atTop] (fun n => (n : ℝ))`, built on
  `mainInternal_iff_fmax` and the trivial bound `fmax n ≤ n²` (to absorb the finitely many small
  `n`; `fmax 0 = 0` handles `n = 0`). So `MainInternal` is exactly "f(n) = O(n)" for finite simple
  graphs, with `f(n)` the manuscript's `f(n)` as `fmax` (§2.2).
* **Typeclass binders.** `[Fintype V]` is needed for `Fintype.card V` (instance-independent value).
  `[DecidableEq V]` is unused by the body; I verified `MainInternal ↔` the same statement without
  that binder (every type has a classical `DecidableEq`). Neither binder weakens or strengthens the
  statement.
* **Universe.** Only `V : Type`. Because `∃ c` is outermost and f is invariant under relabelling,
  this loses nothing: `mainInternal_iff_fnum_edges` (any universe `u`, `FGraph` form) is proved in
  `FnumMain.lean`; my scratch `mainInternal_universe` derives the `SimpleGraph` form for any
  `Fintype V : Type u`; and `EGCheck/Bridge.lean` (`of_mainInternal`, proved) transports it to the
  universe-polymorphic upstream `Erdos184.erdos_184` with `f n := c·n`. The bridge is a second,
  independent fidelity check that `MainInternal` is at least as strong as the target.
* **`G.edgeSet` (Set) vs `edgeFinset`.** `IsDecomp` takes a `Set`; `↑G.edgeFinset = G.edgeSet`
  (`coe_edgeFinset`), so this is the same statement as PLAN §3 decision 8 (see note 5.1).
* **Non-vacuity.** Not trivially true: the uniform `c` is the whole content (swapped version is
  trivial, see above; `MainInternal → ∀ n, fmax n ≤ c·n` with f(K₄) = 3, f(star_k) = k nontrivial
  values). Not trivially false: every `G` has *some* decomposition
  (`exists_isDecomp_edgeSet_length_eq_fnum`), so `MainInternal` is precisely the Erdős–Gallai
  conjecture in the manuscript's f-notation, no encoding artefact makes it false.

*Verdict:* approve.

## 4. `EG/Lib/Found/FnumMain.lean` (equivalence check requested by the task)

`mainInternal_iff_fmax : MainInternal ↔ ∃ c : ℕ, ∀ n, fmax n ≤ c * n` — proof read and
axioms checked (standard only). Together with §2.2 (`fmax` = manuscript f(n)) and my
`linear_iff_isBigO`, this is "f(n) = O(n)". `mainInternal_iff_fnum_edges` (`FGraph` form, any
universe) and the one-directional forms also read correctly; `fnum H.edges ≤ c * H.card` is
`f(H) ≤ c|H|` with `|H| = |V(H)|` (s1:convGraphs(a), `FGraph.card_def`). Approve.

## 5. Non-blocking notes

1. **PLAN text vs Spec.** `PLAN_FORMALIZATION.md` §3 decision 8 writes `IsDecomp (edgeFinset G) D`;
   the frozen Spec uses `G.edgeSet`. Same statement (coercion); if anything, update the PLAN
   wording — do not touch the Spec.
2. **Unused `[DecidableEq V]`** in `MainInternal`: inert (proved). Keeping it is fine (it mirrors the
   upstream binder shape); mentioning this in the docstring would save future readers a check.
3. **Loop convention is a footgun for statement authors**, not for this definition: `fnum F ≤ k`
   for a raw `F` that might contain loops is weaker than "F decomposes into ≤ k objects". The
   docstrings and `AGENTS.md` already require looplessness (`FGraph.edges`, `edgeFinset`, or
   `∀ e ∈ F, ¬ e.IsDiag`). Recommend that the statement-lock review checklist for later groups
   includes "every `fnum` argument is loopless by construction or by hypothesis". A cheap lint
   (flag `fnum` applied to a bare `Finset` variable without a looplessness hypothesis in scope)
   would make this mechanical.
4. **Reverse bridge** (upstream `Finset G.Subgraph` decomposition ⇒ `IsDecomp`) is not formalized.
   It is not needed for `EGCheck/Final.lean`, and the mathematical argument (§1.4) is elementary;
   recording it as an optional `EGTest` item would close the last informal step in "the two
   notions of object coincide".
5. `Obj.WF` for a cycle does not literally say "≥ 3 edges", but `Nodup ∧ 3 ≤ length` implies
   exactly `length ≥ 3` distinct non-loop edges (`nodup_cycleEdges`, `length_cycleEdges`); nothing
   to change.

## 6. Summary of verdicts

| Item | Verdict |
|---|---|
| `EG.cycleEdges` | approve |
| `EG.Obj` (+ ctors, derived `DecidableEq`) | approve |
| `EG.Obj.edges` | approve |
| `EG.Obj.WF` | approve |
| `EG.IsDecomp` | approve |
| `EG.fnum` | approve (T0 loop convention documented; note 5.3) |
| `EG.fmax` | approve |
| `EG.Spec.MainInternal` | approve (note 5.1, 5.2) |
| `MainInternal ↔ f(n) = O(n)` (`FnumMain`) | approve; strengthened to `=O[atTop]` form in scratch |

No blocking issues. Recommend locking.

---

## Appendix — scratch files (all compile with `lake env lean`, no `sorry`; axioms standard)

### A.1 `Ax.lean` — elaborated definitions and axioms
```lean
import EG.Lib.Found.FnumMain
#print axioms EG.mainInternal_iff_fmax
#print axioms EG.mainInternal_iff_fnum_edges
#print axioms EG.fnum_le_fmax
#print axioms EG.exists_fnum_eq_fmax
#print axioms EG.fnum_edgeFinset_le_iff
#print axioms EG.fnum_map
#check @EG.Spec.MainInternal
#print EG.Spec.MainInternal
#print EG.fnum
#print EG.fmax
#print EG.IsDecomp
#print EG.Obj.WF
#print EG.Obj.edges
#print EG.cycleEdges
set_option pp.universes true in
#check @EG.IsDecomp
set_option pp.universes true in
#check @EG.Obj
```

### A.2 `EdgeCases.lean` — edge cases and non-vacuity
```lean
import EG.Lib.Found.Fnum

open EG

-- cycleEdges on short lists (excluded by WF, but check the raw behaviour)
example : cycleEdges ([] : List ℕ) = [] := by decide
example : cycleEdges [7] = [s((7 : ℕ), 7)] := by decide
example : cycleEdges [0, 1] = [s((0 : ℕ), 1), s(1, 0)] := by decide
example : cycleEdges [0, 1, 2] = [s((0 : ℕ), 1), s(1, 2), s(2, 0)] := by decide
example : cycleEdges [0, 1, 2, 3] = [s((0 : ℕ), 1), s(1, 2), s(2, 3), s(3, 0)] := by decide
-- the 2-list "cycle" has duplicate edge s(0,1)=s(1,0)
example : ¬ (cycleEdges [0, 1] : List (Sym2 ℕ)).Nodup := by decide

-- WF edge cases
example : ¬ (Obj.cycle ([] : List ℕ)).WF := by unfold Obj.WF; decide
example : ¬ (Obj.cycle [0, 1] : Obj ℕ).WF := by unfold Obj.WF; decide
example : ¬ (Obj.cycle [0, 1, 0] : Obj ℕ).WF := by unfold Obj.WF; decide
example : ¬ (Obj.cycle [0, 1, 2, 1] : Obj ℕ).WF := by unfold Obj.WF; decide
example : (Obj.cycle [0, 1, 2] : Obj ℕ).WF := by unfold Obj.WF; decide
example : (Obj.cycle [0, 1, 2, 3] : Obj ℕ).WF := by unfold Obj.WF; decide
example : ¬ (Obj.edge s((3 : ℕ), 3)).WF := by unfold Obj.WF; decide
example : (Obj.edge s((3 : ℕ), 4)).WF := by unfold Obj.WF; decide

-- IsDecomp: positive and negative examples
-- triangle by one cycle object
example : IsDecomp ({s(0, 1), s(1, 2), s(2, 0)} : Set (Sym2 ℕ)) [Obj.cycle [0, 1, 2]] := by
  refine ⟨fun o ho => ?_, by decide, fun e => ?_⟩
  · simp only [List.mem_singleton] at ho; subst ho; exact ⟨by decide, by decide⟩
  · simp [cycleEdges]
-- a rotation and a reversal of the same triangle also decompose it (same edge set)
example : IsDecomp ({s(0, 1), s(1, 2), s(2, 0)} : Set (Sym2 ℕ)) [Obj.cycle [2, 1, 0]] := by
  refine ⟨fun o ho => ?_, by decide, fun e => ?_⟩
  · simp only [List.mem_singleton] at ho; subst ho; exact ⟨by decide, by decide⟩
  · have hc : cycleEdges [2, 1, 0] = [s((2 : ℕ), 1), s(1, 0), s(0, 2)] := by decide
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Obj.edges, hc,
      List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl | rfl) <;> decide
-- missing edge: the path 0-1-2 is not decomposed by the triangle
example : ¬ IsDecomp ({s(0, 1), s(1, 2)} : Set (Sym2 ℕ)) [Obj.cycle [0, 1, 2]] := by
  rintro ⟨-, -, h⟩
  have := (h s(2, 0)).1 (by simp [cycleEdges])
  simp at this
-- edge shared by two objects: not a decomposition (Nodup fails)
example : ¬ IsDecomp ({s(0, 1), s(1, 2), s(2, 0)} : Set (Sym2 ℕ))
    [Obj.cycle [0, 1, 2], Obj.edge s(0, 1)] := by
  rintro ⟨-, h, -⟩
  revert h; decide
-- the same triangle listed twice is not a decomposition
example : ¬ IsDecomp ({s(0, 1), s(1, 2), s(2, 0)} : Set (Sym2 ℕ))
    [Obj.cycle [0, 1, 2], Obj.cycle [1, 2, 0]] := by
  rintro ⟨-, h, -⟩
  revert h; decide
-- 2-"cycle" object is rejected by WF even though it would "cover" a single edge
example : ¬ IsDecomp ({s(0, 1)} : Set (Sym2 ℕ)) [Obj.cycle [0, 1]] := by
  rintro ⟨h, -, -⟩
  exact absurd (h _ (List.mem_singleton_self _)) (by unfold Obj.WF; decide)
-- a set with a loop cannot be decomposed
example (D : List (Obj ℕ)) : ¬ IsDecomp ({s(0, 0), s(0, 1)} : Set (Sym2 ℕ)) D :=
  fun h => h.not_isDiag (e := s(0, 0)) (by simp) (by simp)
-- extra object outside the set is rejected
example : ¬ IsDecomp ({s(0, 1)} : Set (Sym2 ℕ)) [Obj.edge s(0, 1), Obj.edge s(2, 3)] := by
  rintro ⟨-, -, h⟩
  have := (h s(2, 3)).1 (by simp)
  simp at this

-- the manuscript's f(∅) = 0 and single edge
example : fnum (∅ : Finset (Sym2 ℕ)) = 0 := by simp
example : fnum ({s(0, 1)} : Finset (Sym2 ℕ)) = 1 := fnum_singleton (by decide)
-- number of objects = length even when the same list element is reused? (impossible for WF)
example (o : Obj ℕ) (E : Set (Sym2 ℕ)) : ¬ IsDecomp E [o, o] := by
  rintro ⟨hwf, hnd, -⟩
  have hpos := (hwf o (by simp)).length_edges_pos
  simp [List.nodup_append] at hnd
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hpos
  exact hnd.2 e he e he rfl

-- fmax 0 = 0, fmax 1 = 0
example : fmax 0 = 0 := by
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax 0
  rw [← hH]
  refine le_antisymm ((fnum_le_card _).trans ?_) (Nat.zero_le _)
  have := H.card_edgeFinset_le_card_choose_two
  simpa using this
example : fmax 1 = 0 := by
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax 1
  rw [← hH]
  refine le_antisymm ((fnum_le_card _).trans ?_) (Nat.zero_le _)
  have := H.card_edgeFinset_le_card_choose_two
  simpa using this

-- Quantifier order sanity: with `∃ c` inside `∀ V`, the statement is trivially true
-- (so the `∃ c` first in `MainInternal` is essential).
example : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ c : ℕ, ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V := by
  intro V _ G
  classical
  obtain ⟨D, hD, hlen⟩ := exists_isDecomp_edgeSet_length_eq_fnum G
  refine ⟨G.edgeFinset.card, D, hD, ?_⟩
  rw [hlen]
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · have : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | h a b => exact absurd (Fintype.card_pos_iff.2 ⟨a⟩) (by omega)
    simp [this]
  · exact (fnum_le_card _).trans (Nat.le_mul_of_pos_right _ hpos)

-- Docstring claim of `EG/Defs/Fnum.lean`: `fnum F = f(fromEdgeSet F)`.
example {V : Type} [DecidableEq V] (F : Finset (Sym2 V))
    [Fintype (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).edgeSet] :
    fnum (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).edgeFinset = fnum F := by
  rw [← fnum_filter_not_isDiag F]
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
```

### A.3 `BigO.lean` — `MainInternal ↔ fmax =O[atTop] n`, inert binders, universe transport
```lean
import EG.Lib.Found.FnumMain
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Group.Basic

open EG Filter Asymptotics

/-- Trivial bound f(n) ≤ n² (independent re-derivation for the scratch check). -/
theorem fmax_le_sq' (n : ℕ) : fmax n ≤ n * n := by
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax n
  rw [← hH]
  refine (fnum_le_card _).trans (H.card_edgeFinset_le_card_choose_two.trans ?_)
  rw [Fintype.card_fin, Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- `∃ c : ℕ, ∀ n, fmax n ≤ c n`  ↔  `fmax = O(n)` (as real-valued functions, `atTop`). -/
theorem linear_iff_isBigO :
    (∃ c : ℕ, ∀ n, fmax n ≤ c * n) ↔
      (fun n : ℕ => (fmax n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · rintro ⟨c, hc⟩
    refine (isBigO_iff.2 ⟨c, Eventually.of_forall fun n => ?_⟩)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast hc n
  · intro h
    obtain ⟨C, hC⟩ := isBigO_iff.1 h
    obtain ⟨N, hN⟩ := eventually_atTop.1 hC
    refine ⟨⌈C⌉₊ + N, fun n => ?_⟩
    by_cases hn : N ≤ n
    · have h1 := hN n hn
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at h1
      have h2 : (fmax n : ℝ) ≤ (⌈C⌉₊ : ℝ) * n := h1.trans
        (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity))
      have h3 : fmax n ≤ ⌈C⌉₊ * n := by exact_mod_cast h2
      exact h3.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · push Not at hn
      calc fmax n ≤ n * n := fmax_le_sq' n
        _ ≤ N * n := Nat.mul_le_mul_right _ hn.le
        _ ≤ (⌈C⌉₊ + N) * n := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- The internal spec is exactly `f(n) = O(n)`. -/
theorem mainInternal_iff_isBigO :
    Spec.MainInternal ↔ (fun n : ℕ => (fmax n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
  mainInternal_iff_fmax.trans linear_iff_isBigO

/-- The `[DecidableEq V]` binder in `MainInternal` is inert. -/
theorem mainInternal_iff_noDecEq :
    Spec.MainInternal ↔ ∃ c : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun V _ G => by classical exact hc V G⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun V _ _ G => hc V G⟩

universe u
/-- Universe generality: the spec (over `Type`) gives the bound for `SimpleGraph`s on any
`Fintype V : Type u`. -/
theorem mainInternal_universe (h : Spec.MainInternal) :
    ∃ c : ℕ, ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet],
      ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V := by
  obtain ⟨c, hc⟩ := fnum_edges_le_of_mainInternal.{u} h
  refine ⟨c, fun V _ G _ => ?_⟩
  have := hc V (FGraph.ofSimpleGraph G)
  simp only [FGraph.ofSimpleGraph, FGraph.card_def, Finset.card_univ] at this
  exact (fnum_edgeFinset_le_iff G).1 this

#print axioms mainInternal_iff_isBigO
#print axioms mainInternal_universe
```
