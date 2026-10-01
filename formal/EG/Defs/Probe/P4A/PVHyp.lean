module

public import EG.Defs.Vortex.PVData
public import EG.Defs.Link.HBFamily
public import EG.Defs.Expander

/-!
# The hypotheses of Lemma PV as named predicates (manuscript s4:lemPV)

NEW DEFS FILE of probe unit P4A (probe P-4, part 1). TRIAGE §2.8 (PV-DATA-RECORD): "The PV Spec
takes `D : PVData V` and states its hypotheses about the fields … The PV hypotheses as named Defs
remain the s4 Spec author's job." No locked Defs file provides them; design note
`formal/work/p2b/P4A.md`.

Manuscript v6.1, `s4.tex`, Lemma [s4:lemPV]:
"Let `Z` be a set of `N ≥ N_0` vertices and `L := log₂N`. Put `J := ⌊log₂(L/8)⌋`,
`m := ⌈L^6⌉`, `b := ⌈2^7L^2m⌉`, `t := 2^9L^8`. The following data are fixed (not random):
* a spanning `(2^{-6},s_O)`-expander `O` on `Z` with `2m ≤ s_O`, and sets `A(w) ⊆ N_O(w)`
  (`w ∈ Z`) with `|A(w)| = m` such that every vertex lies in at most `b` of them (such sets
  exist by Lemma s3:lemHB with `ε' = 2^{-6}` and `m = m`);
* pairwise edge-disjoint graphs `R_{j,c}` (`0 ≤ j < J`, `c ∈ [4]`) and `M` on `Z`, the *own
  classes*, each a spanning `(2^{-6},s')`-expander on `Z` with `s' ≥ 2^{145}L^{41}`;
* a partition `Z = Rt ⊔ Pl` into *rooted* and *parentless* vertices;
* an external phase map `ext : Z → [4] ∪ {*}`.
For `w ∈ Z` let `C_w := {wu : u ∈ A(w), wu ∈ E(M), ext(u) = *}`, and assume
(E1′) `|C_w| ≥ L^5/8` for every `w ∈ Pl`."
and, for the conclusion, "for *every* edge set `H_0` all of whose edges have both ends in `Z` and
which contains `E(M)` and every `E(R_{j,c})`".

Formal reading (fields of `EG.Vortex.PVData`; `N = |Z| = D.Z.card`, `L = EG.Vortex.L N`):
* "`N ≥ N_0`": `EG.Vortex.PVSize N` (the size conditions (i), (ii), (iv) of the proof; TRIAGE
  §2.4, blueprint TPV-SIZE-PRED: `N_0` is *defined* through these conditions, so the Spec takes
  the predicate, and `N0Cond N0 → N0 ≤ N → PVSize N` gives the manuscript form);
* "spanning `(ε,s)`-expander on `Z`": `G.verts = Z ∧ G.IsExpander ε s` (CONVENTIONS);
* the `A`-family: `EG.IsHBFamily O m b A` with `m = pvM N`, `b = pvB N` (the count is over
  `w ∈ V(O) = Z`, as "every vertex lies in at most `b` of them (`w ∈ Z`)");
* the own classes `D.R i`, `i : Fin (pvJ N) × Fin 4` (`(j, c)` with `c ∈ [4]` as `Fin 4`), and
  `D.M`; "pairwise edge-disjoint" among all `4J + 1` of them;
* the partition: `Disjoint Rt Pl ∧ Rt ∪ Pl = Z`;
* (E1′): `C_w` is counted through its far ends `u` (`u ↦ wu` is injective), exactly the form
  of `EG.Light.E1_childData` (`EG/Lib/Light/Stages.lean`), so that the s5 instance
  `EG.Light.childData ω Z` meets it with no bridge;
* `H_0` admissible: loopless (T0: "edge set of a simple graph", CONVENTIONS "Objects and f"),
  both ends in `Z`, `E(M) ⊆ H_0`, `E(R_{j,c}) ⊆ H_0`.
-/

@[expose] public section

namespace EG.Vortex

variable {V : Type*} [DecidableEq V]

/-- [s4:lemPV] (E1′) "For `w ∈ Z` let `C_w := {wu : u ∈ A(w), wu ∈ E(M), ext(u) = *}`, and assume
`|C_w| ≥ L^5/8` for every `w ∈ Pl`." The set `C_w` is counted by its far ends `u`. -/
def PVE1' (D : PVData V) : Prop :=
  ∀ w ∈ D.Pl, L D.Z.card ^ 5 / 8 ≤
    (((D.A w).filter fun u => s(w, u) ∈ D.M.edges ∧ D.ext u = none).card : ℝ)

/-- [s4:lemPV] the hypotheses on the fixed data (module docstring): the size condition
(`N ≥ N_0`), the graph `O` and the sets `A(w)`, the own classes, the partition `Z = Rt ⊔ Pl`, and
(E1′). The phase map `ext` is arbitrary. -/
def PVHyp (D : PVData V) : Prop :=
  -- "Let `Z` be a set of `N ≥ N_0` vertices"
  PVSize D.Z.card ∧
  -- "a spanning `(2^{-6},s_O)`-expander `O` on `Z` with `2m ≤ s_O`"
  D.O.verts = D.Z ∧ D.O.IsExpander (2 ^ (-6 : ℤ)) D.sO ∧ 2 * (pvM D.Z.card : ℝ) ≤ D.sO ∧
  -- "sets `A(w) ⊆ N_O(w)` (`w ∈ Z`) with `|A(w)| = m` such that every vertex lies in at most `b`
  -- of them"
  IsHBFamily D.O (pvM D.Z.card) (pvB D.Z.card) D.A ∧
  -- "each a spanning `(2^{-6},s')`-expander on `Z` with `s' ≥ 2^{145}L^{41}`"
  (∀ i, (D.R i).verts = D.Z ∧ (D.R i).IsExpander (2 ^ (-6 : ℤ)) D.sOwn) ∧
  D.M.verts = D.Z ∧ D.M.IsExpander (2 ^ (-6 : ℤ)) D.sOwn ∧
  (2 : ℝ) ^ 145 * L D.Z.card ^ 41 ≤ D.sOwn ∧
  -- "pairwise edge-disjoint graphs `R_{j,c}` … and `M`"
  (∀ i i', i ≠ i' → Disjoint (D.R i).edges (D.R i').edges) ∧
  (∀ i, Disjoint (D.R i).edges D.M.edges) ∧
  -- "a partition `Z = Rt ⊔ Pl`"
  Disjoint D.Rt D.Pl ∧ D.Rt ∪ D.Pl = D.Z ∧
  -- (E1′)
  PVE1' D

/-- [s4:lemPV] the admissible edge sets: "every edge set `H_0` all of whose edges have both ends
in `Z` and which contains `E(M)` and every `E(R_{j,c})`" (loopless: an edge set of a simple
graph). -/
def PVAdm (D : PVData V) (H0 : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ H0, ¬ e.IsDiag) ∧ (∀ e ∈ H0, ∀ v ∈ e, v ∈ D.Z) ∧
    D.M.edges ⊆ H0 ∧ ∀ i, (D.R i).edges ⊆ H0

end EG.Vortex
