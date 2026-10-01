module

public import EG.Lib.Chain.MixCRound
public import EG.Defs.Probe.S5.KRED

/-!
# Edge-set facts for the assembly of Theorem MIX-C (manuscript s6:thmMIXC (a), (b))

Unit P3-s6, round 1. Facts about the chain of `EG.Chain.MixCA.chain_exists` used to show that the
output is a decomposition of `E(G)` (s6:thmMIXC (b)):
* `disjoint_goodLent_E`: the edges lent at round `l'` avoid `E_l(Z)` for `l' ≤ l + 1` (the lent
  classes at round `l'` belong to ancestors of rounds `≤ l' − 2 < l`; s2:propStructure(iii) via
  `StructureHY`);
* `disjoint_goodLent`: lent edges of distinct rounds are distinct (s3:lemCOL(g), classes pairwise
  disjoint, and `E(H_Y)` pairwise disjoint);
* `disjoint_LJS_LJV`: within a round, `LentJS_l ∩ LentJV_l = ∅`;
* `goodLent_subset_edges`: lent edges are edges of `G`;
* `lext_*`: the family `Lent_ext(Y) := LentAll ∩ (⋃ LJS_Y ∪ ⋃ LJV_Y)` of K-RED.
-/

public section

namespace EG.Chain.MixCA

open EG.HB EG.Chain EG.Quot

universe u

variable {V : Type u} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}
  {S : StageData V}

section HY

variable (hHY : EG.Spec.StructureHYStatement.{u}) (hv : run.Valid G Dstar)
include hHY hv

theorem ancGraph_subset_E {Y : PartId} (hY : Y ∈ run.ancestors G) :
    (run.ancGraph G Y).edges ⊆ run.E G Y.1 Y.2 :=
  (hHY V G Dstar run hv).1 Y hY

theorem disjoint_E_of_ne {Y Y' : PartId} (hY : Y ∈ run.ancestors G) (hY' : Y' ∈ run.ancestors G)
    (h : Y ≠ Y') : Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2) :=
  (hHY V G Dstar run hv).2.2.1 Y hY Y' hY' h

theorem disjoint_ancGraph_of_ne {Y Y' : PartId} (hY : Y ∈ run.ancestors G)
    (hY' : Y' ∈ run.ancestors G) (h : Y ≠ Y') :
    Disjoint (run.ancGraph G Y).edges (run.ancGraph G Y').edges :=
  (hHY V G Dstar run hv).2.2.2 Y hY Y' hY' h

/-- Distinct standalone pre-parts (of any rounds) have disjoint `E_l(Z)`. -/
theorem disjoint_E_std {l l' : ℕ} {a a' : Addr} (ha : a ∈ run.Std G l) (ha' : a' ∈ run.Std G l')
    (h : (l, a) ≠ (l', a')) : Disjoint (run.E G l a) (run.E G l' a') :=
  disjoint_E_of_ne hHY hv (Y := (l, a)) (Y' := (l', a'))
    ((Run.mem_ancestors run G).2 ((Run.mem_Std_iff run G).1 ha).1)
    ((Run.mem_ancestors run G).2 ((Run.mem_Std_iff run G).1 ha').1) h

/-- The good lent edges of round `l'` avoid `E_l(Z)` for every `Z ∈ Std_l` with `l' ≤ l + 1`. -/
theorem disjoint_goodLent_E (hS : S.Coherent run G) {l l' : ℕ} (hll : l' ≤ l + 1) {a : Addr}
    (ha : a ∈ run.Std G l) : Disjoint (goodLent run G S l') (run.E G l a) := by
  rw [Finset.disjoint_left]
  intro e he heE
  obtain ⟨Y, hY, hYl, -, heY⟩ := mem_goodLent hS he
  have hZ : ((l, a) : PartId) ∈ run.ancestors G :=
    (Run.mem_ancestors run G).2 ((Run.mem_Std_iff run G).1 ha).1
  have hne : Y ≠ (l, a) := by
    rintro rfl
    simp at hYl
    omega
  exact Finset.disjoint_left.1 (disjoint_E_of_ne hHY hv hY hZ hne)
    (ancGraph_subset_E hHY hv hY heY) heE

omit hHY hv in
/-- The lent class of `Y` at round `l` (JS classes `j < K^JS_l`, or the JV class). -/
theorem goodLent_class {l : ℕ} {e : Sym2 V} (he : e ∈ goodLent run G S l) :
    ∃ Y ∈ lendGoodAnc run G S l,
      (∃ j < Stage1.KJS G run l, e ∈ S.ljs Y l j) ∨ e ∈ S.ljv Y l := by
  unfold goodLent at he
  obtain ⟨Y, hY, he⟩ := Finset.mem_biUnion.1 he
  refine ⟨Y, hY, ?_⟩
  rcases Finset.mem_union.1 he with he | he
  · obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.1 he
    exact Or.inl ⟨j, Finset.mem_range.1 hj, he⟩
  · exact Or.inr he

omit hHY hv in
theorem mem_ancestors_of_lendGoodAnc {l : ℕ} {Y : PartId} (hY : Y ∈ lendGoodAnc run G S l) :
    Y ∈ run.ancestors G := by
  classical
  unfold lendGoodAnc at hY
  exact (Finset.mem_filter.1 hY).1

omit hHY hv in
theorem not_lendBad_of_lendGoodAnc {l : ℕ} {Y : PartId} (hY : Y ∈ lendGoodAnc run G S l) :
    ¬ lendBad run G S Y := by
  classical
  unfold lendGoodAnc at hY
  exact (Finset.mem_filter.1 hY).2.2

omit hHY hv in
theorem class_subset {Y : PartId} (hS : S.Coherent run G) {l : ℕ} {e : Sym2 V}
    (h : (∃ j < Stage1.KJS G run l, e ∈ S.ljs Y l j) ∨ e ∈ S.ljv Y l) :
    e ∈ (run.ancGraph G Y).edges := by
  rcases h with ⟨j, -, h⟩ | h
  · exact hS.ljs_sub Y l j h
  · exact hS.ljv_sub Y l h

/-- Two lent classes containing a common edge belong to the same ancestor. -/
theorem class_eq {Y Y' : PartId} (hS : S.Coherent run G) (hY : Y ∈ run.ancestors G)
    (hY' : Y' ∈ run.ancestors G) {l l' : ℕ} {e : Sym2 V}
    (h : (∃ j < Stage1.KJS G run l, e ∈ S.ljs Y l j) ∨ e ∈ S.ljv Y l)
    (h' : (∃ j < Stage1.KJS G run l', e ∈ S.ljs Y' l' j) ∨ e ∈ S.ljv Y' l') : Y = Y' := by
  by_contra hne
  exact Finset.disjoint_left.1 (disjoint_ancGraph_of_ne hHY hv hY hY' hne)
    (class_subset hS h) (class_subset hS h')

/-- Good lent edges of distinct rounds are distinct. -/
theorem disjoint_goodLent (hS : S.Coherent run G) {l l' : ℕ} (hll : l ≠ l') :
    Disjoint (goodLent run G S l) (goodLent run G S l') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨Y, hY, h⟩ := goodLent_class he
  obtain ⟨Y', hY', h'⟩ := goodLent_class he'
  have hYY := class_eq hHY hv hS (mem_ancestors_of_lendGoodAnc hY)
    (mem_ancestors_of_lendGoodAnc hY') h h'
  subst hYY
  rcases h with ⟨j, -, h⟩ | h <;> rcases h' with ⟨j', -, h'⟩ | h'
  · exact Finset.disjoint_left.1 (hS.ljs_disj Y l j l' j' (by simp [hll])) h h'
  · exact Finset.disjoint_left.1 (hS.ljs_ljv_disj Y l j l') h h'
  · exact Finset.disjoint_left.1 (hS.ljs_ljv_disj Y l' j' l) h' h
  · exact Finset.disjoint_left.1 (hS.ljv_disj Y l l' hll) h h'

/-- Within a round, the JS-lent and the JV-lent edges are distinct. -/
theorem disjoint_LJS_LJV (hS : S.Coherent run G) {l : ℕ} {A B : Finset (Sym2 V)}
    (hA : A ⊆ (lendGoodAnc run G S l).biUnion
        (fun Y => (Finset.range (Stage1.KJS G run l)).biUnion (S.ljs Y l)))
    (hB : B ⊆ (lendGoodAnc run G S l).biUnion (fun Y => S.ljv Y l)) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨Y, hY, h⟩ := Finset.mem_biUnion.1 (hA he)
  obtain ⟨j, hj, h⟩ := Finset.mem_biUnion.1 h
  obtain ⟨Y', hY', h'⟩ := Finset.mem_biUnion.1 (hB he')
  have hYY := class_eq hHY hv hS (l := l) (l' := l) (mem_ancestors_of_lendGoodAnc hY)
    (mem_ancestors_of_lendGoodAnc hY') (Or.inl ⟨j, Finset.mem_range.1 hj, h⟩) (Or.inr h')
  subst hYY
  exact Finset.disjoint_left.1 (hS.ljs_ljv_disj Y l j l) h h'

/-- Good lent edges are edges of `G`. -/
theorem goodLent_subset_edges (hS : S.Coherent run G) (l : ℕ) :
    goodLent run G S l ⊆ G.edges := by
  intro e he
  obtain ⟨Y, hY, -, -, heY⟩ := mem_goodLent hS he
  exact E_subset_edges run G _ _ (ancGraph_subset_E hHY hv hY heY)

end HY

end EG.Chain.MixCA
