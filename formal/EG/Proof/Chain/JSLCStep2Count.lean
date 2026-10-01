module

public import EG.Proof.Chain.JSLCStep2JPlus
public import EG.Lib.Stage1.Pool

/-!
# JS-LC Step 2: counting `J_l` (manuscript s6:lemJSLC, proof, Step 2, (s6:eqJbound))

Probe unit P2J (probe P-2, part 2), proof round 1. "Counting `J_l`.
* PAR deletions: `Σ_{a,b} |J'_ab(Z)| ≤ ½ Σ_{a,b} |V(E_ab(Z))|`. A port `u ∈ Q*_Z` lies in
  `V(E_ab(Z))` only for `{a,b} = {Y(u), Y(v)}` with `uv ∈ B_Z ⊆ E_l(Z)` and `v ∈ Q_Z`. This happens
  for at most `c_pp(u)` pairs, so the PAR deletions number at most `½ Σ_{u∈Q_Z} c_pp(u)`.
* Moves at a hub `h ∈ D_l`: at most one per class `Y` for which `h` is the centre of an edge
  `hu ∈ E_l(Z)` with `u ∈ Q_Z` and `Y(u) = Y`, i.e. with `d_{Y,l}(h) ≥ 1`. So at most `c^agg_{h,l}`
  moves, summed over all parts containing `h`.
* Moves at a fresh centre `x ∈ F_Z`: `x ∉ D_l` lies in one part only, so at most `c_x(Z)` moves.
* Moves at a lost centre `v ∈ Lost_Z`: at most the number of edges of `E_l(Z)` at `v`, which is
  at most `M_l − 1`.
This proves (s6:eqJbound)."
-/

public section

namespace EG.Chain.Step2

open EG.HB

/-- A sum over a `biUnion` is at most the sum of the sums (natural numbers). -/
theorem sum_biUnion_le_nat {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (f : β → ℕ) : ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    omega

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)}

namespace Step2Hyp

variable (H : Step2Hyp run G δ S l B)
include H

/-! ### PAR deletions -/

omit H in
theorem edgeVerts_Epp_subset (a : Addr) (p : Sym2 PartId) :
    edgeVerts (Epp run G δ S l B a p) ⊆ run.classed G l a := by
  intro u hu
  unfold edgeVerts at hu
  obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.1 hu
  exact qs_subset_classed run G δ S l a ((mem_Epp.1 he).2.1 u (Sym2.mem_toFinset.1 hue))

/-- For a port `u`, the class pairs `p` with `u ∈ V(E_p(Z))` are at most `c_pp(u)`. -/
theorem card_pairs_le_cPP {a : Addr} (ha : a ∈ run.Std G l) (P : Finset (Sym2 PartId)) (u : V) :
    (P.filter (fun p => u ∈ edgeVerts (Epp run G δ S l B a p))).card ≤ cPP run G δ l a u := by
  classical
  unfold cPP
  set T := ((run.classed G l a).filter (fun v => s(u, v) ∈ run.E G l a)).image (δ l)
  have hsub : P.filter (fun p => u ∈ edgeVerts (Epp run G δ S l B a p)) ⊆
      T.image (fun Y => s(δ l u, Y)) := by
    intro p hp
    obtain ⟨-, hu⟩ := Finset.mem_filter.1 hp
    unfold edgeVerts at hu
    obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.1 hu
    obtain ⟨heB, hpp, hmap⟩ := mem_Epp.1 he
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.1 (Sym2.mem_toFinset.1 hue)
    refine Finset.mem_image.2 ⟨δ l v, Finset.mem_image.2 ⟨v, Finset.mem_filter.2
      ⟨H.qs_classed (hpp v (by simp)), H.mem_E ha heB⟩, rfl⟩, ?_⟩
    rw [← hmap, Sym2.map_mk]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

open Classical in
/-- The PAR deletions of one part number at most `½ Σ_{u∈Q_Z} c_pp(u)`. -/
theorem two_mul_card_Jpar_part_le {a : Addr} (ha : a ∈ run.Std G l) :
    2 * ((B a).filter (fun e => IsPP run G δ S l a e ∧
      e ∈ parJ run G δ S l B a (e.map (δ l)))).card ≤
      ∑ u ∈ run.classed G l a, cPP run G δ l a u := by
  classical
  set P := ((B a).filter (fun e => IsPP run G δ S l a e)).image (Sym2.map (δ l)) with hP
  have hsub : (B a).filter (fun e => IsPP run G δ S l a e ∧
      e ∈ parJ run G δ S l B a (e.map (δ l))) ⊆ P.biUnion (parJ run G δ S l B a) := by
    intro e he
    obtain ⟨heB, hpp, hJ⟩ := Finset.mem_filter.1 he
    exact Finset.mem_biUnion.2 ⟨e.map (δ l),
      Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨heB, hpp⟩, rfl⟩, hJ⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := P) (t := parJ run G δ S l B a)
  have h3 : ∀ p ∈ P, 2 * (parJ run G δ S l B a p).card ≤
      (edgeVerts (Epp run G δ S l B a p)).card := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨heB, hpp⟩ := Finset.mem_filter.1 he
    exact ((parJ_spec run G δ S l B a _).2 H.Epp_map (H.map_not_isDiag ha heB hpp)).1
  have h4 : ∑ p ∈ P, (edgeVerts (Epp run G δ S l B a p)).card =
      ∑ u ∈ run.classed G l a, (P.filter (fun p => u ∈ edgeVerts (Epp run G δ S l B a p))).card := by
    have : ∀ p ∈ P, (edgeVerts (Epp run G δ S l B a p)).card =
        ∑ u ∈ run.classed G l a, if u ∈ edgeVerts (Epp run G δ S l B a p) then 1 else 0 := by
      intro p _
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 (edgeVerts_Epp_subset a p)]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => (Finset.card_filter _ _).symm
  have h5 : ∑ u ∈ run.classed G l a,
      (P.filter (fun p => u ∈ edgeVerts (Epp run G δ S l B a p))).card ≤
      ∑ u ∈ run.classed G l a, cPP run G δ l a u :=
    Finset.sum_le_sum fun u _ => H.card_pairs_le_cPP ha P u
  have h6 : 2 * ∑ p ∈ P, (parJ run G δ S l B a p).card ≤
      ∑ p ∈ P, (edgeVerts (Epp run G δ S l B a p)).card := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum h3
  omega

/-- All PAR deletions: `2 |J^par| ≤ Σ_Z Σ_{u∈Q_Z} c_pp(u)`. -/
theorem two_mul_card_Jpar_le :
    2 * (Jpar run G δ S l B).card ≤
      ∑ a ∈ run.Std G l, ∑ u ∈ run.classed G l a, cPP run G δ l a u := by
  classical
  have h1 : (Jpar run G δ S l B).card ≤ ∑ a ∈ run.Std G l,
      ((B a).filter (fun e => IsPP run G δ S l a e ∧
        e ∈ parJ run G δ S l B a (e.map (δ l)))).card := by
    unfold Jpar
    exact Finset.card_biUnion_le
  have h2 := Finset.sum_le_sum fun a (ha : a ∈ run.Std G l) => H.two_mul_card_Jpar_part_le ha
  rw [← Finset.mul_sum] at h2
  omega

/-! ### Moves -/

/-- The number of classes with a move at `h`. -/
noncomputable def nMoves (h : V) : ℕ :=
  ((classes run G δ S l).filter (fun Y => h ∈ oddC run G δ S l B Y)).card

omit H in
theorem card_Jmov_le :
    (Jmov run G δ S l B).card ≤ ∑ h ∈ (classes run G δ S l).biUnion (oddC run G δ S l B),
      nMoves (run := run) (G := G) (δ := δ) (S := S) (l := l) (B := B) h := by
  classical
  unfold Jmov nMoves
  refine Finset.card_biUnion_le.trans ?_
  have h1 : ∀ Y ∈ classes run G δ S l, (Moved run G δ S l B Y).card ≤
      ∑ h ∈ (classes run G δ S l).biUnion (oddC run G δ S l B),
        if h ∈ oddC run G δ S l B Y then 1 else 0 := by
    intro Y hY
    unfold Moved
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2]
    exact Finset.subset_biUnion_of_mem _ hY
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun h _ => (Finset.card_filter _ _).symm

/-- An odd centre lies in `A_Z ∪ F_Z ∪ Lost_Z` of its part: in `D_l`, a fresh centre or a lost
centre. -/
theorem mem_roles {Y : PartId} {h : V} (hh : h ∈ oddC run G δ S l B Y) :
    h ∈ run.D G l ∨ h ∈ freshCentres run G l ∨ h ∈ lostRound run G δ S l := by
  obtain ⟨-, a, ha, -, -, -, -, -, hr, -⟩ := H.mv_struct hh
  unfold ret at hr
  rcases Finset.mem_union.1 hr with hr | hr
  · rcases Finset.mem_union.1 hr with hr | hr
    · exact Or.inl (hubs_subset_D run G l a hr)
    · exact Or.inr (Or.inl ((mem_freshCentres run G).2 ⟨a, ha, hr⟩))
  · exact Or.inr (Or.inr ((mem_lostRound run G δ S).2 ⟨a, ha, hr⟩))

/-- The part of the moved edge at a vertex `h ∉ D_l` of `Z^0` is `Z`. -/
theorem part_of_mv {Y : PartId} {h : V} (hh : h ∈ oddC run G δ S l B Y) {a : Addr}
    (ha : a ∈ run.Std G l) (hZ : h ∈ run.Z0 G l a) (hD : h ∉ run.D G l) :
    mv run G δ S l B Y h ∈ B a ∧ ∃ u, mv run G δ S l B Y h = s(h, u) ∧
      u ∈ qs run G δ S l a ∧ δ l u = Y := by
  obtain ⟨-, a', ha', heB, u, heq, hu, hY, -, -⟩ := H.mv_struct hh
  have hhe : h ∈ mv run G δ S l B Y h := by rw [heq]; exact Sym2.mem_mk_left _ _
  obtain rfl : a' = a := eq_of_mem_Z0_of_notMem_D run G (Std_subset_prePartAddrs run G l ha')
    (Std_subset_prePartAddrs run G l ha)
    (Run.partVerts_subset_Z0 run G l a' (Run.mem_partVerts_of_mem_E run G (H.mem_E ha' heB) hhe))
    hZ hD
  exact ⟨heB, u, heq, hu, hY⟩

theorem nMoves_le_cAgg (h : V) :
    nMoves (run := run) (G := G) (δ := δ) (S := S) (l := l) (B := B) h ≤ cAgg run G δ h l := by
  classical
  unfold nMoves cAgg
  refine Finset.card_le_card fun Y hY => ?_
  obtain ⟨-, hh⟩ := Finset.mem_filter.1 hY
  obtain ⟨-, a, ha, heB, u, heq, hu, rfl, -, -⟩ := H.mv_struct hh
  unfold cAggClasses
  refine Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2
    ⟨H.qs_classed hu, ?_⟩⟩, rfl⟩
  rw [← heq]; exact H.mem_E ha heB

theorem nMoves_le_cFresh {a : Addr} (ha : a ∈ run.Std G l) {x : V}
    (hx : x ∈ run.fresh G l a) :
    nMoves (run := run) (G := G) (δ := δ) (S := S) (l := l) (B := B) x ≤ cFresh run G δ l a x := by
  classical
  unfold nMoves cFresh
  have hxp := fresh_subset_ports run G l a hx
  refine Finset.card_le_card fun Y hY => ?_
  obtain ⟨-, hh⟩ := Finset.mem_filter.1 hY
  obtain ⟨heB, u, heq, hu, rfl⟩ := H.part_of_mv hh ha (ports_subset_Z0 run G l a hxp)
    (not_mem_D_of_mem_ports run G hxp)
  refine Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨H.qs_classed hu, ?_⟩, rfl⟩
  rw [← heq]; exact H.mem_E ha heB

theorem nMoves_le_M {a : Addr} (ha : a ∈ run.Std G l) {v : V}
    (hv : v ∈ lost run G δ S l a) :
    nMoves (run := run) (G := G) (δ := δ) (S := S) (l := l) (B := B) v ≤ run.M G l - 1 := by
  classical
  unfold nMoves
  have hvp := classed_subset_ports run G l a (lost_subset_classed run G δ S l a hv)
  refine le_trans ?_ (H.cap a ha v)
  refine Finset.card_le_card_of_injOn (fun Y => mv run G δ S l B Y v) ?_ ?_
  · intro Y hY
    obtain ⟨-, hh⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hY)
    obtain ⟨heB, u, heq, -, -⟩ := H.part_of_mv hh ha (ports_subset_Z0 run G l a hvp)
      (not_mem_D_of_mem_ports run G hvp)
    refine Finset.mem_coe.2 (FGraph.mem_edgesAt.2 ⟨H.mem_E ha heB, ?_⟩)
    show v ∈ mv run G δ S l B Y v
    rw [heq]; exact Sym2.mem_mk_left _ _
  · intro Y hY Y' hY' heq
    obtain ⟨-, hh⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hY)
    obtain ⟨-, hh'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hY')
    by_contra hne
    have h1 := (H.mv_struct hh).1
    have h2 := (H.mv_struct hh').1
    simp only at heq
    rw [heq] at h1
    exact Finset.disjoint_left.1 (H.R0_disjoint hne) h1 h2

/-- The moves number at most `Σ_{h∈D_l} c^agg_{h,l} + Σ_Z [Σ_{x∈F_Z} c_x(Z) + (M_l−1)|Lost_Z|]`. -/
theorem card_Jmov_le_bound :
    (Jmov run G δ S l B).card ≤ ∑ h ∈ run.D G l, cAgg run G δ h l +
      ∑ a ∈ run.Std G l, (∑ x ∈ run.fresh G l a, cFresh run G δ l a x +
        (run.M G l - 1) * (lost run G δ S l a).card) := by
  classical
  set f := fun h => nMoves (run := run) (G := G) (δ := δ) (S := S) (l := l) (B := B) h
  set W := (classes run G δ S l).biUnion (oddC run G δ S l B)
  have hW : W ⊆ run.D G l ∪ (freshCentres run G l ∪ lostRound run G δ S l) := by
    intro h hh
    obtain ⟨Y, -, hh⟩ := Finset.mem_biUnion.1 hh
    rcases H.mem_roles hh with h1 | h1 | h1
    · exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h1)
  have h1 : ∑ h ∈ W, f h ≤ ∑ h ∈ run.D G l ∪ (freshCentres run G l ∪ lostRound run G δ S l), f h :=
    Finset.sum_le_sum_of_subset hW
  have h2 := Finset.sum_union_inter (s₁ := run.D G l)
    (s₂ := freshCentres run G l ∪ lostRound run G δ S l) (f := f)
  have h3 := Finset.sum_union_inter (s₁ := freshCentres run G l)
    (s₂ := lostRound run G δ S l) (f := f)
  have hD : ∑ h ∈ run.D G l, f h ≤ ∑ h ∈ run.D G l, cAgg run G δ h l :=
    Finset.sum_le_sum fun h _ => H.nMoves_le_cAgg h
  have hF : ∑ h ∈ freshCentres run G l, f h ≤
      ∑ a ∈ run.Std G l, ∑ x ∈ run.fresh G l a, cFresh run G δ l a x := by
    unfold freshCentres
    refine (sum_biUnion_le_nat _ _ _).trans (Finset.sum_le_sum fun a ha =>
      Finset.sum_le_sum fun x hx => H.nMoves_le_cFresh ha hx)
  have hL : ∑ h ∈ lostRound run G δ S l, f h ≤
      ∑ a ∈ run.Std G l, (run.M G l - 1) * (lost run G δ S l a).card := by
    unfold lostRound
    refine (sum_biUnion_le_nat _ _ _).trans (Finset.sum_le_sum fun a ha => ?_)
    refine (Finset.sum_le_sum fun v hv => H.nMoves_le_M ha hv).trans (le_of_eq ?_)
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h4 : (Jmov run G δ S l B).card ≤ ∑ h ∈ W, f h :=
    card_Jmov_le (run := run) (G := G) (δ := δ) (S := S) (l := l) (B := B)
  rw [Finset.sum_add_distrib]
  omega

/-- (s6:eqJbound) `|J_l| ≤ Σ_{h∈D_l} c^agg_{h,l} + Σ_Z [Σ_{x∈F_Z} c_x(Z) + (M_l−1)|Lost_Z|
+ ½ Σ_{u∈Q_Z} c_pp(u)]`. -/
theorem card_J_le_jBound : ((J run G δ S l B).card : ℝ) ≤ jBound run G δ S l := by
  have h1 : (J run G δ S l B).card ≤ (Jpar run G δ S l B).card + (Jmov run G δ S l B).card :=
    Finset.card_union_le _ _
  have h2 := H.two_mul_card_Jpar_le
  have h3 := H.card_Jmov_le_bound
  have hM : 1 ≤ run.M G l := le_trans (Nat.one_le_two_pow) (EG.Stage1.two_pow_le_M G run l)
  have h1' : ((J run G δ S l B).card : ℝ) ≤ (Jpar run G δ S l B).card + (Jmov run G δ S l B).card := by
    exact_mod_cast h1
  have h2' : 2 * ((Jpar run G δ S l B).card : ℝ) ≤
      ∑ a ∈ run.Std G l, ∑ u ∈ run.classed G l a, (cPP run G δ l a u : ℝ) := by
    exact_mod_cast h2
  have h3' : ((Jmov run G δ S l B).card : ℝ) ≤ ∑ h ∈ run.D G l, (cAgg run G δ h l : ℝ) +
      ∑ a ∈ run.Std G l, (∑ x ∈ run.fresh G l a, (cFresh run G δ l a x : ℝ) +
        ((run.M G l : ℝ) - 1) * ((lost run G δ S l a).card : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 h3
    push_cast [Nat.cast_sub hM] at this
    exact this
  unfold jBound
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib] at h3'
  have h4 : ∑ a ∈ run.Std G l, (1 / 2 : ℝ) * ∑ u ∈ run.classed G l a, (cPP run G δ l a u : ℝ) =
      (1 / 2) * ∑ a ∈ run.Std G l, ∑ u ∈ run.classed G l a, (cPP run G δ l a u : ℝ) := by
    rw [Finset.mul_sum]
  rw [h4]
  linarith

end Step2Hyp

end EG.Chain.Step2
