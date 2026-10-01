module

public import EG.Spec.HB.HS
public import EG.Lib.Found.Graph

/-!
# Lemma HS: expansion after deleting a vertex set (manuscript s2:lemHS)

Helper lemmas for the P3 stubs `EG.Todo.HS` and `EG.Todo.HSCor` (unit P3-s2).
* `EG.HB.card_deleteVerts_real`: `z' = z - |W|` (as reals) for `W ⊆ V(X)`;
* `EG.HB.hs_expander`: the expansion claim of the proof ("Put `F := F' ∪ E_X(U,W)` … Hence
  `Nbr_{X-F}(U) = Nbr_{(X-W)-F'}(U)` …");
* `EG.HB.hs_ratio`: "`(log z'/log z)² ≥ 1/2` … it suffices that `log z ≥ 3.414…`, i.e.
  `z ≥ 10.67`; this holds as `z ≥ 11`" (we use `log₂ 11 ≥ 69/20`).
-/

public section

namespace EG.HB

open Real EG.FGraph

variable {V : Type*} [DecidableEq V]

/-- `|X - W| = |X| - |W|` (as reals) for `W ⊆ V(X)`. -/
theorem card_deleteVerts_real (X : FGraph V) {W : Finset V} (hW : W ⊆ X.verts) :
    ((X.deleteVerts W).card : ℝ) = (X.card : ℝ) - W.card := by
  have h1 : (X.deleteVerts W).card = X.card - W.card := by
    rw [card_def, deleteVerts_verts, Finset.card_sdiff_of_subset hW, card_def]
  have h2 : W.card ≤ X.card := by rw [card_def]; exact Finset.card_le_card hW
  rw [h1, Nat.cast_sub h2]

/-- `log₂ 11 ≥ 69/20` (as `2^{69} ≤ 11^{20}`). -/
theorem logb_eleven_ge : (69 / 20 : ℝ) ≤ logb 2 11 := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h : ((2 : ℝ) ^ ((69 : ℝ) / 20)) ^ (20 : ℕ) = (2 : ℝ) ^ (69 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ ((69 : ℝ) / 20) := by positivity
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num : (20 : ℕ) ≠ 0)
  rw [h] at this
  norm_num at this

/-- Proof of [s2:lemHS]: "`(log z'/log z)² ≥ 1/2` … since `z' ≥ z/2`, it suffices that
`log z ≥ 3.414…`; this holds as `z ≥ 11`" (for real `z ≥ 11` and `z/2 ≤ z'`). -/
theorem hs_ratio {z z' : ℝ} (hz : 11 ≤ z) (hz' : z / 2 ≤ z') :
    1 / 2 ≤ (logb 2 z' / logb 2 z) ^ 2 := by
  have hzpos : 0 < z := by linarith
  have hz'pos : 0 < z' := by linarith
  have hL : 69 / 20 ≤ logb 2 z :=
    logb_eleven_ge.trans (Real.logb_le_logb_of_le (by norm_num) (by norm_num) hz)
  have hL' : logb 2 z - 1 ≤ logb 2 z' := by
    have h1 : logb 2 (z / 2) ≤ logb 2 z' :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hz'
    rw [Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one (by norm_num)] at h1
    exact h1
  have hLpos : 0 < logb 2 z := by linarith
  rw [div_pow, le_div_iff₀ (by positivity)]
  have hL'nn : 0 ≤ logb 2 z - 1 := by linarith
  have hsq : (logb 2 z - 1) ^ 2 ≤ logb 2 z' ^ 2 := pow_le_pow_left₀ hL'nn hL' 2
  nlinarith

/-- The expansion claim of [s2:lemHS] (proof): `X - W` is an `(ε'(log z'/log z)², s - s_W)`-
expander. -/
theorem hs_expander (X : FGraph V) (W : Finset V) (ε' s sW : ℝ) (hz : 11 ≤ X.card)
    (hX : X.IsExpander ε' s) (hW : W ⊆ X.verts) (hWc : (W.card : ℝ) ≤ (X.card : ℝ) / 2)
    (hdeg : ∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ sW) :
    (X.deleteVerts W).IsExpander
      (ε' * (logb 2 ((X.card : ℝ) - W.card) / logb 2 X.card) ^ 2) (s - sW) := by
  intro U F' hU hF' h1 h2 h3
  rw [deleteVerts_verts] at hU
  have hcard := card_deleteVerts_real X hW
  set EUW : Finset (Sym2 V) := U.biUnion (fun u => (X.nbrs u ∩ W).image (fun w => s(u, w)))
    with hEUW
  have hEUWc : (EUW.card : ℝ) ≤ sW * U.card := by
    have hc1 : EUW.card ≤ ∑ u ∈ U, ((X.nbrs u ∩ W).image (fun w => s(u, w))).card :=
      Finset.card_biUnion_le
    have hc2 : ∑ u ∈ U, ((X.nbrs u ∩ W).image (fun w => s(u, w))).card ≤
        ∑ u ∈ U, (X.nbrs u ∩ W).card :=
      Finset.sum_le_sum (fun u _ => Finset.card_image_le)
    have hc3 : (∑ u ∈ U, ((X.nbrs u ∩ W).card : ℝ)) ≤ ∑ _u ∈ U, sW :=
      Finset.sum_le_sum (fun u hu => hdeg u (hU hu))
    rw [Finset.sum_const, nsmul_eq_mul] at hc3
    have : (EUW.card : ℝ) ≤ ∑ u ∈ U, ((X.nbrs u ∩ W).card : ℝ) := by
      exact_mod_cast hc1.trans hc2
    linarith
  set F := F' ∪ EUW with hF
  have hFsub : F ⊆ X.edges := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact (X.deleteVerts_le W).2 (hF' he)
    · obtain ⟨u, -, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
      exact (X.mem_nbrs).1 (Finset.mem_inter.1 hw).1
  have hFc : (F.card : ℝ) ≤ s * U.card := by
    have : F.card ≤ F'.card + EUW.card := Finset.card_union_le _ _
    have : (F.card : ℝ) ≤ F'.card + EUW.card := by exact_mod_cast this
    nlinarith
  have hUX : U ⊆ X.verts := fun u hu => (Finset.mem_sdiff.1 (hU hu)).1
  have hU2 : (U.card : ℝ) ≤ 2 * (X.card : ℝ) / 3 := by
    rw [hcard] at h2
    have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    linarith
  have key := hX U F hUX hFsub h1 hU2 hFc
  have hsub : (X.deleteEdges F).nbrSet U ⊆ ((X.deleteVerts W).deleteEdges F').nbrSet U := by
    intro v hv
    rw [mem_nbrSet] at hv ⊢
    obtain ⟨hvX, hvU, u, hu, hadj⟩ := hv
    rw [deleteEdges_adj] at hadj
    have hvW : v ∉ W := by
      intro hvW
      apply hadj.2
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_image.2
        ⟨v, Finset.mem_inter.2 ⟨(X.mem_nbrs).2 hadj.1, hvW⟩, rfl⟩⟩)
    have huW : u ∉ W := (Finset.mem_sdiff.1 (hU hu)).2
    refine ⟨?_, hvU, u, hu, ?_⟩
    · rw [deleteEdges_verts, deleteVerts_verts]
      exact Finset.mem_sdiff.2 ⟨by rwa [deleteEdges_verts] at hvX, hvW⟩
    · rw [deleteEdges_adj, deleteVerts_adj]
      exact ⟨⟨hadj.1, huW, hvW⟩, fun h => hadj.2 (Finset.mem_union_left _ h)⟩
  have hcardle : (((X.deleteEdges F).nbrSet U).card : ℝ) ≤
      ((((X.deleteVerts W).deleteEdges F').nbrSet U).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans (le_of_eq ?_) (key.trans hcardle)
  rw [hcard]
  have hz11 : (11 : ℝ) ≤ X.card := by exact_mod_cast hz
  have hz' : (X.card : ℝ) / 2 ≤ (X.card : ℝ) - W.card := by linarith
  have hLz : 0 < logb 2 (X.card : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hLz' : 0 < logb 2 ((X.card : ℝ) - W.card) := Real.logb_pos (by norm_num) (by linarith)
  field_simp

end EG.HB
