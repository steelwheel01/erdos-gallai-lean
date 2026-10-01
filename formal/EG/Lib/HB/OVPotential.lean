module

public import EG.Lib.HB.Address

/-!
# Lemma OV: the potential argument (manuscript s2:lemOVgeneric)

Unit P3A, proof round 1 (hazard H2 of `work/p2b/P3A.md`: potential instead of the chain/integral
argument).

Per-vertex form of the charging of (a). Fix `M ≥ 2` and a vertex `u`. The charge of `u` is
`Σ w(|ν|)` over the non-leaf nodes `ν` with `|ν| ≥ M` and `u ∈ U'_ν`, `w(x) = 1/log² x`. With
`C = 1/log² M + 1/(c_OV log M)` and the potential
`Φ(x) = [x ≥ M] (C - 1/(c_OV log x))`, the charge of `u` in the subtree of a node `ν` is at most
`ℓ_u(ν) Φ(|ν|)`, where `ℓ_u(ν)` is the number of leaves below `ν` containing `u`
(`STree.ov_vertex`, induction on the tree). Two facts about `Φ` are used:
`w(x) ≤ Φ(x)` for `x ≥ M`, and `w(x) + Φ(x₁) ≤ Φ(x)` for `M ≤ x₁ ≤ (3/4) x`
(`log x ≥ log x₁ + c_OV`, so `1/log² x ≤ 1/(log x log x₁) ≤ (1/c_OV)(1/log x₁ - 1/log x)`).
Summing over `u` gives `Σ_{|ν| ≥ M} |U'_ν| w(|ν|) ≤ C S` (`STree.ov_charge`), which is (a).

Also: (b) by induction (`STree.ov_leaves_le`), the identity `Σ_v dup_{≥M}(v) = Δ_{≥M}`, the
consequence of (b), and (c). Numerics: `c_OV ≥ 17/41` (`2^65 ≥ 3^41`, hazard H1).
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

/-! ### Numerics -/

/-- `c_OV = log₂(4/3) ≥ 17/41` (from `2^65 ≥ 3^41`). -/
theorem cOV_ge : (17 / 41 : ℝ) ≤ cOV := by
  unfold cOV
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h : ((2 : ℝ) ^ ((17 : ℝ) / 41)) ^ (41 : ℕ) = 2 ^ (17 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (41 : ℕ) ≠ 0), h]
  norm_num

theorem cOV_pos : 0 < cOV := lt_of_lt_of_le (by norm_num) cOV_ge

/-- `logb 2 (4/3 * x) = c_OV + logb 2 x` for `x ≠ 0`. -/
theorem logb_four_thirds_mul {x : ℝ} (hx : x ≠ 0) :
    logb 2 (4 / 3 * x) = cOV + logb 2 x := by
  rw [Real.logb_mul (by norm_num) hx]
  rfl

/-- The weight `w(x) = 1 / log² x`. -/
@[expose] noncomputable def ovW (x : ℝ) : ℝ := 1 / logb 2 x ^ 2

/-- The constant `C = 1/log² M + 1/(c_OV log M)`. -/
@[expose] noncomputable def ovC (M : ℝ) : ℝ := 1 / logb 2 M ^ 2 + 1 / (cOV * logb 2 M)

/-- The potential `Φ(x) = [x ≥ M] (C - 1/(c_OV log x))`. -/
@[expose] noncomputable def ovPhi (M x : ℝ) : ℝ :=
  if M ≤ x then ovC M - 1 / (cOV * logb 2 x) else 0

section Numerics

variable {M : ℝ}

theorem one_le_logb_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 ≤ logb 2 x := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
  simpa using hx

theorem ovW_nonneg (x : ℝ) : 0 ≤ ovW x := by
  unfold ovW
  positivity

theorem ovPhi_nonneg (hM : 2 ≤ M) (x : ℝ) : 0 ≤ ovPhi M x := by
  unfold ovPhi ovC
  split_ifs with hx
  · have hLM := one_le_logb_of_two_le hM
    have hLx : logb 2 M ≤ logb 2 x := Real.logb_le_logb_of_le (by norm_num) (by linarith) hx
    have hc := cOV_pos
    have h1 : 1 / (cOV * logb 2 x) ≤ 1 / (cOV * logb 2 M) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hLx hc.le
    have h2 : 0 ≤ 1 / logb 2 M ^ 2 := by positivity
    linarith
  · exact le_rfl

theorem ovPhi_le_ovC (hM : 2 ≤ M) (x : ℝ) : ovPhi M x ≤ ovC M := by
  have hLM := one_le_logb_of_two_le hM
  have hC : 0 ≤ ovC M := by
    unfold ovC
    have := cOV_pos
    positivity
  unfold ovPhi
  split_ifs with hx
  · have hLx : 0 < logb 2 x := by
      have := one_le_logb_of_two_le (le_trans hM hx)
      linarith
    have := cOV_pos
    have : 0 ≤ 1 / (cOV * logb 2 x) := by positivity
    linarith
  · exact hC

theorem ovPhi_mono (hM : 2 ≤ M) {x y : ℝ} (hxy : x ≤ y) : ovPhi M x ≤ ovPhi M y := by
  by_cases hx : M ≤ x
  · have hy : M ≤ y := le_trans hx hxy
    unfold ovPhi
    rw [if_pos hx, if_pos hy]
    have hLx : 1 ≤ logb 2 x := one_le_logb_of_two_le (le_trans hM hx)
    have hLxy : logb 2 x ≤ logb 2 y := Real.logb_le_logb_of_le (by norm_num) (by linarith) hxy
    have hc := cOV_pos
    have : 1 / (cOV * logb 2 y) ≤ 1 / (cOV * logb 2 x) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hLxy hc.le
    linarith
  · have : ovPhi M x = 0 := by unfold ovPhi; rw [if_neg hx]
    rw [this]
    exact ovPhi_nonneg hM y

/-- `w(x) ≤ Φ(x)` for `x ≥ M`. -/
theorem ovW_le_ovPhi (hM : 2 ≤ M) {x : ℝ} (hx : M ≤ x) : ovW x ≤ ovPhi M x := by
  unfold ovW ovPhi ovC
  rw [if_pos hx]
  have hLM := one_le_logb_of_two_le hM
  have hLxy : logb 2 M ≤ logb 2 x := Real.logb_le_logb_of_le (by norm_num) (by linarith) hx
  have hc := cOV_pos
  have h1 : 1 / logb 2 x ^ 2 ≤ 1 / logb 2 M ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by linarith) hLxy 2
  have h2 : 1 / (cOV * logb 2 x) ≤ 1 / (cOV * logb 2 M) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hLxy hc.le
  linarith

/-- The potential step: `w(x) + Φ(x₁) ≤ Φ(x)` for `M ≤ x₁` and `x₁ ≤ (3/4) x`. -/
theorem ovW_add_ovPhi_le (hM : 2 ≤ M) {x x₁ : ℝ} (hx₁ : M ≤ x₁) (h34 : x₁ ≤ 3 / 4 * x) :
    ovW x + ovPhi M x₁ ≤ ovPhi M x := by
  have hx : M ≤ x := by linarith
  unfold ovW ovPhi
  rw [if_pos hx₁, if_pos hx]
  have hc := cOV_pos
  set y₁ := logb 2 x₁ with hy₁
  set y := logb 2 x with hy
  have hy₁1 : 1 ≤ y₁ := one_le_logb_of_two_le (le_trans hM hx₁)
  have hstep : cOV + y₁ ≤ y := by
    rw [hy₁, ← logb_four_thirds_mul (by linarith)]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hy1 : 1 ≤ y := by linarith
  -- `1/y² ≤ 1/(y y₁) ≤ (y - y₁)/(c y y₁) = 1/(c y₁) - 1/(c y)`
  have key : 1 / y ^ 2 ≤ 1 / (cOV * y₁) - 1 / (cOV * y) := by
    have hyp : 0 < y := by linarith
    have hy1p : 0 < y₁ := by linarith
    have e : 1 / (cOV * y₁) - 1 / (cOV * y) = (y - y₁) / (cOV * y * y₁) := by
      field_simp
    rw [e, div_le_div_iff₀ (pow_pos hyp 2) (mul_pos (mul_pos hc hyp) hy1p)]
    have h1 : cOV * y * y₁ ≤ cOV * y * y :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos hc hyp).le
    have h2 : cOV * y * y ≤ (y - y₁) * y ^ 2 := by
      rw [show cOV * y * y = cOV * y ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_pos hyp 2).le
    linarith
  linarith

theorem ovC_le (hM : 2 ≤ M) : ovC M ≤ 3.42 / logb 2 M := by
  unfold ovC
  have hL := one_le_logb_of_two_le hM
  have hc := cOV_ge
  have hcp := cOV_pos
  have h1 : 1 / logb 2 M ^ 2 ≤ 1 / logb 2 M := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h2 : 1 / (cOV * logb 2 M) ≤ (41 / 17) / logb 2 M := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3 : 1 / logb 2 M + (41 / 17) / logb 2 M ≤ 3.42 / logb 2 M := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    norm_num
  linarith

/-- The sharp form `C ≤ (1 + 41/17)/log M` (for `1.6 (1 + 1/c_OV) ≤ 5.46`, hazard H1). -/
theorem ovC_le_sharp (hM : 2 ≤ M) : ovC M ≤ (58 / 17) / logb 2 M := by
  unfold ovC
  have hL := one_le_logb_of_two_le hM
  have hc := cOV_ge
  have hcp := cOV_pos
  have h1 : 1 / logb 2 M ^ 2 ≤ 1 / logb 2 M := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h2 : 1 / (cOV * logb 2 M) ≤ (41 / 17) / logb 2 M := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3 : 1 / logb 2 M + (41 / 17) / logb 2 M = (58 / 17) / logb 2 M := by
    rw [← add_div]
    norm_num
  linarith

theorem ovC_nonneg (hM : 2 ≤ M) : 0 ≤ ovC M := by
  unfold ovC
  have := cOV_pos
  have := one_le_logb_of_two_le hM
  positivity

end Numerics

namespace STree

/-! ### Node decomposition of `OVHyp` -/

theorem ovHyp_node {ε c : ℝ} {p : Finset V × Finset V} {l r : STree V} {K : FGraph V}
    (h : (STree.node p l r).OVHyp ε c K) :
    (p.1 ⊆ K.verts ∧ p.2 ⊆ K.verts ∧ Disjoint p.1 p.2) ∧
      (2 ≤ K.card ∧ ((splitFst K p.1 p.2).card : ℝ) ≤ 3 / 4 * (K.card : ℝ) ∧
        (p.2.card : ℝ) ≤ c * ε * p.1.card / Real.logb 2 K.card ^ 2) ∧
      l.OVHyp ε c (splitFst K p.1 p.2) ∧ r.OVHyp ε c (splitSnd K p.1 p.2) := by
  obtain ⟨hwf, hn⟩ := h
  obtain ⟨h0, hl, hr⟩ := (wf_node_iff p l r K).1 hwf
  refine ⟨h0, by simpa using hn [] (by simp [internalAddrs_node]), ⟨hl, fun a ha => ?_⟩,
    ⟨hr, fun a ha => ?_⟩⟩
  · simpa using hn (false :: a) (by simpa using ha)
  · simpa using hn (true :: a) (by simpa using ha)

/-! ### (a): the per-vertex potential bound -/

/-- The charge of `u` in `t` (rooted at `K`): `Σ w(|ν|)` over the non-leaf `ν` with `|ν| ≥ M`
and `u ∈ U'_ν`. -/
@[expose] noncomputable def ovCharge (M : ℝ) (t : STree V) (K : FGraph V) (u : V) : ℝ :=
  ∑ a ∈ t.internalAddrs,
    if M ≤ ((t.graphAtD K a).card : ℝ) ∧ u ∈ t.labelU a then ovW (t.graphAtD K a).card else 0

theorem card_filter_leaf_verts_eq_zero (t : STree V) {K : FGraph V} {u : V}
    (hu : u ∉ K.verts) : (t.leafAddrs.filter (fun a => u ∈ (t.graphAtD K a).verts)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun a _ h => hu (graphAtD_verts_subset t K a h)

theorem one_le_card_filter_leaf_verts (t : STree V) {K : FGraph V} {u : V}
    (hu : u ∈ K.verts) : 1 ≤ (t.leafAddrs.filter (fun a => u ∈ (t.graphAtD K a).verts)).card := by
  obtain ⟨a, ha, hua⟩ := exists_mem_leafAddrs_mem_verts t hu
  exact Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, hua⟩⟩

theorem ovCharge_nonneg (M : ℝ) (t : STree V) (K : FGraph V) (u : V) :
    0 ≤ t.ovCharge M K u := by
  unfold ovCharge
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact ovW_nonneg _
  · exact le_rfl

theorem ovCharge_eq_zero (M : ℝ) (t : STree V) {K : FGraph V} (hK : t.WF K) {u : V}
    (hu : u ∉ K.verts) : t.ovCharge M K u = 0 := by
  unfold ovCharge
  apply Finset.sum_eq_zero
  intro a ha
  rw [if_neg]
  rintro ⟨-, hua⟩
  exact hu (labelU_subset_root hK ha hua)

/-- [s2:lemOVgeneric] (a), per vertex: the charge of `u` is at most
`ℓ_u · Φ(|H_0|)`. -/
theorem ov_vertex {ε c M : ℝ} (hM : 2 ≤ M) (t : STree V) {K : FGraph V}
    (ht : t.OVHyp ε c K) (u : V) :
    t.ovCharge M K u ≤
      ((t.leafAddrs.filter (fun a => u ∈ (t.graphAtD K a).verts)).card : ℝ) *
        ovPhi M (K.card : ℝ) := by
  induction t generalizing K with
  | nil =>
    simp only [ovCharge, internalAddrs_nil, Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) (ovPhi_nonneg hM _)
  | node p l r ihl ihr =>
    obtain ⟨⟨hU, -, -⟩, ⟨-, h34, -⟩, hl, hr⟩ := ovHyp_node ht
    have hcnt : ((STree.node p l r).leafAddrs.filter
        (fun a => u ∈ ((STree.node p l r).graphAtD K a).verts)).card =
        (l.leafAddrs.filter (fun a => u ∈ (l.graphAtD (splitFst K p.1 p.2) a).verts)).card +
        (r.leafAddrs.filter (fun a => u ∈ (r.graphAtD (splitSnd K p.1 p.2) a).verts)).card :=
      card_filter_leafAddrs_node p l r _
    have hG : (STree.node p l r).ovCharge M K u =
        (if M ≤ (K.card : ℝ) ∧ u ∈ p.1 then ovW (K.card : ℝ) else 0) +
          (l.ovCharge M (splitFst K p.1 p.2) u + r.ovCharge M (splitSnd K p.1 p.2) u) := by
      unfold ovCharge
      rw [sum_internalAddrs_node]
      simp only [graphAtD_node_nil, graphAtD_node_false, graphAtD_node_true, labelU_node_nil,
        labelU_node_false, labelU_node_true]
      rfl
    rw [hG, hcnt]
    have il := ihl hl
    have ir := ihr hr
    set ℓl := (l.leafAddrs.filter (fun a => u ∈ (l.graphAtD (splitFst K p.1 p.2) a).verts)).card
    set ℓr := (r.leafAddrs.filter (fun a => u ∈ (r.graphAtD (splitSnd K p.1 p.2) a).verts)).card
    have hf : ((splitFst K p.1 p.2).card : ℝ) ≤ K.card := by
      exact_mod_cast splitFst_card_le K p.1 p.2
    have hg : ((splitSnd K p.1 p.2).card : ℝ) ≤ K.card := by
      exact_mod_cast splitSnd_card_le K p.1 p.2
    have hPl := ovPhi_mono hM hf
    have hPg := ovPhi_mono hM hg
    have hΦK := ovPhi_nonneg hM (K.card : ℝ)
    have hΦf := ovPhi_nonneg hM ((splitFst K p.1 p.2).card : ℝ)
    have hΦg := ovPhi_nonneg hM ((splitSnd K p.1 p.2).card : ℝ)
    by_cases hup : u ∈ p.1
    · -- `u` goes only to the first child
      have hℓr : ℓr = 0 := card_filter_leaf_verts_eq_zero r (not_mem_splitSnd_verts_of_mem_left hup)
      have hℓl : 1 ≤ ℓl := one_le_card_filter_leaf_verts l (mem_splitFst_verts_of_mem_left hU hup)
      have hℓl' : (1 : ℝ) ≤ ℓl := by exact_mod_cast hℓl
      rw [hℓr] at ir ⊢
      simp only [Nat.cast_zero, zero_mul, add_zero] at ir ⊢
      by_cases hMK : M ≤ (K.card : ℝ)
      · rw [if_pos ⟨hMK, hup⟩]
        have hstep : ovW (K.card : ℝ) + ovPhi M ((splitFst K p.1 p.2).card : ℝ) ≤
            ovPhi M (K.card : ℝ) := by
          by_cases hMf : M ≤ ((splitFst K p.1 p.2).card : ℝ)
          · exact ovW_add_ovPhi_le hM hMf h34
          · have : ovPhi M ((splitFst K p.1 p.2).card : ℝ) = 0 := by
              unfold ovPhi; rw [if_neg hMf]
            rw [this, add_zero]
            exact ovW_le_ovPhi hM hMK
        have hw := ovW_nonneg (K.card : ℝ)
        have hr0 : r.ovCharge M (splitSnd K p.1 p.2) u ≤ 0 := ir
        nlinarith
      · rw [if_neg (fun h => hMK h.1)]
        have hr0 : r.ovCharge M (splitSnd K p.1 p.2) u ≤ 0 := ir
        nlinarith
    · rw [if_neg (fun h => hup h.2), zero_add, Nat.cast_add]
      have h1 : (ℓl : ℝ) * ovPhi M ((splitFst K p.1 p.2).card : ℝ) ≤ ℓl * ovPhi M K.card :=
        mul_le_mul_of_nonneg_left hPl (Nat.cast_nonneg _)
      have h2 : (ℓr : ℝ) * ovPhi M ((splitSnd K p.1 p.2).card : ℝ) ≤ ℓr * ovPhi M K.card :=
        mul_le_mul_of_nonneg_left hPg (Nat.cast_nonneg _)
      nlinarith

/-- [s2:lemOVgeneric] (a), charge form: `Σ_{|ν| ≥ M} |U'_ν| / log²|ν| ≤ C S`. -/
theorem ov_charge {ε c M : ℝ} (hM : 2 ≤ M) (t : STree V) {H : FGraph V}
    (ht : t.OVHyp ε c H) :
    ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)),
        ((t.labelU a).card : ℝ) * ovW (t.graphAtD H a).card ≤ ovC M * t.leafMass H := by
  -- sum the per-vertex bound over `u ∈ V(H)`
  have hsum : ∑ u ∈ H.verts, t.ovCharge M H u =
      ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)),
        ((t.labelU a).card : ℝ) * ovW (t.graphAtD H a).card := by
    unfold ovCharge
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hMa : M ≤ ((t.graphAtD H a).card : ℝ)
    · rw [if_pos hMa]
      have : ∀ u, (if M ≤ ((t.graphAtD H a).card : ℝ) ∧ u ∈ t.labelU a then
          ovW ((t.graphAtD H a).card : ℝ) else 0) =
          if u ∈ t.labelU a then ovW ((t.graphAtD H a).card : ℝ) else 0 := by
        intro u
        simp only [hMa, true_and]
      simp_rw [this]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (labelU_subset_root ht.1 ha),
        Finset.sum_const, nsmul_eq_mul]
    · rw [if_neg hMa]
      apply Finset.sum_eq_zero
      intro u _
      rw [if_neg (fun h => hMa h.1)]
  have hleaf : ∑ u ∈ H.verts,
      ((t.leafAddrs.filter (fun a => u ∈ (t.graphAtD H a).verts)).card : ℝ) =
        (t.leafMass H : ℝ) := by
    unfold leafMass
    push_cast
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 (graphAtD_verts_subset t H a)]
    rfl
  rw [← hsum]
  calc ∑ u ∈ H.verts, t.ovCharge M H u
      ≤ ∑ u ∈ H.verts, ((t.leafAddrs.filter (fun a => u ∈ (t.graphAtD H a).verts)).card : ℝ) *
          ovPhi M (H.card : ℝ) := Finset.sum_le_sum fun u _ => ov_vertex hM t ht u
    _ ≤ ∑ u ∈ H.verts, ((t.leafAddrs.filter (fun a => u ∈ (t.graphAtD H a).verts)).card : ℝ) *
          ovC M := Finset.sum_le_sum fun u _ =>
            mul_le_mul_of_nonneg_left (ovPhi_le_ovC hM _) (Nat.cast_nonneg _)
    _ = ovC M * t.leafMass H := by rw [← Finset.sum_mul, hleaf, mul_comm]

/-- [s2:lemOVgeneric] (a), first inequality: `Δ_{≥M} ≤ c ε C S`. -/
theorem ov_a {ε c M : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (hM : 2 ≤ M) (t : STree V) {H : FGraph V}
    (ht : t.OVHyp ε c H) :
    (t.DeltaGe H M : ℝ) ≤ c * ε * ovC M * t.leafMass H := by
  unfold DeltaGe
  push_cast
  calc ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)),
        ((t.labelN a).card : ℝ)
      ≤ ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)),
          c * ε * (((t.labelU a).card : ℝ) * ovW (t.graphAtD H a).card) := by
        apply Finset.sum_le_sum
        intro a ha
        have := (ht.2 a (Finset.mem_filter.1 ha).1).2.2
        unfold ovW
        calc ((t.labelN a).card : ℝ) ≤ c * ε * (t.labelU a).card /
              Real.logb 2 (t.graphAtD H a).card ^ 2 := this
          _ = _ := by ring
    _ = c * ε * ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)),
          ((t.labelU a).card : ℝ) * ovW (t.graphAtD H a).card := by rw [Finset.mul_sum]
    _ ≤ c * ε * (ovC M * t.leafMass H) :=
        mul_le_mul_of_nonneg_left (ov_charge hM t ht) (mul_nonneg hc hε)
    _ = c * ε * ovC M * t.leafMass H := by ring

/-! ### (b) -/

/-- [s2:lemOVgeneric] (b), subtree form: the number of leaves of size `≥ M` containing `v` is at
most `[v ∈ V(K), |K| ≥ M] + dup_{≥M}(v)`. -/
theorem ov_leaves_le (M : ℝ) (t : STree V) (K : FGraph V) (v : V) :
    (t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD K L).card : ℝ) ∧
        v ∈ (t.graphAtD K L).verts)).card ≤
      (if v ∈ K.verts ∧ M ≤ (K.card : ℝ) then 1 else 0) + t.dupGe K M v := by
  induction t generalizing K with
  | nil =>
    unfold dupGe
    simp only [leafAddrs_nil, graphAtD_nil, internalAddrs_nil, Finset.filter_empty,
      Finset.card_empty, add_zero]
    split_ifs with h
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · rw [Finset.card_eq_zero.2]
      rw [Finset.filter_eq_empty_iff]
      intro _ _ h'
      exact h ⟨h'.2, h'.1⟩
  | node p l r ihl ihr =>
    have hcnt : ((STree.node p l r).leafAddrs.filter
        (fun L => M ≤ (((STree.node p l r).graphAtD K L).card : ℝ) ∧
          v ∈ ((STree.node p l r).graphAtD K L).verts)).card =
        (l.leafAddrs.filter (fun L => M ≤ ((l.graphAtD (splitFst K p.1 p.2) L).card : ℝ) ∧
          v ∈ (l.graphAtD (splitFst K p.1 p.2) L).verts)).card +
        (r.leafAddrs.filter (fun L => M ≤ ((r.graphAtD (splitSnd K p.1 p.2) L).card : ℝ) ∧
          v ∈ (r.graphAtD (splitSnd K p.1 p.2) L).verts)).card :=
      card_filter_leafAddrs_node p l r _
    have hdup : (STree.node p l r).dupGe K M v =
        (if M ≤ (K.card : ℝ) ∧ v ∈ p.2 then 1 else 0) +
          (l.dupGe (splitFst K p.1 p.2) M v + r.dupGe (splitSnd K p.1 p.2) M v) :=
      card_filter_internalAddrs_node p l r _
    rw [hcnt, hdup]
    have il := ihl (splitFst K p.1 p.2)
    have ir := ihr (splitSnd K p.1 p.2)
    have hf : ((splitFst K p.1 p.2).card : ℝ) ≤ K.card := by
      exact_mod_cast splitFst_card_le K p.1 p.2
    have hg : ((splitSnd K p.1 p.2).card : ℝ) ≤ K.card := by
      exact_mod_cast splitSnd_card_le K p.1 p.2
    have hfv : (splitFst K p.1 p.2).verts ⊆ K.verts := (splitFst_le K p.1 p.2).1
    have hgv : (splitSnd K p.1 p.2).verts ⊆ K.verts := (splitSnd_le K p.1 p.2).1
    have key : (if v ∈ (splitFst K p.1 p.2).verts ∧ M ≤ ((splitFst K p.1 p.2).card : ℝ)
        then 1 else 0) + (if v ∈ (splitSnd K p.1 p.2).verts ∧
          M ≤ ((splitSnd K p.1 p.2).card : ℝ) then 1 else 0) ≤
        (if v ∈ K.verts ∧ M ≤ (K.card : ℝ) then 1 else 0) +
          (if M ≤ (K.card : ℝ) ∧ v ∈ p.2 then 1 else 0) := by
      by_cases hA : v ∈ (splitFst K p.1 p.2).verts ∧ M ≤ ((splitFst K p.1 p.2).card : ℝ)
      · have hP : v ∈ K.verts ∧ M ≤ (K.card : ℝ) := ⟨hfv hA.1, le_trans hA.2 hf⟩
        by_cases hB : v ∈ (splitSnd K p.1 p.2).verts ∧ M ≤ ((splitSnd K p.1 p.2).card : ℝ)
        · have hQ : M ≤ (K.card : ℝ) ∧ v ∈ p.2 :=
            ⟨hP.2, mem_right_of_mem_both hA.1 hB.1⟩
          rw [if_pos hA, if_pos hB, if_pos hP, if_pos hQ]
        · rw [if_pos hA, if_neg hB, if_pos hP]
          omega
      · by_cases hB : v ∈ (splitSnd K p.1 p.2).verts ∧ M ≤ ((splitSnd K p.1 p.2).card : ℝ)
        · have hP : v ∈ K.verts ∧ M ≤ (K.card : ℝ) := ⟨hgv hB.1, le_trans hB.2 hg⟩
          rw [if_neg hA, if_pos hB, if_pos hP]
          omega
        · rw [if_neg hA, if_neg hB]
          omega
    omega


/-! ### The identity `Σ_v dup_{≥M}(v) = Δ_{≥M}`, the consequence of (b), and (c) -/

/-- [s2:lemOVgeneric] "(so `Σ_v dup_{≥M}(v) = Δ_{≥M}`)". -/
theorem sum_dupGe (M : ℝ) (t : STree V) {H : FGraph V} (ht : t.WF H) :
    ∑ v ∈ H.verts, t.dupGe H M v = t.DeltaGe H M := by
  unfold dupGe DeltaGe
  have e1 : ∀ v, (t.internalAddrs.filter
      (fun a => M ≤ ((t.graphAtD H a).card : ℝ) ∧ v ∈ t.labelN a)).card =
      ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)),
        if v ∈ t.labelN a then 1 else 0 := by
    intro v
    rw [← Finset.filter_filter, Finset.card_filter]
  simp_rw [e1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 (labelN_subset_root ht (Finset.mem_filter.1 ha).1)]
  simp

/-- [s2:lemOVgeneric] (b) "for every vertex `v`, the number of leaves `Leaf` with `|Leaf| ≥ M`
containing `v` is at most `1 + dup_{≥M}(v)`". -/
theorem ov_b (M : ℝ) (t : STree V) (H : FGraph V) (v : V) :
    (t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ) ∧
        v ∈ (t.graphAtD H L).verts)).card ≤ 1 + t.dupGe H M v := by
  refine le_trans (ov_leaves_le M t H v) ?_
  split_ifs <;> omega

/-- [s2:lemOVgeneric] (b), consequence:
`Σ_{Leaf:|Leaf|≥M} |Leaf| ≤ |⋃_{Leaf:|Leaf|≥M} V(Leaf)| + Δ_{≥M}`. -/
theorem ov_b_sum (M : ℝ) (t : STree V) {H : FGraph V} (ht : t.WF H) :
    ∑ L ∈ t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ)),
        (t.graphAtD H L).card ≤
      ((t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ))).biUnion
          (fun L => (t.graphAtD H L).verts)).card + t.DeltaGe H M := by
  set LM := t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ))
  set B := LM.biUnion (fun L => (t.graphAtD H L).verts)
  have h1 : ∀ L ∈ LM, (t.graphAtD H L).card = ∑ v ∈ B, if v ∈ (t.graphAtD H L).verts then 1 else 0 := by
    intro L hL
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem _ hL)]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ v ∈ B, (∑ L ∈ LM, if v ∈ (t.graphAtD H L).verts then 1 else 0) ≤
      1 + t.dupGe H M v := by
    intro v _
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    rw [Finset.filter_filter]
    exact ov_b M t H v
  calc ∑ v ∈ B, ∑ L ∈ LM, (if v ∈ (t.graphAtD H L).verts then 1 else 0)
      ≤ ∑ v ∈ B, (1 + t.dupGe H M v) := Finset.sum_le_sum h2
    _ = B.card + ∑ v ∈ B, t.dupGe H M v := by rw [Finset.sum_add_distrib]; simp
    _ ≤ B.card + ∑ v ∈ H.verts, t.dupGe H M v := by
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum_of_subset
        intro v hv
        obtain ⟨L, -, hvL⟩ := Finset.mem_biUnion.1 hv
        exact graphAtD_verts_subset t H L hvL
    _ = B.card + t.DeltaGe H M := by rw [sum_dupGe M t ht]

/-- At `M = 2`, `Δ_{≥2}` is the sum over all non-leaf nodes (they have size `≥ 2`). -/
theorem deltaGe_two {ε c : ℝ} {t : STree V} {H : FGraph V} (ht : t.OVHyp ε c H) :
    t.DeltaGe H 2 = ∑ a ∈ t.internalAddrs, (t.labelN a).card := by
  unfold DeltaGe
  rw [Finset.filter_true_of_mem]
  intro a ha
  exact_mod_cast (ht.2 a ha).1

/-- [s2:lemOVgeneric] (c) "`S ≤ n_0/(1 - 3.42 c ε)`" (no hypothesis `n_0 ≥ 1` needed). -/
theorem ov_c {ε c : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (h342 : 3.42 * c * ε < 1) {t : STree V}
    {H : FGraph V} (ht : t.OVHyp ε c H) :
    (t.leafMass H : ℝ) ≤ H.card / (1 - 3.42 * c * ε) := by
  have hS := leafMass_eq t ht.1
  rw [← deltaGe_two ht] at hS
  have ha := ov_a hc hε (le_refl 2) t ht
  have hC := ovC_le (le_refl (2 : ℝ))
  rw [show Real.logb 2 2 = 1 from Real.logb_self_eq_one (by norm_num), div_one] at hC
  have hS' : (t.leafMass H : ℝ) = H.card + t.DeltaGe H 2 := by exact_mod_cast hS
  have hSnn : (0 : ℝ) ≤ t.leafMass H := Nat.cast_nonneg _
  have hce : 0 ≤ c * ε := mul_nonneg hc hε
  have h1 : c * ε * ovC 2 * t.leafMass H ≤ c * ε * 3.42 * t.leafMass H := by
    have := mul_le_mul_of_nonneg_left hC hce
    exact mul_le_mul_of_nonneg_right this hSnn
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end STree

end EG.HB
