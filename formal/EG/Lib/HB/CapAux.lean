module

public import EG.Lib.HB.Params
public import EG.Lib.HB.Run

/-!
# Helpers for Lemma s2:lemCap (ii) (manuscript s2:lemCap)

Helper lemmas for `EG.Todo.CapRound` (unit P3-s2); only `D_* ≥ 2^{117}` (Γ2(a)) is used.
* `degE_le_card_sub_one'`: a vertex meets at most `|Z| - 1` edges of a loopless edge set inside
  `Z` ("every vertex meets at most `|Z^0| - 1 ≤ M_l - 1` of them");
* `T_ge_of_d_ge`: `T_l = d_l log² d_l ≥ 2^{117}` for `d_l ≥ 2^{117}`;
* `forty_le_LamOf`: `Λ_l ≥ 40` (as `M_l ≥ 2^{40}`), for every real `d`;
* `one_le_sOf`: `s_l ≥ 1`;
* `tau_ge_of_card_le`: `τ_l ≥ 128 s_l log² m` for `m ≤ M_l`.
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

theorem degE_le_card_sub_one' {Z : Finset V} {H : Finset (Sym2 V)} (hD : ∀ e ∈ H, ¬ e.IsDiag)
    (hZ : ∀ e ∈ H, ∀ v ∈ e, v ∈ Z) (x : V) : degE H x ≤ Z.card - 1 := by
  by_cases hx : x ∈ Z
  · have hsub : edgesAt H x ⊆ (Z.erase x).image (fun y => s(x, y)) := by
      intro e he
      simp only [edgesAt, Finset.mem_filter] at he
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 he.2
      rw [Finset.mem_image]
      refine ⟨y, Finset.mem_erase.2 ⟨?_, hZ _ he.1 y (Sym2.mem_mk_right _ _)⟩, rfl⟩
      rintro rfl
      exact hD _ he.1 (Sym2.mk_isDiag_iff.2 rfl)
    calc degE H x = (edgesAt H x).card := rfl
      _ ≤ ((Z.erase x).image (fun y => s(x, y))).card := Finset.card_le_card hsub
      _ ≤ (Z.erase x).card := Finset.card_image_le
      _ = Z.card - 1 := Finset.card_erase_of_mem hx
  · have : edgesAt H x = ∅ := by
      ext e
      simp only [edgesAt, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro he hxe
      exact hx (hZ e he x hxe)
    simp [degE, this]

theorem T_ge_of_d_ge {d : ℝ} (hd : (2 : ℝ) ^ 117 ≤ d) : (2 : ℝ) ^ 117 ≤ TOf d := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hl : 1 ≤ logb 2 d := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hd0]
    have : (2 : ℝ) ^ (1 : ℝ) ≤ 2 ^ 117 := by norm_num
    linarith
  have : 1 ≤ logb 2 d ^ 2 := one_le_pow₀ hl
  change (2 : ℝ) ^ 117 ≤ logb 2 d ^ 2 * d
  nlinarith

theorem forty_le_LamOf (d : ℝ) : 40 ≤ LamOf d := by
  have h := ParamHyp.two40_le_M (d := d)
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
  change 40 ≤ logb 2 (MOf d : ℝ); push_cast at this; linarith

theorem one_le_sOf (d : ℝ) : 1 ≤ sOf d := by
  have h1 : (1 : ℝ) ≤ LamOf d ^ sigmaC := one_le_pow₀ (by linarith [forty_le_LamOf d])
  have h2 : LamOf d ^ sigmaC ≤ (sOf d : ℝ) := Nat.le_ceil _
  exact_mod_cast h1.trans h2

theorem tau_ge_of_card_le (d : ℝ) {m : ℕ} (hm : m ≤ MOf d) :
    128 * (sOf d : ℝ) * logb 2 (m : ℝ) ^ 2 ≤ (tauOf d : ℝ) := by
  refine le_trans ?_ (Nat.le_ceil _)
  have hL : 0 ≤ logb 2 (m : ℝ) ∧ logb 2 (m : ℝ) ≤ logb 2 (MOf d : ℝ) := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp only [Nat.cast_zero, Real.logb_zero, le_refl, true_and]
      have := forty_le_LamOf d; change 40 ≤ logb 2 (MOf d : ℝ) at this; linarith
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h0
      exact ⟨Real.logb_nonneg (by norm_num) hm1,
        Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast hm)⟩
  have hs : (0 : ℝ) ≤ sOf d := Nat.cast_nonneg _
  have : logb 2 (m : ℝ) ^ 2 ≤ logb 2 (MOf d : ℝ) ^ 2 := pow_le_pow_left₀ hL.1 hL.2 2
  nlinarith

/-! ### Parameters under `d ≥ 2^{117}` only (Γ2(a)) -/

section G2

variable {d : ℝ}

theorem lam_ge_117 (hd : (2 : ℝ) ^ 117 ≤ d) : 117 ≤ logb 2 d := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  rw [Real.le_logb_iff_rpow_le (by norm_num) hd0]
  calc (2 : ℝ) ^ (117 : ℝ) = (2 : ℝ) ^ (117 : ℕ) := by norm_num
    _ ≤ d := hd

theorem d_le_M_of_ge (hd : (2 : ℝ) ^ 117 ≤ d) : d ≤ (MOf d : ℝ) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hl := lam_ge_117 hd
  have hT := T_ge_of_d_ge hd
  have hdT : d ≤ TOf d := by
    have : 1 ≤ logb 2 d ^ 2 := one_le_pow₀ (by linarith)
    change d ≤ logb 2 d ^ 2 * d; nlinarith
  have hlT : 1 ≤ logb 2 (TOf d) := by
    have := lam_ge_117 hT; linarith
  have h4 : 1 ≤ logb 2 (TOf d) ^ 4 := one_le_pow₀ hlT
  have hT0 : 0 ≤ TOf d := by linarith
  have : d ≤ 2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4 := by nlinarith
  exact this.trans ((le_max_right _ _).trans (Nat.le_ceil _))

theorem lam_le_LamOf (hd : (2 : ℝ) ^ 117 ≤ d) : logb 2 d ≤ LamOf d :=
  Real.logb_le_logb_of_le (by norm_num) (lt_of_lt_of_le (by positivity) hd) (d_le_M_of_ge hd)

theorem lam100_le_sOf (hd : (2 : ℝ) ^ 117 ≤ d) : logb 2 d ^ 100 ≤ (sOf d : ℝ) := by
  have hl := lam_ge_117 hd
  have h1 : logb 2 d ^ 100 ≤ LamOf d ^ 100 :=
    pow_le_pow_left₀ (by linarith) (lam_le_LamOf hd) 100
  have h2 : LamOf d ^ sigmaC ≤ (sOf d : ℝ) := Nat.le_ceil _
  rw [sigmaC_eq] at h2
  linarith

theorem eleven_le_POf (hd : (2 : ℝ) ^ 117 ≤ d) : 11 ≤ POf d := by
  have hl := lam_ge_117 hd
  have h1 : logb 2 d ^ Cp ≤ (POf d : ℝ) := Nat.le_ceil _
  rw [Cp_eq] at h1
  have h2 : logb 2 d ≤ logb 2 d ^ 103 := le_self_pow₀ (by linarith) (by norm_num)
  have : (11 : ℝ) ≤ POf d := by linarith
  exact_mod_cast this

end G2

end EG.HB
