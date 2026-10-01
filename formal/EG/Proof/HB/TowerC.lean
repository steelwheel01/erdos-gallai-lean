module

public import EG.Spec.HB.TowerC
public import EG.Lib.HB.TowerRun

/-!
# Declared-input stub of unit P3A: Lemma "tower facts" (c) (manuscript s2:lemTower (c))

This is the only `sorry` of unit P3A (the former second stub, `EG.edgeLaminarity` in
`EG/Proof/HB/EL.lean`, is proved since fix round 1 of the proof stage). [s2:lemGC] (iv) is
[s2:lemTower] (c); its proof (s2.tex, proof of lemTower (c)) needs [s2:lemTower] (b)
(`Λ_r ≤ 2λ_r` from [s2:propDegRec], `s_r ≤ 2Λ_r^σ`), the definitions of the round parameters
(`P_r ≥ λ_r^{σ+3}`) and Γ1(a); these are not nodes of probe P-3. Owner: the s2 tower unit; the
full Tower Spec must import `EG/Spec/HB/TowerC.lean` and must not restate (c). Justification:
design note `formal/work/p2b/P3A.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:lemTower] (c) "For `r ≤ R`: `τ_r ≤ 257 Λ_r^{σ+2} ≤ 2^{σ+11} λ_r^{σ+2}`
and `τ_r/P_r ≤ 2^{σ+11}/λ_r`; and `θ^GC_r(Z^0) ≥ P_r λ_r^{-1/2} > τ_r` for every round-`r`
pre-part `Z`." Owner: s2 tower unit (blueprint s2b, `TowerCStatement`). -/
theorem towerC : EG.Spec.TowerCStatement := by
  intro V _ G Dstar run hD hv _ r hr
  have h := EG.HB.Run.paramHyp hD hv hr
  have hlam : run.lam G r = Real.logb 2 (run.d G r) := rfl
  have hL : run.Lam G r = EG.HB.LamOf (run.d G r) := rfl
  have htau : run.tau G r = EG.HB.tauOf (run.d G r) := rfl
  have hPd : run.P G r = EG.HB.POf (run.d G r) := rfl
  rw [hlam, hL, htau, hPd]
  set l := Real.logb 2 (run.d G r) with hl
  have hl0 : 0 < l := h.lam_pos
  have hlg : (2 : ℝ) ^ 256 ≤ l := h.lam_ge
  have h1 := h.tau_le
  rw [EG.sigmaC_eq] at h1 ⊢
  have h2 : 257 * EG.HB.LamOf (run.d G r) ^ (100 + 2) ≤ 2 ^ (100 + 11) * l ^ (100 + 2) := by
    have := pow_le_pow_left₀ h.Lam_pos.le h.Lam_le_two_lam 102
    have e : (2 * l) ^ 102 = 2 ^ 102 * l ^ 102 := by ring
    rw [e] at this
    have hp : 0 ≤ l ^ 102 := by positivity
    norm_num
    nlinarith
  have hP := EG.HB.ParamHyp.P_ge (d := run.d G r)
  rw [EG.Cp_eq] at hP
  have hl103 : 0 < l ^ 103 := by positivity
  have hPpos : (0 : ℝ) < EG.HB.POf (run.d G r) := lt_of_lt_of_le hl103 hP
  have htl : (EG.HB.tauOf (run.d G r) : ℝ) ≤ 2 ^ 111 * l ^ 102 := by
    have := h1.trans h2; norm_num at this ⊢; exact this
  -- `λ^{1/2} > 2^{111}`
  have hsqrt : (2 : ℝ) ^ 111 < l ^ (1 / 2 : ℝ) := by
    have e : (2 : ℝ) ^ (256 : ℕ) = ((2 : ℝ) ^ (128 : ℕ)) ^ (2 : ℝ) := by
      rw [Real.rpow_two, ← pow_mul]
    have h3 : ((2 : ℝ) ^ (128 : ℕ)) ≤ l ^ (1 / 2 : ℝ) := by
      rw [e] at hlg
      calc (2 : ℝ) ^ (128 : ℕ) = (((2 : ℝ) ^ (128 : ℕ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ l ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hlg (by norm_num)
    have : (2 : ℝ) ^ 111 < 2 ^ 128 := by norm_num
    linarith
  have hsplit : l ^ (103 : ℕ) * l ^ (-(1 / 2 : ℝ)) = l ^ (102 : ℕ) * l ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hl0, ← Real.rpow_add hl0]
    norm_num
  have hneg : 0 < l ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hl0 _
  refine ⟨h1, h2, ?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [div_le_div_iff₀ hPpos hl0]
    rw [show (100 + 11 : ℕ) = 111 from rfl]
    calc (EG.HB.tauOf (run.d G r) : ℝ) * l ≤ 2 ^ 111 * l ^ 102 * l :=
          mul_le_mul_of_nonneg_right htl hl0.le
      _ = 2 ^ 111 * l ^ 103 := by ring
      _ ≤ 2 ^ 111 * (EG.HB.POf (run.d G r) : ℝ) := by nlinarith
  · rw [EG.HB.Run.thetaGC_eq]
    refine le_trans ?_ (Nat.le_ceil _)
    have hZ : (EG.HB.POf (run.d G r) : ℝ) ≤ (run.Z0 G r a).card := by
      exact_mod_cast EG.HB.Run.P_le_card_Z0 ha
    exact mul_le_mul_of_nonneg_right hZ hneg.le
  · calc (EG.HB.tauOf (run.d G r) : ℝ) ≤ 2 ^ 111 * l ^ 102 := htl
      _ < l ^ (102 : ℕ) * l ^ (1 / 2 : ℝ) := by
          have : 0 < l ^ 102 := by positivity
          nlinarith
      _ = l ^ (103 : ℕ) * l ^ (-(1 / 2 : ℝ)) := hsplit.symm
      _ ≤ (EG.HB.POf (run.d G r) : ℝ) * l ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hP hneg.le

end EG
