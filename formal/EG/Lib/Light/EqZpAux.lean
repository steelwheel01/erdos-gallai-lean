module

public import EG.Lib.HB.TowerRun
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tower facts for the sum (s5:eqZp)

Library of the P3-s5 unit (`formal/work/p3/s5.md`). Manuscript v6.1, `s5.tex`, setting paragraph,
proof of (s5:eqZp): "For `r < R`, Lemma s2:lemTower(a) gives `λ_r ≥ d_{r+1}^{1/A} = 2^{λ_{r+1}/A}`,
hence `log₂λ_r ≥ λ_{r+1}/A = 2^{log₂λ_{r+1}}/A ≥ 2 log₂λ_{r+1}`, because
`x := log₂λ_{r+1} ≥ log₂log₂D_*`, so that Γ1(a),(b) at `x` give `x ≥ 2^8` and
`2^x ≥ 2^{14} A x^3 ≥ 2 A x`. Hence `log₂λ_r ≥ 2^{R−r} log₂λ_R ≥ 2^{R−r}·2^8`, by Γ1(a) at
`log₂λ_R`, and `Σ_{r≤R} (102 log₂λ_r)^{-2} ≤ (102·2^8)^{-2} Σ_{k≥0} 4^{-k} … < 1/2`."

* `sum_Icc_half_pow_le`: `Σ_{r=1}^{R} (1/2)^{R−r} ≤ 2`;
* `logb_lam_step`: one step `2 log₂λ_{r+1} ≤ log₂λ_r` from `d_{r+1}^{1/A} ≤ λ_r`;
* `logb_lam_ge`: `2^8 · 2^{R−r} ≤ log₂λ_r` for `1 ≤ r ≤ R`, from the first clause of
  s2:lemTower (a) (passed as a hypothesis).
-/

public section

namespace EG.Light

open EG.HB Real

/-- `Σ_{r=1}^{R} (1/2)^{R−r} ≤ 2`. -/
theorem sum_Icc_half_pow_le (R : ℕ) :
    ∑ r ∈ Finset.Icc 1 R, (1 / (2 : ℝ)) ^ (R - r) ≤ 2 := by
  have hinj : Set.InjOn (fun r => R - r) (Finset.Icc 1 R : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    simp only at hab
    omega
  rw [← Finset.sum_image (f := fun k => (1 / (2 : ℝ)) ^ k) hinj]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity)
    (sum_geometric_two_le R)
  intro k hk
  simp only [Finset.mem_image, Finset.mem_Icc] at hk
  obtain ⟨r, ⟨h1, h2⟩, rfl⟩ := hk
  simp only [Finset.mem_range]
  omega

/-- One tower step: if `D_* ≤ d` (so `ParamHyp d`) and `d^{1/A} ≤ λ` then
`2 log₂(log₂ d) ≤ log₂ λ`. -/
theorem logb_lam_step {d lam : ℝ} (hp : ParamHyp d) (h : d ^ ((1 : ℝ) / (Aexp : ℝ)) ≤ lam) :
    2 * logb 2 (logb 2 d) ≤ logb 2 lam := by
  have hd := hp.d_pos
  have hpos : 0 < d ^ ((1 : ℝ) / (Aexp : ℝ)) := Real.rpow_pos_of_pos hd _
  have h1 : logb 2 (d ^ ((1 : ℝ) / (Aexp : ℝ))) ≤ logb 2 lam :=
    Real.logb_le_logb_of_le (by norm_num) hpos h
  rw [Real.logb_rpow_eq_mul_logb_of_pos hd] at h1
  have hA : (Aexp : ℝ) = 105 := by norm_num [Aexp]
  rw [hA] at h1
  have hx := hp.mu_ge
  have hc := hp.mu_cube_le
  set x := logb 2 (logb 2 d)
  have hx3 : x ≤ x ^ 3 := by
    have e : x ^ 3 = x * (x * x) := by ring
    rw [e]; nlinarith
  nlinarith

/-- `2^8 · 2^{R−r} ≤ log₂λ_r` for every round `1 ≤ r ≤ R` of a valid run with `D_*` satisfying
Γ1 (a)–(e), given the first clause of s2:lemTower (a) (`d_{r+1}^{1/A} ≤ λ_r`). -/
theorem logb_lam_ge {V : Type*} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}
    (hD : Gamma1core Dstar) (hv : run.Valid G Dstar)
    (hTA : ∀ r ∈ Finset.Icc 1 run.R, run.d G (r + 1) ^ ((1 : ℝ) / (Aexp : ℝ)) ≤ run.lam G r) :
    ∀ r ∈ Finset.Icc 1 run.R, (2 : ℝ) ^ 8 * 2 ^ (run.R - r) ≤ logb 2 (run.lam G r) := by
  have key : ∀ k : ℕ, k + 1 ≤ run.R →
      (2 : ℝ) ^ 8 * 2 ^ k ≤ logb 2 (run.lam G (run.R - k)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hp := Run.paramHyp hD hv (r := run.R) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
      have := hp.mu_ge
      simp only [pow_zero, mul_one, Nat.sub_zero]
      rw [Run.lam, lamOf]
      norm_num at this ⊢
      linarith
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hp := Run.paramHyp hD hv (r := run.R - k) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      have hstep := hTA (run.R - (k + 1)) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      have he : run.R - (k + 1) + 1 = run.R - k := by omega
      rw [he] at hstep
      have h2 := logb_lam_step hp hstep
      have hlam : run.lam G (run.R - k) = logb 2 (run.d G (run.R - k)) := rfl
      rw [hlam] at ih'
      have hs : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ _ _
      rw [hs]
      linarith
  intro r hr
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hr
  have := key (run.R - r) (by omega)
  rwa [show run.R - (run.R - r) = r by omega] at this

end EG.Light
