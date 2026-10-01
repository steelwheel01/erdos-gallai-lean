module

public import EG.Spec.Num.StarInputs
public import EG.Lib.Link.Star

/-!
# (S2) numeric part and (S3) (manuscript s3:eqStar), proved

Proofs of the statements of `EG/Spec/Num/StarInputs.lean`. Stage 1 declared `starS2Num` and
`starS3` as inputs (`sorry` stubs); fix round 1 (review I-1, `formal/work/p2b/NUM.md`) proves them
from the definitions (`EG/Defs/Link/Star.lean`) and the Lib API (`EG/Lib/Link/Star.lean`):

* `numStarS3Margin`: the real-arithmetic margins of (S3);
* `starS2Num`: `p_* ≥ 0.1ρ/ℓ_*` by Bernoulli's inequality applied to the defining equation
  `(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)` (`EG.Star.one_sub_p_pow`), and `p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`
  from it (the manuscript's "so");
* `starS3`: `Δ_* ≤ 2p^{-2}+8.34p^{-1}+2.34` from `d_* < 1/p+1`, `λ_* < 6/p+1` and
  `⌈x⌉ < x+1` (the exact bound is `2p^{-2}+(25/3)p^{-1}+7/3`), then the margins.

Recorded slacks: `8.34p+2.34p^2 ≤ 1` at `p = 0.11` is `0.9457` (5.4%); at `p = 1`, `12.68 ≤ 13`
(2.5%); `25/3 = 8.333… ≤ 8.34`, `7/3 = 2.333… ≤ 2.34`.
-/

public section


namespace EG

open Real

/-- [s3:eqS3] The margins: `2p^{-2}+8.34p^{-1}+2.34 ≤ 3p^{-2}` for `0 < p ≤ 0.11` and
`≤ 13p^{-2}` for `0 < p ≤ 1`. -/
theorem numStarS3Margin : EG.Spec.NumStarS3MarginStatement := by
  intro p hp
  have hq : 0 < p⁻¹ := inv_pos.mpr hp
  have hpq : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  constructor
  · intro h
    -- `p⁻¹ ≥ 100/11`, so `8.34 p⁻¹ + 2.34 ≤ p⁻¹^2`.
    have h1 : (100 / 11 : ℝ) ≤ p⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hp]; linarith
    nlinarith
  · intro h
    have h1 : (1 : ℝ) ≤ p⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hp]; linarith
    nlinarith

/-- [s3:eqS2] (numeric part) "`p_* ≥ 0.1ρ/ℓ_*`, so `p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`" (Bernoulli's
inequality on the defining equation of `p_*`). -/
theorem starS2Num : EG.Spec.StarS2NumStatement := by
  intro n ρ hn h0 h1
  have hp0 := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := n) h1
  have hl : (2 : ℝ) ≤ Star.ell n := by exact_mod_cast Star.two_le_ell hn
  have hk : ((Star.ell n - 1 : ℕ) : ℝ) = (Star.ell n : ℝ) - 1 := Star.cast_ell_sub_one hn
  -- Bernoulli: `1 - (ℓ-1)p ≤ (1-p)^{ℓ-1} = (1-ρ)/(1-0.9ρ)`.
  have hB : 1 + ((Star.ell n - 1 : ℕ) : ℝ) * (-Star.p n ρ) ≤
      (1 + -Star.p n ρ) ^ (Star.ell n - 1) :=
    one_add_mul_le_pow (by linarith) _
  rw [← sub_eq_add_neg, Star.one_sub_p_pow hn h1, hk] at hB
  have hden : 0 < 1 - 9 / 10 * ρ := by linarith
  -- `1 - (1-ρ)/(1-0.9ρ) = 0.1ρ/(1-0.9ρ) ≥ 0.1ρ`.
  have hbase : (1 - ρ) / (1 - 9 / 10 * ρ) ≤ 1 - 0.1 * ρ := by
    rw [div_le_iff₀ hden]; nlinarith
  have hmain : 0.1 * ρ ≤ ((Star.ell n : ℝ) - 1) * Star.p n ρ := by nlinarith
  have hS2 : 0.1 * ρ / (Star.ell n : ℝ) ≤ Star.p n ρ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  refine ⟨hS2, ?_⟩
  -- `p⁻¹ ≤ 10ℓ/ρ`, square it.
  have hinv : (Star.p n ρ)⁻¹ ≤ 10 * (Star.ell n : ℝ) * ρ⁻¹ := by
    rw [inv_le_comm₀ hp0 (by positivity)]
    calc (10 * (Star.ell n : ℝ) * ρ⁻¹)⁻¹ = 0.1 * ρ / (Star.ell n : ℝ) := by
          field_simp; norm_num
      _ ≤ Star.p n ρ := hS2
  have hi0 : 0 ≤ (Star.p n ρ)⁻¹ := (inv_pos.mpr hp0).le
  calc (Star.p n ρ)⁻¹ ^ 2 ≤ (10 * (Star.ell n : ℝ) * ρ⁻¹) ^ 2 := by gcongr
    _ = 100 * (Star.ell n : ℝ) ^ 2 * ρ⁻¹ ^ 2 := by ring

/-- [s3:eqS3] "`Δ_* ≤ 2p^{-2}+8.34p^{-1}+2.34`. Hence `Δ_* ≤ 3p^{-2}` if `p ≤ 0.11`, and
`Δ_* ≤ 13p^{-2}` for every `p ∈ (0,1]`." -/
theorem starS3 : EG.Spec.StarS3Statement := by
  intro n ρ hn h0 h1
  have hp0 := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := n) h1
  set p := Star.p n ρ with hpdef
  have hd := Star.d_lt hn h0 h1
  have hlam := Star.lam_lt hn h0 h1
  have hd0 : (0 : ℝ) ≤ Star.d n ρ := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ Star.lam n ρ := Nat.cast_nonneg _
  have hceil : (⌈((Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ)) / 3⌉₊ : ℝ) <
      ((Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ)) / 3 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hD : (Star.Delta n ρ : ℝ) =
      Star.lam n ρ + (⌈((Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ)) / 3⌉₊ : ℝ) := by
    rw [Star.Delta_eq]; push_cast; ring
  have hq : 0 < p⁻¹ := inv_pos.mpr hp0
  have h1p : 1 / p = p⁻¹ := one_div p
  rw [h1p] at hd
  have h6p : 6 / p = 6 * p⁻¹ := by rw [div_eq_mul_inv]
  rw [h6p] at hlam
  -- `d λ < (p⁻¹+1)(6p⁻¹+1)`.
  have hdl : (Star.d n ρ : ℝ) * Star.lam n ρ ≤ (p⁻¹ + 1) * (6 * p⁻¹ + 1) :=
    mul_le_mul hd.le hlam.le hl0 (by positivity)
  have hS3 : (Star.Delta n ρ : ℝ) ≤ 2 * p⁻¹ ^ 2 + 8.34 * p⁻¹ + 2.34 := by
    rw [hD]; nlinarith
  have hm := numStarS3Margin p hp0
  exact ⟨hS3, fun h => le_trans hS3 (hm.1 h), le_trans hS3 (hm.2 hp1)⟩

end EG
