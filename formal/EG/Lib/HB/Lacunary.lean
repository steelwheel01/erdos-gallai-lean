module

public import EG.Spec.HB.LacunaryGeom
public import EG.Defs.HB.Run
public import EG.Lib.Found.Gamma

/-!
# Tower-lacunary sums: arithmetic core (manuscript s2:lemLacunary (i)–(iii))

Helper lemmas for the P3 stubs of s2:lemLacunary (unit P3-s2):
* `EG.HB.lacGeom`: part (i) (induction on `R`: `S_{R+1} = S_R + X_{R+1}` and
  `W_{R+1} = W_R + S_{R+1}` for the plain sum `S` and the weighted sum `W`);
* `EG.HB.lacSeq`: part (iii), sequence form ("By (H) with `x = λ_{r+1}` and `y = λ_r`,
  `F(λ_r) ≤ F(λ_{r+1})/2`, and (i) applies to `X_r := F(λ_r)`");
* `EG.HB.lacShift_sum`, `EG.HB.lacShift_wsum`: "For sums of `F(λ_{l-2})` over `3 ≤ l ≤ R` apply
  the same to `r = l - 2 ≤ R - 2`" (reindexing);
* `EG.HB.le_two_rpow_div_A`: proof of (ii), "`2^{x/A} ≥ x`" for `x ≥ log D_*` under Γ1 (a), (b);
* `EG.HB.hypH_of_antitone`: proof of (ii), "monotone and halving ⇒ (H)";
* `EG.HB.lam_step_of_d_le`: proof of (iii), "`d_{r+1} ≤ λ_r^A`, i.e. `λ_r ≥ 2^{λ_{r+1}/A}`".
-/

public section

namespace EG.HB

open Real

/-- [s2:lemLacunary] (i), both sums at once, by induction on `R`. -/
theorem lacGeom_aux (X : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) (h0 : ∀ r ∈ Finset.Icc 1 R, 0 ≤ X r)
    (hh : ∀ r ∈ Finset.Ico 1 R, X r ≤ X (r + 1) / 2) :
    ∑ r ∈ Finset.Icc 1 R, X r ≤ 2 * X R ∧
      ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * X r ≤ 4 * X R := by
  induction R, hR using Nat.le_induction with
  | base =>
    have h1 : 0 ≤ X 1 := h0 1 (by simp)
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, zero_add, Nat.cast_one,
      one_mul]
    constructor <;> linarith
  | succ R hR ih =>
    have h0' : ∀ r ∈ Finset.Icc 1 R, 0 ≤ X r := fun r hr =>
      h0 r (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hr).1, by linarith [(Finset.mem_Icc.1 hr).2]⟩)
    have hh' : ∀ r ∈ Finset.Ico 1 R, X r ≤ X (r + 1) / 2 := fun r hr =>
      hh r (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hr).1, by linarith [(Finset.mem_Ico.1 hr).2]⟩)
    obtain ⟨ihS, ihW⟩ := ih h0' hh'
    have hstep : X R ≤ X (R + 1) / 2 := hh R (Finset.mem_Ico.2 ⟨hR, by omega⟩)
    have hS : ∑ r ∈ Finset.Icc 1 (R + 1), X r = ∑ r ∈ Finset.Icc 1 R, X r + X (R + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hW : ∑ r ∈ Finset.Icc 1 (R + 1), ((R + 1 - r + 1 : ℕ) : ℝ) * X r =
        ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * X r + ∑ r ∈ Finset.Icc 1 (R + 1), X r := by
      rw [Finset.sum_Icc_succ_top (by omega), hS, Finset.sum_congr rfl
        (g := fun r => ((R - r + 1 : ℕ) : ℝ) * X r + X r)]
      · rw [Finset.sum_add_distrib]; simp; ring
      · intro r hr
        have := (Finset.mem_Icc.1 hr).2
        have e : R + 1 - r + 1 = (R - r + 1) + 1 := by omega
        rw [e]; push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [hS]; linarith
    · rw [hW, hS]; linarith

/-- [s2:lemLacunary] (i). -/
theorem lacGeom : EG.Spec.LacunaryGeomStatement := fun X R hR h0 hh => lacGeom_aux X R hR h0 hh

/-- [s2:lemLacunary] (iii), sequence form. -/
theorem lacSeq (x0 : ℝ) (F : ℝ → ℝ) (lam : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R)
    (hF0 : ∀ x : ℝ, x0 ≤ x → 0 ≤ F x) (hH : HypH x0 F)
    (hx0 : ∀ r ∈ Finset.Icc 1 R, x0 ≤ lam r)
    (hstep : ∀ r ∈ Finset.Ico 1 R, (2 : ℝ) ^ (lam (r + 1) / (Aexp : ℝ)) ≤ lam r) :
    ∑ r ∈ Finset.Icc 1 R, F (lam r) ≤ 2 * F (lam R) ∧
      ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * F (lam r) ≤ 4 * F (lam R) := by
  apply lacGeom_aux (fun r => F (lam r)) R hR
  · intro r hr; exact hF0 _ (hx0 r hr)
  · intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
    exact hH (lam (r + 1)) (lam r) (hx0 (r + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
      (hx0 r (Finset.mem_Icc.2 ⟨h1, h2.le⟩)) (hstep r hr)

/-- Reindexing `l = r + 2` of the shifted sums (plain). -/
theorem lacShift_sum (g : ℕ → ℝ) (R : ℕ) :
    ∑ l ∈ Finset.Icc 3 R, g (l - 2) = ∑ r ∈ Finset.Icc 1 (R - 2), g r := by
  refine Finset.sum_nbij' (fun l => l - 2) (fun r => r + 2) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [Finset.mem_Icc] at hl ⊢; omega
  · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
  · intro l hl; simp only [Finset.mem_Icc] at hl; omega
  · intro r _; simp
  · intro l _; rfl

/-- Reindexing `l = r + 2` of the shifted sums (weighted). -/
theorem lacShift_wsum (g : ℕ → ℝ) (R : ℕ) :
    ∑ l ∈ Finset.Icc 3 R, ((R - l + 1 : ℕ) : ℝ) * g (l - 2) =
      ∑ r ∈ Finset.Icc 1 (R - 2), ((R - 2 - r + 1 : ℕ) : ℝ) * g r := by
  refine Finset.sum_nbij' (fun l => l - 2) (fun r => r + 2) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [Finset.mem_Icc] at hl ⊢; omega
  · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
  · intro l hl; simp only [Finset.mem_Icc] at hl; omega
  · intro r _; simp
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    have e : R - l + 1 = R - 2 - (l - 2) + 1 := by omega
    rw [e]

/-- [s2:lemLacunary] (iii), shifted sums, sequence form: with `R ≥ 3` and the hypotheses of
`lacSeq`, the sums of `F(λ_{l-2})` over `3 ≤ l ≤ R`. -/
theorem lacSeq_shift (x0 : ℝ) (F : ℝ → ℝ) (lam : ℕ → ℝ) (R : ℕ) (hR : 3 ≤ R)
    (hF0 : ∀ x : ℝ, x0 ≤ x → 0 ≤ F x) (hH : HypH x0 F)
    (hx0 : ∀ r ∈ Finset.Icc 1 R, x0 ≤ lam r)
    (hstep : ∀ r ∈ Finset.Ico 1 R, (2 : ℝ) ^ (lam (r + 1) / (Aexp : ℝ)) ≤ lam r) :
    ∑ l ∈ Finset.Icc 3 R, F (lam (l - 2)) ≤ 2 * F (lam (R - 2)) ∧
      ∑ l ∈ Finset.Icc 3 R, ((R - l + 1 : ℕ) : ℝ) * F (lam (l - 2)) ≤ 4 * F (lam (R - 2)) := by
  rw [lacShift_sum (fun r => F (lam r)), lacShift_wsum (fun r => F (lam r))]
  apply lacSeq x0 F lam (R - 2) (by omega) hF0 hH
  · intro r hr; simp only [Finset.mem_Icc] at hr; exact hx0 r (Finset.mem_Icc.2 ⟨hr.1, by omega⟩)
  · intro r hr; simp only [Finset.mem_Ico] at hr; exact hstep r (Finset.mem_Ico.2 ⟨hr.1, by omega⟩)

/-- Proof of [s2:lemLacunary] (ii): "Let `x ≥ x_0`. Then `μ := log x ≥ log log D_*`, so Γ1 (a), (b)
at `μ` give `μ ≥ 2^8` and `x = 2^μ ≥ 2^{14} A μ^3 ≥ A μ = A log x`, that is, `2^{x/A} ≥ x`." -/
theorem le_two_rpow_div_A {Dstar x : ℝ} (hD : Gamma1core Dstar) (hx : logb 2 Dstar ≤ x) :
    x ≤ (2 : ℝ) ^ (x / (Aexp : ℝ)) := by
  have hI := hD.items_logb_of_le hx
  have hxpos : 0 < x := lt_of_lt_of_le (zero_lt_one.trans hD.one_lt_logb) hx
  set μ := logb 2 x with hμ
  have ha : (2 : ℝ) ^ 8 ≤ μ := hI.a
  have hb : (2 : ℝ) ^ 14 * (Aexp : ℝ) * μ ^ 3 ≤ (2 : ℝ) ^ μ := hI.b
  have hxμ : (2 : ℝ) ^ μ = x := Real.rpow_logb (by norm_num) (by norm_num) hxpos
  have hA : (0 : ℝ) < Aexp := by norm_num [Aexp]
  have hμ1 : 1 ≤ μ := le_trans (by norm_num) ha
  have hμ2 : 1 ≤ μ * μ := by nlinarith
  have hμ3 : μ ≤ μ ^ 3 := by
    have e : μ ^ 3 = μ * (μ * μ) := by ring
    rw [e]; nlinarith
  have hAμ : (Aexp : ℝ) * μ ≤ x := by
    rw [← hxμ]
    have : (Aexp : ℝ) * μ ≤ (2 : ℝ) ^ 14 * (Aexp : ℝ) * μ ^ 3 := by nlinarith
    linarith
  have hle : μ ≤ x / (Aexp : ℝ) := by rw [le_div_iff₀ hA]; linarith
  calc x = (2 : ℝ) ^ μ := hxμ.symm
    _ ≤ (2 : ℝ) ^ (x / (Aexp : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle

/-- Proof of [s2:lemLacunary] (ii): "If `F` is non-increasing and `F(2^{x/A}) ≤ F(x)/2`, then for
`y ≥ 2^{x/A}` we get `F(y) ≤ F(2^{x/A}) ≤ F(x)/2`, which is (H)." -/
theorem hypH_of_antitone {Dstar : ℝ} (hD : Gamma1core Dstar) (F : ℝ → ℝ)
    (hmono : AntitoneOn F (Set.Ici (logb 2 Dstar)))
    (hhalf : ∀ x : ℝ, logb 2 Dstar ≤ x → F ((2 : ℝ) ^ (x / (Aexp : ℝ))) ≤ F x / 2) :
    HypH (logb 2 Dstar) F := by
  intro x y hx hy hxy
  have h1 : logb 2 Dstar ≤ (2 : ℝ) ^ (x / (Aexp : ℝ)) := hx.trans (le_two_rpow_div_A hD hx)
  exact (hmono (Set.mem_Ici.2 h1) (Set.mem_Ici.2 hy) hxy).trans (hhalf x hx)

/-- Proof of [s2:lemLacunary] (iii): "`d_{r+1} ≤ λ_r^A`, i.e. `λ_{r+1} ≤ A log λ_r`, i.e.
`λ_r ≥ 2^{λ_{r+1}/A}`" (for `d_{r+1} > 0` and `λ_r > 0`; `λ = log₂ d`). -/
theorem lam_step_of_d_le {d1 lam0 : ℝ} (hd1 : 0 < d1) (hlam0 : 0 < lam0)
    (h : d1 ≤ lam0 ^ Aexp) : (2 : ℝ) ^ (logb 2 d1 / (Aexp : ℝ)) ≤ lam0 := by
  have hA : (0 : ℝ) < Aexp := by norm_num [Aexp]
  have h1 : logb 2 d1 ≤ (Aexp : ℝ) * logb 2 lam0 := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hd1 h
    rwa [Real.logb_pow] at this
  have h2 : logb 2 d1 / (Aexp : ℝ) ≤ logb 2 lam0 := by rw [div_le_iff₀ hA]; linarith
  calc (2 : ℝ) ^ (logb 2 d1 / (Aexp : ℝ)) ≤ (2 : ℝ) ^ (logb 2 lam0) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    _ = lam0 := Real.rpow_logb (by norm_num) (by norm_num) hlam0

end EG.HB
