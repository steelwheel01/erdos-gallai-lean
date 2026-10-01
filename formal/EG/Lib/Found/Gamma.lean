module

public import EG.Defs.Gamma.Core
public import EG.Lib.Found.Log
public import EG.Lib.Found.Constants

/-!
# API for `Gamma1core` and `Gamma2a` (manuscript s1:condGamma)

* access: `Gamma1core.two_lt`, `Gamma1core.items` (items (a)–(e) on the ray
  `μ ≥ log₂log₂D`), `Gamma1Items.a` … `Gamma1Items.e`;
* upward closure ("Γ1 is upward closed in `D_*`"): `Gamma1core.mono`, `Gamma2a.mono`;
* the values of [s1:condG1] "They also hold at `μ = log₂log₂d` for every `d ≥ D_*`, and at
  `μ = log₂D_*`": `Gamma1core.items_loglog`, `Gamma1core.items_logb`, and the transfer
  `Gamma1core.items_logb_of_le` (`log₂D_* ≤ x → Γ1-items at μ = log₂x`, s2:lemLacunary(iv));
* "(a) at `μ = log₂log₂D_*` already gives …": `Gamma1core.two_pow_eight_le_loglog`,
  `Gamma1core.two_pow_256_le_logb`;
* [s1:condG2] "(a) is immediate from Γ1": `Gamma1core.gamma2a`;
* non-vacuity: `gamma1Items_of_le` (items (a)–(e) for every `μ ≥ 2^{20}`),
  `eventually_gamma1Items`, `gamma1core_two_rpow_two_rpow` (`D = 2^{2^{2^{20}}}`),
  `exists_gamma1core`, `eventually_gamma1core`. These cover items (a)–(e) only; item (f)
  (`Gamma1f`, COL-JV column 3) needs its own non-vacuity check once defined.
-/

public section


namespace EG

open Real

theorem Gamma1Items.a {μ : ℝ} (h : Gamma1Items μ) : Gamma1a μ := h.1
theorem Gamma1Items.b {μ : ℝ} (h : Gamma1Items μ) : Gamma1b μ := h.2.1
theorem Gamma1Items.c {μ : ℝ} (h : Gamma1Items μ) : Gamma1c μ := h.2.2.1
theorem Gamma1Items.d {μ : ℝ} (h : Gamma1Items μ) : Gamma1d μ := h.2.2.2.1
theorem Gamma1Items.e {μ : ℝ} (h : Gamma1Items μ) : Gamma1e μ := h.2.2.2.2

theorem Gamma1core.two_lt {D : ℝ} (h : Gamma1core D) : 2 < D := h.1

theorem Gamma1core.items {D μ : ℝ} (h : Gamma1core D) (hμ : logb 2 (logb 2 D) ≤ μ) :
    Gamma1Items μ := h.2 μ hμ

theorem Gamma1core.one_lt_logb {D : ℝ} (h : Gamma1core D) : 1 < logb 2 D := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith [h.two_lt])]
  norm_num
  exact h.two_lt

/-- `log₂log₂` is monotone above `D > 2`. -/
theorem loglog_mono {D d : ℝ} (hD : 2 < D) (hd : D ≤ d) :
    logb 2 (logb 2 D) ≤ logb 2 (logb 2 d) := by
  have hD0 : 0 < D := by linarith
  have h1 : 0 < logb 2 D := Real.logb_pos (by norm_num) (by linarith)
  exact Real.logb_le_logb_of_le (by norm_num) h1
    (Real.logb_le_logb_of_le (by norm_num) hD0 hd)

/-- [s1:condG1] "Γ1 is upward closed in `D_*`" (items (a)–(e)). -/
theorem Gamma1core.mono {D D' : ℝ} (h : Gamma1core D) (hD : D ≤ D') : Gamma1core D' :=
  ⟨h.two_lt.trans_le hD, fun _ hμ => h.items ((loglog_mono h.two_lt hD).trans hμ)⟩

/-- [s1:condG1] "They also hold at `μ = log₂log₂d` for every `d ≥ D_*`". -/
theorem Gamma1core.items_loglog {D d : ℝ} (h : Gamma1core D) (hd : D ≤ d) :
    Gamma1Items (logb 2 (logb 2 d)) :=
  h.items (loglog_mono h.two_lt hd)

/-- (a) at `μ = log₂log₂D`. -/
theorem Gamma1core.two_pow_eight_le_loglog {D : ℝ} (h : Gamma1core D) :
    (2 : ℝ) ^ 8 ≤ logb 2 (logb 2 D) :=
  (h.items le_rfl).a

/-- [s1:condG1] "By (a) at `μ = log₂log₂D_*`, `log₂D_* ≥ 2^{256}`". -/
theorem Gamma1core.two_pow_256_le_logb {D : ℝ} (h : Gamma1core D) :
    (2 : ℝ) ^ 256 ≤ logb 2 D := by
  have h8 := h.two_pow_eight_le_loglog
  have hpos : 0 < logb 2 D := zero_lt_one.trans h.one_lt_logb
  rw [Real.le_logb_iff_rpow_le (by norm_num) hpos] at h8
  have : (2 : ℝ) ^ ((2 : ℝ) ^ 8) = (2 : ℝ) ^ (256 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rwa [this] at h8

/-- [s1:condG1] "and at `μ = log₂D_*` (as `t ≥ log₂t` for `t > 0`)". -/
theorem Gamma1core.items_logb {D : ℝ} (h : Gamma1core D) : Gamma1Items (logb 2 D) := by
  apply h.items
  have h2 : (2 : ℝ) ≤ logb 2 D := by
    have := h.two_pow_256_le_logb
    have : (2 : ℝ) ≤ 2 ^ 256 := by norm_num
    linarith
  have := logb_le_sub_one h2
  linarith

/-- Transfer used in s2:lemLacunary(iv) (blueprint s2b): the items hold at `μ = log₂ x` for
every `x ≥ log₂ D_*`. -/
theorem Gamma1core.items_logb_of_le {D x : ℝ} (h : Gamma1core D) (hx : logb 2 D ≤ x) :
    Gamma1Items (logb 2 x) :=
  h.items (Real.logb_le_logb_of_le (by norm_num) (zero_lt_one.trans h.one_lt_logb) hx)

/-- [s1:condG2] "(a) is immediate from Γ1": `Γ1 ⇒ D_* ≥ 2^{117}`. -/
theorem Gamma1core.gamma2a {D : ℝ} (h : Gamma1core D) : Gamma2a D := by
  have h256 := h.two_pow_256_le_logb
  have h117 : (117 : ℝ) ≤ logb 2 D := le_trans (by norm_num) h256
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith [h.two_lt])] at h117
  unfold Gamma2a
  have : (2 : ℝ) ^ (117 : ℝ) = (2 : ℝ) ^ (117 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rwa [this] at h117

/-- Γ2(a) is a lower bound on `D_*`, hence upward closed. -/
theorem Gamma2a.mono {D D' : ℝ} (h : Gamma2a D) (hD : D ≤ D') : Gamma2a D' :=
  le_trans h hD

/-! ### Non-vacuity: items (a)–(e) hold on a ray -/

/-- For `μ ≥ 2^{20}`, `t = log₂ μ ≥ 20` and `μ = 2^t ≥ 1024 (t - 9)` (Bernoulli at `t - 10`). -/
theorem two_pow_twenty_le_logb_bound {μ : ℝ} (hμ : (2 : ℝ) ^ 20 ≤ μ) :
    (20 : ℝ) ≤ logb 2 μ ∧ 1024 * (logb 2 μ - 9) ≤ μ := by
  have hμ0 : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  have ht : (20 : ℝ) ≤ logb 2 μ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hμ0]
    have : (2 : ℝ) ^ (20 : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rwa [this]
  refine ⟨ht, ?_⟩
  have h1 := add_one_le_two_rpow (y := logb 2 μ - 10) (by linarith)
  have h2 : (2 : ℝ) ^ (logb 2 μ - 10) = μ / 1024 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hμ0]
    norm_num
  rw [h2] at h1
  linarith

/-- `log₂(Aμ) ≤ 7 + log₂ μ` (`A = 105 ≤ 2^7`). -/
theorem logb_Aexp_mul_le {μ : ℝ} (hμ : 0 < μ) : logb 2 ((Aexp : ℝ) * μ) ≤ 7 + logb 2 μ := by
  rw [cast_Aexp, Real.logb_mul (by norm_num) hμ.ne']
  have : logb 2 (105 : ℝ) ≤ 7 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    have : (2 : ℝ) ^ (7 : ℝ) = (2 : ℝ) ^ (7 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [this]; norm_num
  linarith

/-- Non-vacuity of Γ1 (a)–(e): every item holds for every real `μ ≥ 2^{20}`. This is the (a)–(e)
part of the eventuality claim of s7:lemGammaSat ("each of them holds for all sufficiently large
`μ`"), with an explicit (non-optimised) threshold; it does not replace that lemma's Spec. -/
theorem gamma1Items_of_le {μ : ℝ} (hμ : (2 : ℝ) ^ 20 ≤ μ) : Gamma1Items μ := by
  obtain ⟨ht, hlin⟩ := two_pow_twenty_le_logb_bound hμ
  have hμ0 : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  set t := logb 2 μ with ht_def
  have hμt : (2 : ℝ) ^ t = μ := Real.rpow_logb (by norm_num) (by norm_num) hμ0
  have hA := logb_Aexp_mul_le hμ0
  have hAμ : 0 < (Aexp : ℝ) * μ := by rw [cast_Aexp]; positivity
  have hAμle : (Aexp : ℝ) * μ ≤ (2 : ℝ) ^ (7 + t) := by
    rw [← Real.logb_le_iff_le_rpow (by norm_num) hAμ]; exact hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Gamma1a
    exact le_trans (by norm_num) hμ
  · unfold Gamma1b
    have e1 : μ ^ 3 = (2 : ℝ) ^ (t * 3) := by
      rw [← hμt, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have e2 : (2 : ℝ) ^ 14 * (Aexp : ℝ) ≤ (2 : ℝ) ^ (21 : ℝ) := by
      rw [cast_Aexp]
      have : (2 : ℝ) ^ (21 : ℝ) = (2 : ℝ) ^ (21 : ℕ) := by
        rw [← Real.rpow_natCast]; norm_num
      rw [this]; norm_num
    calc (2 : ℝ) ^ 14 * (Aexp : ℝ) * μ ^ 3 ≤ (2 : ℝ) ^ (21 : ℝ) * (2 : ℝ) ^ (t * 3) := by
          rw [e1]; gcongr
      _ = (2 : ℝ) ^ (21 + t * 3) := by rw [Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ μ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · unfold Gamma1c
    rw [cast_Aexp] at hA ⊢
    have h1 : 2 * (105 : ℝ) * logb 2 ((105 : ℝ) * μ) ≤ 210 * (7 + t) := by linarith
    have : (210 : ℝ) * (7 + t) ≤ 1.6 * μ := by norm_num; linarith
    linarith
  · unfold Gamma1d
    linarith
  · unfold Gamma1e
    have e1 : ((Aexp : ℝ) * μ) ^ (46 * Aexp) ≤ (2 : ℝ) ^ ((7 + t) * ((46 * Aexp : ℕ) : ℝ)) := by
      rw [Real.rpow_mul_natCast (by norm_num)]
      gcongr
    have e2 : ((2 : ℝ) ^ μ) ^ 36 = (2 : ℝ) ^ (μ * 36) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have e3 : (2 : ℝ) ^ 240 = (2 : ℝ) ^ (240 : ℝ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e2]
    calc (2 : ℝ) ^ 240 * ((Aexp : ℝ) * μ) ^ (46 * Aexp)
        ≤ (2 : ℝ) ^ (240 : ℝ) * (2 : ℝ) ^ ((7 + t) * ((46 * Aexp : ℕ) : ℝ)) := by
          rw [e3]; gcongr
      _ = (2 : ℝ) ^ (240 + (7 + t) * ((46 * Aexp : ℕ) : ℝ)) := by
          rw [Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ (μ * 36) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [Aexp_eq]; push_cast
          nlinarith

/-- [s1:condG1] "each of them holds for all sufficiently large `μ`" (items (a)–(e)). -/
theorem eventually_gamma1Items : ∀ᶠ μ in Filter.atTop, Gamma1Items μ :=
  (Filter.eventually_ge_atTop _).mono fun _ h => gamma1Items_of_le h

/-- An explicit `D` satisfying `Gamma1core`: `D = 2^{2^{2^{20}}}` (so `log₂log₂D = 2^{20}`). -/
theorem gamma1core_two_rpow_two_rpow : Gamma1core ((2 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) ^ (20 : ℕ)))) := by
  refine ⟨?_, fun μ hμ => gamma1Items_of_le ?_⟩
  · calc (2 : ℝ) < (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by
            calc (2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := by norm_num
              _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  · rwa [Real.logb_rpow (by norm_num) (by norm_num),
      Real.logb_rpow (by norm_num) (by norm_num)] at hμ

/-- `Gamma1core` is satisfiable, so Specs assuming it are not vacuous on that account. -/
theorem exists_gamma1core : ∃ D : ℝ, Gamma1core D := ⟨_, gamma1core_two_rpow_two_rpow⟩

/-- Every sufficiently large `D` satisfies `Gamma1core` (upward closure + `exists_gamma1core`). -/
theorem eventually_gamma1core : ∀ᶠ D in Filter.atTop, Gamma1core D :=
  Filter.eventually_atTop.2 ⟨_, fun _ hD => gamma1core_two_rpow_two_rpow.mono hD⟩

end EG
