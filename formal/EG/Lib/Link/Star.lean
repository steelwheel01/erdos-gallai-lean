module

public import EG.Defs.Link.Star

/-!
# API for the (eqStar) parameters (manuscript s3:eqStar)

Characterization and elementary lemmas for the definitions of `EG/Defs/Link/Star.lean`. These
are facts about the *definitions* (in particular, that the explicit `p_*` is the number that the
manuscript defines implicitly); the facts (S1)–(S6) as a whole are the Spec
`StarFactsStatement` (blueprint s3a) and are not proved here.

* `L`: `L_eq`, `one_le_L` (`n ≥ 2 ⇒ L ≥ 1`), `L_nonneg`;
* `ell`: `ell_le`, `lt_ell` (the two bounds of (S1), from the floor), `two_pow_ten_le_ell`,
  `two_le_ell`;
* `p` (decision STAR-PSTAR-IMPLICIT): `base_nonneg`, `base_lt_one`, `p_pos`, `p_le_one`,
  `one_sub_p_pow` (the defining equation `(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)`), `p_unique` (any
  `x ≤ 1` with `(1-x)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)` equals `p_*`), `p_spec`, `existsUnique_p`;
* ceilings: `one_div_p_le_d`, `d_lt`, `one_le_d`, `six_div_p_le_lam`, `lam_lt`, `one_le_lam`,
  `lam_le_Delta`, `dlam_div_three_le`;
* positivity: `q_pos`, `sigma_pos`, `theta_pos`, `mu_pos`, `sbar_pos`, `g_pos`;
  `M_pos`, `le_M`, `div_le_K`, `ell_pos`, `K_pos`, `K_ne_zero` (T16* colours `E(X)` with
  `Fin (K n ε' ρ t)`, which needs `K_* ≠ 0`).
-/

public section


namespace EG.Star

open Real

theorem L_eq (n : ℕ) : L n = logb 2 (n : ℝ) := rfl

theorem one_le_L {n : ℕ} (hn : 2 ≤ n) : 1 ≤ L n := by
  rw [L, Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num
  exact_mod_cast hn

theorem L_pos {n : ℕ} (hn : 2 ≤ n) : 0 < L n := lt_of_lt_of_le one_pos (one_le_L hn)

theorem L_nonneg (n : ℕ) : 0 ≤ L n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [L]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

/-! ## `ℓ_*` -/

theorem ell_le (n : ℕ) : (ell n : ℝ) ≤ (2 : ℝ) ^ 10 * L n ^ 3 :=
  Nat.floor_le (by have := L_nonneg n; positivity)

theorem lt_ell (n : ℕ) : (2 : ℝ) ^ 10 * L n ^ 3 - 1 < ell n := by
  have := Nat.lt_floor_add_one ((2 : ℝ) ^ 10 * L n ^ 3)
  rw [ell]; linarith

theorem two_pow_ten_le_ell {n : ℕ} (hn : 2 ≤ n) : 2 ^ 10 ≤ ell n := by
  apply Nat.le_floor
  have h1 := one_le_L hn
  have : (1 : ℝ) ≤ L n ^ 3 := one_le_pow₀ h1
  push_cast
  nlinarith

theorem two_le_ell {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ell n :=
  le_trans (by norm_num) (two_pow_ten_le_ell hn)

/-- The real number `ℓ_* - 1` equals the cast of the natural number `ℓ_* - 1` (for `ℓ_* ≥ 1`). -/
theorem cast_ell_sub_one {n : ℕ} (hn : 2 ≤ n) : ((ell n - 1 : ℕ) : ℝ) = (ell n : ℝ) - 1 := by
  have := two_le_ell hn
  push_cast [show 1 ≤ ell n by omega]
  ring

/-! ## `p_*` -/

/-- The base `(1-ρ)/(1-0.9ρ)` of the defining equation of `p_*`. -/
theorem base_nonneg {ρ : ℝ} (h1 : ρ ≤ 1) : 0 ≤ (1 - ρ) / (1 - 9 / 10 * ρ) :=
  div_nonneg (by linarith) (by linarith)

theorem base_lt_one {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) : (1 - ρ) / (1 - 9 / 10 * ρ) < 1 := by
  rw [div_lt_one (by linarith)]; linarith

theorem p_eq (n : ℕ) (ρ : ℝ) :
    p n ρ = 1 - ((1 - ρ) / (1 - 9 / 10 * ρ)) ^ ((1 : ℝ) / ((ell n : ℝ) - 1)) := rfl

private theorem one_div_ell_sub_one_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (1 : ℝ) / ((ell n : ℝ) - 1) := by
  have : (2 : ℝ) ≤ ell n := by exact_mod_cast two_le_ell hn
  apply div_pos one_pos; linarith

theorem p_pos {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : 0 < p n ρ := by
  rw [p_eq, sub_pos]
  exact Real.rpow_lt_one (base_nonneg h1) (base_lt_one h0 h1) (one_div_ell_sub_one_pos hn)

theorem p_le_one {n : ℕ} {ρ : ℝ} (h1 : ρ ≤ 1) : p n ρ ≤ 1 := by
  rw [p_eq]
  have := Real.rpow_nonneg (base_nonneg h1) ((1 : ℝ) / ((ell n : ℝ) - 1))
  linarith

/-- [s3:eqStar] the defining equation "`(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)`" (natural-number power
`ℓ_* - 1`). -/
theorem one_sub_p_pow {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h1 : ρ ≤ 1) :
    (1 - p n ρ) ^ (ell n - 1) = (1 - ρ) / (1 - 9 / 10 * ρ) := by
  have hb := base_nonneg h1
  have hl : (2 : ℝ) ≤ ell n := by exact_mod_cast two_le_ell hn
  rw [p_eq, sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul hb, cast_ell_sub_one hn,
    one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]

/-- [s3:eqS2] "The number `p_*` exists, is unique": every `x ≤ 1` with
`(1-x)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)` is `p_*`. -/
theorem p_unique {n : ℕ} {ρ x : ℝ} (hn : 2 ≤ n) (h1 : ρ ≤ 1)
    (hx1 : x ≤ 1) (hx : (1 - x) ^ (ell n - 1) = (1 - ρ) / (1 - 9 / 10 * ρ)) : x = p n ρ := by
  have hk : ell n - 1 ≠ 0 := by have := two_le_ell hn; omega
  have hp1 := p_le_one (n := n) h1
  rw [← one_sub_p_pow hn h1] at hx
  have := (pow_left_inj₀ (by linarith) (by linarith) hk).1 hx
  linarith

/-- [s3:eqStar] "`p_* ∈ (0,1]` given by `(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)`". -/
theorem p_spec {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    0 < p n ρ ∧ p n ρ ≤ 1 ∧ (1 - p n ρ) ^ (ell n - 1) = (1 - ρ) / (1 - 9 / 10 * ρ) :=
  ⟨p_pos hn h0 h1, p_le_one h1, one_sub_p_pow hn h1⟩

/-- [s3:eqS2] existence and uniqueness of `p_*` in `(0,1]`, with `p_*` the witness. -/
theorem existsUnique_p {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    ∃! x : ℝ, (0 < x ∧ x ≤ 1 ∧ (1 - x) ^ (ell n - 1) = (1 - ρ) / (1 - 9 / 10 * ρ)) :=
  ⟨p n ρ, p_spec hn h0 h1, fun _ hx => p_unique hn h1 hx.2.1 hx.2.2⟩

theorem p_one {n : ℕ} (hn : 2 ≤ n) : p n 1 = 1 := by
  have h := one_div_ell_sub_one_pos hn
  rw [one_div] at h
  rw [p_eq]
  norm_num
  rw [Real.zero_rpow (ne_of_gt h)]

/-! ## The integer ceilings -/

theorem one_div_p_le_d (n : ℕ) (ρ : ℝ) : 1 / p n ρ ≤ d n ρ := Nat.le_ceil _

theorem d_lt {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (d n ρ : ℝ) < 1 / p n ρ + 1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos one_pos (p_pos hn h0 h1)))

theorem one_le_d {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : 1 ≤ d n ρ :=
  Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (div_pos one_pos
    (p_pos hn h0 h1))))

theorem six_div_p_le_lam (n : ℕ) (ρ : ℝ) : 6 / p n ρ ≤ lam n ρ := Nat.le_ceil _

theorem lam_lt {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (lam n ρ : ℝ) < 6 / p n ρ + 1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num) (p_pos hn h0 h1)))

theorem one_le_lam {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : 1 ≤ lam n ρ :=
  Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (div_pos (by norm_num)
    (p_pos hn h0 h1))))

theorem lam_le_Delta (n : ℕ) (ρ : ℝ) : lam n ρ ≤ Delta n ρ := Nat.le_add_right _ _

theorem Delta_eq (n : ℕ) (ρ : ℝ) :
    Delta n ρ = lam n ρ + ⌈((d n ρ : ℝ) * (lam n ρ : ℝ)) / 3⌉₊ := rfl

/-- "`Δ_* - λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3`" (the P13* check after (S6)). -/
theorem dlam_div_three_le (n : ℕ) (ρ : ℝ) :
    ((d n ρ : ℝ) * (lam n ρ : ℝ)) / 3 ≤ (Delta n ρ : ℝ) - lam n ρ := by
  rw [Delta_eq]; push_cast
  have := Nat.le_ceil (((d n ρ : ℝ) * (lam n ρ : ℝ)) / 3)
  linarith

theorem le_M (ρ : ℝ) : (21 / 10 : ℝ) / ρ ≤ M ρ := Nat.le_ceil _

theorem M_lt {ρ : ℝ} (h0 : 0 < ρ) : (M ρ : ℝ) < (21 / 10 : ℝ) / ρ + 1 :=
  Nat.ceil_lt_add_one (by positivity)

theorem M_pos {ρ : ℝ} (h0 : 0 < ρ) : 0 < M ρ := Nat.ceil_pos.2 (by positivity)

theorem div_le_K (n : ℕ) (ε' ρ t : ℝ) :
    6 * sbar n ρ t * theta n ε' ρ * L n ^ 2 / ε' ≤ K n ε' ρ t := Nat.le_ceil _

/-! ## Positivity -/

theorem q_pos {ρ : ℝ} (h0 : 0 < ρ) : 0 < q ρ := by unfold q; positivity

theorem g_pos {n : ℕ} {ε' : ℝ} (hn : 2 ≤ n) (hε : 0 < ε') : 0 < g n ε' := by
  have := L_pos hn; unfold g; positivity

theorem sigma_pos {n : ℕ} {ε' : ℝ} (hn : 2 ≤ n) (hε : 0 < ε') : 0 < sigma n ε' := by
  have := L_pos hn; unfold sigma; positivity

theorem theta_pos {n : ℕ} {ε' ρ : ℝ} (hn : 2 ≤ n) (hε : 0 < ε') (h0 : 0 < ρ) :
    0 < theta n ε' ρ := by
  have := L_pos hn
  have : (0 : ℝ) < ell n := by exact_mod_cast (show 0 < ell n by have := two_le_ell hn; omega)
  unfold theta; positivity

theorem mu_pos {n : ℕ} {ε' ρ : ℝ} (hn : 2 ≤ n) (hε : 0 < ε') (h0 : 0 < ρ) :
    0 < mu n ε' ρ := by
  have := L_pos hn; have := theta_pos hn hε h0
  unfold mu; positivity

theorem sbar_pos {n : ℕ} {ρ t : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (ht : 0 < t) :
    0 < sbar n ρ t := by
  have := L_pos hn; unfold sbar; positivity

theorem ell_pos {n : ℕ} (hn : 2 ≤ n) : 0 < ell n :=
  lt_of_lt_of_le (by norm_num) (two_le_ell hn)

/-- `K_* > 0` in the domain (T16* colours `E(X)` with `K_*` colours). -/
theorem K_pos {n : ℕ} {ε' ρ t : ℝ} (hn : 2 ≤ n) (hε : 0 < ε') (h0 : 0 < ρ) (ht : 0 < t) :
    0 < K n ε' ρ t := by
  have := L_pos hn; have := sbar_pos hn h0 ht; have := theta_pos hn hε h0
  exact Nat.ceil_pos.2 (by positivity)

theorem K_ne_zero {n : ℕ} {ε' ρ t : ℝ} (hn : 2 ≤ n) (hε : 0 < ε') (h0 : 0 < ρ) (ht : 0 < t) :
    K n ε' ρ t ≠ 0 :=
  (K_pos hn hε h0 ht).ne'

end EG.Star
