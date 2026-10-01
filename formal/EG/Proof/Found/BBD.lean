module

public import EG.Spec.Found.BBD
public import EG.Lib.Prob.Indep
public import EG.Lib.Prob.Named
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Lemma BBD, a Bernstein inequality for bounded differences (manuscript s1:lemBBD)

Proofs of `EG.Spec.BBDStatement` and `EG.Spec.BBDRVStatement`, following the proof in s1.tex
(exponential moments and induction over the coordinates, finite sums only):

* Step 2 (`EG.BBD.one_sub_div_three_mul_exp_le`, `EG.BBD.exp_le_quad`): the elementary
  inequality `(1 − u/3)e^u ≤ 1 + 2u/3 + u²/6` for all real `u`, and its consequence
  `e^u ≤ 1 + u + u²/(2(1 − ζ/3))` for `u ≤ ζ < 3`;
* Step 3 (`EG.BBD.one_coord`): the one-coordinate bound
  `p e^{η(1−p)Ξ} + (1−p) e^{−ηpΞ} ≤ exp(η² p(1−p)c²/(2(1 − ηb/3)))` for `|Ξ| ≤ c ≤ b`;
* Steps 1 and 4 (`EG.BBD.mgf_fin`): the exponential moment bound
  `E exp(η(Ψ(I) − EΨ(I))) ≤ exp(η²β/(2(1 − ηb/3)))` for coordinates `Fin n`, by induction on `n`.
  The induction reveals the first coordinate `x₀` and applies the induction hypothesis to the
  function `Ψ(x₀, ·)` of the remaining coordinates; the partial average
  `Ψ₁(x₀) = E Ψ(x₀, I')` satisfies `EΨ = pΨ₁(1) + (1−p)Ψ₁(0)` and `|Ψ₁(1) − Ψ₁(0)| ≤ c₀`
  (this is (s1:eqBBDavg) and the bound `|Ξ_k| ≤ c_k` of Step 1). It is the manuscript's
  induction over the partial averages `Ψ_k`, organised from the first coordinate;
* `EG.BBD.mgf`: the same for an arbitrary finite index type (transport along `ι ≃ Fin n`);
* Steps 5 and 6 (`EG.BBD.upper_tail`, `EG.bbd`, `EG.bbdRV`): Markov's inequality for
  `e^{η(Ψ − EΨ − a)}` with `η = a/(β + ba/3)`, and the lower tail from `−Ψ`.
-/

public section


namespace EG

namespace BBD

open Finset

/-! ### Step 2: an elementary inequality -/

/-- The derivative of `χ' (u) = 2/3 + u/3 − (2/3 − u/3) e^u` is `(1 − (1 − u)e^u)/3`. -/
theorem hasDerivAt_chi' (u : ℝ) :
    HasDerivAt (fun u => 2 / 3 + u / 3 - (2 / 3 - u / 3) * Real.exp u)
      ((1 - (1 - u) * Real.exp u) / 3) u := by
  have h1 : HasDerivAt (fun u : ℝ => 2 / 3 + u / 3) (1 / 3) u := by
    simpa using ((hasDerivAt_id u).div_const 3).const_add (2 / 3)
  have h2 : HasDerivAt (fun u : ℝ => 2 / 3 - u / 3) (-(1 / 3)) u := by
    simpa using ((hasDerivAt_id u).div_const 3).const_sub (2 / 3)
  exact (h1.sub (h2.mul (Real.hasDerivAt_exp u))).congr_deriv (by ring)

/-- The derivative of `χ (u) = 1 + 2u/3 + u²/6 − (1 − u/3) e^u` is `χ' (u)`. -/
theorem hasDerivAt_chi (u : ℝ) :
    HasDerivAt (fun u => 1 + 2 * u / 3 + u ^ 2 / 6 - (1 - u / 3) * Real.exp u)
      (2 / 3 + u / 3 - (2 / 3 - u / 3) * Real.exp u) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 + 2 * u / 3 + u ^ 2 / 6) (2 / 3 + u / 3) u := by
    have a := (((hasDerivAt_id u).const_mul 2).div_const 3).const_add 1
    have b := ((hasDerivAt_pow 2 u).div_const 6)
    exact (a.add b).congr_deriv (by simp; ring)
  have h2 : HasDerivAt (fun u : ℝ => 1 - u / 3) (-(1 / 3)) u := by
    simpa using ((hasDerivAt_id u).div_const 3).const_sub 1
  exact (h1.sub (h2.mul (Real.hasDerivAt_exp u))).congr_deriv (by ring)

/-- `χ'` is non-decreasing: its derivative `(1 − (1 − u)e^u)/3` is non-negative, as
`1 − u ≤ e^{−u}`. -/
theorem chi'_mono : Monotone fun u : ℝ => 2 / 3 + u / 3 - (2 / 3 - u / 3) * Real.exp u := by
  refine monotone_of_deriv_nonneg (fun u => (hasDerivAt_chi' u).differentiableAt) fun u => ?_
  rw [(hasDerivAt_chi' u).deriv]
  have h := Real.add_one_le_exp (-u)
  have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos u
  have : (1 - u) * Real.exp u ≤ 1 := by nlinarith
  linarith

/-- [s1:lemBBD] Step 2, (s1:eqBBDphi): "For every real `u`,
`(1 − u/3)e^u ≤ 1 + 2u/3 + u²/6`." -/
theorem one_sub_div_three_mul_exp_le (u : ℝ) :
    (1 - u / 3) * Real.exp u ≤ 1 + 2 * u / 3 + u ^ 2 / 6 := by
  set χ : ℝ → ℝ := fun u => 1 + 2 * u / 3 + u ^ 2 / 6 - (1 - u / 3) * Real.exp u with hχ
  have hd : ∀ u, HasDerivAt χ (2 / 3 + u / 3 - (2 / 3 - u / 3) * Real.exp u) u := hasDerivAt_chi
  have hχ0 : χ 0 = 0 := by simp [hχ]
  have hχ'0 : (2 / 3 + (0 : ℝ) / 3 - (2 / 3 - (0 : ℝ) / 3) * Real.exp 0) = 0 := by simp
  have hcont : Continuous χ := continuous_iff_continuousAt.2 fun u => (hd u).continuousAt
  suffices 0 ≤ χ u by simp only [hχ] at this; linarith
  rcases le_total u 0 with hu | hu
  · have hanti : AntitoneOn χ (Set.Iic 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn
        (fun v _ => (hd v).differentiableAt.differentiableWithinAt) fun v hv => ?_
      rw [interior_Iic] at hv
      rw [(hd v).deriv, ← hχ'0]
      exact chi'_mono (le_of_lt hv)
    have := hanti hu (Set.self_mem_Iic) hu
    linarith
  · have hmono : MonotoneOn χ (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
        (fun v _ => (hd v).differentiableAt.differentiableWithinAt) fun v hv => ?_
      rw [interior_Ici] at hv
      rw [(hd v).deriv, ← hχ'0]
      exact chi'_mono (le_of_lt hv)
    have := hmono (Set.self_mem_Ici) hu hu
    linarith

/-- [s1:lemBBD] Step 2, (s1:eqBBDexp): "let `0 ≤ ζ < 3` and `u ≤ ζ`. Then
`e^u ≤ 1 + u + u²/(2(1 − u/3)) ≤ 1 + u + u²/(2(1 − ζ/3))`." -/
theorem exp_le_quad {ζ u : ℝ} (hζ : ζ < 3) (hu : u ≤ ζ) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - ζ / 3)) := by
  have hr : 0 < 1 - ζ / 3 := by linarith
  have hq : 1 - ζ / 3 ≤ 1 - u / 3 := by linarith
  have hq0 : 0 < 1 - u / 3 := lt_of_lt_of_le hr hq
  have h := one_sub_div_three_mul_exp_le u
  have hsq : u ^ 2 / 2 ≤ (1 - u / 3) * (u ^ 2 / (2 * (1 - ζ / 3))) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have := sq_nonneg u
    nlinarith
  have key : (1 - u / 3) * Real.exp u ≤ (1 - u / 3) * (1 + u + u ^ 2 / (2 * (1 - ζ / 3))) := by
    nlinarith
  exact le_of_mul_le_mul_left key hq0

/-! ### Step 3: one coordinate -/

/-- [s1:lemBBD] Step 3, (s1:eqBBDstep): for `p ∈ [0,1]`, `|Ξ| ≤ c ≤ b`, `η ≥ 0` and `ηb < 3`,
"`p e^{η(1−p)Ξ} + (1−p) e^{−ηpΞ} ≤ 1 + η²p(1−p)Ξ²/(2(1−ζ/3)) ≤ exp(η²p(1−p)c²/(2(1−ζ/3)))`"
with `ζ = ηb`. -/
theorem one_coord {η b p c Ξ : ℝ} (hη : 0 ≤ η) (hζ : η * b < 3) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hΞ : |Ξ| ≤ c) (hcb : c ≤ b) :
    p * Real.exp (η * ((1 - p) * Ξ)) + (1 - p) * Real.exp (η * (-(p * Ξ))) ≤
      Real.exp (η ^ 2 / (2 * (1 - η * b / 3)) * (p * (1 - p) * c ^ 2)) := by
  have hr : 0 < 1 - η * b / 3 := by linarith
  have hΞb : |Ξ| ≤ b := hΞ.trans hcb
  have hu1 : η * ((1 - p) * Ξ) ≤ η * b := by
    refine mul_le_mul_of_nonneg_left ?_ hη
    have h1 : (1 - p) * Ξ ≤ (1 - p) * |Ξ| := mul_le_mul_of_nonneg_left (le_abs_self Ξ) (by linarith)
    have h2 : (1 - p) * |Ξ| ≤ |Ξ| := by nlinarith [abs_nonneg Ξ]
    linarith
  have hu2 : η * (-(p * Ξ)) ≤ η * b := by
    refine mul_le_mul_of_nonneg_left ?_ hη
    have h1 : -(p * Ξ) ≤ p * |Ξ| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs Ξ) hp0
    have h2 : p * |Ξ| ≤ |Ξ| := by nlinarith [abs_nonneg Ξ]
    linarith
  have e1 := exp_le_quad hζ hu1
  have e2 := exp_le_quad hζ hu2
  have hsum : p * Real.exp (η * ((1 - p) * Ξ)) + (1 - p) * Real.exp (η * (-(p * Ξ))) ≤
      1 + η ^ 2 / (2 * (1 - η * b / 3)) * (p * (1 - p) * Ξ ^ 2) := by
    have := add_le_add (mul_le_mul_of_nonneg_left e1 hp0)
      (mul_le_mul_of_nonneg_left e2 (sub_nonneg.2 hp1))
    refine this.trans (le_of_eq ?_)
    ring
  have hsq : Ξ ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg Ξ) hΞ 2
  have hD : 0 ≤ η ^ 2 / (2 * (1 - η * b / 3)) := by positivity
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.2 hp1)
  calc _ ≤ 1 + η ^ 2 / (2 * (1 - η * b / 3)) * (p * (1 - p) * Ξ ^ 2) := hsum
    _ ≤ 1 + η ^ 2 / (2 * (1 - η * b / 3)) * (p * (1 - p) * c ^ 2) := by
        gcongr
    _ ≤ _ := by
        rw [add_comm]; exact Real.add_one_le_exp _

/-! ### Steps 1 and 4: the exponential moment, by induction over the coordinates -/

/-- The product Bernoulli weight `wt_m(x) = ∏_k (p_k x_k + (1 − p_k)(1 − x_k))` of s1:lemBBD,
for `x : ι → Bool` (`true` for `1`). It is the weight of `x` under
`pi (fun k => bernoulli (p k) _ _)` (`EG.BBD.pi_bernoulli_w`). -/
@[expose] noncomputable def wt {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ k, cond (x k) (p k) (1 - p k)

theorem pi_bernoulli_w {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (x : ι → Bool) :
    (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).w x = wt p x := rfl

theorem wt_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (x : ι → Bool) : 0 ≤ wt p x := by
  rw [← pi_bernoulli_w p hp0 hp1]; exact FinDist.w_nonneg _ _

theorem sum_wt {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ} (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) : ∑ x, wt p x = 1 := by
  simp only [← pi_bernoulli_w p hp0 hp1]; exact FinDist.sum_w _

theorem wt_cons {n : ℕ} (p : Fin (n + 1) → ℝ) (x₀ : Bool) (x : Fin n → Bool) :
    wt p (Fin.cons x₀ x) = cond x₀ (p 0) (1 - p 0) * wt (Fin.tail p) x := by
  simp only [wt, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x, F x = ∑ x₀ : Bool, ∑ x : Fin n → Bool, F (Fin.cons x₀ x) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

/-- [s1:lemBBD] Steps 1 and 4 for the coordinates `Fin n`: with `D = η²/(2(1 − ηb/3))`,
`E exp(η(Ψ(I) − EΨ(I))) ≤ exp(D ∑_k p_k(1 − p_k)c_k²)`. -/
theorem mgf_fin {η b : ℝ} (hη : 0 ≤ η) (hζ : η * b < 3) : ∀ (n : ℕ) (p : Fin n → ℝ),
    (∀ k, 0 ≤ p k) → (∀ k, p k ≤ 1) → ∀ (Ψ : (Fin n → Bool) → ℝ) (c : Fin n → ℝ),
    (∀ k, c k ≤ b) → (∀ k x v, |Ψ (Function.update x k v) - Ψ x| ≤ c k) →
    ∑ x, wt p x * Real.exp (η * (Ψ x - ∑ y, wt p y * Ψ y)) ≤
      Real.exp (η ^ 2 / (2 * (1 - η * b / 3)) * ∑ k, p k * (1 - p k) * c k ^ 2) := by
  set D := η ^ 2 / (2 * (1 - η * b / 3)) with hD
  intro n
  induction n with
  | zero =>
    intro p _ _ Ψ c _ _
    simp [wt]
  | succ n ih =>
    intro p hp0 hp1 Ψ c hc hΨ
    set p' : Fin n → ℝ := Fin.tail p with hp'
    set c' : Fin n → ℝ := Fin.tail c with hc'
    have hp0' : ∀ k, 0 ≤ p' k := fun k => hp0 _
    have hp1' : ∀ k, p' k ≤ 1 := fun k => hp1 _
    -- the partial averages `Ψ₁(x₀) = E Ψ(x₀, I')`
    set M' : Bool → ℝ := fun x₀ => ∑ y, wt p' y * Ψ (Fin.cons x₀ y) with hM'
    set M : ℝ := ∑ y, wt p y * Ψ y with hM
    have hMsplit : M = p 0 * M' true + (1 - p 0) * M' false := by
      rw [hM, sum_cons, Fintype.sum_bool]
      simp only [wt_cons, hM', mul_sum, cond_true, cond_false, mul_assoc]
      rfl
    -- the induction hypothesis for `Ψ(x₀, ·)`
    have hih : ∀ x₀ : Bool, ∑ y, wt p' y * Real.exp (η * (Ψ (Fin.cons x₀ y) - M' x₀)) ≤
        Real.exp (D * ∑ k, p' k * (1 - p' k) * c' k ^ 2) := by
      intro x₀
      refine ih p' hp0' hp1' (fun y => Ψ (Fin.cons x₀ y)) c' (fun k => hc _) fun k y v => ?_
      rw [Fin.cons_update]
      exact hΨ _ _ _
    -- `|Ξ| ≤ c₀`
    have hΞ : |M' true - M' false| ≤ c 0 := by
      have : M' true - M' false =
          ∑ y, wt p' y * (Ψ (Function.update (Fin.cons false y) 0 true) - Ψ (Fin.cons false y)) := by
        simp only [hM', Fin.update_cons_zero, mul_sub, sum_sub_distrib]
      rw [this]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ y, |wt p' y * (Ψ (Function.update (Fin.cons false y) 0 true) - Ψ (Fin.cons false y))|
          ≤ ∑ y, wt p' y * c 0 := by
            refine sum_le_sum fun y _ => ?_
            rw [abs_mul, abs_of_nonneg (wt_nonneg hp0' hp1' y)]
            exact mul_le_mul_of_nonneg_left (hΨ _ _ _) (wt_nonneg hp0' hp1' y)
        _ = c 0 := by rw [← sum_mul, sum_wt hp0' hp1', one_mul]
    set S' := ∑ k, p' k * (1 - p' k) * c' k ^ 2 with hS'
    have hexp : ∀ x₀ y, Real.exp (η * (Ψ (Fin.cons x₀ y) - M)) =
        Real.exp (η * (M' x₀ - M)) * Real.exp (η * (Ψ (Fin.cons x₀ y) - M' x₀)) := by
      intro x₀ y; rw [← Real.exp_add]; ring_nf
    have hwpos : ∀ x₀ : Bool, 0 ≤ cond x₀ (p 0) (1 - p 0) := by
      intro x₀; cases x₀
      · simpa using hp1 0
      · simpa using hp0 0
    calc ∑ x, wt p x * Real.exp (η * (Ψ x - M))
        = ∑ x₀ : Bool, cond x₀ (p 0) (1 - p 0) * Real.exp (η * (M' x₀ - M)) *
            ∑ y, wt p' y * Real.exp (η * (Ψ (Fin.cons x₀ y) - M' x₀)) := by
          rw [sum_cons]
          refine sum_congr rfl fun x₀ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun y _ => ?_
          rw [wt_cons, hexp]
          ring
      _ ≤ ∑ x₀ : Bool, cond x₀ (p 0) (1 - p 0) * Real.exp (η * (M' x₀ - M)) *
            Real.exp (D * S') := by
          refine sum_le_sum fun x₀ _ => ?_
          exact mul_le_mul_of_nonneg_left (hih x₀)
            (mul_nonneg (hwpos x₀) (Real.exp_pos _).le)
      _ = (p 0 * Real.exp (η * ((1 - p 0) * (M' true - M' false))) +
            (1 - p 0) * Real.exp (η * (-(p 0 * (M' true - M' false))))) *
            Real.exp (D * S') := by
          rw [Fintype.sum_bool, cond_true, cond_false, hMsplit]
          ring_nf
      _ ≤ Real.exp (D * (p 0 * (1 - p 0) * c 0 ^ 2)) * Real.exp (D * S') := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact one_coord hη hζ (hp0 0) (hp1 0) hΞ (hc 0)
      _ = Real.exp (D * ∑ k, p k * (1 - p k) * c k ^ 2) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          congr 1
          rw [hS']
          ring_nf
          rfl

/-- [s1:lemBBD] Steps 1 and 4 for an arbitrary finite index type (transport of `mgf_fin` along
`ι ≃ Fin n`): with `D = η²/(2(1 − ηb/3))`,
`E exp(η(Ψ(I) − EΨ(I))) ≤ exp(D ∑_k p_k(1 − p_k)c_k²)`. -/
theorem mgf {ι : Type*} [Fintype ι] [DecidableEq ι] {η b : ℝ} (hη : 0 ≤ η) (hζ : η * b < 3)
    (p : ι → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (Ψ : (ι → Bool) → ℝ) (c : ι → ℝ)
    (hc : ∀ k, c k ≤ b) (hΨ : ∀ k x v, |Ψ (Function.update x k v) - Ψ x| ≤ c k) :
    ∑ x, wt p x * Real.exp (η * (Ψ x - ∑ y, wt p y * Ψ y)) ≤
      Real.exp (η ^ 2 / (2 * (1 - η * b / 3)) * ∑ k, p k * (1 - p k) * c k ^ 2) := by
  set e := Fintype.equivFin ι
  set E : (ι → Bool) ≃ (Fin (Fintype.card ι) → Bool) := e.arrowCongr (Equiv.refl Bool)
  have hE : ∀ x, E x = x ∘ e.symm := fun x => rfl
  set p' : Fin (Fintype.card ι) → ℝ := p ∘ e.symm
  set c' : Fin (Fintype.card ι) → ℝ := c ∘ e.symm
  set Ψ' : (Fin (Fintype.card ι) → Bool) → ℝ := fun y => Ψ (y ∘ e)
  have hwt : ∀ x, wt p x = wt p' (E x) := by
    intro x
    refine Fintype.prod_equiv e _ _ fun i => ?_
    simp [hE, p']
  have hΨE : ∀ x, Ψ x = Ψ' (E x) := by
    intro x
    simp only [Ψ', hE]
    congr 1
    ext i
    simp
  have hsumE : ∀ F : (Fin (Fintype.card ι) → Bool) → ℝ, ∑ x, F (E x) = ∑ y, F y :=
    fun F => E.sum_comp F
  have hM : ∑ y, wt p y * Ψ y = ∑ y, wt p' y * Ψ' y := by
    simp only [hwt, hΨE]; exact hsumE fun y => wt p' y * Ψ' y
  have hS : ∑ k, p k * (1 - p k) * c k ^ 2 = ∑ k, p' k * (1 - p' k) * c' k ^ 2 := by
    simp only [p', c', Function.comp]
    exact (e.symm.sum_comp fun k => p k * (1 - p k) * c k ^ 2).symm
  have h := mgf_fin hη hζ (Fintype.card ι) p' (fun k => hp0 _) (fun k => hp1 _) Ψ' c'
    (fun k => hc _) fun k y v => by
      simp only [Ψ', c', Function.comp_apply]
      rw [Function.update_comp_equiv]
      exact hΨ _ _ _
  rw [hM, hS]
  refine le_trans (le_of_eq ?_) h
  simp only [hwt, hΨE]
  exact hsumE fun y => wt p' y * Real.exp (η * (Ψ' y - ∑ y, wt p' y * Ψ' y))

/-! ### Steps 5 and 6: the tails -/

/-- The expectation under the product Bernoulli law is the weighted sum `∑_x wt_m(x) g(x)`. -/
theorem expect_pi_bernoulli {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (g : (ι → Bool) → ℝ) :
    (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).expect g =
      ∑ x, wt p x * g x := by
  rw [FinDist.expect_eq_sum]; rfl

/-- [s1:lemBBD] Step 5, the upper tail: `P(Ψ(I) ≥ EΨ(I) + a) ≤ exp(−a²/(2(β + ba/3)))`. Here
the bounded-differences hypothesis is in the `Function.update` form. -/
theorem upper_tail {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (Ψ : (ι → Bool) → ℝ) (b : ℝ) (c : ι → ℝ) (β a : ℝ)
    (hc : ∀ k, c k ≤ b) (hΨ : ∀ k x v, |Ψ (Function.update x k v) - Ψ x| ≤ c k)
    (hβ : 0 < β) (hS : ∑ k, p k * (1 - p k) * c k ^ 2 ≤ β) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).prob
        {x | (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).expect Ψ + a ≤ Ψ x} ≤
      Real.exp (-(a ^ 2 / (2 * (β + b * a / 3)))) := by
  set μ := FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k) with hμ
  set T := β + b * a / 3 with hT
  have hT0 : 0 < T := by positivity
  set η := a / T with hη
  have hη0 : 0 ≤ η := by positivity
  have hηb : η * b < 3 := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ hT0]
    nlinarith
  have hr : 1 - η * b / 3 = β / T := by
    rw [hη]; field_simp; rw [hT]; ring
  set M := μ.expect Ψ with hM
  have hMs : M = ∑ y, wt p y * Ψ y := expect_pi_bernoulli p hp0 hp1 Ψ
  set D := η ^ 2 / (2 * (1 - η * b / 3)) with hD
  have hD0 : 0 ≤ D := by rw [hD, hr]; positivity
  have hmgf := mgf hη0 hηb p hp0 hp1 Ψ c hc hΨ
  rw [← hMs] at hmgf
  calc μ.prob {x | M + a ≤ Ψ x}
      = ∑ x, {x | M + a ≤ Ψ x}.indicator μ.w x := FinDist.prob_eq_sum _ _
    _ ≤ ∑ x, wt p x * Real.exp (η * (Ψ x - M - a)) := by
        refine sum_le_sum fun x _ => ?_
        by_cases hx : x ∈ {x | M + a ≤ Ψ x}
        · rw [Set.indicator_of_mem hx]
          change wt p x ≤ _
          have h1 : 1 ≤ Real.exp (η * (Ψ x - M - a)) := by
            rw [Real.one_le_exp_iff]
            have : 0 ≤ Ψ x - M - a := by simp only [Set.mem_ofPred_eq] at hx; linarith
            positivity
          nlinarith [wt_nonneg hp0 hp1 x]
        · rw [Set.indicator_of_notMem hx]
          exact mul_nonneg (wt_nonneg hp0 hp1 x) (Real.exp_pos _).le
    _ = Real.exp (-(η * a)) * ∑ x, wt p x * Real.exp (η * (Ψ x - M)) := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(η * a)) * Real.exp (D * ∑ k, p k * (1 - p k) * c k ^ 2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (-(η * a)) * Real.exp (D * β) := by
        gcongr
    _ = Real.exp (-(a ^ 2 / (2 * T))) := by
        rw [← Real.exp_add]
        congr 1
        rw [hD, hr, hη]
        field_simp
        ring

/-- [s1:lemBBD] in the `Function.update` form of the bounded-differences hypothesis: both tails.
Step 6: "The function `−Ψ` satisfies the hypotheses with the same `b`, `c_1, …, c_m` and `β`, and
`E(−Ψ(I)) = −EΨ(I)`. So the first bound for `−Ψ` is the second bound for `Ψ`." -/
theorem tails {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (Ψ : (ι → Bool) → ℝ) (b : ℝ) (c : ι → ℝ) (β a : ℝ)
    (hc : ∀ k, c k ≤ b) (hΨ : ∀ k x v, |Ψ (Function.update x k v) - Ψ x| ≤ c k)
    (hβ : 0 < β) (hS : ∑ k, p k * (1 - p k) * c k ^ 2 ≤ β) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).prob
        {x | (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).expect Ψ + a ≤ Ψ x} ≤
      Real.exp (-(a ^ 2 / (2 * (β + b * a / 3)))) ∧
    (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).prob
        {x | Ψ x ≤ (FinDist.pi fun k => FinDist.bernoulli (p k) (hp0 k) (hp1 k)).expect Ψ - a} ≤
      Real.exp (-(a ^ 2 / (2 * (β + b * a / 3)))) := by
  refine ⟨upper_tail p hp0 hp1 Ψ b c β a hc hΨ hβ hS ha hb, ?_⟩
  have h := upper_tail p hp0 hp1 (fun x => -Ψ x) b c β a hc
    (fun k x v => by rw [neg_sub_neg, abs_sub_comm]; exact hΨ k x v) hβ hS ha hb
  rw [FinDist.expect_neg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

end BBD

end EG

namespace EG

universe u v

/-- [s1:lemBBD] Lemma BBD (Bernstein inequality for bounded differences), canonical form: the
coordinates `I_k` are the coordinates of `ι → Bool` under the product of the laws
`bernoulli (p k)`. -/
theorem bbd : EG.Spec.BBDStatement.{v} := by
  intro ι _ p hp0 hp1 Ψ b c β a hb hc hΨ hβ hS ha μ
  classical
  refine BBD.tails p hp0 hp1 Ψ b c β a (fun k => (hc k).2) (fun k x v => ?_) hβ hS ha hb
  refine hΨ k _ _ fun j hj => ?_
  rw [Function.update_of_ne hj]

/-- [s1:lemBBD] Lemma BBD (Bernstein inequality for bounded differences), random-variable form:
`I : Ω → (ι → Bool)` with mutually independent coordinates and `P(I_k = true) = p_k`. -/
theorem bbdRV : EG.Spec.BBDRVStatement.{u, v} := by
  intro Ω μ ι _ p I Ψ b c β a hp hind hmarg hb hc hΨ hβ hS ha
  have hmap : μ.map I = FinDist.pi fun k =>
      FinDist.bernoulli (p k) (hp k).1 (hp k).2 := by
    have h := (FinDist.iIndepFun_iff_map_eq_pi μ).1 hind
    refine h.trans ?_
    congr 1
    funext k
    exact FinDist.map_eq_bernoulli (hp k).1 (hp k).2 μ _ (hmarg k)
  have key := bbd ι p (fun k => (hp k).1) (fun k => (hp k).2) Ψ b c β a hb hc hΨ hβ hS ha
  simp only at key
  rw [← hmap, FinDist.prob_map, FinDist.prob_map, FinDist.expect_map] at key
  exact key

end EG
