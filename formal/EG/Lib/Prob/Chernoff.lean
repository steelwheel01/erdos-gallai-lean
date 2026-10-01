module

public import EG.Lib.Prob.Indep
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Chernoff bounds for sums of independent indicators

Manuscript: [s1:citChernoff] (B–M Theorem 4, binomial) and [s1:citChernoffGen] (JLR Theorems 2.1
and 2.8, Poisson-binomial, with the tail (b)). Everything is proved from scratch on top of
`EG.FinDist` by the exponential moment method; no measure theory is used.

## Main results

The core objects are events `A i` (`i ∈ s`, a `Finset`) that are *mutually independent*
(`FinDist.IndepEvents μ s A`: `P(⋂_{i ∈ T} A i) = ∏_{i ∈ T} P(A i)` for all `T ⊆ s`), and the
count `X ω = ∑_{i ∈ s} 1_{A i}(ω)`. For these (`IndepEvents.*`):

* `expect_exp_mul_sum`: `E e^{tX} = ∏_i (1 + p_i (e^t - 1))`, and `expect_exp_mul_sum_le`:
  `E e^{tX} ≤ exp((e^t - 1) ∑_i p_i)`;
* upper tail `prob_ge_le_exp_div` (`δ ≥ 0`: `P(X ≥ (1+δ)m) ≤ exp(-δ²m/(2+δ))`) and
  `prob_ge_le` (`0 ≤ δ ≤ 1`: `≤ exp(-δ²m/3)`), for every `m ≥ E X`;
* lower tail `prob_le_le` (`δ ≥ 0`: `P(X ≤ (1-δ)m) ≤ exp(-δ²m/2)`), for every `0 ≤ m ≤ E X`;
* the tail (b) `prob_ge_nat_le` (`P(X ≥ j) ≤ m^j/j!`) and `prob_ge_nat_le_exp`
  (`≤ (e m / j)^j`), for every `m ≥ E X` and every `j : ℕ`;
* the same bounds for any real random variable `X` that equals the count on the outcomes of
  positive weight: `chernoff_upper`, `chernoff_lower`, `chernoff_tail`, `chernoff_tail_exp`,
  and the most used instance `chernoff_lower_half` (`δ = 1/2`: `P(X < m/2) ≤ exp(-m/8)`).

Sources of `IndepEvents`:

* `iIndepFun.indepEvents`: events `A i` whose indicator propositions are `iIndepFun`
  (the shared vocabulary); `iIndepFun.indepEvents_of_subtype` when only the subfamily indexed by
  the subtype `↥s` is independent;
* `indepEvents_pi_coord`: events `{f | f i ∈ C i}` about distinct coordinates of `pi μ`;
* `indepEvents_pi_of_dependsOn`: events depending on pairwise disjoint blocks of coordinates of
  `pi μ` ("indicators that are functions of distinct coordinates");
* `IsRSubset.indepEvents`: the membership events `a ∈ V` of a ρ-random subset `V`.

Manuscript statements:

* [s1:citChernoffGen] (a), (b) for real indicator variables `I i` (`I i ω ∈ {0, 1}`) with
  `μ.iIndepFun I`: `chernoffGen_upper`, `chernoffGen_lower`, `chernoffGen_tail`,
  `chernoffGen_tail_exp` (both inequalities of (b)), and `chernoffGen_lower_half` (`δ = 1/2`);
  the variants `chernoffGen_upper_on`, `chernoffGen_lower_on`, `chernoffGen_lower_half_on`,
  `chernoffGen_tail_on`, `chernoffGen_tail_exp_on` ask `{0, 1}`-values and independence only of
  the summands (`∀ i ∈ s, …` and `μ.iIndepFun fun i : ↥s => I i`);
* [s1:citChernoff] for `X ∼ Bin(n, p)` (`μ.map X = binomial n p _ _`): `chernoff_binomial`
  (both strict tails, together with `E X = n p`), `chernoff_binomial_upper`,
  `chernoff_binomial_lower`, `expect_of_map_eq_binomial`.

Corollaries in the forms used downstream:

* products of Bernoulli coins `pi fun i => bernoulli (p i) _ _` and the number of successes in a
  set `s` of coordinates: `chernoff_pi_bernoulli_upper/lower/tail` (the tail with both bounds
  `m^j/j!` and `(e m/j)^j`);
* indicators that are functions of pairwise disjoint blocks of coordinates of an arbitrary finite
  product: `chernoff_pi_dependsOn_upper/lower/tail`;
* ρ-random subsets (`IsRSubset`): `IsRSubset.chernoff_card_inter_upper/lower/lower_half/tail`
  for `|V ∩ E|` (mean `ρ |S ∩ E|`; the tail with both bounds of (b)),
  `IsRSubset.chernoff_card_upper/lower/lower_half` for `|V|`
  (mean `ρ |S|`);
* colour classes of a uniform `k`-colouring: `chernoff_randColouring_upper/lower/lower_half` for
  `#{e ∈ E | c e = j}` (mean `|E| / k`);
* the binomial distribution itself: `binomial`, `prob_binomial`, `expect_binomial`,
  `binomial_prob_ge_le`, `binomial_prob_le_le` (non-strict tails).

The elementary inequalities used (`Chernoff.exp_neg_le_quadratic`,
`Chernoff.two_mul_div_two_add_le_log_one_add`, `Chernoff.sq_div_two_add_le`,
`Chernoff.sum_powersetCard_prod_le`, `Chernoff.pow_div_factorial_le`) are in the namespace
`EG.Chernoff`.

In the manuscript the mean is called `μ`; here `μ` is the distribution and the mean parameter
is `m`.
-/

public section

namespace EG

open Finset

/-! ### Elementary inequalities -/

namespace Chernoff

/-- `e^{-x} ≤ 1 - x + x²/2` for `x ≥ 0`. (From `e^x ≥ 1 + x + x²/2` and
`(1 - x + x²/2)(1 + x + x²/2) = 1 + x⁴/4 ≥ 1`.) -/
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  calc (Real.exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ := inv_anti₀ hpos h
    _ ≤ 1 - x + x ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [sq_nonneg (x ^ 2)]

/-- `log(1 + x) ≥ 2x/(2 + x)` for `x ≥ 0`: the first term of the series
`log((1+y)/(1-y)) = 2 ∑_k y^{2k+1}/(2k+1)` at `y = x/(2+x)`. -/
theorem two_mul_div_two_add_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    2 * x / (2 + x) ≤ Real.log (1 + x) := by
  set y := x / (2 + x) with hy
  have h2 : 0 < 2 + x := by linarith
  have hy0 : 0 ≤ y := div_nonneg hx h2.le
  have hy1 : y < 1 := by rw [hy, div_lt_one h2]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  have h0 := le_hasSum hs 0 fun j _ => by positivity
  have e1 : 1 + y = (2 + 2 * x) / (2 + x) := by rw [hy]; field_simp; ring
  have e2 : 1 - y = 2 / (2 + x) := by rw [hy]; field_simp; ring
  have e3 : Real.log (1 + y) - Real.log (1 - y) = Real.log (1 + x) := by
    rw [← Real.log_div (by rw [e1]; positivity) (by rw [e2]; positivity), e1, e2]
    congr 1
    field_simp
  rw [e3] at h0
  refine le_trans (le_of_eq ?_) h0
  rw [hy]
  push_cast
  ring

/-- The exponent of the upper tail: `(1 + δ) log(1 + δ) - δ ≥ δ²/(2 + δ)` for `δ ≥ 0`. -/
theorem sq_div_two_add_le {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ^ 2 / (2 + δ) ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  have h := mul_le_mul_of_nonneg_left (two_mul_div_two_add_le_log_one_add hδ)
    (by linarith : (0 : ℝ) ≤ 1 + δ)
  have e : (1 + δ) * (2 * δ / (2 + δ)) = δ + δ ^ 2 / (2 + δ) := by
    field_simp
    ring
  linarith

/-- `m^{n+1} + (n+1) p m^n ≤ (m + p)^{n+1}` for `m, p ≥ 0` (the first two terms of the binomial
expansion). -/
theorem pow_add_mul_le_pow {m p : ℝ} (hm : 0 ≤ m) (hp : 0 ≤ p) (n : ℕ) :
    m ^ (n + 1) + (n + 1) * p * m ^ n ≤ (m + p) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmn : 0 ≤ ((n : ℝ) + 1) * p ^ 2 * m ^ n := by positivity
    have e : (m + p) * (m ^ (n + 1) + ((n : ℝ) + 1) * p * m ^ n) =
        m ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * p * m ^ (n + 1) +
          ((n : ℝ) + 1) * p ^ 2 * m ^ n := by
      push_cast; ring
    calc m ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * p * m ^ (n + 1)
        ≤ (m + p) * (m ^ (n + 1) + ((n : ℝ) + 1) * p * m ^ n) := by rw [e]; linarith
      _ ≤ (m + p) * (m + p) ^ (n + 1) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (m + p) ^ (n + 1 + 1) := by ring

/-- The elementary symmetric polynomial bound `e_j(p) ≤ (∑_i p_i)^j / j!` for `p ≥ 0`: every
product `∏_{i ∈ T} p_i` with `|T| = j` occurs `j!` times in the expansion of `(∑_i p_i)^j`
(proved by induction on `s`). -/
theorem sum_powersetCard_prod_le {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (j : ℕ) :
    ∑ T ∈ s.powersetCard j, ∏ i ∈ T, p i ≤ (∑ i ∈ s, p i) ^ j / j.factorial := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    cases j with
    | zero => simp
    | succ n => rw [powersetCard_eq_empty.2 (by simp)]; simp
  | insert a s ha ih =>
    have hp' : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp i (mem_insert_of_mem hi)
    have hpa : 0 ≤ p a := hp a (mem_insert_self a s)
    have hm : 0 ≤ ∑ i ∈ s, p i := sum_nonneg hp'
    cases j with
    | zero => simp
    | succ n =>
      have hins := powersetCard_succ_insert ha n
      simp only [Nat.succ_eq_add_one] at hins
      have hdisj : Disjoint (s.powersetCard (n + 1)) ((s.powersetCard n).image (insert a)) := by
        rw [disjoint_left]
        intro T hT hT'
        obtain ⟨U, _, rfl⟩ := mem_image.1 hT'
        exact ha ((mem_powersetCard.1 hT).1 (mem_insert_self a U))
      have hinj : Set.InjOn (insert a) (s.powersetCard n : Set (Finset ι)) := by
        intro T₁ h₁ T₂ h₂ heq
        have h₁' : a ∉ T₁ := fun h => ha ((mem_powersetCard.1 h₁).1 h)
        have h₂' : a ∉ T₂ := fun h => ha ((mem_powersetCard.1 h₂).1 h)
        rw [← erase_insert h₁', heq, erase_insert h₂']
      rw [hins, sum_union hdisj, sum_image hinj, sum_insert ha]
      have e : ∑ T ∈ s.powersetCard n, ∏ i ∈ insert a T, p i =
          p a * ∑ T ∈ s.powersetCard n, ∏ i ∈ T, p i := by
        rw [mul_sum]
        exact sum_congr rfl fun T hT =>
          prod_insert fun haT => ha ((mem_powersetCard.1 hT).1 haT)
      rw [e]
      have h1 := ih hp' (n + 1)
      have h2 := ih hp' n
      have h3 := pow_add_mul_le_pow hm hpa n
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      calc _ ≤ (∑ i ∈ s, p i) ^ (n + 1) / (n + 1).factorial +
            p a * ((∑ i ∈ s, p i) ^ n / n.factorial) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hpa)
        _ = ((∑ i ∈ s, p i) ^ (n + 1) + (n + 1) * p a * (∑ i ∈ s, p i) ^ n) /
            (n + 1).factorial := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp
        _ ≤ (p a + ∑ i ∈ s, p i) ^ (n + 1) / (n + 1).factorial := by
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          rw [add_comm (p a)]
          exact h3

/-- `m^j / j! ≤ (e m / j)^j` for `m ≥ 0` (from `j! ≥ (j/e)^j`; both sides are `1` for `j = 0`). -/
theorem pow_div_factorial_le {m : ℝ} (hm : 0 ≤ m) (j : ℕ) :
    m ^ j / j.factorial ≤ (Real.exp 1 * m / j) ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have key := Real.pow_div_factorial_le_exp _ hj'.le j
  rw [div_le_iff₀ hf, show Real.exp ((j : ℝ)) = Real.exp 1 ^ j by
    rw [← Real.exp_nat_mul, mul_one]] at key
  rw [div_pow, mul_pow, div_le_div_iff₀ hf (pow_pos hj' j)]
  have := mul_le_mul_of_nonneg_left key (pow_nonneg hm j)
  nlinarith [this]

end Chernoff

namespace FinDist

variable {Ω ι α : Type*}

/-! ### Mutually independent events -/

/-- The events `A i`, `i ∈ s`, are mutually independent under `μ`: for every `T ⊆ s`,
`P(A i for all i ∈ T) = ∏_{i ∈ T} P(A i)`. This is what "the indicators `1_{A i}` are
independent" means for [s1:citChernoffGen]; it follows from the shared vocabulary
(`iIndepFun.indepEvents`) and from the product structure of `pi` (`indepEvents_pi_coord`,
`indepEvents_pi_of_dependsOn`). -/
@[expose] def IndepEvents (μ : FinDist Ω) (s : Finset ι) (A : ι → Set Ω) : Prop :=
  ∀ T ⊆ s, μ.prob {ω | ∀ i ∈ T, ω ∈ A i} = ∏ i ∈ T, μ.prob (A i)

theorem IndepEvents.mono {μ : FinDist Ω} {s t : Finset ι} {A : ι → Set Ω}
    (h : μ.IndepEvents s A) (hts : t ⊆ s) : μ.IndepEvents t A :=
  fun T hT => h T (hT.trans hts)

/-- Events whose indicator propositions are mutually independent random variables are mutually
independent events. -/
theorem iIndepFun.indepEvents {μ : FinDist Ω} {A : ι → Set Ω}
    (h : μ.iIndepFun fun i ω => ω ∈ A i) (s : Finset ι) : μ.IndepEvents s A :=
  fun T _ => h T fun _ => {P | P}

/-- Events `A i`, `i ∈ s`, whose indicator propositions form a mutually independent family
indexed by the subtype `↥s` are mutually independent events. Only the subfamily indexed by `s`
has to be independent (for example the `χ_u`, `u ∈ Aw_Y(w)`, of [s5:lemE1] proof of (a)). -/
theorem iIndepFun.indepEvents_of_subtype {μ : FinDist Ω} {s : Finset ι} {A : ι → Set Ω}
    (h : μ.iIndepFun fun (i : s) ω => ω ∈ A i) : μ.IndepEvents s A := by
  classical
  intro T hT
  have key : μ.prob {ω | ∀ u ∈ T.subtype (· ∈ s), ω ∈ A u} =
      ∏ u ∈ T.subtype (· ∈ s), μ.prob (A u) := h _ fun _ => {P | P}
  rw [prod_subtype_eq_prod_filter (fun i => μ.prob (A i)), filter_true_of_mem hT] at key
  rw [← key]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, mem_subtype, Subtype.forall]
  exact ⟨fun H i _ hi => H i hi, fun H i hi => H i (hT hi) hi⟩

/-- Events about distinct coordinates of a finite product are mutually independent. -/
theorem indepEvents_pi_coord [Fintype ι] {κ : ι → Type*} (μ : ∀ i, FinDist (κ i))
    (C : ∀ i, Set (κ i)) (s : Finset ι) :
    (pi μ).IndepEvents s (fun i => {f | f i ∈ C i}) :=
  fun T _ => (prob_pi_forall_mem μ T C).trans
    (prod_congr rfl fun i _ => (prob_pi_eval μ i (C i)).symm)

/-- Events depending on pairwise disjoint blocks `B u` of coordinates of a finite product are
mutually independent ("indicators that are functions of distinct coordinates"). -/
theorem indepEvents_pi_of_dependsOn {U ι : Type*} [Fintype ι] {κ : ι → Type*}
    (μ : ∀ i, FinDist (κ i)) (s : Finset U) (B : U → Set ι)
    (hB : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (B u) (B v)) (A : U → Set (∀ i, κ i))
    (hA : ∀ u ∈ s, ∀ f g, (∀ i ∈ B u, f i = g i) → f ∈ A u → g ∈ A u) :
    (pi μ).IndepEvents s A :=
  fun T hT => prob_pi_forall_of_dependsOn μ T B (fun u hu v hv => hB u (hT hu) v (hT hv)) A
    (fun u hu => hA u (hT hu))

/-- The membership events `a ∈ V` (`a ∈ S`) of a ρ-random subset `V` of `S` are mutually
independent. -/
theorem IsRSubset.indepEvents [DecidableEq α] {μ : FinDist Ω} {V : Ω → Finset α} {S : Finset α}
    {ρ : ℝ} (h : μ.IsRSubset V S ρ) : μ.IndepEvents S (fun a => {ω | a ∈ V ω}) := by
  intro T hT
  rw [prod_congr rfl fun a ha => h.prob_mem (hT ha), prod_const]
  exact h.prob_superset hT

/-! ### Sums of indicators -/

/-- A product of indicators is the indicator of the intersection. -/
theorem prod_indicator_one_eq (T : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    ∏ i ∈ T, (A i).indicator (1 : Ω → ℝ) ω = {ω | ∀ i ∈ T, ω ∈ A i}.indicator 1 ω := by
  by_cases h : ∀ i ∈ T, ω ∈ A i
  · rw [Set.indicator_of_mem (show ω ∈ {ω | ∀ i ∈ T, ω ∈ A i} from h)]
    exact prod_eq_one fun i hi => by simp [h i hi]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∀ i ∈ T, ω ∈ A i} from h)]
    simp only [not_forall] at h
    obtain ⟨i, hi, hA⟩ := h
    exact prod_eq_zero hi (by simp [hA])

/-- A sum of indicators is a count: if `ω ∈ A i ↔ P i` for `i ∈ s`, then
`∑_{i ∈ s} 1_{A i}(ω) = #{i ∈ s | P i}`. -/
theorem sum_indicator_one_eq_card (s : Finset ι) (A : ι → Set Ω) (ω : Ω) (P : ι → Prop)
    [DecidablePred P] (hP : ∀ i ∈ s, ω ∈ A i ↔ P i) :
    ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω = #{i ∈ s | P i} := by
  rw [natCast_card_filter]
  refine sum_congr rfl fun i hi => ?_
  by_cases h : P i
  · simp [h, (hP i hi).2 h]
  · simp [h, mt (hP i hi).1 h]

theorem sum_indicator_one_nonneg (s : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    0 ≤ ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω :=
  sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω

/-! ### The exponential moment -/

/-- Markov's inequality applied to `e^{tX}`: `P(t a ≤ t X) ≤ e^{-t a} E e^{tX}` for every real
`t` (for `t ≥ 0` this bounds `P(X ≥ a)`, for `t ≤ 0` it bounds `P(X ≤ a)`). -/
theorem prob_mul_le_mul_le (μ : FinDist Ω) (X : Ω → ℝ) (t a : ℝ) :
    μ.prob {ω | t * a ≤ t * X ω} ≤
      Real.exp (-(t * a)) * μ.expect (fun ω => Real.exp (t * X ω)) := by
  have hM := μ.prob_le_expect_div (X := fun ω => Real.exp (t * X ω))
    (fun ω => (Real.exp_pos _).le) (Real.exp_pos (t * a))
  have e : {ω | Real.exp (t * a) ≤ Real.exp (t * X ω)} = {ω | t * a ≤ t * X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Real.exp_le_exp]
  rw [e] at hM
  rw [Real.exp_neg, inv_mul_eq_div]
  exact hM

variable {μ : FinDist Ω} {s : Finset ι} {A : ι → Set Ω}

/-- The moment generating function of a sum of independent indicators:
`E e^{tX} = ∏_{i ∈ s} ((e^t - 1) p_i + 1)` with `p_i = P(A i)`. -/
theorem IndepEvents.expect_exp_mul_sum (h : μ.IndepEvents s A) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * ∑ i ∈ s, (A i).indicator 1 ω)) =
      ∏ i ∈ s, ((Real.exp t - 1) * μ.prob (A i) + 1) := by
  classical
  have h1 : (fun ω => Real.exp (t * ∑ i ∈ s, (A i).indicator 1 ω)) = fun ω =>
      ∑ T ∈ s.powerset, (Real.exp t - 1) ^ T.card * {ω | ∀ i ∈ T, ω ∈ A i}.indicator 1 ω := by
    funext ω
    have e : ∀ i, Real.exp (t * (A i).indicator 1 ω) =
        (Real.exp t - 1) * (A i).indicator 1 ω + 1 := by
      intro i
      by_cases hi : ω ∈ A i <;> simp [hi]
    rw [mul_sum, Real.exp_sum]
    simp only [e]
    rw [prod_add]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_const_one, mul_one, prod_mul_distrib, prod_const, prod_indicator_one_eq]
  rw [h1, expect_sum, prod_add]
  refine sum_congr rfl fun T hT => ?_
  rw [expect_const_mul, ← prob_eq_expect, h T (mem_powerset.1 hT), prod_const_one, mul_one,
    prod_mul_distrib, prod_const]

/-- The bound on the moment generating function: `E e^{tX} ≤ exp((e^t - 1) ∑_i p_i)`. -/
theorem IndepEvents.expect_exp_mul_sum_le (h : μ.IndepEvents s A) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * ∑ i ∈ s, (A i).indicator 1 ω)) ≤
      Real.exp ((Real.exp t - 1) * ∑ i ∈ s, μ.prob (A i)) := by
  rw [h.expect_exp_mul_sum, mul_sum, Real.exp_sum]
  refine prod_le_prod (fun i _ => ?_) (fun i _ => Real.add_one_le_exp _)
  have h0 := μ.prob_nonneg (A i)
  have h1 := μ.prob_le_one (A i)
  have := mul_nonneg h0 (Real.exp_pos t).le
  nlinarith

/-! ### The tail bounds for independent events -/

/-- Upper tail, general `δ ≥ 0`: if `∑_i P(A i) ≤ m` then
`P(X ≥ (1 + δ) m) ≤ exp(-δ² m / (2 + δ))`. -/
theorem IndepEvents.prob_ge_le_exp_div (h : μ.IndepEvents s A) {m δ : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (hδ : 0 ≤ δ) :
    μ.prob {ω | (1 + δ) * m ≤ ∑ i ∈ s, (A i).indicator 1 ω} ≤
      Real.exp (-(δ ^ 2 * m / (2 + δ))) := by
  have hm0 : 0 ≤ m := (sum_nonneg fun i _ => μ.prob_nonneg _).trans hm
  set t := Real.log (1 + δ) with ht_def
  have ht : 0 ≤ t := Real.log_nonneg (by linarith)
  have het : Real.exp t = 1 + δ := Real.exp_log (by linarith)
  calc μ.prob {ω | (1 + δ) * m ≤ ∑ i ∈ s, (A i).indicator 1 ω}
      ≤ μ.prob {ω | t * ((1 + δ) * m) ≤ t * ∑ i ∈ s, (A i).indicator 1 ω} :=
        μ.prob_mono fun ω hω => mul_le_mul_of_nonneg_left hω ht
    _ ≤ Real.exp (-(t * ((1 + δ) * m))) *
        μ.expect (fun ω => Real.exp (t * ∑ i ∈ s, (A i).indicator 1 ω)) :=
        prob_mul_le_mul_le μ _ t _
    _ ≤ Real.exp (-(t * ((1 + δ) * m))) *
        Real.exp ((Real.exp t - 1) * ∑ i ∈ s, μ.prob (A i)) :=
        mul_le_mul_of_nonneg_left (h.expect_exp_mul_sum_le t) (Real.exp_pos _).le
    _ ≤ Real.exp (-(t * ((1 + δ) * m))) * Real.exp (δ * m) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        rw [het, add_sub_cancel_left]
        exact mul_le_mul_of_nonneg_left hm hδ
    _ = Real.exp (-(m * ((1 + δ) * Real.log (1 + δ) - δ))) := by
        rw [← Real.exp_add, ht_def]
        ring_nf
    _ ≤ Real.exp (-(δ ^ 2 * m / (2 + δ))) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (Chernoff.sq_div_two_add_le hδ) hm0
        have e : δ ^ 2 * m / (2 + δ) = m * (δ ^ 2 / (2 + δ)) := by ring
        linarith

/-- [s1:citChernoffGen](a), upper tail, for mutually independent events `A i`: if
`∑_i P(A i) ≤ m` (i.e. `E X ≤ m`) and `0 ≤ δ ≤ 1`, then `P(X ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem IndepEvents.prob_ge_le (h : μ.IndepEvents s A) {m δ : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * m ≤ ∑ i ∈ s, (A i).indicator 1 ω} ≤ Real.exp (-(δ ^ 2 * m / 3)) := by
  have hm0 : 0 ≤ m := (sum_nonneg fun i _ => μ.prob_nonneg _).trans hm
  refine (h.prob_ge_le_exp_div hm hδ0).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- [s1:citChernoffGen](a), lower tail, for mutually independent events `A i`: if
`0 ≤ m ≤ ∑_i P(A i)` (i.e. `0 ≤ m ≤ E X`) and `δ ≥ 0`, then
`P(X ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`. (The manuscript assumes `δ ≤ 1`; it is not needed.) -/
theorem IndepEvents.prob_le_le (h : μ.IndepEvents s A) {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ∑ i ∈ s, μ.prob (A i)) (hδ : 0 ≤ δ) :
    μ.prob {ω | ∑ i ∈ s, (A i).indicator 1 ω ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) := by
  have hneg : Real.exp (-δ) - 1 ≤ 0 := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hδ)
    linarith
  calc μ.prob {ω | ∑ i ∈ s, (A i).indicator 1 ω ≤ (1 - δ) * m}
      ≤ μ.prob {ω | (-δ) * ((1 - δ) * m) ≤ (-δ) * ∑ i ∈ s, (A i).indicator 1 ω} :=
        μ.prob_mono fun ω hω => mul_le_mul_of_nonpos_left hω (neg_nonpos.2 hδ)
    _ ≤ Real.exp (-((-δ) * ((1 - δ) * m))) *
        μ.expect (fun ω => Real.exp ((-δ) * ∑ i ∈ s, (A i).indicator 1 ω)) :=
        prob_mul_le_mul_le μ _ (-δ) _
    _ ≤ Real.exp (-((-δ) * ((1 - δ) * m))) *
        Real.exp ((Real.exp (-δ) - 1) * ∑ i ∈ s, μ.prob (A i)) :=
        mul_le_mul_of_nonneg_left (h.expect_exp_mul_sum_le (-δ)) (Real.exp_pos _).le
    _ ≤ Real.exp (-((-δ) * ((1 - δ) * m))) * Real.exp ((Real.exp (-δ) - 1) * m) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hm hneg))
          (Real.exp_pos _).le
    _ ≤ Real.exp (-(δ ^ 2 * m / 2)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have hq := Chernoff.exp_neg_le_quadratic hδ
        have := mul_le_mul_of_nonneg_left hq hm0
        nlinarith

/-- [s1:citChernoffGen](b), first inequality, for mutually independent events `A i`: if
`∑_i P(A i) ≤ m` (i.e. `E X ≤ m`), then `P(X ≥ j) ≤ m^j / j!` for every `j : ℕ` (the manuscript
states it for `j ≥ 1`; for `j = 0` it is trivial). Union bound over the `j`-subsets of `s`,
and `Chernoff.sum_powersetCard_prod_le`. -/
theorem IndepEvents.prob_ge_nat_le (h : μ.IndepEvents s A) {m : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, (A i).indicator 1 ω} ≤ m ^ j / j.factorial := by
  classical
  have hsub : {ω | (j : ℝ) ≤ ∑ i ∈ s, (A i).indicator 1 ω} ⊆
      ⋃ T ∈ s.powersetCard j, {ω | ∀ i ∈ T, ω ∈ A i} := by
    intro ω hω
    rw [Set.mem_ofPred_eq, sum_indicator_one_eq_card s A ω (fun i => ω ∈ A i)
      (fun _ _ => Iff.rfl), Nat.cast_le] at hω
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hω
    simp only [Set.mem_iUnion]
    exact ⟨T, mem_powersetCard.2 ⟨hT.trans (filter_subset _ _), hTc⟩,
      fun i hi => (mem_filter.1 (hT hi)).2⟩
  have hs0 : 0 ≤ ∑ i ∈ s, μ.prob (A i) := sum_nonneg fun i _ => μ.prob_nonneg _
  calc μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, (A i).indicator 1 ω}
      ≤ μ.prob (⋃ T ∈ s.powersetCard j, {ω | ∀ i ∈ T, ω ∈ A i}) := μ.prob_mono hsub
    _ ≤ ∑ T ∈ s.powersetCard j, μ.prob {ω | ∀ i ∈ T, ω ∈ A i} := μ.prob_biUnion_le _ _
    _ = ∑ T ∈ s.powersetCard j, ∏ i ∈ T, μ.prob (A i) :=
        sum_congr rfl fun T hT => h T (mem_powersetCard.1 hT).1
    _ ≤ (∑ i ∈ s, μ.prob (A i)) ^ j / j.factorial :=
        Chernoff.sum_powersetCard_prod_le s _ (fun i _ => μ.prob_nonneg _) j
    _ ≤ m ^ j / j.factorial := by gcongr

/-- [s1:citChernoffGen](b), second inequality, for mutually independent events `A i`: if
`E X ≤ m`, then
`P(X ≥ j) ≤ (e m / j)^j` for every `j : ℕ`. -/
theorem IndepEvents.prob_ge_nat_le_exp (h : μ.IndepEvents s A) {m : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, (A i).indicator 1 ω} ≤ (Real.exp 1 * m / j) ^ j :=
  (h.prob_ge_nat_le hm j).trans
    (Chernoff.pow_div_factorial_le ((sum_nonneg fun _ _ => μ.prob_nonneg _).trans hm) j)

/-! ### The tail bounds for a random variable equal to the count

The forms used downstream: `X` is any real random variable that equals the number of the
independent events `A i` (`i ∈ s`) that occur, at least on the outcomes of positive weight. -/

/-- Upper tail for a count `X` of independent events: if `E X = ∑_i P(A i) ≤ m` and
`0 ≤ δ ≤ 1`, then `P(X ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem IndepEvents.chernoff_upper (h : μ.IndepEvents s A) {X : Ω → ℝ}
    (hX : ∀ ω, 0 < μ.w ω → X ω = ∑ i ∈ s, (A i).indicator 1 ω) {m δ : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * m ≤ X ω} ≤ Real.exp (-(δ ^ 2 * m / 3)) := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans (h.prob_ge_le hm hδ0 hδ1)
  simp only [Set.mem_ofPred_eq, hX ω hω]

/-- Lower tail for a count `X` of independent events: if `0 ≤ m ≤ E X = ∑_i P(A i)` and
`δ ≥ 0`, then `P(X ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`. -/
theorem IndepEvents.chernoff_lower (h : μ.IndepEvents s A) {X : Ω → ℝ}
    (hX : ∀ ω, 0 < μ.w ω → X ω = ∑ i ∈ s, (A i).indicator 1 ω) {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ∑ i ∈ s, μ.prob (A i)) (hδ : 0 ≤ δ) :
    μ.prob {ω | X ω ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans (h.prob_le_le hm0 hm hδ)
  simp only [Set.mem_ofPred_eq, hX ω hω]

/-- The instance `δ = 1/2` of the lower tail, the form used most often in the manuscript
([s3:lemL15p], [s3:lemL17s], [s4:lemTPV], [s5:lemE1], [s7:lemCand]): if `0 ≤ m ≤ E X`, then
`P(X < m / 2) ≤ exp(-m / 8)`. -/
theorem IndepEvents.chernoff_lower_half (h : μ.IndepEvents s A) {X : Ω → ℝ}
    (hX : ∀ ω, 0 < μ.w ω → X ω = ∑ i ∈ s, (A i).indicator 1 ω) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ∑ i ∈ s, μ.prob (A i)) :
    μ.prob {ω | X ω < m / 2} ≤ Real.exp (-(m / 8)) := by
  have h' := h.chernoff_lower hX hm0 hm (δ := 1 / 2) (by norm_num)
  refine le_trans (μ.prob_mono fun ω (hω : X ω < m / 2) => ?_) (h'.trans (le_of_eq ?_))
  · show X ω ≤ (1 - 1 / 2) * m
    linarith
  · congr 1
    ring

/-- The tail (b) for a count `X` of independent events: if `E X = ∑_i P(A i) ≤ m`, then
`P(X ≥ j) ≤ m^j / j!` for every `j : ℕ`. -/
theorem IndepEvents.chernoff_tail (h : μ.IndepEvents s A) {X : Ω → ℝ}
    (hX : ∀ ω, 0 < μ.w ω → X ω = ∑ i ∈ s, (A i).indicator 1 ω) {m : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ X ω} ≤ m ^ j / j.factorial := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans (h.prob_ge_nat_le hm j)
  simp only [Set.mem_ofPred_eq, hX ω hω]

/-- The tail (b), second form, for a count `X` of independent events: if `E X ≤ m`, then
`P(X ≥ j) ≤ (e m / j)^j` for every `j : ℕ`. -/
theorem IndepEvents.chernoff_tail_exp (h : μ.IndepEvents s A) {X : Ω → ℝ}
    (hX : ∀ ω, 0 < μ.w ω → X ω = ∑ i ∈ s, (A i).indicator 1 ω) {m : ℝ}
    (hm : ∑ i ∈ s, μ.prob (A i) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ X ω} ≤ (Real.exp 1 * m / j) ^ j := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans (h.prob_ge_nat_le_exp hm j)
  simp only [Set.mem_ofPred_eq, hX ω hω]

/-! ### [s1:citChernoffGen]: sums of independent indicator variables -/

section Gen

variable {I : ι → Ω → ℝ}

/-- A sum of variables that are `{0, 1}`-valued on the summation range `s` is the count of the
events `{I i = 1}`. -/
theorem sum_eq_sum_indicator_of_zero_or_one_on (s : Finset ι)
    (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1) (ω : Ω) :
    ∑ i ∈ s, I i ω = ∑ i ∈ s, {ω | I i ω = 1}.indicator (1 : Ω → ℝ) ω := by
  refine sum_congr rfl fun i hi => ?_
  rcases hI i hi ω with h | h
  · rw [h, Set.indicator_of_notMem (show ω ∉ {ω | I i ω = 1} by
      rw [Set.mem_ofPred_eq, h]; exact zero_ne_one)]
  · rw [h, Set.indicator_of_mem (show ω ∈ {ω | I i ω = 1} from h), Pi.one_apply]

/-- A `{0, 1}`-valued variable is the indicator of the event `{I = 1}`. -/
theorem sum_eq_sum_indicator_of_zero_or_one (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1)
    (s : Finset ι) (ω : Ω) :
    ∑ i ∈ s, I i ω = ∑ i ∈ s, {ω | I i ω = 1}.indicator (1 : Ω → ℝ) ω :=
  sum_eq_sum_indicator_of_zero_or_one_on s (fun i _ => hI i) ω

/-- Mutually independent indicator variables give mutually independent events `{I i = 1}`. -/
theorem iIndepFun.indepEvents_eq_one (hind : μ.iIndepFun I) (s : Finset ι) :
    μ.IndepEvents s (fun i => {ω | I i ω = 1}) :=
  (hind.comp fun _ x => x = 1).indepEvents s

/-- Variables `I i`, `i ∈ s`, that are mutually independent as a family indexed by the subtype
`↥s` give mutually independent events `{I i = 1}`, `i ∈ s`. -/
theorem iIndepFun.indepEvents_eq_one_of_subtype {s : Finset ι}
    (hind : μ.iIndepFun fun i : s => I i) : μ.IndepEvents s (fun i => {ω | I i ω = 1}) :=
  iIndepFun.indepEvents_of_subtype (hind.comp fun _ x => x = 1)

/-- The expectation of a sum of variables that are `{0, 1}`-valued on the summation range. -/
theorem expect_sum_of_zero_or_one_on (s : Finset ι) (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1) :
    μ.expect (fun ω => ∑ i ∈ s, I i ω) = ∑ i ∈ s, μ.prob {ω | I i ω = 1} := by
  simp only [sum_eq_sum_indicator_of_zero_or_one_on s hI]
  exact μ.expect_sum_indicator s _

/-- The expectation of a sum of indicator variables. -/
theorem expect_sum_of_zero_or_one (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1) (s : Finset ι) :
    μ.expect (fun ω => ∑ i ∈ s, I i ω) = ∑ i ∈ s, μ.prob {ω | I i ω = 1} :=
  expect_sum_of_zero_or_one_on s fun i _ => hI i

/-- [s1:citChernoffGen](a), upper tail. "Let `X = ∑_{i=1}^m I_i` be a sum of independent
indicator variables with `P(I_i = 1) = p_i` (a Poisson-binomial variable), and let
`0 ≤ δ ≤ 1`. (a) If `μ ≥ E X` then `P(X ≥ (1+δ)μ) ≤ e^{-δ²μ/3}`."

Here the indicator variables are real random variables `I i` (`i ∈ s`) with values in `{0, 1}`
that are mutually independent (`μ.iIndepFun I`), and the manuscript's `μ` is `m`. -/
theorem chernoffGen_upper (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1) (hind : μ.iIndepFun I)
    (s : Finset ι) {m δ : ℝ} (hm : μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * m ≤ ∑ i ∈ s, I i ω} ≤ Real.exp (-(δ ^ 2 * m / 3)) := by
  rw [expect_sum_of_zero_or_one hI] at hm
  exact (hind.indepEvents_eq_one s).chernoff_upper
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one hI s ω) hm hδ0 hδ1

/-- [s1:citChernoffGen](a), lower tail. "… if `0 ≤ μ ≤ E X` then
`P(X ≤ (1-δ)μ) ≤ e^{-δ²μ/2}`." (The manuscript assumes `0 ≤ δ ≤ 1`; only `δ ≥ 0` is needed.)
The setting is that of `chernoffGen_upper`. -/
theorem chernoffGen_lower (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1) (hind : μ.iIndepFun I)
    (s : Finset ι) {m δ : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ μ.expect (fun ω => ∑ i ∈ s, I i ω))
    (hδ : 0 ≤ δ) :
    μ.prob {ω | ∑ i ∈ s, I i ω ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) := by
  rw [expect_sum_of_zero_or_one hI] at hm
  exact (hind.indepEvents_eq_one s).chernoff_lower
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one hI s ω) hm0 hm hδ

/-- [s1:citChernoffGen](a), lower tail with `δ = 1/2`: if `0 ≤ m ≤ E X` then
`P(X < m/2) ≤ e^{-m/8}` (e.g. [s5:lemE1] proof of (a), [s7:lemCand] proof of (iii)). The setting
is that of `chernoffGen_upper`. -/
theorem chernoffGen_lower_half (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1) (hind : μ.iIndepFun I)
    (s : Finset ι) {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ μ.expect (fun ω => ∑ i ∈ s, I i ω)) :
    μ.prob {ω | ∑ i ∈ s, I i ω < m / 2} ≤ Real.exp (-(m / 8)) := by
  rw [expect_sum_of_zero_or_one hI] at hm
  exact (hind.indepEvents_eq_one s).chernoff_lower_half
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one hI s ω) hm0 hm

/-- [s1:citChernoffGen](b), first inequality. "If `E X ≤ μ` then for every integer `j ≥ 1`,
`P(X ≥ j) ≤ μ^j/j!`." (Also true for `j = 0`.) The setting is that of `chernoffGen_upper`. -/
theorem chernoffGen_tail (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1) (hind : μ.iIndepFun I)
    (s : Finset ι) {m : ℝ} (hm : μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, I i ω} ≤ m ^ j / j.factorial := by
  rw [expect_sum_of_zero_or_one hI] at hm
  exact (hind.indepEvents_eq_one s).chernoff_tail
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one hI s ω) hm j

/-- [s1:citChernoffGen](b), both inequalities. "If `E X ≤ μ` then for every integer `j ≥ 1`,
`P(X ≥ j) ≤ μ^j/j! ≤ (eμ/j)^j`." (Also true for `j = 0`.) The setting is that of
`chernoffGen_upper`. -/
theorem chernoffGen_tail_exp (hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1) (hind : μ.iIndepFun I)
    (s : Finset ι) {m : ℝ} (hm : μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, I i ω} ≤ m ^ j / j.factorial ∧
      m ^ j / j.factorial ≤ (Real.exp 1 * m / j) ^ j := by
  refine ⟨chernoffGen_tail hI hind s hm j, Chernoff.pow_div_factorial_le ?_ j⟩
  refine le_trans ?_ hm
  exact μ.expect_nonneg fun ω => sum_nonneg fun i _ => by rcases hI i ω with h | h <;> simp [h]

/-! #### The same statements with hypotheses on the summation range only

In the forms above the family `I` is indexed by a type `ι` and all its members are assumed to be
`{0, 1}`-valued and mutually independent. The forms below ask this only of the summands
`I i`, `i ∈ s`: `hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1` and
`hind : μ.iIndepFun fun i : ↥s => I i`. They apply directly to families such as the `χ_u`,
`u ∈ Aw_Y(w)`, of [s5:lemE1] proof of (a), which are indicators and independent only on
`Aw_Y(w)`. With `ι := Fin m`, `s := univ`, both kinds are the manuscript statement. -/

/-- [s1:citChernoffGen](a), upper tail. "Let `X = ∑_{i=1}^m I_i` be a sum of independent
indicator variables with `P(I_i = 1) = p_i` (a Poisson-binomial variable), and let
`0 ≤ δ ≤ 1`. (a) If `μ ≥ E X` then `P(X ≥ (1+δ)μ) ≤ e^{-δ²μ/3}`."

Here the indicator variables are the real random variables `I i`, `i ∈ s`, with values in
`{0, 1}`, mutually independent as a family indexed by `↥s`; the manuscript's `μ` is `m`. -/
theorem chernoffGen_upper_on (s : Finset ι) (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1)
    (hind : μ.iIndepFun fun i : s => I i) {m δ : ℝ}
    (hm : μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * m ≤ ∑ i ∈ s, I i ω} ≤ Real.exp (-(δ ^ 2 * m / 3)) := by
  rw [expect_sum_of_zero_or_one_on s hI] at hm
  exact hind.indepEvents_eq_one_of_subtype.chernoff_upper
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one_on s hI ω) hm hδ0 hδ1

/-- [s1:citChernoffGen](a), lower tail. "… if `0 ≤ μ ≤ E X` then
`P(X ≤ (1-δ)μ) ≤ e^{-δ²μ/2}`." (The manuscript assumes `0 ≤ δ ≤ 1`; only `δ ≥ 0` is needed.)
The setting is that of `chernoffGen_upper_on`. -/
theorem chernoffGen_lower_on (s : Finset ι) (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1)
    (hind : μ.iIndepFun fun i : s => I i) {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ μ.expect (fun ω => ∑ i ∈ s, I i ω)) (hδ : 0 ≤ δ) :
    μ.prob {ω | ∑ i ∈ s, I i ω ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) := by
  rw [expect_sum_of_zero_or_one_on s hI] at hm
  exact hind.indepEvents_eq_one_of_subtype.chernoff_lower
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one_on s hI ω) hm0 hm hδ

/-- [s1:citChernoffGen](a), lower tail with `δ = 1/2`: if `0 ≤ m ≤ E X` then
`P(X < m/2) ≤ e^{-m/8}` (e.g. [s5:lemE1] proof of (a), [s7:lemCand] proof of (iii)). The setting
is that of `chernoffGen_upper_on`. -/
theorem chernoffGen_lower_half_on (s : Finset ι) (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1)
    (hind : μ.iIndepFun fun i : s => I i) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ μ.expect (fun ω => ∑ i ∈ s, I i ω)) :
    μ.prob {ω | ∑ i ∈ s, I i ω < m / 2} ≤ Real.exp (-(m / 8)) := by
  rw [expect_sum_of_zero_or_one_on s hI] at hm
  exact hind.indepEvents_eq_one_of_subtype.chernoff_lower_half
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one_on s hI ω) hm0 hm

/-- [s1:citChernoffGen](b), first inequality. "If `E X ≤ μ` then for every integer `j ≥ 1`,
`P(X ≥ j) ≤ μ^j/j!`." (Also true for `j = 0`.) The setting is that of
`chernoffGen_upper_on`. -/
theorem chernoffGen_tail_on (s : Finset ι) (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1)
    (hind : μ.iIndepFun fun i : s => I i) {m : ℝ}
    (hm : μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, I i ω} ≤ m ^ j / j.factorial := by
  rw [expect_sum_of_zero_or_one_on s hI] at hm
  exact hind.indepEvents_eq_one_of_subtype.chernoff_tail
    (fun ω _ => sum_eq_sum_indicator_of_zero_or_one_on s hI ω) hm j

/-- [s1:citChernoffGen](b), both inequalities. "If `E X ≤ μ` then for every integer `j ≥ 1`,
`P(X ≥ j) ≤ μ^j/j! ≤ (eμ/j)^j`." (Also true for `j = 0`.) The setting is that of
`chernoffGen_upper_on`. -/
theorem chernoffGen_tail_exp_on (s : Finset ι) (hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1)
    (hind : μ.iIndepFun fun i : s => I i) {m : ℝ}
    (hm : μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m) (j : ℕ) :
    μ.prob {ω | (j : ℝ) ≤ ∑ i ∈ s, I i ω} ≤ m ^ j / j.factorial ∧
      m ^ j / j.factorial ≤ (Real.exp 1 * m / j) ^ j := by
  refine ⟨chernoffGen_tail_on s hI hind hm j, Chernoff.pow_div_factorial_le ?_ j⟩
  refine le_trans ?_ hm
  exact μ.expect_nonneg fun ω => sum_nonneg fun i hi => by
    rcases hI i hi ω with h | h <;> simp [h]

end Gen

/-! ### Products of Bernoulli coins -/

section Bernoulli

variable [Fintype ι] (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)

/-- The success events of independent Bernoulli coins are mutually independent. -/
theorem indepEvents_pi_bernoulli (s : Finset ι) :
    (pi fun i => bernoulli (p i) (h0 i) (h1 i)).IndepEvents s (fun i => {f | f i = true}) :=
  indepEvents_pi_coord _ (fun _ => {b | b = true}) s

theorem prob_pi_bernoulli_apply (i : ι) :
    (pi fun i => bernoulli (p i) (h0 i) (h1 i)).prob {f | f i = true} = p i :=
  (prob_pi_eval (fun i => bernoulli (p i) (h0 i) (h1 i)) i {b | b = true}).trans
    (prob_bernoulli_eq_true _ _)

theorem sum_prob_pi_bernoulli (s : Finset ι) :
    ∑ i ∈ s, (pi fun i => bernoulli (p i) (h0 i) (h1 i)).prob {f | f i = true} = ∑ i ∈ s, p i :=
  sum_congr rfl fun i _ => prob_pi_bernoulli_apply p h0 h1 i

omit [Fintype ι] in
theorem card_eq_sum_indicator_pi_bernoulli (s : Finset ι) (f : ι → Bool) :
    (#{i ∈ s | f i = true} : ℝ) = ∑ i ∈ s, {f : ι → Bool | f i = true}.indicator 1 f :=
  (sum_indicator_one_eq_card s _ f (fun i => f i = true) fun _ _ => Iff.rfl).symm

/-- Upper tail for the number of successes among the coins in `s` of a product of independent
Bernoulli(`p i`) coins: if `∑_{i ∈ s} p i ≤ m` and `0 ≤ δ ≤ 1`, then
`P(#successes ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem chernoff_pi_bernoulli_upper (s : Finset ι) {m δ : ℝ} (hm : ∑ i ∈ s, p i ≤ m)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (pi fun i => bernoulli (p i) (h0 i) (h1 i)).prob
      {f | (1 + δ) * m ≤ #{i ∈ s | f i = true}} ≤ Real.exp (-(δ ^ 2 * m / 3)) :=
  (indepEvents_pi_bernoulli p h0 h1 s).chernoff_upper
    (fun f _ => card_eq_sum_indicator_pi_bernoulli s f)
    ((sum_prob_pi_bernoulli p h0 h1 s).le.trans hm) hδ0 hδ1

/-- Lower tail for the number of successes among the coins in `s`: if
`0 ≤ m ≤ ∑_{i ∈ s} p i` and `δ ≥ 0`, then `P(#successes ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`. -/
theorem chernoff_pi_bernoulli_lower (s : Finset ι) {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ∑ i ∈ s, p i) (hδ : 0 ≤ δ) :
    (pi fun i => bernoulli (p i) (h0 i) (h1 i)).prob
      {f | (#{i ∈ s | f i = true} : ℝ) ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) :=
  (indepEvents_pi_bernoulli p h0 h1 s).chernoff_lower
    (fun f _ => card_eq_sum_indicator_pi_bernoulli s f) hm0
    (hm.trans (sum_prob_pi_bernoulli p h0 h1 s).ge) hδ

/-- The tail (b) for the number of successes among the coins in `s`: if `∑_{i ∈ s} p i ≤ m`,
then `P(#successes ≥ j) ≤ m^j / j!` and `≤ (e m / j)^j`. -/
theorem chernoff_pi_bernoulli_tail (s : Finset ι) {m : ℝ} (hm : ∑ i ∈ s, p i ≤ m) (j : ℕ) :
    (pi fun i => bernoulli (p i) (h0 i) (h1 i)).prob
        {f | j ≤ #{i ∈ s | f i = true}} ≤ m ^ j / j.factorial ∧
      (pi fun i => bernoulli (p i) (h0 i) (h1 i)).prob
        {f | j ≤ #{i ∈ s | f i = true}} ≤ (Real.exp 1 * m / j) ^ j := by
  have hX := fun f (_ : 0 < (pi fun i => bernoulli (p i) (h0 i) (h1 i)).w f) =>
    card_eq_sum_indicator_pi_bernoulli s f
  have hm' := (sum_prob_pi_bernoulli p h0 h1 s).le.trans hm
  have h1' := (indepEvents_pi_bernoulli p h0 h1 s).chernoff_tail hX hm' j
  have h2' := (indepEvents_pi_bernoulli p h0 h1 s).chernoff_tail_exp hX hm' j
  simp only [Nat.cast_le] at h1' h2'
  exact ⟨h1', h2'⟩

end Bernoulli

/-! ### [s1:citChernoff]: the binomial distribution -/

section Binomial

variable {n : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- The binomial distribution `Bin(n, p)` on `ℕ`: the law of the number of successes in `n`
independent Bernoulli(`p`) trials. A random variable `X : Ω → ℕ` is `Bin(n, p)`-distributed
under `μ` when `μ.map X = binomial n p h0 h1`. -/
@[expose] noncomputable def binomial (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDist ℕ :=
  (pi fun _ : Fin n => bernoulli p h0 h1).map fun f => #{i | f i = true}

theorem prob_binomial (B : Set ℕ) :
    (binomial n p h0 h1).prob B =
      (pi fun _ : Fin n => bernoulli p h0 h1).prob {f | #{i | f i = true} ∈ B} :=
  prob_map _ _ _

private theorem sum_prob_binomial_coins :
    ∑ i : Fin n, (pi fun _ : Fin n => bernoulli p h0 h1).prob {f | f i ∈ {b | b = true}} =
      n * p := by
  rw [sum_congr rfl fun i _ => (prob_pi_eval (fun _ : Fin n => bernoulli p h0 h1) i
    {b | b = true}).trans (prob_bernoulli_eq_true h0 h1), sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]

private theorem card_eq_sum_indicator_binomial (f : Fin n → Bool) :
    (#{i | f i = true} : ℝ) =
      ∑ i, {f : Fin n → Bool | f i ∈ {b | b = true}}.indicator 1 f :=
  (sum_indicator_one_eq_card univ _ f (fun i => f i = true) fun _ _ => Iff.rfl).symm

/-- The mean of `Bin(n, p)` is `n p`. -/
theorem expect_binomial : (binomial n p h0 h1).expect (fun k => (k : ℝ)) = n * p := by
  rw [binomial, expect_map]
  simp only [card_eq_sum_indicator_binomial]
  rw [expect_sum_indicator, sum_prob_binomial_coins]

/-- Upper tail of `Bin(n, p)`, non-strict form: `P(X ≥ (1 + δ) n p) ≤ exp(-δ² n p / 3)`. -/
theorem binomial_prob_ge_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (binomial n p h0 h1).prob {k | (1 + δ) * (n * p) ≤ k} ≤
      Real.exp (-(δ ^ 2 * (n * p) / 3)) := by
  rw [prob_binomial]
  exact (indepEvents_pi_coord (fun _ : Fin n => bernoulli p h0 h1) (fun _ => {b | b = true})
    univ).chernoff_upper (X := fun f => (#{i | f i = true} : ℝ))
    (fun f _ => card_eq_sum_indicator_binomial f) (sum_prob_binomial_coins h0 h1).le hδ0 hδ1

/-- Lower tail of `Bin(n, p)`, non-strict form: `P(X ≤ (1 - δ) n p) ≤ exp(-δ² n p / 2)`. -/
theorem binomial_prob_le_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (binomial n p h0 h1).prob {k | (k : ℝ) ≤ (1 - δ) * (n * p)} ≤
      Real.exp (-(δ ^ 2 * (n * p) / 2)) := by
  rw [prob_binomial]
  exact (indepEvents_pi_coord (fun _ : Fin n => bernoulli p h0 h1) (fun _ => {b | b = true})
    univ).chernoff_lower (X := fun f => (#{i | f i = true} : ℝ))
    (fun f _ => card_eq_sum_indicator_binomial f) (by positivity)
    (sum_prob_binomial_coins h0 h1).ge hδ

variable {μ : FinDist Ω} {X : Ω → ℕ}

/-- If `X ∼ Bin(n, p)` then `E X = n p`. -/
theorem expect_of_map_eq_binomial (hX : μ.map X = binomial n p h0 h1) :
    μ.expect (fun ω => (X ω : ℝ)) = n * p := by
  rw [← expect_map μ X (fun k => (k : ℝ)), hX, expect_binomial]

/-- [s1:citChernoff], upper tail: for `X ∼ Bin(n, p)` and `0 ≤ δ ≤ 1`,
`P(X > (1 + δ) μ) ≤ e^{-δ²μ/3}` with `μ = E X = n p`. -/
theorem chernoff_binomial_upper (hX : μ.map X = binomial n p h0 h1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * (n * p) < X ω} ≤ Real.exp (-(δ ^ 2 * (n * p) / 3)) := by
  refine le_trans ?_ (binomial_prob_ge_le h0 h1 hδ0 hδ1)
  rw [← hX, prob_map]
  exact μ.prob_mono fun ω (hω : (1 + δ) * (n * p) < X ω) =>
    show (1 + δ) * (n * p) ≤ (X ω : ℝ) from hω.le

/-- [s1:citChernoff], lower tail: for `X ∼ Bin(n, p)` and `δ ≥ 0` (the manuscript has
`0 ≤ δ ≤ 1`), `P(X < (1 - δ) μ) ≤ e^{-δ²μ/2}` with `μ = E X = n p`. -/
theorem chernoff_binomial_lower (hX : μ.map X = binomial n p h0 h1) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.prob {ω | (X ω : ℝ) < (1 - δ) * (n * p)} ≤ Real.exp (-(δ ^ 2 * (n * p) / 2)) := by
  refine le_trans ?_ (binomial_prob_le_le h0 h1 hδ)
  rw [← hX, prob_map]
  exact μ.prob_mono fun ω (hω : (X ω : ℝ) < (1 - δ) * (n * p)) =>
    show (X ω : ℝ) ≤ (1 - δ) * (n * p) from hω.le

/-- [s1:citChernoff] (B–M Theorem 4). "Let `n` be an integer, `0 ≤ δ, p ≤ 1`, `X ∼ Bin(n,p)`
and `μ := E X = np`. Then `P(X > (1+δ)μ) ≤ e^{-δ²μ/3}` and `P(X < (1-δ)μ) ≤ e^{-δ²μ/2}`."

`X ∼ Bin(n, p)` is `μ.map X = binomial n p h0 h1` (here `μ` is the distribution); the first
conjunct is `E X = n p`. -/
theorem chernoff_binomial (hX : μ.map X = binomial n p h0 h1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    μ.expect (fun ω => (X ω : ℝ)) = n * p ∧
      μ.prob {ω | (1 + δ) * (n * p) < X ω} ≤ Real.exp (-(δ ^ 2 * (n * p) / 3)) ∧
      μ.prob {ω | (X ω : ℝ) < (1 - δ) * (n * p)} ≤ Real.exp (-(δ ^ 2 * (n * p) / 2)) :=
  ⟨expect_of_map_eq_binomial h0 h1 hX, chernoff_binomial_upper h0 h1 hX hδ0 hδ1,
    chernoff_binomial_lower h0 h1 hX hδ0⟩

end Binomial

/-! ### Indicators that are functions of distinct coordinates of a finite product -/

section DependsOn

variable {U : Type*} [Fintype ι] {κ : ι → Type*} (ν : ∀ i, FinDist (κ i)) (s : Finset U)
  (B : U → Set ι) (hB : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (B u) (B v))
  (E : U → Set (∀ i, κ i)) (hE : ∀ u ∈ s, ∀ f g, (∀ i ∈ B u, f i = g i) → f ∈ E u → g ∈ E u)
include hB hE

/-- Upper tail for indicators of events `E u` (`u ∈ s`) of a finite product space, each
depending only on its own block `B u` of coordinates, the blocks being pairwise disjoint (for
single coordinates: `B u = {σ u}` with `σ` injective on `s`): if `∑_u P(E u) ≤ m` and
`0 ≤ δ ≤ 1`, then `P(∑_u 1_{E u} ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem chernoff_pi_dependsOn_upper {m δ : ℝ} (hm : ∑ u ∈ s, (pi ν).prob (E u) ≤ m)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (pi ν).prob {f | (1 + δ) * m ≤ ∑ u ∈ s, (E u).indicator 1 f} ≤
      Real.exp (-(δ ^ 2 * m / 3)) :=
  (indepEvents_pi_of_dependsOn ν s B hB E hE).prob_ge_le hm hδ0 hδ1

/-- Lower tail in the setting of `chernoff_pi_dependsOn_upper`: if `0 ≤ m ≤ ∑_u P(E u)` and
`δ ≥ 0`, then `P(∑_u 1_{E u} ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`. -/
theorem chernoff_pi_dependsOn_lower {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ∑ u ∈ s, (pi ν).prob (E u)) (hδ : 0 ≤ δ) :
    (pi ν).prob {f | ∑ u ∈ s, (E u).indicator 1 f ≤ (1 - δ) * m} ≤
      Real.exp (-(δ ^ 2 * m / 2)) :=
  (indepEvents_pi_of_dependsOn ν s B hB E hE).prob_le_le hm0 hm hδ

/-- The tail (b) in the setting of `chernoff_pi_dependsOn_upper`: if `∑_u P(E u) ≤ m`, then
`P(∑_u 1_{E u} ≥ j) ≤ m^j / j!` and `≤ (e m / j)^j`. -/
theorem chernoff_pi_dependsOn_tail {m : ℝ} (hm : ∑ u ∈ s, (pi ν).prob (E u) ≤ m) (j : ℕ) :
    (pi ν).prob {f | (j : ℝ) ≤ ∑ u ∈ s, (E u).indicator 1 f} ≤ m ^ j / j.factorial ∧
      (pi ν).prob {f | (j : ℝ) ≤ ∑ u ∈ s, (E u).indicator 1 f} ≤ (Real.exp 1 * m / j) ^ j :=
  ⟨(indepEvents_pi_of_dependsOn ν s B hB E hE).prob_ge_nat_le hm j,
    (indepEvents_pi_of_dependsOn ν s B hB E hE).prob_ge_nat_le_exp hm j⟩

end DependsOn

/-! ### ρ-random subsets -/

section RSubset

variable [DecidableEq α] {μ : FinDist Ω} {V : Ω → Finset α} {S : Finset α} {ρ : ℝ}

private theorem IsRSubset.card_inter_eq_sum (hV : μ.IsRSubset V S ρ) (E : Finset α) (ω : Ω)
    (hω : 0 < μ.w ω) :
    ((V ω ∩ E).card : ℝ) = ∑ a ∈ S ∩ E, {ω | a ∈ V ω}.indicator 1 ω := by
  rw [sum_indicator_one_eq_card (S ∩ E) _ ω (fun a => a ∈ V ω) fun _ _ => Iff.rfl]
  congr 2
  ext a
  simp only [mem_inter, mem_filter]
  have hsub : a ∈ V ω → a ∈ S := fun h => hV.subset_ae ω hω h
  tauto

private theorem IsRSubset.sum_prob_inter (hV : μ.IsRSubset V S ρ) (E : Finset α) :
    ∑ a ∈ S ∩ E, μ.prob {ω | a ∈ V ω} = ρ * (S ∩ E).card := by
  rw [sum_congr rfl fun a ha => hV.prob_mem (mem_inter.1 ha).1, sum_const, nsmul_eq_mul,
    mul_comm]

/-- Chernoff upper tail for a ρ-random subset `V` of `S` and a fixed set `E`
(`|V ∩ E| ∼ Bin(|S ∩ E|, ρ)`): if `ρ |S ∩ E| ≤ m` and `0 ≤ δ ≤ 1`, then
`P(|V ∩ E| ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem IsRSubset.chernoff_card_inter_upper (hV : μ.IsRSubset V S ρ) (E : Finset α) {m δ : ℝ}
    (hm : ρ * (S ∩ E).card ≤ m) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * m ≤ (V ω ∩ E).card} ≤ Real.exp (-(δ ^ 2 * m / 3)) :=
  (hV.indepEvents.mono inter_subset_left).chernoff_upper (hV.card_inter_eq_sum E)
    ((hV.sum_prob_inter E).le.trans hm) hδ0 hδ1

/-- Chernoff lower tail for a ρ-random subset `V` of `S` and a fixed set `E`: if
`0 ≤ m ≤ ρ |S ∩ E|` and `δ ≥ 0`, then `P(|V ∩ E| ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`. -/
theorem IsRSubset.chernoff_card_inter_lower (hV : μ.IsRSubset V S ρ) (E : Finset α) {m δ : ℝ}
    (hm0 : 0 ≤ m) (hm : m ≤ ρ * (S ∩ E).card) (hδ : 0 ≤ δ) :
    μ.prob {ω | ((V ω ∩ E).card : ℝ) ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) :=
  (hV.indepEvents.mono inter_subset_left).chernoff_lower (hV.card_inter_eq_sum E) hm0
    (hm.trans (hV.sum_prob_inter E).ge) hδ

/-- Chernoff lower tail with `δ = 1/2` for a ρ-random subset `V` of `S` and a fixed set `E`: if
`0 ≤ m ≤ ρ |S ∩ E|`, then `P(|V ∩ E| < m / 2) ≤ exp(-m / 8)` ([s3:lemL17s] proof, Case (a):
"`|Cen ∩ V_i| ∼ Bin(|Cen|, p_*)`, so … `P(|Cen ∩ V_i| < p_*|Cen|/2) ≤ exp(-p_*|Cen|/8)`"). -/
theorem IsRSubset.chernoff_card_inter_lower_half (hV : μ.IsRSubset V S ρ) (E : Finset α)
    {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ ρ * (S ∩ E).card) :
    μ.prob {ω | ((V ω ∩ E).card : ℝ) < m / 2} ≤ Real.exp (-(m / 8)) :=
  (hV.indepEvents.mono inter_subset_left).chernoff_lower_half (hV.card_inter_eq_sum E) hm0
    (hm.trans (hV.sum_prob_inter E).ge)

/-- The tail (b) for a ρ-random subset `V` of `S` and a fixed set `E`: if `ρ |S ∩ E| ≤ m`, then
`P(|V ∩ E| ≥ j) ≤ m^j / j!` and `≤ (e m / j)^j`. -/
theorem IsRSubset.chernoff_card_inter_tail (hV : μ.IsRSubset V S ρ) (E : Finset α) {m : ℝ}
    (hm : ρ * (S ∩ E).card ≤ m) (j : ℕ) :
    μ.prob {ω | j ≤ (V ω ∩ E).card} ≤ m ^ j / j.factorial ∧
      μ.prob {ω | j ≤ (V ω ∩ E).card} ≤ (Real.exp 1 * m / j) ^ j := by
  have h1 := (hV.indepEvents.mono inter_subset_left).chernoff_tail (hV.card_inter_eq_sum E)
    ((hV.sum_prob_inter E).le.trans hm) j
  have h2 := (hV.indepEvents.mono inter_subset_left).chernoff_tail_exp (hV.card_inter_eq_sum E)
    ((hV.sum_prob_inter E).le.trans hm) j
  simp only [Nat.cast_le] at h1 h2
  exact ⟨h1, h2⟩

private theorem IsRSubset.card_eq_card_inter (hV : μ.IsRSubset V S ρ) (ω : Ω)
    (hω : 0 < μ.w ω) : V ω ∩ S = V ω :=
  inter_eq_left.2 (hV.subset_ae ω hω)

/-- Chernoff upper tail for the size of a ρ-random subset `V` of `S` (`|V| ∼ Bin(|S|, ρ)`): if
`ρ |S| ≤ m` and `0 ≤ δ ≤ 1`, then `P(|V| ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem IsRSubset.chernoff_card_upper (hV : μ.IsRSubset V S ρ) {m δ : ℝ}
    (hm : ρ * S.card ≤ m) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.prob {ω | (1 + δ) * m ≤ (V ω).card} ≤ Real.exp (-(δ ^ 2 * m / 3)) := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans
    (hV.chernoff_card_inter_upper S (by rwa [inter_self]) hδ0 hδ1)
  simp only [Set.mem_ofPred_eq, hV.card_eq_card_inter ω hω]

/-- Chernoff lower tail for the size of a ρ-random subset `V` of `S`: if `0 ≤ m ≤ ρ |S|` and
`δ ≥ 0`, then `P(|V| ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`. Example: [s3:lemL17s] proof, Step 3:
"Since `|V| ∼ Bin(N, ρ)`, the Chernoff bound gives `P(|V| < ρN/2) ≤ e^{-ρN/8}`". -/
theorem IsRSubset.chernoff_card_lower (hV : μ.IsRSubset V S ρ) {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ρ * S.card) (hδ : 0 ≤ δ) :
    μ.prob {ω | ((V ω).card : ℝ) ≤ (1 - δ) * m} ≤ Real.exp (-(δ ^ 2 * m / 2)) := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans
    (hV.chernoff_card_inter_lower S hm0 (by rwa [inter_self]) hδ)
  simp only [Set.mem_ofPred_eq, hV.card_eq_card_inter ω hω]

/-- Chernoff lower tail with `δ = 1/2` for the size of a ρ-random subset `V` of `S`: if
`0 ≤ m ≤ ρ |S|`, then `P(|V| < m / 2) ≤ exp(-m / 8)` ([s3:lemL17s] proof, Step 3). -/
theorem IsRSubset.chernoff_card_lower_half (hV : μ.IsRSubset V S ρ) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ρ * S.card) :
    μ.prob {ω | ((V ω).card : ℝ) < m / 2} ≤ Real.exp (-(m / 8)) := by
  refine (le_of_eq (μ.prob_congr fun ω hω => ?_)).trans
    (hV.chernoff_card_inter_lower_half S hm0 (by rwa [inter_self]))
  simp only [Set.mem_ofPred_eq, hV.card_eq_card_inter ω hω]

end RSubset

/-! ### Colour classes of a uniform random colouring -/

section Colouring

variable [Fintype ι] {k : ℕ} [NeZero k]

/-- The events "`e` has colour `j`" (`e ∈ E`) of a uniform random colouring are mutually
independent. -/
theorem indepEvents_randColouring (E : Finset ι) (j : Fin k) :
    (randColouring ι k).IndepEvents E (fun e => {c | c e = j}) :=
  indepEvents_pi_coord (fun _ : ι => uniform (Fin k)) (fun _ => {x | x = j}) E

omit [Fintype ι] [NeZero k] in
private theorem card_eq_sum_indicator_colour (E : Finset ι) (j : Fin k) (c : ι → Fin k) :
    (#{e ∈ E | c e = j} : ℝ) = ∑ e ∈ E, {c : ι → Fin k | c e = j}.indicator 1 c :=
  (sum_indicator_one_eq_card E _ c (fun e => c e = j) fun _ _ => Iff.rfl).symm

private theorem sum_prob_colour (E : Finset ι) (j : Fin k) :
    ∑ e ∈ E, (randColouring ι k).prob {c | c e = j} = E.card / k := by
  rw [sum_congr rfl fun e _ => prob_randColouring_apply e j, sum_const, nsmul_eq_mul]
  ring

/-- Chernoff upper tail for a colour class of a uniform random `k`-colouring
(`#{e ∈ E | c e = j} ∼ Bin(|E|, 1/k)`, as in [s3:lemL15p] proof, Step 3): if `|E| / k ≤ m` and
`0 ≤ δ ≤ 1`, then `P(#{e ∈ E | c e = j} ≥ (1 + δ) m) ≤ exp(-δ² m / 3)`. -/
theorem chernoff_randColouring_upper (E : Finset ι) (j : Fin k) {m δ : ℝ}
    (hm : (E.card : ℝ) / k ≤ m) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (randColouring ι k).prob {c | (1 + δ) * m ≤ #{e ∈ E | c e = j}} ≤
      Real.exp (-(δ ^ 2 * m / 3)) :=
  (indepEvents_randColouring E j).chernoff_upper
    (fun c _ => card_eq_sum_indicator_colour E j c) ((sum_prob_colour E j).le.trans hm) hδ0 hδ1

/-- Chernoff lower tail for a colour class of a uniform random `k`-colouring: if
`0 ≤ m ≤ |E| / k` and `δ ≥ 0`, then `P(#{e ∈ E | c e = j} ≤ (1 - δ) m) ≤ exp(-δ² m / 2)`.
[s3:lemL15p] proof, Step 3: "`Z := e_H(U, N∖T) ∼ Bin(e, 1/k)` … By the lower Chernoff bound with
`δ = 1/2`, `P(Z ≤ su/(2k)) ≤ e^{-μ_Z/8}`". -/
theorem chernoff_randColouring_lower (E : Finset ι) (j : Fin k) {m δ : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ (E.card : ℝ) / k) (hδ : 0 ≤ δ) :
    (randColouring ι k).prob {c | (#{e ∈ E | c e = j} : ℝ) ≤ (1 - δ) * m} ≤
      Real.exp (-(δ ^ 2 * m / 2)) :=
  (indepEvents_randColouring E j).chernoff_lower
    (fun c _ => card_eq_sum_indicator_colour E j c) hm0 (hm.trans (sum_prob_colour E j).ge) hδ

/-- Chernoff lower tail with `δ = 1/2` for a colour class of a uniform random `k`-colouring: if
`0 ≤ m ≤ |E| / k`, then `P(#{e ∈ E | c e = j} < m / 2) ≤ exp(-m / 8)` ([s3:lemL15p] proof,
Step 3, with `m = μ_Z = e/k`). -/
theorem chernoff_randColouring_lower_half (E : Finset ι) (j : Fin k) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ (E.card : ℝ) / k) :
    (randColouring ι k).prob {c | (#{e ∈ E | c e = j} : ℝ) < m / 2} ≤ Real.exp (-(m / 8)) :=
  (indepEvents_randColouring E j).chernoff_lower_half
    (fun c _ => card_eq_sum_indicator_colour E j c) hm0 (hm.trans (sum_prob_colour E j).ge)

end Colouring

end FinDist

end EG
