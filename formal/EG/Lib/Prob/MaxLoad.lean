module

public import EG.Lib.Prob.Chernoff
public import EG.Lib.Prob.Indep
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The maximum load of independent random choices (manuscript s7:lemUltra (ii))

`N` independent random choices `X_i ∈ W ∪ {⊥}` (`i ∈ S`), each equal to a given `w` with probability
at most `p`; the load of `w` is `m_w = #{i : X_i = w}`. Then
`E[max_w m_w] ≤ log₂N + 2e·Np + 8` ([s7:lemUltra] (ii) with `p = 2/Hcd_l`, `μ* = Np`):

"Let `m_w := #{i : ω_i = w}`. It is a sum of independent indicators with mean `μ_w ≤ μ*`, and
`Σ_w μ_w = N`. Put `T := max(⌈2eμ*⌉, ⌈log₂N⌉ + 1)`. For `j ≥ T` we have `eμ_w/j ≤ 1/2`, so by
Cited result s1:citChernoffGen `P(m_w ≥ j) ≤ (eμ_w/j)^j ≤ (eμ_w/j)2^{1-j}`, and summing over `w`
gives `Σ_w P(m_w ≥ j) ≤ (eN/j)2^{1-j}`. Hence
`E[max_w m_w] = Σ_{j≥1} P(max_w m_w ≥ j) ≤ (T−1) + Σ_{j≥T} (eN/j)2^{1-j} ≤ T − 1 + 2e/T`."

* `expect_nat_eq_sum_prob`: the tail-sum formula `E Y = Σ_{j=1}^K P(Y ≥ j)` for `0 ≤ Y ≤ K`;
* `maxLoad_le`: the bound.
-/

public section

namespace EG

namespace FinDist

open Finset

variable {Ω ι β : Type*}

/-- The tail-sum formula for a bounded `ℕ`-valued variable. -/
theorem expect_nat_eq_sum_prob (μ : FinDist Ω) (Y : Ω → ℕ) (K : ℕ) (hY : ∀ ω, Y ω ≤ K) :
    μ.expect (fun ω => (Y ω : ℝ)) = ∑ j ∈ Icc 1 K, μ.prob {ω | j ≤ Y ω} := by
  classical
  have h1 : ∀ ω, (Y ω : ℝ) = ∑ j ∈ Icc 1 K, (if j ≤ Y ω then (1 : ℝ) else 0) := by
    intro ω
    rw [Finset.sum_boole]
    have : (Icc 1 K).filter (fun j => j ≤ Y ω) = Icc 1 (Y ω) := by
      ext j; simp only [mem_filter, mem_Icc]; have := hY ω; omega
    rw [this, Nat.card_Icc]; simp
  simp_rw [h1]
  rw [expect_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [prob_eq_expect]
  congr 1
  funext ω
  by_cases h : j ≤ Y ω <;> simp [Set.indicator, h]

/-- The expectation of an indicator is the probability of its event. -/
theorem expect_indicator_ite (μ : FinDist Ω) (P : Ω → Prop) [DecidablePred P] :
    μ.expect (fun ω => if P ω then (1 : ℝ) else 0) = μ.prob {ω | P ω} := by
  rw [prob_eq_expect]
  congr 1
  funext ω
  by_cases h : P ω <;> simp [Set.indicator, h]

variable [DecidableEq β] (μ : FinDist Ω) (S : Finset ι) (W : Finset β) (X : ι → Ω → Option β)

/-- The load `m_w = #{i ∈ S : X_i = w}`. -/
@[expose] noncomputable def load (w : β) (ω : Ω) : ℕ := (S.filter (fun i => X i ω = some w)).card

theorem load_le (w : β) (ω : Ω) : load S X w ω ≤ S.card := Finset.card_filter_le _ _

theorem load_eq_sum (w : β) (ω : Ω) :
    (load S X w ω : ℝ) = ∑ i ∈ S, (if X i ω = some w then (1 : ℝ) else 0) := by
  classical
  unfold load
  rw [Finset.sum_boole]

theorem sum_ite_eq_some_le_one (x : Option β) :
    ∑ w ∈ W, (if x = some w then (1 : ℝ) else 0) ≤ 1 := by
  rcases x with _ | v
  · simp
  · simp only [Option.some.injEq]
    rw [Finset.sum_ite_eq]
    split_ifs <;> norm_num

/-- `Σ_w μ_w ≤ N`. -/
theorem sum_expect_load_le :
    ∑ w ∈ W, μ.expect (fun ω => (load S X w ω : ℝ)) ≤ S.card := by
  classical
  simp_rw [load_eq_sum]
  rw [← expect_sum]
  have : ∀ ω, ∑ w ∈ W, ∑ i ∈ S, (if X i ω = some w then (1 : ℝ) else 0) ≤ S.card := by
    intro ω
    rw [Finset.sum_comm]
    calc ∑ i ∈ S, ∑ w ∈ W, (if X i ω = some w then (1 : ℝ) else 0)
        ≤ ∑ i ∈ S, (1 : ℝ) := Finset.sum_le_sum fun i _ => sum_ite_eq_some_le_one W (X i ω)
      _ = S.card := by simp
  exact μ.expect_le_of_le this

/-- [s1:citChernoffGen] for one load: `P(m_w ≥ j) ≤ (eμ_w/j)^j`. -/
theorem prob_load_ge (hind : μ.iIndepFun fun i : S => X i) (w : β) (j : ℕ) :
    μ.prob {ω | j ≤ load S X w ω} ≤
      (Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) / j) ^ j := by
  classical
  have hI : ∀ i ∈ S, ∀ ω, (if X i ω = some w then (1 : ℝ) else 0) = 0 ∨
      (if X i ω = some w then (1 : ℝ) else 0) = 1 := by
    intro i _ ω; by_cases h : X i ω = some w <;> simp [h]
  have hind' : μ.iIndepFun fun i : S => fun ω => (if X i ω = some w then (1 : ℝ) else 0) :=
    hind.comp fun _ x => if x = some w then (1 : ℝ) else 0
  have he : μ.expect (fun ω => ∑ i ∈ S, (if X i ω = some w then (1 : ℝ) else 0)) =
      μ.expect (fun ω => (load S X w ω : ℝ)) := by simp_rw [load_eq_sum]
  have h := chernoffGen_tail_exp_on (μ := μ) S hI hind' (le_of_eq he) j
  have hset : {ω | j ≤ load S X w ω} =
      {ω | (j : ℝ) ≤ ∑ i ∈ S, (if X i ω = some w then (1 : ℝ) else 0)} := by
    ext ω; simp only [Set.mem_ofPred_eq, ← load_eq_sum]; exact_mod_cast Iff.rfl
  rw [hset]
  exact h.1.trans h.2

/-- [s7:lemUltra] (ii): `E[max_{w∈W} m_w] ≤ log₂N + 2e·Np + 8` for `N = |S| ≥ 1` independent
choices, each hitting a given `w` with probability at most `p`. -/
theorem maxLoad_le (hind : μ.iIndepFun fun i : S => X i) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ i ∈ S, ∀ w, μ.prob {ω | X i ω = some w} ≤ p) (hN : 1 ≤ S.card) :
    μ.expect (fun ω => ((W.sup fun w => load S X w ω : ℕ) : ℝ)) ≤
      Real.logb 2 S.card + 2 * Real.exp 1 * (S.card * p) + 8 := by
  classical
  set N := S.card with hNdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have he0 := Real.exp_pos 1
  have he3 := Real.exp_one_lt_d9
  -- the means `μ_w ≤ Np`
  have hmean : ∀ w, μ.expect (fun ω => (load S X w ω : ℝ)) ≤ N * p := by
    intro w
    simp_rw [load_eq_sum]
    rw [expect_sum]
    calc ∑ i ∈ S, μ.expect (fun ω => if X i ω = some w then (1 : ℝ) else 0)
        ≤ ∑ i ∈ S, p := Finset.sum_le_sum fun i hi => by rw [expect_indicator_ite]; exact hp i hi w
      _ = N * p := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmean0 : ∀ w, 0 ≤ μ.expect (fun ω => (load S X w ω : ℝ)) :=
    fun w => μ.expect_nonneg fun ω => Nat.cast_nonneg _
  -- the threshold `T`
  set T : ℕ := max ⌈2 * Real.exp 1 * (N * p)⌉₊ (⌈Real.logb 2 N⌉₊ + 1) with hT
  have hT1 : 1 ≤ T := le_trans (by omega) (le_max_right _ _)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hTm : 2 * Real.exp 1 * (N * p) ≤ T :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
  have hlog0 : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN1
  have hTN : (2 : ℝ) * N ≤ 2 ^ T := by
    have h1 : Real.logb 2 N + 1 ≤ (T : ℝ) := by
      have := Nat.le_ceil (Real.logb 2 N)
      have h2' : ⌈Real.logb 2 N⌉₊ + 1 ≤ T := le_max_right _ _
      have h2 : ((⌈Real.logb 2 N⌉₊ + 1 : ℕ) : ℝ) ≤ (T : ℝ) := Nat.cast_le.2 h2'
      rw [Nat.cast_add, Nat.cast_one] at h2
      linarith
    have h3 : (2 : ℝ) ^ (Real.logb 2 N + 1) ≤ (2 : ℝ) ^ (T : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hN0,
      Real.rpow_one, Real.rpow_natCast] at h3
    linarith
  have hT1r : (T : ℝ) - 1 ≤ Real.logb 2 N + 2 * Real.exp 1 * (N * p) + 1 := by
    rcases le_total ⌈2 * Real.exp 1 * (N * p)⌉₊ (⌈Real.logb 2 N⌉₊ + 1) with h | h
    · rw [hT, max_eq_right h]
      have := Nat.ceil_lt_add_one hlog0
      rw [Nat.cast_add, Nat.cast_one]
      have : 0 ≤ 2 * Real.exp 1 * (N * p) := by positivity
      linarith
    · rw [hT, max_eq_left h]
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp 1 * (N * p) by positivity)
      linarith
  -- the tail-sum formula for the maximum
  have hY : ∀ ω, W.sup (fun w => load S X w ω) ≤ N :=
    fun ω => Finset.sup_le fun w _ => load_le S X w ω
  rw [expect_nat_eq_sum_prob μ _ N hY, ← Finset.sum_filter_add_sum_filter_not (Icc 1 N)
    (fun j => j < T)]
  -- the rounds `j < T`: at most `T - 1` terms, each at most `1`
  have hA : ∑ j ∈ (Icc 1 N).filter (fun j => j < T),
      μ.prob {ω | j ≤ W.sup fun w => load S X w ω} ≤ (T : ℝ) - 1 := by
    calc _ ≤ ∑ j ∈ (Icc 1 N).filter (fun j => j < T), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => μ.prob_le_one _
      _ = (((Icc 1 N).filter (fun j => j < T)).card : ℝ) := by simp
      _ ≤ (((Icc 1 (T - 1)).card : ℕ) : ℝ) := by
          gcongr
          intro j hj
          simp only [mem_filter, mem_Icc] at hj ⊢
          omega
      _ = (T : ℝ) - 1 := by
          rw [Nat.card_Icc]; push_cast [Nat.sub_add_cancel hT1]
          rw [Nat.cast_sub hT1]; ring
  -- the rounds `j ≥ T`
  have hjB : ∀ j ∈ (Icc 1 N).filter (fun j => ¬ j < T),
      μ.prob {ω | j ≤ W.sup fun w => load S X w ω} ≤
        Real.exp 1 * N / T * (2 * (1 / 2 : ℝ) ^ j) := by
    intro j hj
    simp only [mem_filter, mem_Icc, not_lt] at hj
    have hj1 : 1 ≤ j := hj.1.1
    have hjT : T ≤ j := hj.2
    have hjr : (T : ℝ) ≤ j := by exact_mod_cast hjT
    have hj0 : (0 : ℝ) < j := lt_of_lt_of_le hT0 hjr
    -- union bound over `w`
    have hsub : {ω | j ≤ W.sup fun w => load S X w ω} ⊆
        ⋃ w ∈ W, {ω | j ≤ load S X w ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      obtain ⟨w, hw, hle⟩ := (Finset.le_sup_iff (by rw [Nat.bot_eq_zero]; omega)).1 hω
      exact Set.mem_biUnion hw hle
    have hU := (μ.prob_mono hsub).trans (μ.prob_biUnion_le W _)
    refine hU.trans ?_
    -- each term: `(eμ_w/j)^j ≤ (eμ_w/j)(1/2)^{j-1}`
    have hterm : ∀ w ∈ W, μ.prob {ω | j ≤ load S X w ω} ≤
        Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) / j * (2 * (1 / 2 : ℝ) ^ j) := by
      intro w _
      refine (prob_load_ge μ S X hind w j).trans ?_
      set x := Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) / j with hx
      have hx0 : 0 ≤ x := by rw [hx]; have := hmean0 w; positivity
      have hx1 : x ≤ 1 / 2 := by
        rw [hx, div_le_iff₀ hj0]
        have := hmean w
        nlinarith
      have e1 : x ^ j = x * x ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have e2 : (2 : ℝ) * (1 / 2) ^ j = (1 / 2) ^ (j - 1) := by
        rw [show j = (j - 1) + 1 by omega, pow_succ]; simp; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 _) hx0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hs := sum_expect_load_le μ S W X
    calc ∑ w ∈ W, Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) / j
        = Real.exp 1 / j * ∑ w ∈ W, μ.expect (fun ω => (load S X w ω : ℝ)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ Real.exp 1 / j * N := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ Real.exp 1 * N / T := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_left (by positivity) hT0 hjr
  have hB : ∑ j ∈ (Icc 1 N).filter (fun j => ¬ j < T),
      μ.prob {ω | j ≤ W.sup fun w => load S X w ω} ≤ 2 * Real.exp 1 := by
    refine (Finset.sum_le_sum hjB).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hgeom : ∑ j ∈ (Icc 1 N).filter (fun j => ¬ j < T), (1 / 2 : ℝ) ^ j ≤
        (1 / 2 : ℝ) ^ T / (1 - 1 / 2) := by
      refine le_trans ?_ (geom_sum_Ico_le_of_lt_one (m := T) (n := N + 1) (by norm_num)
        (by norm_num))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [mem_filter, mem_Icc, not_lt, mem_Ico] at hj ⊢
        omega
      · intro _ _ _; positivity
    have hpowT : (1 / 2 : ℝ) ^ T ≤ 1 / (2 * N) := by
      rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
      exact hTN
    calc Real.exp 1 * N / T * (2 * ∑ j ∈ (Icc 1 N).filter (fun j => ¬ j < T), (1 / 2 : ℝ) ^ j)
        ≤ Real.exp 1 * N / T * (2 * ((1 / 2 : ℝ) ^ T / (1 - 1 / 2))) := by gcongr
      _ ≤ Real.exp 1 * N / T * (2 * (1 / (2 * N) / (1 - 1 / 2))) := by gcongr
      _ = 2 * Real.exp 1 / T := by field_simp; ring
      _ ≤ 2 * Real.exp 1 := by
          rw [div_le_iff₀ hT0]
          have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
          nlinarith
  linarith

/-- The tail part of one load: `E[m_w 1{m_w ≥ T}] ≤ 4eμ_w 2^{-T}` for `T ≥ 2eμ_w`, `T ≥ 1`
([s7:lemCC] (ii) "`E[m 1{m ≥ T}] = T P(m ≥ T) + Σ_{j>T} P(m ≥ j) ≤ eμ_{w'}2^{2-T}`"). -/
theorem expect_load_tail_le (hind : μ.iIndepFun fun i : S => X i) (w : β) {T : ℕ} (hT1 : 1 ≤ T)
    (hT : 2 * Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) ≤ T) :
    μ.expect (fun ω => ((if T ≤ load S X w ω then load S X w ω else 0 : ℕ) : ℝ)) ≤
      4 * Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) * (1 / 2 : ℝ) ^ T := by
  classical
  set μw := μ.expect (fun ω => (load S X w ω : ℝ)) with hμw
  have hμ0 : 0 ≤ μw := μ.expect_nonneg fun ω => Nat.cast_nonneg _
  have he0 := Real.exp_pos 1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  set N := S.card
  have hY : ∀ ω, (if T ≤ load S X w ω then load S X w ω else 0) ≤ N := by
    intro ω; split_ifs
    · exact load_le S X w ω
    · exact Nat.zero_le _
  rw [expect_nat_eq_sum_prob μ _ N hY, ← Finset.sum_filter_add_sum_filter_not (Icc 1 N)
    (fun j => j ≤ T)]
  -- the tail bound for `j ≥ T`
  have htail : ∀ j : ℕ, T ≤ j →
      μ.prob {ω | j ≤ load S X w ω} ≤ Real.exp 1 * μw / j * (2 * (1 / 2 : ℝ) ^ j) := by
    intro j hj
    have hjr : (T : ℝ) ≤ j := by exact_mod_cast hj
    have hj0 : (0 : ℝ) < j := lt_of_lt_of_le hT0 hjr
    have hj1 : 1 ≤ j := le_trans hT1 hj
    refine (prob_load_ge μ S X hind w j).trans ?_
    set x := Real.exp 1 * μw / j with hx
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    have hx1 : x ≤ 1 / 2 := by
      rw [hx, div_le_iff₀ hj0]
      nlinarith
    have e1 : x ^ j = x * x ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e2 : (2 : ℝ) * (1 / 2) ^ j = (1 / 2) ^ (j - 1) := by
      rw [show j = (j - 1) + 1 by omega, pow_succ]; simp; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 _) hx0
  -- `j ≤ T`: the event is `{m ≥ T}`
  have hA : ∑ j ∈ (Icc 1 N).filter (fun j => j ≤ T),
      μ.prob {ω | j ≤ (if T ≤ load S X w ω then load S X w ω else 0)} ≤
        2 * Real.exp 1 * μw * (1 / 2 : ℝ) ^ T := by
    have h1 : ∀ j ∈ (Icc 1 N).filter (fun j => j ≤ T),
        μ.prob {ω | j ≤ (if T ≤ load S X w ω then load S X w ω else 0)} =
          μ.prob {ω | T ≤ load S X w ω} := by
      intro j hj
      simp only [mem_filter, mem_Icc] at hj
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => le_trans hj.2 h⟩
      · exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Icc 1 N).filter (fun j => j ≤ T)).card : ℝ) ≤ T := by
      have : ((Icc 1 N).filter (fun j => j ≤ T)) ⊆ Icc 1 T := by
        intro j hj; simp only [mem_filter, mem_Icc] at hj ⊢; omega
      have := Finset.card_le_card this
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : ((Icc 1 N).filter (fun j => j ≤ T)).card ≤ T)
    have hP := htail T le_rfl
    calc (((Icc 1 N).filter (fun j => j ≤ T)).card : ℝ) * μ.prob {ω | T ≤ load S X w ω}
        ≤ T * (Real.exp 1 * μw / T * (2 * (1 / 2 : ℝ) ^ T)) :=
          mul_le_mul hcard hP (μ.prob_nonneg _) hT0.le
      _ = 2 * Real.exp 1 * μw * (1 / 2 : ℝ) ^ T := by field_simp
  -- `j > T`
  have hB : ∑ j ∈ (Icc 1 N).filter (fun j => ¬ j ≤ T),
      μ.prob {ω | j ≤ (if T ≤ load S X w ω then load S X w ω else 0)} ≤
        2 * Real.exp 1 * μw * (1 / 2 : ℝ) ^ T := by
    have h1 : ∀ j ∈ (Icc 1 N).filter (fun j => ¬ j ≤ T),
        μ.prob {ω | j ≤ (if T ≤ load S X w ω then load S X w ω else 0)} ≤
          Real.exp 1 * μw * (2 * (1 / 2 : ℝ) ^ j) := by
      intro j hj
      simp only [mem_filter, mem_Icc, not_le] at hj
      have hsub : {ω | j ≤ (if T ≤ load S X w ω then load S X w ω else 0)} ⊆
          {ω | j ≤ load S X w ω} := by
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        split_ifs at hω <;> omega
      refine (μ.prob_mono hsub).trans ((htail j hj.2.le).trans ?_)
      have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1.1
      have : Real.exp 1 * μw / j ≤ Real.exp 1 * μw := div_le_self (by positivity) hj0
      exact mul_le_mul_of_nonneg_right this (by positivity)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hgeom : ∑ j ∈ (Icc 1 N).filter (fun j => ¬ j ≤ T), (1 / 2 : ℝ) ^ j ≤
        (1 / 2 : ℝ) ^ (T + 1) / (1 - 1 / 2) := by
      refine le_trans ?_ (geom_sum_Ico_le_of_lt_one (m := T + 1) (n := N + 1) (by norm_num)
        (by norm_num))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [mem_filter, mem_Icc, not_le, mem_Ico] at hj ⊢
        omega
      · intro _ _ _; positivity
    calc Real.exp 1 * μw * (2 * ∑ j ∈ (Icc 1 N).filter (fun j => ¬ j ≤ T), (1 / 2 : ℝ) ^ j)
        ≤ Real.exp 1 * μw * (2 * ((1 / 2 : ℝ) ^ (T + 1) / (1 - 1 / 2))) := by gcongr
      _ = 2 * Real.exp 1 * μw * (1 / 2 : ℝ) ^ T := by rw [pow_succ]; ring
  have := add_le_add hA hB
  linarith

/-- [s7:lemCC] (ii): for every integer `t ≥ 1`,
`E[max_w m_w] ≤ t·1[S ≠ ∅] + 2e·Np + 4e 2^{-t} N` (`N = |S|`; with `p = 3/Hcd_l`,
`2eNp = 6e|S_w|/Hcd_l`). "Put `T := max(t, ⌈6e|S_w|/Hcd_l⌉)` … `max_{w'} m ≤ (T−1) +
Σ_{w'} m 1{m ≥ T}`." -/
theorem maxLoad_le_t (hind : μ.iIndepFun fun i : S => X i) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ i ∈ S, ∀ w, μ.prob {ω | X i ω = some w} ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    μ.expect (fun ω => ((W.sup fun w => load S X w ω : ℕ) : ℝ)) ≤
      (t : ℝ) * (if S.Nonempty then 1 else 0) + 2 * Real.exp 1 * (S.card * p) +
        4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) * S.card := by
  classical
  have he0 := Real.exp_pos 1
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- no items: all loads vanish
    have hz : ∀ ω, ((W.sup fun w => load S X w ω : ℕ) : ℝ) = 0 := by
      intro ω
      have : W.sup (fun w => load S X w ω) = 0 :=
        Nat.eq_zero_of_le_zero (Finset.sup_le fun w _ => by
          have h := load_le S X w ω
          have hc : S.card = 0 := by rw [hS]; rfl
          omega)
      simp [this]
    simp_rw [hz, expect_const, hS]
    simp
  · rw [if_pos hS]
    set N := S.card with hNdef
    have hmean : ∀ w, μ.expect (fun ω => (load S X w ω : ℝ)) ≤ N * p := by
      intro w
      simp_rw [load_eq_sum]
      rw [expect_sum]
      calc ∑ i ∈ S, μ.expect (fun ω => if X i ω = some w then (1 : ℝ) else 0)
          ≤ ∑ i ∈ S, p := Finset.sum_le_sum fun i hi => by
            rw [expect_indicator_ite]; exact hp i hi w
        _ = N * p := by rw [Finset.sum_const, nsmul_eq_mul]
    set T : ℕ := max t ⌈2 * Real.exp 1 * (N * p)⌉₊ with hT
    have hT1 : 1 ≤ T := le_trans ht (le_max_left _ _)
    have htT : t ≤ T := le_max_left _ _
    have hTm : 2 * Real.exp 1 * (N * p) ≤ T :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have hNp : 0 ≤ 2 * Real.exp 1 * (N * p) := by positivity
    have hT1r : (T : ℝ) - 1 ≤ t + 2 * Real.exp 1 * (N * p) := by
      rcases le_total t ⌈2 * Real.exp 1 * (N * p)⌉₊ with h | h
      · rw [hT, max_eq_right h]
        have := Nat.ceil_lt_add_one hNp
        have : (0 : ℝ) ≤ t := Nat.cast_nonneg _
        linarith
      · rw [hT, max_eq_left h]
        linarith
    -- pointwise: `max_w m_w ≤ (T − 1) + Σ_w m_w 1{m_w ≥ T}`
    have hpt : ∀ ω, ((W.sup fun w => load S X w ω : ℕ) : ℝ) ≤ ((T : ℝ) - 1) +
        ∑ w ∈ W, ((if T ≤ load S X w ω then load S X w ω else 0 : ℕ) : ℝ) := by
      intro ω
      have hsum0 : 0 ≤ ∑ w ∈ W, ((if T ≤ load S X w ω then load S X w ω else 0 : ℕ) : ℝ) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      by_cases hlt : W.sup (fun w => load S X w ω) < T
      · have : ((W.sup fun w => load S X w ω : ℕ) : ℝ) ≤ (T : ℝ) - 1 := by
          have h' : W.sup (fun w => load S X w ω) ≤ T - 1 := by omega
          have h'' : ((W.sup fun w => load S X w ω : ℕ) : ℝ) ≤ ((T - 1 : ℕ) : ℝ) := by
            exact_mod_cast h'
          rwa [Nat.cast_sub hT1, Nat.cast_one] at h''
        linarith
      · push Not at hlt
        have hW : W.Nonempty := by
          by_contra hW
          rw [Finset.not_nonempty_iff_eq_empty] at hW
          rw [hW, Finset.sup_empty] at hlt
          have h0 : T ≤ 0 := hlt
          omega
        obtain ⟨w0, hw0, he⟩ := Finset.exists_mem_eq_sup W hW (fun w => load S X w ω)
        rw [he] at hlt ⊢
        have h1 : ((load S X w0 ω : ℕ) : ℝ) =
            ((if T ≤ load S X w0 ω then load S X w0 ω else 0 : ℕ) : ℝ) := by rw [if_pos hlt]
        have h2 := Finset.single_le_sum (f := fun w =>
          ((if T ≤ load S X w ω then load S X w ω else 0 : ℕ) : ℝ))
          (fun _ _ => Nat.cast_nonneg _) hw0
        have : (0 : ℝ) ≤ (T : ℝ) - 1 := by
          have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
          linarith
        linarith
    refine (μ.expect_mono hpt).trans ?_
    rw [expect_add, expect_const, expect_sum]
    have htail : ∀ w ∈ W, μ.expect (fun ω =>
        ((if T ≤ load S X w ω then load S X w ω else 0 : ℕ) : ℝ)) ≤
          4 * Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) * (2 : ℝ) ^ (-(t : ℤ)) := by
      intro w _
      refine (expect_load_tail_le μ S X hind w hT1 (le_trans (by
        have := hmean w; nlinarith) hTm)).trans ?_
      have hpow : (1 / 2 : ℝ) ^ T ≤ (2 : ℝ) ^ (-(t : ℤ)) := by
        rw [zpow_neg, zpow_natCast, one_div_pow, one_div]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) htT)
      have := μ.expect_nonneg fun ω => (Nat.cast_nonneg (load S X w ω) : (0 : ℝ) ≤ _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hs := sum_expect_load_le μ S W X
    calc (T : ℝ) - 1 + ∑ w ∈ W, μ.expect (fun ω =>
          ((if T ≤ load S X w ω then load S X w ω else 0 : ℕ) : ℝ))
        ≤ (T : ℝ) - 1 + ∑ w ∈ W,
          4 * Real.exp 1 * μ.expect (fun ω => (load S X w ω : ℝ)) * (2 : ℝ) ^ (-(t : ℤ)) := by
          gcongr with w hw; exact htail w hw
      _ = (T : ℝ) - 1 + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) *
          ∑ w ∈ W, μ.expect (fun ω => (load S X w ω : ℝ)) := by
          rw [Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ (T : ℝ) - 1 + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) * N := by gcongr
      _ ≤ (t : ℝ) * 1 + 2 * Real.exp 1 * (N * p) + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) * N := by
          linarith

end FinDist

end EG
