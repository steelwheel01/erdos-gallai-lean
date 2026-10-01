import EG.Lib.Prob.Chernoff

/-!
Sanity checks for the Chernoff bounds (`EG/Lib/Prob/Chernoff.lean`, [s1:citChernoff],
[s1:citChernoffGen]): each main form is instantiated once on a concrete distribution, and the
resulting numerical bounds are nontrivial (`< 1`).
-/

namespace EGTest.Chernoff

open EG EG.FinDist Finset

/-- A fair coin. -/
noncomputable abbrev coin : FinDist Bool := bernoulli (1 / 2) (by norm_num) (by norm_num)

/-- A coin with success probability `1/100`. -/
noncomputable abbrev rareCoin : FinDist Bool := bernoulli (1 / 100) (by norm_num) (by norm_num)

/-! ### Products of Bernoulli coins -/

/-- 100 fair coins: `P(#heads ≥ 75) ≤ e^{-25/6}` (upper tail, `m = 50`, `δ = 1/2`). -/
example : (pi fun _ : Fin 100 => coin).prob {f | (75 : ℝ) ≤ #{i | f i = true}} ≤
    Real.exp (-(25 / 6)) := by
  have h := chernoff_pi_bernoulli_upper (fun _ : Fin 100 => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (fun _ => by norm_num) univ (m := 50) (δ := 1 / 2) (by simp; norm_num) (by norm_num)
    (by norm_num)
  have e1 : ((1 : ℝ) + 1 / 2) * 50 = 75 := by norm_num
  have e2 : ((1 : ℝ) / 2) ^ 2 * 50 / 3 = 25 / 6 := by norm_num
  rw [e1, e2] at h
  exact h

/-- 100 fair coins: `P(#heads ≤ 25) ≤ e^{-25/4}` (lower tail, `m = 50`, `δ = 1/2`). -/
example : (pi fun _ : Fin 100 => coin).prob {f | (#{i | f i = true} : ℝ) ≤ 25} ≤
    Real.exp (-(25 / 4)) := by
  have h := chernoff_pi_bernoulli_lower (fun _ : Fin 100 => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (fun _ => by norm_num) univ (m := 50) (δ := 1 / 2) (by norm_num) (by simp; norm_num)
    (by norm_num)
  have e1 : ((1 : ℝ) - 1 / 2) * 50 = 25 := by norm_num
  have e2 : ((1 : ℝ) / 2) ^ 2 * 50 / 2 = 25 / 4 := by norm_num
  rw [e1, e2] at h
  exact h

/-- The bound above is nontrivial. -/
example : Real.exp (-(25 / 4)) < 1 := Real.exp_lt_one_iff.2 (by norm_num)

/-- 10 rare coins: `P(#heads ≥ 2) ≤ (1/10)²/2! = 1/200` (the tail (b), `m = 1/10`). -/
example : (pi fun _ : Fin 10 => rareCoin).prob {f | 2 ≤ #{i | f i = true}} ≤ 1 / 200 := by
  have h := chernoff_pi_bernoulli_tail (fun _ : Fin 10 => (1 / 100 : ℝ)) (fun _ => by norm_num)
    (fun _ => by norm_num) univ (m := 1 / 10) (by simp; norm_num) 2
  refine h.1.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

/-- 10 rare coins, second form of the tail (b): `P(#heads ≥ 2) ≤ (e (1/10) / 2)² = e²/400`. -/
example : (pi fun _ : Fin 10 => rareCoin).prob {f | 2 ≤ #{i | f i = true}} ≤
    Real.exp 1 ^ 2 / 400 := by
  have h := chernoff_pi_bernoulli_tail (fun _ : Fin 10 => (1 / 100 : ℝ)) (fun _ => by norm_num)
    (fun _ => by norm_num) univ (m := 1 / 10) (by simp; norm_num) 2
  refine h.2.trans (le_of_eq ?_)
  push_cast
  ring

/-! ### [s1:citChernoffGen] for real indicator variables -/

/-- The indicator variables `I i f = [f i = true]` of 20 fair coins. -/
noncomputable def ind (i : Fin 20) (f : Fin 20 → Bool) : ℝ := if f i = true then 1 else 0

theorem ind_zero_or_one (i : Fin 20) (f : Fin 20 → Bool) : ind i f = 0 ∨ ind i f = 1 := by
  unfold ind; split_ifs <;> simp

theorem ind_iIndep : (pi fun _ : Fin 20 => coin).iIndepFun ind :=
  (iIndepFun_eval_pi fun _ : Fin 20 => coin).comp fun _ b => if b = true then (1 : ℝ) else 0

theorem expect_ind : (pi fun _ : Fin 20 => coin).expect (fun f => ∑ i, ind i f) = 10 := by
  rw [expect_sum_of_zero_or_one ind_zero_or_one]
  have e : ∀ i : Fin 20, (pi fun _ : Fin 20 => coin).prob {f | ind i f = 1} = 1 / 2 := by
    intro i
    have : {f : Fin 20 → Bool | ind i f = 1} = {f | f i = true} := by
      ext f
      simp only [Set.mem_ofPred_eq]
      unfold ind
      split_ifs with h <;> simp [h]
    rw [this]
    exact prob_pi_bernoulli_apply (fun _ : Fin 20 => (1 / 2 : ℝ)) (fun _ => by norm_num)
      (fun _ => by norm_num) i
  simp only [e, sum_const, card_univ, Fintype.card_fin]
  norm_num

/-- Upper tail (a) with `μ = E X = 10`, `δ = 1`: `P(X ≥ 20) ≤ e^{-10/3}`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | (1 + 1) * 10 ≤ ∑ i, ind i f} ≤
    Real.exp (-(1 ^ 2 * 10 / 3)) :=
  chernoffGen_upper ind_zero_or_one ind_iIndep univ expect_ind.le (by norm_num) le_rfl

/-- Lower tail (a) with `μ = 10 ≤ E X`, `δ = 1/2`: `P(X < 5) ≤ e^{-10/8}`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | ∑ i, ind i f < 10 / 2} ≤
    Real.exp (-(10 / 8)) :=
  chernoffGen_lower_half ind_zero_or_one ind_iIndep univ (by norm_num) expect_ind.ge

/-- The tail (b) with `μ = 10`, `j = 30`: `P(X ≥ 30) ≤ 10^30/30!`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | ((30 : ℕ) : ℝ) ≤ ∑ i, ind i f} ≤
    10 ^ 30 / (30 : ℕ).factorial :=
  (chernoffGen_tail_exp ind_zero_or_one ind_iIndep univ expect_ind.le 30).1

/-! ### [s1:citChernoffGen] with hypotheses on the summation range only -/

/-- The summation range `s = {i | i < 10}` of `Fin 20`. -/
def s10 : Finset (Fin 20) := {i | (i : ℕ) < 10}

/-- A family that is an indicator family only on `s10`: outside `s10` it is the constant `5`. -/
noncomputable def ind' (i : Fin 20) (f : Fin 20 → Bool) : ℝ := if (i : ℕ) < 10 then ind i f else 5

theorem ind'_zero_or_one : ∀ i ∈ s10, ∀ f, ind' i f = 0 ∨ ind' i f = 1 := by
  intro i hi f
  have hi' : (i : ℕ) < 10 := by simpa [s10] using hi
  simp only [ind', hi', if_true]
  exact ind_zero_or_one i f

/-- The family `ind'` is not `{0, 1}`-valued on all of `Fin 20`, so the forms of
`chernoffGen_upper` do not apply to it directly. -/
example : ¬ ∀ i f, ind' i f = 0 ∨ ind' i f = 1 := by
  intro h
  rcases h 10 fun _ => true with h | h <;> norm_num [ind'] at h

/-- The summands `ind' i`, `i ∈ s10`, are functions of distinct coordinates, hence independent. -/
theorem ind'_iIndep : (pi fun _ : Fin 20 => coin).iIndepFun fun i : s10 => ind' i :=
  iIndepFun_pi_of_dependsOn (fun _ : Fin 20 => coin) (fun u : s10 => {(u : Fin 20)})
    (fun _ _ huv => Set.disjoint_singleton.2 (Subtype.coe_injective.ne huv))
    (fun (u : s10) f => ind' u f) fun u f f' h => by
      have hu : f u = f' u := h u (Set.mem_singleton _)
      show ind' u f = ind' u f'
      unfold ind' ind
      rw [hu]

theorem expect_ind' : (pi fun _ : Fin 20 => coin).expect (fun f => ∑ i ∈ s10, ind' i f) = 5 := by
  rw [expect_sum_of_zero_or_one_on s10 ind'_zero_or_one]
  have e : ∀ i ∈ s10, (pi fun _ : Fin 20 => coin).prob {f | ind' i f = 1} = 1 / 2 := by
    intro i hi
    have hi' : (i : ℕ) < 10 := by simpa [s10] using hi
    have : {f : Fin 20 → Bool | ind' i f = 1} = {f | f i = true} := by
      ext f
      simp only [Set.mem_ofPred_eq, ind', hi', if_true, ind]
      split_ifs with h <;> simp [h]
    rw [this]
    exact prob_pi_bernoulli_apply (fun _ : Fin 20 => (1 / 2 : ℝ)) (fun _ => by norm_num)
      (fun _ => by norm_num) i
  rw [sum_congr rfl e, sum_const, show s10.card = 10 by decide]
  norm_num

/-- Lower tail (a) with `μ = 5 = E X`, `δ = 1/2`, hypotheses on `s10` only:
`P(X < 5/2) ≤ e^{-5/8}`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | ∑ i ∈ s10, ind' i f < 5 / 2} ≤
    Real.exp (-(5 / 8)) :=
  chernoffGen_lower_half_on s10 ind'_zero_or_one ind'_iIndep (by norm_num) expect_ind'.ge

/-- Upper tail (a) with `μ = 5`, `δ = 1`: `P(X ≥ 10) ≤ e^{-5/3}`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | (1 + 1) * 5 ≤ ∑ i ∈ s10, ind' i f} ≤
    Real.exp (-(1 ^ 2 * 5 / 3)) :=
  chernoffGen_upper_on s10 ind'_zero_or_one ind'_iIndep expect_ind'.le (by norm_num) le_rfl

/-- The tail (b) with `μ = 5`, `j = 20`: `P(X ≥ 20) ≤ 5^20/20! ≤ (5e/20)^20`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | ((20 : ℕ) : ℝ) ≤ ∑ i ∈ s10, ind' i f} ≤
      5 ^ 20 / (20 : ℕ).factorial ∧
    (5 : ℝ) ^ 20 / (20 : ℕ).factorial ≤ (Real.exp 1 * 5 / (20 : ℕ)) ^ 20 :=
  chernoffGen_tail_exp_on s10 ind'_zero_or_one ind'_iIndep expect_ind'.le 20

/-! ### [s1:citChernoff] for a binomial variable -/

/-- `X = fun k => k` on `Bin(10, 1/2)`: `E X = 5`, `P(X > 7.5) ≤ e^{-5/12}`,
`P(X < 2.5) ≤ e^{-5/8}`. -/
example : let B := binomial 10 (1 / 2) (by norm_num) (by norm_num)
    B.expect (fun k => (k : ℝ)) = 10 * (1 / 2) ∧
      B.prob {k | (1 + 1 / 2 : ℝ) * (10 * (1 / 2)) < k} ≤
        Real.exp (-((1 / 2) ^ 2 * (10 * (1 / 2)) / 3)) ∧
      B.prob {k | (k : ℝ) < (1 - 1 / 2) * (10 * (1 / 2))} ≤
        Real.exp (-((1 / 2) ^ 2 * (10 * (1 / 2)) / 2)) := by
  intro B
  have h := chernoff_binomial (μ := B) (X := fun k => k) (n := 10) (p := 1 / 2) (by norm_num)
    (by norm_num) (map_id' _) (δ := 1 / 2) (by norm_num) (by norm_num)
  push_cast at h
  exact h

/-! ### ρ-random subsets and colourings -/

/-- A (1/3)-random subset `T` of `S = {0, …, 29}`: `P(|T| < 5) ≤ e^{-10/8}` (`m = ρ|S| = 10`). -/
example : (rsubset (range 30) (1 / 3) (by norm_num) (by norm_num)).prob
    {T | ((T.card : ℕ) : ℝ) < 10 / 2} ≤ Real.exp (-(10 / 8)) :=
  (isRSubset_rsubset (S := range 30) (by norm_num) (by norm_num)).chernoff_card_lower_half
    (by norm_num) (by simp; norm_num)

/-- A uniform 3-colouring of 30 elements: the colour-0 class has fewer than 5 elements with
probability at most `e^{-10/8}` (`m = |E|/k = 10`). -/
example : (randColouring (Fin 30) 3).prob
    {c | (#{e ∈ (univ : Finset (Fin 30)) | c e = 0} : ℝ) < 10 / 2} ≤ Real.exp (-(10 / 8)) :=
  chernoff_randColouring_lower_half univ 0 (by norm_num) (by simp; norm_num)

/-! ### Indicators that are functions of disjoint blocks of coordinates -/

/-- The first coin of pair `u`. -/
def fstC (u : Fin 10) : Fin 20 := ⟨2 * u.val, by have := u.isLt; omega⟩

/-- The second coin of pair `u`. -/
def sndC (u : Fin 10) : Fin 20 := ⟨2 * u.val + 1, by have := u.isLt; omega⟩

/-- The event "both coins of pair `u` are heads". -/
def bothHeads (u : Fin 10) : Set (Fin 20 → Bool) := {f | f (fstC u) = true ∧ f (sndC u) = true}

theorem prob_bothHeads (u : Fin 10) : (pi fun _ : Fin 20 => coin).prob (bothHeads u) = 1 / 4 := by
  have hne : fstC u ≠ sndC u := by simp [fstC, sndC, Fin.ext_iff]
  have e : bothHeads u =
      {f | ∀ i ∈ ({fstC u, sndC u} : Finset (Fin 20)), f i ∈ ({true} : Set Bool)} := by
    ext f; simp [bothHeads]
  rw [e, prob_pi_forall_mem, prod_pair hne, prob_bernoulli_true]
  norm_num

/-- 20 fair coins grouped in 10 disjoint pairs `{2u, 2u+1}`; the events "both coins of pair `u`
are heads" have probability `1/4` and depend on disjoint blocks. With `m = 10 · 1/4` and
`δ = 1`: `P(#{u | both heads} ≥ 5) ≤ e^{-(5/2)/3}`. -/
example : (pi fun _ : Fin 20 => coin).prob {f | (1 + 1 : ℝ) * (10 * (1 / 4)) ≤
      ∑ u : Fin 10, (bothHeads u).indicator 1 f} ≤
      Real.exp (-(1 ^ 2 * (10 * (1 / 4)) / 3)) := by
  refine chernoff_pi_dependsOn_upper (fun _ : Fin 20 => coin) (univ : Finset (Fin 10))
    (fun u => {fstC u, sndC u}) ?_ bothHeads ?_ ?_ (by norm_num) le_rfl
  · intro u _ v _ huv
    rw [Set.disjoint_iff]
    rintro x ⟨hx, hy⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    apply huv
    ext
    rcases hx with rfl | rfl <;> rcases hy with h | h <;>
      simp [fstC, sndC, Fin.ext_iff] at h <;> omega
  · intro u _ f g hfg hf
    have h1 := hfg (fstC u) (by simp)
    have h2 := hfg (sndC u) (by simp)
    simp only [bothHeads, Set.mem_ofPred_eq] at hf ⊢
    rw [← h1, ← h2]
    exact hf
  · simp only [prob_bothHeads, sum_const, card_univ, Fintype.card_fin]
    norm_num

end EGTest.Chernoff
