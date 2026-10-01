import EG.Lib.Prob.Indep

/-!
Sanity checks for `EG.FinDist` (PLAN §3 decision 3): Bernoulli(1/2) probabilities, a product of
two fair coins, finite products and a union-bound use, Markov, conditioning, uniform
distributions, random colourings and ρ-random subsets; the fix-round-1 additions (coordinatewise
maps of products, mutual independence of blocks, the `IndepFun` / `iIndepFun` / `IsRSubset`
vocabulary, almost-sure Markov).
-/

namespace EGTest.Prob

open EG EG.FinDist Finset

/-- A fair coin. -/
noncomputable abbrev coin : FinDist Bool := bernoulli (1 / 2) (by norm_num) (by norm_num)

/-! ### Bernoulli(1/2) -/

example : coin.prob {true} = 1 / 2 := prob_bernoulli_true _ _

example : coin.prob {false} = 1 / 2 := by
  rw [prob_bernoulli_false]; norm_num

example : coin.prob Set.univ = 1 := prob_univ _

example : coin.expect (fun b => if b then 1 else 0) = 1 / 2 := by
  rw [expect_bernoulli]; norm_num

/-- The Bernoulli weights, straight from the definition. -/
example : coin.w true = 1 / 2 ∧ coin.w false = 1 / 2 := by
  refine ⟨rfl, ?_⟩
  show 1 - 1 / 2 = (1 / 2 : ℝ)
  norm_num

/-! ### Product of two fair coins -/

example : (coin.prod coin).prob {(true, true)} = 1 / 4 := by
  rw [prob_singleton, prod_w]; norm_num

/-- Every outcome of two fair coins has weight 1/4. -/
example (p : Bool × Bool) : (coin.prod coin).w p = 1 / 4 := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> (rw [prod_w]; norm_num)

/-- The first coin is fair. -/
example : (coin.prod coin).prob {p | p.1 = true} = 1 / 2 := by
  have := prob_prod_fst coin coin {true}
  rw [prob_bernoulli_true] at this
  exact this

/-- `P(both heads) = P(head) · P(head)` (independence). -/
example : (coin.prod coin).prob ({true} ×ˢ {true}) = 1 / 4 := by
  rw [prob_prod_set_prod, prob_bernoulli_true]; norm_num

/-- `P(the coins agree) = 1/2`, by conditioning on the first coin. -/
example : (coin.prod coin).prob {p | p.1 = p.2} = 1 / 2 := by
  rw [prob_prod_eq_sum, Fintype.sum_bool]
  have ht : Prod.mk true ⁻¹' {p : Bool × Bool | p.1 = p.2} = {true} := by
    ext b; cases b <;> simp
  have hf : Prod.mk false ⁻¹' {p : Bool × Bool | p.1 = p.2} = {false} := by
    ext b; cases b <;> simp
  rw [ht, hf, prob_bernoulli_true, prob_bernoulli_false]
  norm_num

/-- `P(at least one head) = 3/4`, by complement and independence. -/
example : (coin.prod coin).prob {p | p.1 = true ∨ p.2 = true} = 3 / 4 := by
  have hc : {p : Bool × Bool | p.1 = true ∨ p.2 = true}ᶜ = {false} ×ˢ {false} := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp
  have h := prob_compl (coin.prod coin) {p : Bool × Bool | p.1 = true ∨ p.2 = true}
  rw [hc, prob_prod_set_prod, prob_bernoulli_false] at h
  linarith

/-- Fubini, first coordinate outside, on an explicit function. -/
example : (coin.prod coin).expect (fun p => if p.1 && p.2 then 4 else 0) = 1 := by
  rw [expect_prod, expect_bernoulli, expect_bernoulli, expect_bernoulli]
  norm_num

/-- Fubini, second coordinate outside (`expect_prod_swap`), on a function that is not
symmetric in the two coordinates. -/
example : (coin.prod coin).expect (fun p => if p.1 then (if p.2 then 4 else 2) else 0) = 3 / 2 := by
  rw [expect_prod_swap, expect_bernoulli, expect_bernoulli, expect_bernoulli]
  norm_num

/-! ### Finite products and a union bound -/

/-- Three independent coins with head probability 1/10. -/
noncomputable abbrev coins3 : FinDist (Fin 3 → Bool) :=
  pi fun _ : Fin 3 => bernoulli (1 / 10) (by norm_num) (by norm_num)

/-- Each coordinate has the right law. -/
example (i : Fin 3) : coins3.prob {f | f i = true} = 1 / 10 := by
  have := prob_pi_eval (fun _ : Fin 3 => bernoulli (1 / 10) (by norm_num) (by norm_num)) i {true}
  rw [prob_bernoulli_true] at this
  exact this

/-- Union bound: `P(some head) ≤ 3/10`. -/
example : coins3.prob {f | ∃ i, f i = true} ≤ 3 / 10 := by
  have hU : {f : Fin 3 → Bool | ∃ i, f i = true} = ⋃ i, {f | f i ∈ ({true} : Set Bool)} := by
    ext f; simp
  rw [hU]
  refine (prob_iUnion_le _ _).trans (le_of_eq ?_)
  simp only [prob_pi_eval, prob_bernoulli_true, sum_const, card_univ, Fintype.card_fin]
  norm_num

/-- Independence: `P(all heads) = (1/10)^3`. -/
example : coins3.prob {f | ∀ i ∈ univ, f i ∈ ({true} : Set Bool)} = (1 / 10) ^ 3 := by
  rw [prob_pi_forall_mem]
  simp

/-- Existence from the union bound: some outcome of positive weight has no heads. -/
example : ∃ f : Fin 3 → Bool, 0 < coins3.w f ∧ ∀ i, f i = false := by
  obtain ⟨f, hf, h⟩ := coins3.exists_forall_notMem_of_sum_lt_one univ
    (fun i => {f : Fin 3 → Bool | f i ∈ ({true} : Set Bool)}) (by
      simp only [prob_pi_eval, prob_bernoulli_true, sum_const, card_univ, Fintype.card_fin]
      norm_num)
  exact ⟨f, hf, fun i => by simpa using h i (mem_univ i)⟩

/-! ### Markov and conditioning -/

/-- Markov (a) on a fair coin. -/
example : 2 / 3 ≤ coin.prob {b | (if b then (1 : ℝ) else 0) ≤ 3 * coin.expect
    (fun b => if b then 1 else 0)} :=
  coin.two_thirds_le_prob_le_three_mul_expect fun b => by cases b <;> norm_num

/-- Conditioning a fair coin on heads gives the point mass at heads. -/
example (h : 0 < coin.prob {true}) : coin.cond {true} h = dirac true := by
  ext b
  rw [cond_w, prob_bernoulli_true]
  cases b
  · rw [Set.indicator_of_notMem (by simp), dirac_w_of_ne (by simp), zero_div]
  · rw [Set.indicator_of_mem (Set.mem_singleton true), dirac_w_self]; norm_num

/-! ### Uniform distributions and random colourings -/

example : (uniform (Fin 6)).prob {x | x.val < 2} = 1 / 3 := by
  rw [prob_uniform]
  simp only [Fintype.card_fin]
  have : (univ.filter fun x : Fin 6 => x ∈ {x : Fin 6 | x.val < 2}).card = 2 := by decide
  rw [this]
  norm_num

/-- Uniform 3-colouring of 5 elements: each element gets colour 0 with probability 1/3. -/
example (e : Fin 5) : (randColouring (Fin 5) 3).prob {c | c e = 0} = 1 / 3 := by
  rw [prob_randColouring_apply]; norm_num

example (c : Fin 5 → Fin 3) : (randColouring (Fin 5) 3).w c = (1 / 3) ^ 5 := by
  rw [randColouring_w]; norm_num

/-! ### ρ-random subsets -/

/-- A (1/3)-random subset of `{0, 1}`: the subset `{0}` has probability (1/3)(2/3) = 2/9. -/
example : (rsubset ({0, 1} : Finset ℕ) (1 / 3) (by norm_num) (by norm_num)).w {0} = 2 / 9 := by
  rw [rsubset_w, if_pos (by decide)]
  have h1 : ({0} : Finset ℕ).card = 1 := rfl
  have h2 : (({0, 1} : Finset ℕ) \ {0}).card = 1 := by decide
  rw [h1, h2]
  norm_num

/-- Subsets not contained in `S` have weight zero. -/
example : (rsubset ({0, 1} : Finset ℕ) (1 / 3) (by norm_num) (by norm_num)).w {2} = 0 := by
  rw [rsubset_w, if_neg (by decide)]

example : (rsubset ({0, 1, 2} : Finset ℕ) (1 / 3) (by norm_num) (by norm_num)).prob
    {T | 1 ∈ T} = 1 / 3 :=
  prob_mem_rsubset _ _ (by decide)

example : (rsubset ({0, 1, 2} : Finset ℕ) (1 / 3) (by norm_num) (by norm_num)).expect
    (fun T => (T.card : ℝ)) = 1 := by
  rw [expect_card_rsubset]
  norm_num

/-- A colour class of a uniform 2-colouring of `Fin 4` is a (1/2)-random subset. -/
example (j : Fin 2) :
    (randColouring (Fin 4) 2).map (fun c => univ.filter fun e => c e = j) =
      rsubset univ (1 / 2) (by norm_num) (by norm_num) := by
  have := map_colourClass_randColouring (ι := Fin 4) j (by norm_num) (by norm_num)
  norm_num at this ⊢
  exact this

/-! ### Fix round 1: coordinatewise maps, blocks, vocabulary -/

/-- `map_prod_map`: negating both fair coins gives two fair coins. -/
example : (coin.prod coin).map (Prod.map (!·) (!·)) = coin.prod coin := by
  rw [map_prod_map]
  have : coin.map (!·) = coin :=
    map_eq_bernoulli (by norm_num) (by norm_num) _ _ (by
      have e : {b : Bool | (!b) = true} = {false} := by ext b; cases b <;> simp
      rw [e, prob_bernoulli_false]; norm_num)
  rw [this]

/-- `map_pi`: coordinatewise, the indicators "colour = 0" of a 3-colouring of `Fin 4` are
independent Bernoulli(1/3) coins. -/
example : (randColouring (Fin 4) 3).map (fun c i => decide (c i = 0)) =
    pi fun _ : Fin 4 => bernoulli (1 / 3) (by norm_num) (by norm_num) := by
  rw [randColouring, map_pi _ fun _ c => decide (c = (0 : Fin 3))]
  have := map_decide_eq_uniform (k := 3) 0 (by norm_num) (by norm_num)
  norm_num at this
  simp only [this]

/-- Two distinct coins of a family of independent fair coins agree with probability 1/2. -/
theorem coins_agree {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    (pi fun _ : ι => coin).prob {g | g i = g j} = 1 / 2 := by
  have e : {g : ι → Bool | g i = g j} =
      {g | g i = true ∧ g j = true} ∪ {g | g i = false ∧ g j = false} := by
    ext g; cases hi : g i <;> cases hj : g j <;> simp [hi, hj]
  rw [e, prob_union_of_disjoint]
  · have e1 : {g : ι → Bool | g i = true ∧ g j = true} =
        {g | ∀ l ∈ ({i, j} : Finset ι), g l ∈ ({true} : Set Bool)} := by
      ext g; simp
    have e2 : {g : ι → Bool | g i = false ∧ g j = false} =
        {g | ∀ l ∈ ({i, j} : Finset ι), g l ∈ ({false} : Set Bool)} := by
      ext g; simp
    rw [e1, e2, prob_pi_forall_mem, prob_pi_forall_mem, prod_pair hij, prod_pair hij,
      prob_bernoulli_true, prob_bernoulli_false]
    norm_num
  · rw [Set.disjoint_left]
    rintro g ⟨h1, -⟩ ⟨h2, -⟩
    rw [h1] at h2
    exact Bool.false_ne_true h2.symm

/-- Mutual independence of blocks (`prob_pi_forall_of_dependsOn`): four independent fair coins
indexed by `Fin 2 × Fin 2`; the events "coins `(u, 0)` and `(u, 1)` agree" (`u = 0, 1`) depend
on the disjoint blocks `{(u, 0), (u, 1)}`, so both hold with probability `1/2 · 1/2`. -/
example : (pi fun _ : Fin 2 × Fin 2 => coin).prob
    {f | ∀ u ∈ (univ : Finset (Fin 2)), f ∈ ({g | g (u, 0) = g (u, 1)} : Set _)} = 1 / 4 := by
  rw [prob_pi_forall_of_dependsOn _ univ (fun u : Fin 2 => {i : Fin 2 × Fin 2 | i.1 = u})]
  · rw [prod_congr rfl fun u _ => coins_agree (by simp : ((u, 0) : Fin 2 × Fin 2) ≠ (u, 1)),
      prod_const, card_univ, Fintype.card_fin]
    norm_num
  · exact fun u _ v _ huv => Set.disjoint_left.2 fun i (hu : i.1 = u) (hv : i.1 = v) =>
      huv (hu.symm.trans hv)
  · intro u _ f g hfg hf
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [← hfg (u, 0) rfl, ← hfg (u, 1) rfl, hf]

/-- The ambient colour class: the edges of colour `j` in a uniform 2-colouring of the elements
of `E = {0, 1, 2}` form a (1/2)-random subset of `E`. -/
example (j : Fin 2) :
    (randColouring ({0, 1, 2} : Finset ℕ) 2).map
        (fun c => selectSet {0, 1, 2} fun e => decide (c e = j)) =
      rsubset {0, 1, 2} (1 / 2) (by norm_num) (by norm_num) := by
  have := map_selectSet_randColouring (k := 2) ({0, 1, 2} : Finset ℕ) j (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  exact this

/-- `IsRSubset` from independent Bernoulli indicators, and a consequence: `E|V| = ρ|S|`. -/
example : (pi fun _ : ({0, 1, 2} : Finset ℕ) => coin).IsRSubset
    (fun f => selectSet {0, 1, 2} fun a => f a) {0, 1, 2} (1 / 2) :=
  isRSubset_selectSet (by norm_num) (by norm_num) (iIndepFun_eval_pi _) fun a => by
    have := prob_pi_eval (fun _ : ({0, 1, 2} : Finset ℕ) => coin) a {true}
    rw [prob_bernoulli_true] at this
    exact this

example {Ω : Type*} (μ : FinDist Ω) (V : Ω → Finset ℕ)
    (h : μ.IsRSubset V {0, 1, 2} (1 / 2)) : μ.expect (fun ω => ((V ω).card : ℝ)) = 3 / 2 := by
  rw [h.expect_card]
  norm_num

/-- The elementwise reading of `IsRSubset` recovers the marginals. -/
example {Ω : Type*} (μ : FinDist Ω) (V : Ω → Finset ℕ)
    (h : μ.IsRSubset V {0, 1, 2} (1 / 3)) : μ.prob {ω | 2 ∈ V ω} = 1 / 3 :=
  ((isRSubset_iff).1 h).2.2.2.2 2 (by decide)

/-- `IndepFun`: the two coordinates of a product; conditioning on the first leaves the law of
the second unchanged ([s1:citMarkov](c)). -/
example (h : 0 < (coin.prod coin).prob (Prod.fst ⁻¹' {true})) :
    ((coin.prod coin).cond (Prod.fst ⁻¹' {true}) h).map Prod.snd = coin := by
  rw [(indepFun_fst_snd coin coin).map_cond, map_snd_prod]

/-- A uniform 2-colouring of `Fin 2` together with an independent (1/3)-random subset of
`{0, 1, 2}`. -/
noncomputable abbrev colSet : FinDist ((Fin 2 → Fin 2) × Finset ℕ) :=
  (randColouring (Fin 2) 2).prod (rsubset {0, 1, 2} (1 / 3) (by norm_num) (by norm_num))

theorem colSet_isRSubset : colSet.IsRSubset Prod.snd {0, 1, 2} (1 / 3) :=
  ⟨by norm_num, by norm_num, map_snd_prod _ _⟩

/-- "A ρ-random subset, independent of the colouring" (`IsRSubset.cond_of_indepFun`): after
fixing the colouring, the set still contains `2` with probability 1/3. -/
example (x : Fin 2 → Fin 2) (hx : 0 < colSet.prob (Prod.fst ⁻¹' {x})) :
    (colSet.cond (Prod.fst ⁻¹' {x}) hx).prob {ω | 2 ∈ ω.2} = 1 / 3 :=
  (colSet_isRSubset.cond_of_indepFun (indepFun_fst_snd _ _) x hx).prob_mem (by decide)

/-- The joint law of the colouring and the set (`IsRSubset.map_pair_eq_prod`). -/
example : colSet.map (fun ω => (ω.1, ω.2)) =
    (colSet.map Prod.fst).prod (rsubset {0, 1, 2} (1 / 3) (by norm_num) (by norm_num)) :=
  colSet_isRSubset.map_pair_eq_prod (indepFun_fst_snd _ _)

/-- `iIndepFun`: pairwise independence of two coordinates of a finite product. -/
example : (pi fun _ : Fin 3 => coin).IndepFun (fun f => f 0) (fun f => f 2) :=
  (iIndepFun_eval_pi fun _ : Fin 3 => coin).indepFun (by decide)

/-- Markov (a), almost-sure form: `X` is negative on an outcome of weight zero. -/
example : 2 / 3 ≤ (dirac true).prob
    {b | (if b then (1 : ℝ) else -1) ≤ 3 * (dirac true).expect (fun b => if b then 1 else -1)} :=
  (dirac true).two_thirds_le_prob_le_three_mul_expect_ae fun b hb => by
    cases b
    · rw [dirac_w_of_ne (by simp)] at hb
      exact absurd hb (lt_irrefl 0)
    · norm_num

end EGTest.Prob
