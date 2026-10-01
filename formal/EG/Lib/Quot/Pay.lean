module

public import EG.Lib.Quot.E2
public import EG.Lib.Quot.Injection
public import EG.Lib.Quot.Items
public import EG.Lib.Quot.Cuckoo
public import EG.Lib.Quot.Junction
public import EG.Lib.Quot.ListAux
public import EG.Lib.Prob.Indep
public import EG.Proof.Num.WellDef

/-!
# Payments of the round step (manuscript s7:lemPay), round level

Universe-polymorphic lemmas for Lemma s7:lemPay on an abstract valid round input `I`
(`RoundInput.Valid`) with valid fixed rules `R`:

* (a1) `card_Jlost_le`: `|J^lost_l| ≤ (M_l − 1)|Lost_l|` ("every `J^lost` edge joins a vertex of
  `Lost_l` to a port, and every vertex carries at most `M_l − 1` J-edges by (J2)");
* (b) `card_unpairedLegs_filter_le`, `card_unpairedLegs_le`: at most one unpaired fresh leg at
  every fresh centre, so at most `|⋃_Z F_Z|` of them;
* (c) SDR: `prob_not_sdrExists_le` (Lemma s7:lemWellDef (iii) on `Type*`, the proof of
  `EG.cuckooSDR`), `expect_sdrPaid_le`: `E[SDR-failure payments] ≤ n(M_l − 1)(4M_l)^{-4}` ("A port
  `u` pays at most `M_l − 1` items for an SDR failure, and it fails with probability at most
  `(4M_l)^{-4}`"; there are at most `n` ports);
* (c) loops: `prob_looped_le` ("A PAR object has its two ends at distinct ports `p ≠ q`. Their
  junctions are independent, and the junction at `q` is uniform on a set of size at least
  `Hcd_l/2` (Lemma s7:lemWellDef (v)). So the probability that the two junctions coincide is
  `Σ_w P(p → w) P(q → w) ≤ max_w P(q → w) ≤ 2/Hcd_l`"), `expect_loopPaid_le` ("A looped object
  costs at most two edges"), `card_parObjs_le'` (`#PAR objects ≤ |J_l| ≤ n(M_l − 1)`).
-/

public section

namespace EG.Quot

open EG.HB EG.Chain EG.FinDist Finset

/-- The probabilities of the pairwise disjoint events `{X = some w}` (`w ∈ s`) sum to at most `1`. -/
theorem sum_prob_eq_some_le_one {Ω W : Type*} (μ : FinDist Ω) (X : Ω → Option W)
    (s : Finset W) : ∑ w ∈ s, μ.prob {ω | X ω = some w} ≤ 1 := by
  classical
  rw [← μ.expect_sum_indicator]
  refine μ.expect_le_of_le fun ω => ?_
  rcases hX : X ω with _ | v
  · have : ∀ w ∈ s, ({ω' | X ω' = some w} : Set Ω).indicator (1 : Ω → ℝ) ω = 0 := by
      intro w _
      simp [Set.indicator, hX]
    rw [sum_congr rfl this, sum_const_zero]
    norm_num
  · have : ∀ w ∈ s, ({ω' | X ω' = some w} : Set Ω).indicator (1 : Ω → ℝ) ω =
        if v = w then 1 else 0 := by
      intro w _
      by_cases h : v = w
      · subst h; simp [Set.indicator, hX]
      · simp [Set.indicator, hX, h]
    rw [sum_congr rfl this, sum_ite_eq]
    split_ifs <;> norm_num

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

/-! ## (a1) -/

/-- [s7:lemPay] (a1) "`|J^lost_l| ≤ (M_l − 1)|Lost_l|`". -/
theorem card_Jlost_le (hI : I.Valid) : I.Jlost.card ≤ I.lost.card * (I.M - 1) := by
  classical
  have hsub : I.Jlost ⊆ I.lost.biUnion (fun v => edgesAt I.J v) := by
    intro e he
    obtain ⟨v, hv, u, -, rfl⟩ := hI.lost_typed e he
    refine mem_biUnion.2 ⟨v, hv, ?_⟩
    simp only [edgesAt, mem_filter]
    exact ⟨RoundInput.mem_J.2 (Or.inl he), Sym2.mem_mk_left v u⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun v hv => ?_
  have hvh : v ∉ I.hubs := fun hh =>
    Finset.disjoint_left.1 hI.roles.2.2.1 hh hv
  exact hI.J2 v hvh

/-! ## (b) -/

/-- [s7:lemPay] (b) "Every fresh centre has at most one unpaired fresh leg per round." -/
theorem card_unpairedLegs_filter_le (hI : I.Valid) (hR : R.Valid) {x : V} (hx : x ∈ I.fresh) :
    (R.unpairedLegs.filter (fun e => x ∈ e)).card ≤ 1 := by
  classical
  -- every unpaired leg at `x` is `s(x, u)` with `leftover (pairing x) = some u`
  have key : ∀ e ∈ R.unpairedLegs.filter (fun e => x ∈ e),
      ∃ u, leftover (R.pairing x) = some u ∧ e = s(x, u) := by
    intro e he
    obtain ⟨he, hxe⟩ := mem_filter.1 he
    obtain ⟨x', hx', he'⟩ := mem_biUnion.1 he
    rw [Option.mem_toFinset] at he'
    obtain ⟨u, hu, rfl⟩ := Option.mem_map.1 he'
    have hup : u ∈ I.ports := by
      have hmem := mem_of_leftover hu
      rw [← List.mem_toFinset, (hR.pairing x' hx').2] at hmem
      exact ((RoundInput.mem_frPorts I).1 hmem).1
    rcases Sym2.mem_iff.1 hxe with rfl | rfl
    · exact ⟨u, hu, rfl⟩
    · exact absurd rfl (RoundInput.fresh_ne_port hI hx hup)
  rw [card_le_one]
  intro e he e' he'
  obtain ⟨u, hu, rfl⟩ := key e he
  obtain ⟨u', hu', rfl⟩ := key e' he'
  rw [hu] at hu'
  cases hu'
  rfl

/-- [s7:lemPay] (b): at most one unpaired fresh leg per fresh centre. -/
theorem card_unpairedLegs_le : R.unpairedLegs.card ≤ I.fresh.card := by
  classical
  refine card_biUnion_le.trans ?_
  rw [card_eq_sum_ones]
  refine sum_le_sum fun x _ => ?_
  rcases leftover (R.pairing x) with _ | u <;> simp

/-! ## (c) SDR failures -/

/-- [s7:lemWellDef] (ii) on `Type*` (the proof of `EG.wellDefLists`): "`3k_h ≤ 4M_l`" for a
non-ultra hub. -/
theorem three_kh_le (hI : I.Valid) {h : V} (hnu : ¬ I.ultra h) : 3 * I.kh h ≤ 4 * I.M := by
  have hM : (2 : ℝ) ^ 40 ≤ (I.M : ℝ) := by exact_mod_cast hI.M_ge
  have hMpos : (0 : ℝ) < I.M := lt_of_lt_of_le (by positivity) hM
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  have hc : (I.clive h : ℝ) ≤ (I.M : ℝ) * I.Hcd / 7 := by
    have h1 : I.clive h ≤ I.thult := not_lt.1 hnu
    have h2 : (I.thult : ℝ) ≤ (I.M : ℝ) * I.Hcd / 7 := by
      show ((⌊(I.M : ℝ) * I.Hcd / 7⌋₊ : ℕ) : ℝ) ≤ _
      exact Nat.floor_le (by positivity)
    exact le_trans (by exact_mod_cast h1) h2
  have hk : 8 * (I.clive h : ℝ) / I.Hcd ≤ 8 * (I.M : ℝ) / 7 := by
    rw [div_le_iff₀ hH]
    have : 8 * (I.M : ℝ) / 7 * I.Hcd = 8 * ((I.M : ℝ) * I.Hcd / 7) := by ring
    rw [this]
    linarith
  have hk1 : I.kh h ≤ ⌈8 * (I.M : ℝ) / 7⌉₊ := Nat.ceil_mono hk
  have hk2 : (I.kh h : ℝ) < 8 * (I.M : ℝ) / 7 + 1 :=
    lt_of_le_of_lt (by exact_mod_cast hk1) (Nat.ceil_lt_add_one (by positivity))
  have : (3 * I.kh h : ℝ) < 4 * (I.M : ℝ) := by nlinarith
  exact_mod_cast this.le

/-- [s7:lemWellDef] (iii) *Cuckoo SDR* on `Type*` (the proof of `EG.cuckooSDR`):
`P(SDR failure at u | Past_l) ≤ (4M_l)^{-4}`. -/
theorem prob_not_sdrExists_le (hI : I.Valid) (hR : R.Valid) {u : V} (hu : u ∈ I.ports) :
    (roundLaw I.G I.M).prob {ξ | ¬ R.SDRExists ξ.1 u} ≤ ((4 * I.M : ℕ) : ℝ) ^ (-4 : ℤ) := by
  have hk : ∀ h ∈ I.hubs, ¬ I.ultra h → 3 * I.kh h ≤ 4 * I.M :=
    fun h _ hnu => three_kh_le hI hnu
  have h1 : (roundLaw I.G I.M).prob {ξ | ¬ R.SDRExists ξ.1 u} =
      (listsLaw I.G I.M).prob {L | ¬ R.SDRExists L u} :=
    FinDist.prob_prod_fst (listsLaw I.G I.M) (ordersLaw I.G) {L | ¬ R.SDRExists L u}
  rw [h1]
  refine (Rules.prob_not_sdr_le hI hR hk hu).trans ?_
  have h2 := numWellDefSDRUse I.M (I.hubItemsAt u).card hI.M_ge
    (RoundInput.card_hubItemsAt_le_M hI hu)
  unfold EG.Spec.numSDRTerm at h2
  exact h2

open Classical in
/-- The SDR-failure payments are the live hub items of the ports without an SDR. -/
theorem card_sdrPaid_le (hI : I.Valid) (L : Lists I.G I.M) :
    ((R.sdrPaid L).card : ℝ) ≤
      ∑ u ∈ I.ports, ((I.M : ℝ) - 1) * (if R.SDRExists L u then (0 : ℝ) else 1) := by
  classical
  have hM1 : 1 ≤ I.M := le_trans (by norm_num) hI.M_ge
  have hsub : I.hubItems.filter (fun it => ¬ R.SDRExists L it.2) ⊆
      (I.ports.filter (fun u => ¬ R.SDRExists L u)).biUnion I.hubItemsAt := by
    intro it hit
    obtain ⟨hit, hns⟩ := mem_filter.1 hit
    refine mem_biUnion.2 ⟨it.2, mem_filter.2 ⟨RoundInput.hubItems_port hit, hns⟩, ?_⟩
    exact (RoundInput.mem_hubItemsAt I).2 ⟨hit, rfl⟩
  have hc : (R.sdrPaid L).card ≤ (I.ports.filter (fun u => ¬ R.SDRExists L u)).card * (I.M - 1) := by
    refine card_image_le.trans ((card_le_card hsub).trans (card_biUnion_le.trans ?_))
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun u hu => RoundInput.card_hubItemsAt_le_M hI (mem_filter.1 hu).1
  have hc' : ((R.sdrPaid L).card : ℝ) ≤
      ((I.ports.filter (fun u => ¬ R.SDRExists L u)).card : ℝ) * ((I.M : ℝ) - 1) := by
    have : (((I.ports.filter (fun u => ¬ R.SDRExists L u)).card * (I.M - 1) : ℕ) : ℝ) =
        ((I.ports.filter (fun u => ¬ R.SDRExists L u)).card : ℝ) * ((I.M : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hM1, Nat.cast_one]
    rw [← this]
    exact_mod_cast hc
  refine hc'.trans (le_of_eq ?_)
  rw [card_filter, Nat.cast_sum, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  by_cases h : R.SDRExists L u <;> simp [h]

/-- [s7:lemPay] (c) "`E[SDR-failure payments | Past_l] ≤ n(M_l − 1)(4M_l)^{-4}`". -/
theorem expect_sdrPaid_le (hI : I.Valid) (hR : R.Valid) :
    (roundLaw I.G I.M).expect (fun ξ => ((R.sdrPaid ξ.1).card : ℝ)) ≤
      (I.G.card : ℝ) * ((I.M : ℝ) - 1) / (4 * (I.M : ℝ)) ^ 4 := by
  classical
  have hM1 : (1 : ℝ) ≤ I.M := by exact_mod_cast le_trans (by norm_num) hI.M_ge
  have hM0 : (0 : ℝ) ≤ (I.M : ℝ) - 1 := by linarith
  have h1 : (roundLaw I.G I.M).expect (fun ξ => ((R.sdrPaid ξ.1).card : ℝ)) ≤
      (roundLaw I.G I.M).expect (fun ξ => ∑ u ∈ I.ports,
        ((I.M : ℝ) - 1) * ({ξ' : Xi I.G I.M | ¬ R.SDRExists ξ'.1 u} : Set _).indicator 1 ξ) := by
    refine expect_mono _ fun ξ => (card_sdrPaid_le hI ξ.1).trans (le_of_eq ?_)
    refine sum_congr rfl fun u _ => ?_
    by_cases h : R.SDRExists ξ.1 u <;> simp [h, Set.indicator]
  refine h1.trans ?_
  rw [expect_sum]
  have h2 : ∀ u ∈ I.ports, (roundLaw I.G I.M).expect (fun ξ =>
      ((I.M : ℝ) - 1) * ({ξ' : Xi I.G I.M | ¬ R.SDRExists ξ'.1 u} : Set _).indicator 1 ξ) ≤
      ((I.M : ℝ) - 1) * (1 / (4 * (I.M : ℝ)) ^ 4) := by
    intro u hu
    rw [expect_const_mul, ← prob_eq_expect]
    refine mul_le_mul_of_nonneg_left ((prob_not_sdrExists_le hI hR hu).trans (le_of_eq ?_)) hM0
    rw [zpow_neg, one_div]
    push_cast
    rfl
  refine (sum_le_sum h2).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hp : (I.ports.card : ℝ) ≤ I.G.card := by exact_mod_cast card_le_card hI.ports_sub
  have hpos : (0 : ℝ) ≤ ((I.M : ℝ) - 1) * (1 / (4 * (I.M : ℝ)) ^ 4) := by positivity
  calc (I.ports.card : ℝ) * (((I.M : ℝ) - 1) * (1 / (4 * (I.M : ℝ)) ^ 4))
      ≤ (I.G.card : ℝ) * (((I.M : ℝ) - 1) * (1 / (4 * (I.M : ℝ)) ^ 4)) :=
        mul_le_mul_of_nonneg_right hp hpos
    _ = (I.G.card : ℝ) * ((I.M : ℝ) - 1) / (4 * (I.M : ℝ)) ^ 4 := by ring

/-! ## (c) loops -/

/-- The junction of the end `e` at the port `x` as a function of the order `≺_x` (the lists `L`
fixed): the element of `C(x) = Cand_l(x) \ Used(x)` at the position of `e` in `E'(x)`. -/
noncomputable def endJ (R : Rules I) (L : Lists I.G I.M) (x : V) (e : REnd V)
    (σ : ↥I.G.verts ≃ Fin I.G.card) : Option V :=
  ((rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map Subtype.val)[
    (R.e2Order L x).idxOf e]?

theorem endJ_mem {L : Lists I.G I.M} {x : V} {e : REnd V} {σ : ↥I.G.verts ≃ Fin I.G.card}
    {w : V} (h : endJ R L x e σ = some w) : w ∈ I.cand x \ R.used L x := by
  have hmem : w ∈ (rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
      Subtype.val := List.mem_of_getElem? h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hmem
  exact Finset.mem_subtype.1 ((mem_rankList _ _ _).1 hy)

/-- [s7:lemPay] (c) "A PAR object has its two ends at distinct ports `p ≠ q`. Their junctions are
independent, and the junction at `q` is uniform on a set of size at least `Hcd_l/2`
(Lemma s7:lemWellDef (v)). So the probability that the two junctions coincide is
`Σ_w P(p → w) P(q → w) ≤ max_w P(q → w) ≤ 2/Hcd_l`" (the lists fixed). -/
theorem prob_looped_le (hI : I.Valid) (hR : R.Valid) (L : Lists I.G I.M) {o : ParObj V}
    (ho : o ∈ R.parObjs) :
    (ordersLaw I.G).prob {O | R.Looped (L, O) o} ≤ 2 / I.Hcd := by
  classical
  have hp : o.endAt false ∈ I.ports := Rules.parObj_end_port hI hR ho false
  have hq : o.endAt true ∈ I.ports := Rules.parObj_end_port hI hR ho true
  have hpq : o.endAt false ≠ o.endAt true := Rules.parObj_ends_ne hI hR ho
  have hep : REnd.par o false ∈ R.E' L (o.endAt false) :=
    (Rules.mem_E').2 (Or.inl ⟨o, ho, false, rfl, rfl⟩)
  have heq : REnd.par o true ∈ R.E' L (o.endAt true) :=
    (Rules.mem_E').2 (Or.inl ⟨o, ho, true, rfl, rfl⟩)
  have hpG : o.endAt false ∈ I.G.verts := hI.ports_sub hp
  have hqG : o.endAt true ∈ I.G.verts := hI.ports_sub hq
  -- the size of `C(q)`
  obtain ⟨O0⟩ : Nonempty (Orders I.G) := inferInstance
  obtain ⟨h1, h2, h3, h4⟩ := Rules.wellDefE2_ineqs hI hR (L, O0) hq
    (Rules.parObj_end_live hI hR ho true)
  have h1' : I.Hcd - ((I.M : ℝ) - 1) ≤
      ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ) := h1
  have h4' : (R.E' L (o.endAt true)).card < I.M := h4
  have hMpos : (0 : ℝ) < I.M := by
    have : (2 : ℝ) ^ 40 ≤ (I.M : ℝ) := by exact_mod_cast hI.M_ge
    linarith [show (0 : ℝ) < 2 ^ 40 by positivity]
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  have hCqH : I.Hcd / 2 ≤ ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ) :=
    h2.trans h1'
  have hCq0 : (0 : ℝ) < ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ) :=
    lt_of_lt_of_le (half_pos hH) hCqH
  have hle : (R.E' L (o.endAt true)).card ≤
      (I.cand (o.endAt true) \ R.used L (o.endAt true)).card := by
    have h5 : ((R.E' L (o.endAt true)).card : ℝ) < I.M := by exact_mod_cast h4'
    have h6 : ((R.E' L (o.endAt true)).card : ℝ) <
        ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ) := by linarith
    exact_mod_cast h6.le
  set Fp := endJ R L (o.endAt false) (REnd.par o false) with hFp
  set Fq := endJ R L (o.endAt true) (REnd.par o true) with hFq
  have hJp : ∀ O : Orders I.G, R.junction (L, O) (.par o false) = Fp (O ⟨_, hpG⟩) := fun O =>
    Rules.e2Junc_eq_endJunc hI hR L O hp hep
  have hJq : ∀ O : Orders I.G, R.junction (L, O) (.par o true) = Fq (O ⟨_, hqG⟩) := fun O =>
    Rules.e2Junc_eq_endJunc hI hR L O hq heq
  -- the law of `Fq` at a point
  have hPq : ∀ w, (ordersLaw I.G).prob {O | Fq (O ⟨_, hqG⟩) = some w} ≤
      1 / ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ) := by
    intro w
    have e : (ordersLaw I.G).prob ((fun O : Orders I.G => O ⟨_, hqG⟩) ⁻¹' {σ | Fq σ = some w}) =
        (FinDist.uniform (↥I.G.verts ≃ Fin I.G.card)).prob {σ | Fq σ = some w} :=
      prob_pi_eval (fun _ : ↥I.G.verts => FinDist.uniform (↥I.G.verts ≃ Fin I.G.card))
        ⟨_, hqG⟩ {σ | Fq σ = some w}
    change (ordersLaw I.G).prob ((fun O : Orders I.G => O ⟨_, hqG⟩) ⁻¹' {σ | Fq σ = some w}) ≤ _
    rw [e]
    by_cases hw : w ∈ I.cand (o.endAt true) \ R.used L (o.endAt true)
    · exact le_of_eq (Rules.prob_endJunc hI hR L hq heq hle hw)
    · have : {σ | Fq σ = some w} = (∅ : Set (↥I.G.verts ≃ Fin I.G.card)) := by
        ext σ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hw (endJ_mem h)
      rw [this, prob_empty]
      positivity
  -- independence of the coordinates `≺_p`, `≺_q`
  have hind : (ordersLaw I.G).IndepFun (fun O : Orders I.G => O ⟨_, hpG⟩)
      (fun O : Orders I.G => O ⟨_, hqG⟩) := by
    have := iIndepFun_eval_pi (fun _ : ↥I.G.verts => FinDist.uniform (↥I.G.verts ≃ Fin I.G.card))
    exact this.indepFun (fun h => hpq (congrArg Subtype.val h))
  -- the union bound over the common junction `w ∈ C(q)`
  have hsub : {O : Orders I.G | R.Looped (L, O) o} ⊆
      ⋃ w ∈ I.cand (o.endAt true) \ R.used L (o.endAt true),
        ((fun O : Orders I.G => O ⟨_, hpG⟩) ⁻¹' {σ | Fp σ = some w} ∩
          (fun O : Orders I.G => O ⟨_, hqG⟩) ⁻¹' {σ | Fq σ = some w}) := by
    intro O hO
    obtain ⟨w, hw1, hw2⟩ := hO
    rw [hJp] at hw1
    rw [hJq] at hw2
    exact Set.mem_biUnion (endJ_mem hw2) ⟨hw1, hw2⟩
  refine (prob_mono _ hsub).trans ((prob_biUnion_le _ _ _).trans ?_)
  have hterm : ∀ w ∈ I.cand (o.endAt true) \ R.used L (o.endAt true), (ordersLaw I.G).prob
      ((fun O : Orders I.G => O ⟨_, hpG⟩) ⁻¹' {σ | Fp σ = some w} ∩
        (fun O : Orders I.G => O ⟨_, hqG⟩) ⁻¹' {σ | Fq σ = some w}) ≤
      (ordersLaw I.G).prob {O | Fp (O ⟨_, hpG⟩) = some w} *
        (1 / ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ)) := by
    intro w _
    rw [hind {σ | Fp σ = some w} {σ | Fq σ = some w}]
    exact mul_le_mul_of_nonneg_left (hPq w) (prob_nonneg _ _)
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_mul]
  have hs := sum_prob_eq_some_le_one (ordersLaw I.G) (fun O => Fp (O ⟨_, hpG⟩))
    (I.cand (o.endAt true) \ R.used L (o.endAt true))
  calc (∑ w ∈ I.cand (o.endAt true) \ R.used L (o.endAt true),
          (ordersLaw I.G).prob {O | Fp (O ⟨_, hpG⟩) = some w}) *
        (1 / ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ))
      ≤ 1 * (1 / ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ)) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 1 / ((I.cand (o.endAt true) \ R.used L (o.endAt true)).card : ℝ) := one_mul _
    _ ≤ 1 / (I.Hcd / 2) := one_div_le_one_div_of_le (half_pos hH) hCqH
    _ = 2 / I.Hcd := by field_simp

open Classical in
/-- A looped object costs at most two edges. -/
theorem card_loopPaid_le (ξ : Xi I.G I.M) :
    (R.loopPaid ξ).card ≤ 2 * (R.parObjs.filter (R.Looped ξ)).card := by
  classical
  refine card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun o _ => (List.toFinset_card_le _).trans ?_
  cases o <;> simp [ParObj.edgeList]

/-- [s7:lemPay] (c) "`E[loop-paid edges | Past_l] ≤ 2·(2/Hcd_l)·#{PAR objects}`". -/
theorem expect_loopPaid_le (hI : I.Valid) (hR : R.Valid) :
    (roundLaw I.G I.M).expect (fun ξ => ((R.loopPaid ξ).card : ℝ)) ≤
      2 * (2 / I.Hcd) * (R.parObjs.card : ℝ) := by
  classical
  have h1 : (roundLaw I.G I.M).expect (fun ξ => ((R.loopPaid ξ).card : ℝ)) ≤
      (roundLaw I.G I.M).expect (fun ξ => 2 * ((R.parObjs.filter
        (fun o => ξ ∈ {ξ' : Xi I.G I.M | R.Looped ξ' o})).card : ℝ)) := by
    refine expect_mono _ fun ξ => ?_
    have := card_loopPaid_le (R := R) ξ
    exact_mod_cast this
  refine h1.trans ?_
  rw [expect_const_mul, expect_card_filter]
  have h2 : ∀ o ∈ R.parObjs, (roundLaw I.G I.M).prob {ξ' : Xi I.G I.M | R.Looped ξ' o} ≤
      2 / I.Hcd := by
    intro o ho
    unfold roundLaw
    rw [prob_prod]
    exact expect_le_of_le _ fun L => prob_looped_le hI hR L ho
  have h3 := sum_le_sum h2
  rw [sum_const, nsmul_eq_mul] at h3
  nlinarith

/-- There are at most `|J_l| ≤ n(M_l − 1)` PAR objects (`o ↦` its J-edge at the end `false`). -/
theorem card_parObjs_le' (hI : I.Valid) (hR : R.Valid) :
    R.parObjs.card ≤ I.G.card * (I.M - 1) := by
  refine le_trans ?_ hI.J2tot
  refine card_le_card_of_injOn (fun o => o.jAt false) ?_ ?_
  · intro o ho
    exact RoundInput.live_mem_J ((Rules.parObj_facts hI hR (mem_coe.1 ho)).1 false)
  · intro o ho o' ho' e
    exact Rules.parObj_eq_of_jAt hI hR (mem_coe.1 ho) (mem_coe.1 ho') e

end EG.Quot
