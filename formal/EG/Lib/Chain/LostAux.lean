module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Lib.Stage1.Law
public import EG.Lib.Chain.Lending
public import EG.Lib.Chain.Design
public import EG.Lib.Prob.Basic
public import EG.Lib.HB.Run
public import EG.Lib.HB.TowerRun
public import EG.Lib.Lend.Standing

/-!
# Helpers for Lemma "lost ports" (manuscript s6:lemLost)

Unit P3-s6, round 1. Consumed by `EG.Todo.Lost`.
* `prob_labAt_ne_none_le`: "By Definition s3:defCOL(iv), `lab_{Y,l}(u) ≠ ∗` has probability
  `K^JS_l ρ_l = M_l^2 · M_l^{-4} = M_l^{-2}`" (an upper bound; the label is `∗` off the sites);
* `prob_lost_le`: the union bound `P(u ∈ Lost_Z) ≤ P(lab ≠ ∗) + P(Y(u) lend-bad)`;
* `expect_card_lostRound_le`: (K6) from a per-port bound ("round `l` has at most `n` classed
  ports; linearity of expectation").
-/

public section

namespace EG.Chain

open EG.HB EG.Stage1 EG.Quot

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- [s3:defCOL] (iv) "`lab_{Y,l}(u) ≠ ∗` has probability `M_l^{-2}`" (at most, for every `y`: the
label is `∗` off the sites of `Y`). -/
theorem prob_labAt_ne_none_le {Y : PartId} (hY : Y ∈ run.ancestors G) (l : ℕ) (y : V) :
    (law G run).prob {ω | ω.labAt Y l y ≠ none} ≤ (run.M G l : ℝ) ^ (-2 : ℤ) := by
  classical
  by_cases hs : (l, y) ∈ jsSites G run Y
  · let c : Coord G run := Sum.inr (Sum.inr (Sum.inl ⟨⟨Y, hY⟩, ⟨(l, y), hs⟩⟩))
    have hset : {ω : Outcome G run | ω.labAt Y l y ≠ none} =
        (fun ω : Outcome G run => (ω.toCoords c : Option ℕ)) ⁻¹' {o | o ≠ none} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Outcome.labAt, dif_pos hs, Outcome.jsAt,
        dif_pos hY]
      rfl
    have hmap : (law G run).map (fun ω : Outcome G run => (ω.toCoords c : Option ℕ)) =
        jsLabelLaw G run l :=
      map_toCoords_apply G run c
    have key : (jsLabelLaw G run l).prob ({none} : Set (Option ℕ))ᶜ ≤
        (run.M G l : ℝ) ^ (-2 : ℤ) := by
      rw [FinDist.prob_compl, prob_jsLabelLaw_none]
      linarith
    rw [hset, ← FinDist.prob_map, hmap]
    exact key
  · have : {ω : Outcome G run | ω.labAt Y l y ≠ none} = ∅ := by
      ext ω; simp [Outcome.labAt, hs]
    rw [this, FinDist.prob_empty]
    positivity

variable (δ : Designation V)

/-- The union bound of s6:lemLost (i): "`P(u ∈ Lost) ≤ K^JS_l ρ_l + P(Y(u) lend-bad)`", for a
classed port `u` of `Z ∈ Std_l`, `l ≥ 3`, whose ancestor `Y(u)` is an ancestor. -/
theorem prob_lost_le {l : ℕ} (hl : 3 ≤ l) (a : Addr) (u : V) (hY : δ l u ∈ run.ancestors G) :
    (law G run).prob {ω | u ∈ lost run G δ (stageOf ω) l a} ≤
      (KJS G run l : ℝ) * rhoJS G run l +
        (law G run).prob {ω | lendBad run G (stageOf ω) (δ l u)} := by
  rw [Stage1.KJS_mul_rhoJS]
  have hsub : {ω : Outcome G run | u ∈ lost run G δ (stageOf ω) l a} ⊆
      {ω | ω.labAt (δ l u) l u ≠ none} ∪ {ω | lendBad run G (stageOf ω) (δ l u)} := by
    intro ω hω
    have h := ((mem_lost_iff run G δ (stageOf ω) hl).1 hω).2
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc _ ≤ _ := FinDist.prob_mono _ hsub
    _ ≤ _ := FinDist.prob_union_le _ _ _
    _ ≤ _ := by
      have := prob_labAt_ne_none_le G run hY l u
      linarith

/-- (K6), counting step: if every classed port `u ∈ Q_Z` (`Z ∈ Std_l`) is lost with probability
at most `p`, then `E|Lost_l| ≤ p · n` ("round `l` has at most `n` classed ports; linearity of
expectation"). -/
theorem expect_card_lostRound_le (l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (h : ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a,
      (law G run).prob {ω | u ∈ lost run G δ (stageOf ω) l a} ≤ p) :
    (law G run).expect (fun ω => ((lostRound run G δ (stageOf ω) l).card : ℝ)) ≤
      p * (G.card : ℝ) := by
  classical
  have hcard : ∀ ω : Outcome G run, ((lostRound run G δ (stageOf ω) l).card : ℝ) =
      ∑ a ∈ run.Std G l, (((run.classed G l a).filter
        (fun u => ω ∈ {ω' : Outcome G run | u ∈ lost run G δ (stageOf ω') l a})).card : ℝ) := by
    intro ω
    rw [card_lostRound]
    push_cast
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 2
    ext u
    simp only [Set.mem_ofPred_eq, Finset.mem_filter]
    constructor
    · intro hu; exact ⟨lost_subset_classed run G δ _ l a hu, hu⟩
    · intro hu; exact hu.2
  rw [FinDist.expect_congr _ (fun ω _ => hcard ω), FinDist.expect_sum]
  have hstep : ∀ a ∈ run.Std G l,
      (law G run).expect (fun ω => (((run.classed G l a).filter
        (fun u => ω ∈ {ω' : Outcome G run | u ∈ lost run G δ (stageOf ω') l a})).card : ℝ)) ≤
      p * ((run.classed G l a).card : ℝ) := by
    intro a ha
    rw [FinDist.expect_card_filter]
    calc _ ≤ ∑ _u ∈ run.classed G l a, p := Finset.sum_le_sum (fun u hu => h a ha u hu)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc _ ≤ ∑ a ∈ run.Std G l, p * ((run.classed G l a).card : ℝ) := Finset.sum_le_sum hstep
    _ = p * ((classedPorts run G l).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      unfold classedPorts
      rw [Finset.card_biUnion]
      · push_cast; rfl
      · intro a ha b hb hab
        exact classed_disjoint run G (Std_subset_prePartAddrs run G l ha)
          (Std_subset_prePartAddrs run G l hb) hab
    _ ≤ p * (G.card : ℝ) := by
      gcongr
      have hsub : classedPorts run G l ⊆ G.verts := by
        intro u hu
        obtain ⟨a, _, hu⟩ := (mem_classedPorts run G).1 hu
        exact run.Z0_subset_verts G l a
          (ports_subset_Z0 run G l a (classed_subset_ports run G l a hu))
      exact_mod_cast Finset.card_le_card hsub

/-- (i), "Size of `V(Y)`": for an ancestor `Y` of round `r ≤ l - 2` (`3 ≤ l ≤ R`) of a valid run,
`|V(Y)| ≥ λ_r^{103}/2 ≥ λ_{l-2}^{103}/2 ≥ (P_{l-2} - 1)/2`, so `P_{l-2} ≥ M_l^{13}` (Lemma
s2:lemTower(b), the hypothesis `hPM`) gives `|V(Y)| ≥ (M_l^{13} - 1)/2`. -/
theorem card_ancVerts_ge_M {Dstar : ℝ} (hD : 2 < Dstar) (hv : run.Valid G Dstar) {l : ℕ}
    (hl3 : 3 ≤ l) (hlR : l ≤ run.R) {Y : PartId} (hY : Y ∈ run.ancestors G) (hYl : Y.1 + 2 ≤ l)
    (hPM : run.M G l ^ 13 ≤ run.P G (l - 2)) :
    ((run.M G l : ℝ) ^ 13 - 1) / 2 ≤ ((run.ancVerts G Y).card : ℝ) := by
  have hV := EG.Standing.card_ancVerts_ge hY
  have hl2 : l - 2 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hdl : Dstar ≤ run.d G (l - 2) := (hv.1 _ hl2).1
  have hdr : run.d G (l - 2) ≤ run.d G Y.1 := Run.d_anti run G (by omega)
  have hlam : run.lam G (l - 2) ≤ run.lam G Y.1 :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hdr
  have hlam0 : 0 ≤ run.lam G (l - 2) := Real.logb_nonneg (by norm_num) (by linarith)
  have hpow : run.lam G (l - 2) ^ 103 ≤ run.lam G Y.1 ^ 103 := pow_le_pow_left₀ hlam0 hlam _
  have hP : (run.P G (l - 2) : ℝ) < run.lam G (l - 2) ^ 103 + 1 := by
    have h := Nat.ceil_lt_add_one (pow_nonneg hlam0 103)
    have e : run.P G (l - 2) = ⌈run.lam G (l - 2) ^ 103⌉₊ := by
      show POf _ = _
      unfold POf
      rw [show Cp = 103 from rfl]
      rfl
    rw [e]
    exact h
  have hPM' : (run.M G l : ℝ) ^ 13 ≤ (run.P G (l - 2) : ℝ) := by exact_mod_cast hPM
  linarith

/-! ### Arithmetic of s6:lemLost -/

/-- (i), last step: "`2|V(Y)|^{-2} ≤ 8M_l^{-26} ≤ M_l^{-2}`", in the form: if `M ≥ 2^{40}` and
`(M^{13} - 1)/2 ≤ N`, then `2N^{-2} ≤ M^{-2}`. -/
theorem two_zpow_neg_two_le {M N : ℝ} (hM : (2 : ℝ) ^ 40 ≤ M) (hN : (M ^ 13 - 1) / 2 ≤ N) :
    2 * N ^ (-2 : ℤ) ≤ M ^ (-2 : ℤ) := by
  have hM1 : (1 : ℝ) ≤ M := le_trans (by norm_num) hM
  have hM0 : (0 : ℝ) < M := by linarith
  have h11 : (1 : ℝ) ≤ M ^ 11 := one_le_pow₀ hM1
  have h13 : M ^ 2 ≤ M ^ 13 := by
    have : M ^ 13 = M ^ 2 * M ^ 11 := by ring
    rw [this]; nlinarith [sq_nonneg M]
  have hM2 : (2 : ℝ) ^ 40 * M ≤ M ^ 2 := by nlinarith
  have h2M : 2 * M ≤ N := by nlinarith
  have hN0 : 0 < N := by linarith
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have : 2 * M ^ 2 ≤ N ^ 2 := by nlinarith
  calc (2 : ℝ) = 2 * M ^ 2 * (M ^ 2)⁻¹ := by field_simp
    _ ≤ N ^ 2 * (M ^ 2)⁻¹ := by gcongr
    _ = (M ^ 2)⁻¹ * N ^ 2 := by ring

/-- (iii), last step: "`Σ_l(338n/M_l^2 + 2n/M_l) ≤ (2 + 338/2^{40}) n Σ_l 1/M_l ≤
(2 + 338/2^{40}) 2n/D_* ≤ 5.5n/D_*`, using `M_l ≥ 2^{40}` and `Σ_l 1/M_l ≤ 2/D_*`". -/
theorem sum_lost_cost_le {ι : Type*} (s : Finset ι) (M : ι → ℝ) {n D : ℝ} (hn : 0 ≤ n)
    (hD : 0 < D) (hM : ∀ i ∈ s, (2 : ℝ) ^ 40 ≤ M i) (hsum : ∑ i ∈ s, 1 / M i ≤ 2 / D) :
    ∑ i ∈ s, 2 * n * (169 + M i) / M i ^ 2 ≤ 5.5 * n / D := by
  have hterm : ∀ i ∈ s, 2 * n * (169 + M i) / M i ^ 2 ≤ (2 + 338 / 2 ^ 40) * n * (1 / M i) := by
    intro i hi
    have hMi := hM i hi
    have hM0 : 0 < M i := lt_of_lt_of_le (by norm_num) hMi
    rw [div_le_iff₀ (by positivity)]
    have h1 : 338 * n ≤ 338 / 2 ^ 40 * n * M i := by
      have : 338 / 2 ^ 40 * n * M i = 338 * n * (M i / 2 ^ 40) := by ring
      rw [this]
      have : 1 ≤ M i / 2 ^ 40 := by rw [le_div_iff₀ (by norm_num)]; linarith
      nlinarith
    have : (2 + 338 / 2 ^ 40) * n * (1 / M i) * M i ^ 2 = (2 + 338 / 2 ^ 40) * n * M i := by
      field_simp
    rw [this]
    nlinarith
  calc _ ≤ ∑ i ∈ s, (2 + 338 / 2 ^ 40) * n * (1 / M i) := Finset.sum_le_sum hterm
    _ = (2 + 338 / 2 ^ 40) * n * ∑ i ∈ s, 1 / M i := by rw [Finset.mul_sum]
    _ ≤ (2 + 338 / 2 ^ 40) * n * (2 / D) := by gcongr
    _ ≤ 5.5 * n / D := by
      rw [show (2 + 338 / 2 ^ 40) * n * (2 / D) = ((2 + 338 / 2 ^ 40) * 2) * n / D by ring]
      gcongr
      norm_num

end EG.Chain
