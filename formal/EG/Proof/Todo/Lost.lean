module

public import EG.Spec.Chain.Lost
public import EG.Lib.Chain.LostAux
public import EG.Lib.Gamma.Full
public import EG.Proof.Todo.COL
public import EG.Proof.Todo.LemE1
public import EG.Proof.Todo.LemExpect
public import EG.Proof.HB.TowerBLate
public import EG.Proof.HB.TowerBM

/-!
# P3 stub: `EG.Spec.LostStatement` (s6:lemLost)

Generated at the P2→P3 transition (2026-09-30), proved in P3 (round 1 of P3-s6), following the
manuscript proof:
* (i) the label: `EG.Chain.prob_lost_le`, `EG.Stage1.KJS_mul_rhoJS` (s3:defCOL(iv));
  lend-bad: union bound over "an event of s3:lemCOL(a) or (b) fails" (`EG.Todo.COL`) and "`Y` is
  demoted" (`EG.Todo.LemE1` (b)); size of `V(Y)`: `EG.Chain.card_ancVerts_ge_M` with
  `P_{l-2} ≥ M_l^{13}` (`EG.towerBLate`, s2:lemTower(b)) and `EG.Chain.two_zpow_neg_two_le`;
* (K6): `EG.Chain.expect_card_lostRound_le` (classed ports of one round are disjoint subsets of
  `V(G)`);
* (iii): `EG.Todo.LemExpect` (s5:lemExpect), (K6), and `EG.Chain.sum_lost_cost_le` with
  `Σ_l 1/M_l ≤ 2/D_*` (`EG.towerBM`, s2:lemTower(b)).
Keep the name `EG.Todo.Lost`; consumers import this module.
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot EG.Stage1

universe u

/-- [s6:lemLost] see `EG.Spec.LostStatement`. Proved in P3. -/
theorem Lost : EG.Spec.LostStatement.{u} := by
  intro V _ G N0 Dstar run δ hrun hδ
  have hD : Gamma1core Dstar := hrun.gamma1core
  have hv := hrun.valid
  have hd1 := hrun.le_d_one
  have hD2 : 2 < Dstar := hD.two_lt
  -- P(Y lend-bad) ≤ 2|V(Y)|^{-2}
  have hbad : ∀ Y ∈ run.ancestors G,
      (law G run).prob {ω | lendBad run G (stageOf ω) Y} ≤
        2 * ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) := by
    intro Y hY
    set N : ℝ := ((run.ancVerts G Y).card : ℝ) with hN
    have hN0 : 0 ≤ N ^ (-2 : ℤ) := by positivity
    have hsub : {ω : Outcome G run | lendBad run G (stageOf ω) Y} ⊆
        {ω | run.isLight G Y.1 Y.2 ∧ Light.demoted ω Y} ∪
          {ω | COLa G run Y (ω.cOutAt Y) ∧ COLb G run Y (ω.cOutAt Y) ∧ COLe G run Y}ᶜ := by
      intro ω hω
      rcases hω with h | h | h
      · exact Or.inl h
      · exact Or.inr (fun h' => h h'.1)
      · exact Or.inr (fun h' => h h'.2.1)
    have h1 : (law G run).prob {ω : Outcome G run | run.isLight G Y.1 Y.2 ∧ Light.demoted ω Y} ≤
        N ^ (-2 : ℤ) / 2 := by
      by_cases hl : run.isLight G Y.1 Y.2
      · have hYl : Y ∈ run.lightParts G :=
          (Run.mem_lightParts run G).2 ⟨(Run.mem_ancestors run G).1 hY, hl⟩
        have hE := (EG.Todo.LemE1.{u} V G N0 Dstar run hrun Y hYl).2.1
        calc _ ≤ (law G run).prob {ω | Light.demoted ω Y} :=
              FinDist.prob_mono _ (fun ω h => h.2)
          _ ≤ _ := hE
      · have : {ω : Outcome G run | run.isLight G Y.1 Y.2 ∧ Light.demoted ω Y} = ∅ := by
          ext ω; simp [hl]
        rw [this, FinDist.prob_empty]
        positivity
    have h2 : (law G run).prob
        {ω : Outcome G run | COLa G run Y (ω.cOutAt Y) ∧ COLb G run Y (ω.cOutAt Y) ∧
          COLe G run Y}ᶜ ≤ N ^ (-2 : ℤ) / 2 := by
      have hC := (EG.Todo.COL.{u, u} V G Dstar run hrun.gamma1 hv Y hY).2.2.2.1
        (Outcome G run) (law G run) (fun ω => ω.cOutAt Y) (map_cOutAt G run hY)
      rw [FinDist.prob_compl]
      linarith
    calc _ ≤ _ := FinDist.prob_mono _ hsub
      _ ≤ _ := FinDist.prob_union_le _ _ _
      _ ≤ N ^ (-2 : ℤ) / 2 + N ^ (-2 : ℤ) / 2 := add_le_add h1 h2
      _ ≤ 2 * N ^ (-2 : ℤ) := by linarith
  -- 2|V(Y)|^{-2} ≤ M_l^{-2}
  have hsize : ∀ l : ℕ, 3 ≤ l → l ≤ run.R → ∀ Y ∈ run.ancestors G, Y.1 + 2 ≤ l →
      2 * ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) ≤ (run.M G l : ℝ) ^ (-2 : ℤ) := by
    intro l hl3 hlR Y hY hYl
    have hPM := (EG.towerBLate V G Dstar run hD hv hd1 l hl3 hlR).1
    have hM : (2 : ℝ) ^ 40 ≤ (run.M G l : ℝ) := by exact_mod_cast two_pow_le_M G run l
    exact two_zpow_neg_two_le hM (card_ancVerts_ge_M G run hD2 hv hl3 hlR hY hYl hPM)
  -- (i)
  have hi : ∀ l : ℕ, 3 ≤ l → ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a,
      (law G run).prob {ω | u ∈ lost run G δ (stageOf ω) l a} ≤
          (KJS G run l : ℝ) * rhoJS G run l +
            (law G run).prob {ω | lendBad run G (stageOf ω) (δ l u)} ∧
      (KJS G run l : ℝ) * rhoJS G run l +
            (law G run).prob {ω | lendBad run G (stageOf ω) (δ l u)} ≤
          (run.M G l : ℝ) ^ (-2 : ℤ) + 2 * ((run.ancVerts G (δ l u)).card : ℝ) ^ (-2 : ℤ) ∧
      (run.M G l : ℝ) ^ (-2 : ℤ) + 2 * ((run.ancVerts G (δ l u)).card : ℝ) ^ (-2 : ℤ) ≤
          2 * (run.M G l : ℝ) ^ (-2 : ℤ) := by
    intro l hl3 a ha u hu
    have hlR : l ≤ run.R :=
      (Run.isRound_of_mem_prePartAddrs ((Run.mem_Std_iff run G).1 ha).1).2
    obtain ⟨hYanc, hYl, -⟩ := (Run.mem_anc run G).1 (hδ l hl3 a ha u hu)
    refine ⟨prob_lost_le G run δ hl3 a u hYanc, ?_, ?_⟩
    · rw [Stage1.KJS_mul_rhoJS]
      linarith [hbad _ hYanc]
    · linarith [hsize l hl3 hlR _ hYanc hYl]
  -- (K6)
  have hK6 : ∀ l : ℕ,
      (law G run).expect (fun ω => ((lostRound run G δ (stageOf ω) l).card : ℝ)) ≤
        2 * (G.card : ℝ) / (run.M G l : ℝ) ^ 2 := by
    intro l
    have hp : (0 : ℝ) ≤ 2 * (run.M G l : ℝ) ^ (-2 : ℤ) := by positivity
    have h := expect_card_lostRound_le G run δ l hp (fun a ha u hu => by
      by_cases hl3 : 3 ≤ l
      · obtain ⟨h1, h2, h3⟩ := hi l hl3 a ha u hu
        linarith
      · have : {ω : Outcome G run | u ∈ lost run G δ (stageOf ω) l a} = ∅ := by
          ext ω
          simp [lost_of_le_two run G δ (stageOf ω) (show l ≤ 2 by omega) a]
        rw [this, FinDist.prob_empty]
        exact hp)
    calc _ ≤ _ := h
      _ = 2 * (G.card : ℝ) / (run.M G l : ℝ) ^ 2 := by
        rw [zpow_neg, zpow_ofNat]; ring
  refine ⟨hi, hK6, ?_, ?_⟩
  -- (iii), first inequality
  · have hX : ∀ ω : Outcome G run, (XUOf run G δ ω : ℝ) =
        (80 * (Light.dem ω : ℝ) + 369 * (Light.lp ω : ℝ)) +
          ∑ l ∈ Finset.Icc 1 run.R, (169 + (run.M G l : ℝ)) *
            ((lostRound run G δ (stageOf ω) l).card : ℝ) := by
      intro ω
      show ((80 * (stageOf ω).dem + 369 * (stageOf ω).lp +
        ∑ l ∈ Finset.Icc 1 run.R, (169 + run.M G l) *
          (lostRound run G δ (stageOf ω) l).card : ℕ) : ℝ) = _
      push_cast
      rfl
    rw [FinDist.expect_congr _ (fun ω _ => hX ω), FinDist.expect_add, FinDist.expect_sum]
    have hE := EG.Todo.LemExpect.{u} V G N0 Dstar run hrun
    have hS : ∑ l ∈ Finset.Icc 1 run.R, (law G run).expect (fun ω => (169 + (run.M G l : ℝ)) *
          ((lostRound run G δ (stageOf ω) l).card : ℝ)) ≤
        ∑ l ∈ Finset.Icc 1 run.R,
          2 * (G.card : ℝ) * (169 + (run.M G l : ℝ)) / (run.M G l : ℝ) ^ 2 := by
      refine Finset.sum_le_sum (fun l _ => ?_)
      rw [FinDist.expect_const_mul]
      have hM0 : (0 : ℝ) ≤ 169 + (run.M G l : ℝ) := by positivity
      calc _ ≤ (169 + (run.M G l : ℝ)) * (2 * (G.card : ℝ) / (run.M G l : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (hK6 l) hM0
        _ = _ := by ring
    linarith
  -- (iii), second inequality
  · have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
    have hsum := (EG.towerBM V G Dstar run hD hv hd1).2
    have := sum_lost_cost_le (Finset.Icc 1 run.R) (fun l => (run.M G l : ℝ)) hn
      (by linarith) (fun l _ => by exact_mod_cast two_pow_le_M G run l) hsum
    linarith

end EG.Todo
