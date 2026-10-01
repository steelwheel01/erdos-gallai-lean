module

public import EG.Spec.Quot.Cost
public import EG.Proof.Todo.MixC
public import EG.Proof.Todo.MixCConc
public import EG.Proof.Todo.PayGlobal
public import EG.Proof.Todo.OneOutcomeRound
public import EG.Proof.Todo.EXprime
public import EG.Lib.Quot.CostRound

/-!
# P3 stub: `EG.Spec.CostStatement` (s7:propCost)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.Cost`; consumers import this module.

Proof (manuscript s7:propCost). "By Lemma s7:lemLift (iv), the round step is a J-consumer": the
past of every round is valid (`EG.Quot.ofPast_valid`, OBL-P1-1), so `roundOut` satisfies (JC1),
(JC2) (`EG.liftJConsumerRun_univ`). "So Theorem s6:thmMIXC applies" (`EG.Todo.MixC`, with the
per-round bound `b l J := |Obj_l(J)|`), and "By Theorem s6:thmCONCL(iv),
`1.5 Σ m_{Y,l} ≤ 1.5 ε_CONC(D_*) n`" (`EG.Todo.MixCConc`). "The objects of `Obj_l` are the paid
single edges and the lifted objects" (`EG.Quot.card_roundOut_le`: s7:lemPay (a1)–(a3), s7:lemLift
(iv)); "at most `2n` unpaired fresh legs over all rounds; and `pay^rd_l` SDR-failure and loop edges,
with `Σ_l pay^rd_l ≤ 9n/D_*` by Lemma s7:lemPay(d), since the outcome satisfies Lemma
s7:lemOneOutcome(3)" (`EG.Todo.PayGlobal`, `EG.Todo.OneOutcomeRound`, `Rules.xiChosen_spec`). "The
bracketed terms and the terms `Σ_l (M_l − 1)|Lost_l|` and `X_pool` together equal
`80 dem + 369 lp + Σ_l (169 + M_l − 1)|Lost_l| + X_pool ≤ X_U + X_pool ≤ X'`. By Lemma
s7:lemOneOutcome(1) and Lemma s7:lemEXprime, `X' ≤ 3E X' ≤ 3ε_X(D_*)n`" (`EG.Todo.EXprime`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot Finset

/-- Proved in P3. [s7:propCost] see `EG.Spec.CostStatement`. -/
theorem Cost : EG.Spec.CostStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω hX
  have hcoh : (stageOf ω).Coherent run G := coherent_ofOutcome hω _ _ _
  have hval : ∀ l J, 3 ≤ l → l ≤ run.R → JPlusProps run G δ (stageOf ω) l J →
      (RoundInput.ofPast run G δ (stageOf ω) ω.pool l J).Valid :=
    fun l J hl hlR hJ => ofPast_valid ω.pool hR hδ hcoh hl hlR hJ
  -- the round step is a J-consumer (s7:lemLift (iv))
  let C : JConsumer run G δ (stageOf ω) :=
    { out := roundOut run G δ (stageOf ω) ω.pool
      jc1 := fun l J hl hlR hJ =>
        (EG.liftJConsumerRun_univ V run G δ (stageOf ω) ω.pool l J hl hlR hJ
          (hval l J hl hlR hJ)).1
      jc2 := fun l J hl hlR hJ =>
        (EG.liftJConsumerRun_univ V run G δ (stageOf ω) ω.pool l J hl hlR hJ
          (hval l J hl hlR hJ)).2.1 }
  -- Theorem MIX-C
  obtain ⟨Js, hJs, D, hD, hDle⟩ := EG.Todo.MixC V G N0 Dstar run δ hR hδ ω hω C
    (fun l J => ((roundOut run G δ (stageOf ω) ω.pool l J).1.length : ℝ))
    (fun _ _ _ _ _ => le_rfl)
  refine ⟨Js, hJs, D, hD, ?_⟩
  have hDle' : (D.length : ℝ) ≤ (Dstar / 2 + 745 + 338) * (G.card : ℝ) +
      epsM Dstar * (G.card : ℝ) +
      (80 * (Light.dem ω : ℝ) + 369 * (Light.lp ω : ℝ) +
        169 * ∑ l ∈ Icc 1 run.R, ((lostRound run G δ (stageOf ω) l).card : ℝ)) +
      1.5 * ∑ l ∈ Icc 1 run.R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) +
      ∑ l ∈ Icc 3 run.R, ((roundOut run G δ (stageOf ω) ω.pool l (Js l)).1.length : ℝ) := hDle
  have hconc := EG.Todo.MixCConc V G N0 Dstar run δ hR hδ
  -- the objects of each round step
  have hround : ∀ l ∈ Icc 3 run.R,
      ((roundOut run G δ (stageOf ω) ω.pool l (Js l)).1.length : ℝ) ≤
        (((run.M G l : ℝ) - 1) * ((lostRound run G δ (stageOf ω) l).card : ℝ) +
        ((∑ v ∈ Stage1.poolL G ω.pool l, poolWeight run G δ l v : ℕ) : ℝ) +
        ((run.M G l : ℝ) - 1) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) +
        ((RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.unpairedLegs.card
          : ℝ) +
        ((RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.payrd
          (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.xiChosen : ℝ) +
        2 * (fnum (roundQuotient run G δ (stageOf ω) ω.pool l (Js l)).edges : ℝ) := by
    intro l hl
    obtain ⟨hl3, hlR⟩ := mem_Icc.1 hl
    have := card_roundOut_le (π := ω.pool) (hJs l hl) hl3 hlR (hval l (Js l) hl3 hlR (hJs l hl))
    linarith
  have hsum := sum_le_sum hround
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum] at hsum
  -- payments over all rounds (s7:lemPay (b), (d))
  have hRs : ∀ l ∈ Icc 3 run.R,
      (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.Valid := fun l hl =>
    RoundInput.chosenRules_valid (hval l (Js l) (mem_Icc.1 hl).1 (mem_Icc.1 hl).2 (hJs l hl))
  obtain ⟨⟨hb1, hb2⟩, hd⟩ := EG.Todo.PayGlobal V G N0 Dstar run δ hR hδ ω hω Js hJs
    (fun l => (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules) hRs
  have hMk : ∀ l ∈ Icc 3 run.R,
      (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.MarkovEvent
        (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.xiChosen := by
    intro l hl
    have hO := (EG.Todo.OneOutcomeRound V G N0 Dstar run δ hR hδ ω hω l (mem_Icc.1 hl).1
      (mem_Icc.1 hl).2 (Js l) (hJs l hl) (pastOf run G δ ω l (Js l)) rfl
      (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules (hRs l hl)).1
    exact (Rules.xiChosen_spec _ hO).2
  have hpay := hd (fun l => (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.xiChosen)
    hMk
  have hpay' : ∑ l ∈ Icc 3 run.R,
      ((RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.payrd
          (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.xiChosen : ℝ) ≤
      9 * (G.card : ℝ) / Dstar := hpay
  have hlegs : ∑ l ∈ Icc 3 run.R,
      ((RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.unpairedLegs.card
        : ℝ) ≤ 2 * (G.card : ℝ) := by
    have h1 : ((∑ l ∈ Icc 3 run.R,
        (RoundInput.ofPast run G δ (stageOf ω) ω.pool l (Js l)).chosenRules.unpairedLegs.card
          : ℕ) : ℝ) ≤
        ((∑ l ∈ Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card : ℕ) : ℝ) := by
      exact_mod_cast hb1
    rw [Nat.cast_sum] at h1
    linarith
  -- the bracketed terms: `≤ X_U + X_pool ≤ X' ≤ 3E X' ≤ 3ε_X n`
  have hM1 : ∀ l, (1 : ℝ) ≤ (run.M G l : ℝ) := fun l => by
    exact_mod_cast le_trans (by norm_num) (Stage1.two_pow_le_M G run l)
  have hMc : ∀ l, ((run.M G l - 1 : ℕ) : ℝ) = (run.M G l : ℝ) - 1 := fun l => by
    rw [Nat.cast_sub (by exact_mod_cast hM1 l), Nat.cast_one]
  have hXU : (XU run G δ (stageOf ω) : ℝ) = 80 * (Light.dem ω : ℝ) + 369 * (Light.lp ω : ℝ) +
      169 * ∑ l ∈ Icc 1 run.R, ((lostRound run G δ (stageOf ω) l).card : ℝ) +
      ∑ l ∈ Icc 1 run.R, (run.M G l : ℝ) * ((lostRound run G δ (stageOf ω) l).card : ℝ) := by
    have e1 : (stageOf ω).dem = Light.dem ω := rfl
    have e2 : (stageOf ω).lp = Light.lp ω := rfl
    unfold XU
    rw [e1, e2]
    push_cast
    rw [mul_sum, add_assoc _ (∑ i ∈ Icc 1 run.R, _), ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun l _ => by ring
  have hXpool : (Xpool run G δ (stageOf ω) ω.pool : ℝ) =
      ∑ l ∈ Icc 3 run.R, ((∑ v ∈ Stage1.poolL G ω.pool l, poolWeight run G δ l v : ℕ) : ℝ) +
      ∑ l ∈ Icc 3 run.R,
        ((run.M G l : ℝ) - 1) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ) := by
    unfold Xpool
    rw [Nat.cast_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [Nat.cast_add, Nat.cast_mul, hMc l]
  have hXp : (XprimeOf run G δ ω : ℝ) = (XU run G δ (stageOf ω) : ℝ) +
      (Xpool run G δ (stageOf ω) ω.pool : ℝ) + (XV run G ω.pool : ℝ) := by
    unfold XprimeOf Xprime
    push_cast
    ring
  have hXV : (0 : ℝ) ≤ (XV run G ω.pool : ℝ) := Nat.cast_nonneg _
  have hlost : ∑ l ∈ Icc 3 run.R,
      ((run.M G l : ℝ) - 1) * ((lostRound run G δ (stageOf ω) l).card : ℝ) ≤
      ∑ l ∈ Icc 1 run.R, (run.M G l : ℝ) * ((lostRound run G δ (stageOf ω) l).card : ℝ) := by
    refine (sum_le_sum fun l _ => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
        (fun l _ _ => by positivity))
    have : (0 : ℝ) ≤ ((lostRound run G δ (stageOf ω) l).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsplit : ∑ l ∈ Icc 3 run.R,
      (((run.M G l : ℝ) - 1) * ((lostRound run G δ (stageOf ω) l).card : ℝ) +
        ((∑ v ∈ Stage1.poolL G ω.pool l, poolWeight run G δ l v : ℕ) : ℝ) +
        ((run.M G l : ℝ) - 1) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) =
      ∑ l ∈ Icc 3 run.R, ((run.M G l : ℝ) - 1) * ((lostRound run G δ (stageOf ω) l).card : ℝ) +
        ∑ l ∈ Icc 3 run.R, ((∑ v ∈ Stage1.poolL G ω.pool l, poolWeight run G δ l v : ℕ) : ℝ) +
        ∑ l ∈ Icc 3 run.R,
          ((run.M G l : ℝ) - 1) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ) := by
    rw [sum_add_distrib, sum_add_distrib]
  have hEX := (EG.Todo.EXprime V G N0 Dstar run δ hR hδ).1
  -- the constants
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hC : (Dstar / 2 + 1085 + eps1 Dstar) * (G.card : ℝ) =
      (Dstar / 2 + 745 + 338) * (G.card : ℝ) + epsM Dstar * (G.card : ℝ) +
        1.5 * epsCONC Dstar * (G.card : ℝ) + 3 * (epsX Dstar * (G.card : ℝ)) +
        9 * (G.card : ℝ) / Dstar + 2 * (G.card : ℝ) := by
    unfold eps1 epsM
    ring
  rw [hC]
  linarith

end EG.Todo
