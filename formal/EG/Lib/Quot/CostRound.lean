module

public import EG.Lib.Quot.PayRun
public import EG.Lib.Quot.LiftUniv

/-!
# The objects of one round step (manuscript s7:propCost, proof)

"The objects of `Obj_l` are the paid single edges and the lifted objects. By Lemma s7:lemPay, the
paid single edges number at most: `(M_l − 1)|Lost_l|` in (a1); the round-`l` summand of `X_pool`
in (a2) and (a3); … unpaired fresh legs; and `pay^rd_l` SDR-failure and loop edges … By Lemma
s7:lemLift (iv), the lifted objects number at most `2f(Q_l)`."

`card_roundOut_le`: for the past `I = RoundInput.ofPast run G δ S π l J` of a round with
`JPlusProps` and `I.Valid`, the output `Obj_l` of the J-consumer `roundOut` (chosen rules, chosen
`ξ_l`) has at most
`(M_l − 1)|Lost_l| + Σ_{v∈Pool_l} ω_l(v) + (M_l − 1)·#JV-bad + #unpaired legs + pay^rd_l + 2f(Q_l)`
objects.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain Finset

universe u

variable {V : Type u} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {J : Finset (Sym2 V)}

/-- The paid single edges of a round: `|paid| ≤ |J^lost| + |pool items| + |JV-bad items| +
|unpaired legs| + pay^rd_l` ([s7:lemPay] (e): no other item is paid). -/
theorem card_paidEdges_le {I : RoundInput V} (R : Rules I) (ξ : Xi I.G I.M) :
    (R.paidEdges ξ).card ≤ I.Jlost.card + I.paidPool.card + I.paidJVBad.card +
      R.unpairedLegs.card + R.payrd ξ := by
  classical
  unfold Rules.paidEdges Rules.payrd RoundInput.paidA
  rw [union_assoc (I.Jlost ∪ I.paidPool ∪ I.paidJVBad ∪ R.unpairedLegs)]
  refine (card_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (card_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (card_union_le _ _).trans (add_le_add ?_ le_rfl)
  exact card_union_le _ _

/-- [s7:propCost] the objects of one round step: `|Obj_l| ≤ |paid| + 2f(Q_l)`, with the paid
edges bounded by s7:lemPay (a1)–(a3) and the lift by s7:lemLift (iv). -/
theorem card_roundOut_le (hJ : JPlusProps run G δ S l J) (hl : 3 ≤ l) (hlR : l ≤ run.R)
    (hI : (RoundInput.ofPast run G δ S π l J).Valid) :
    ((roundOut run G δ S π l J).1.length : ℝ) ≤
      ((run.M G l : ℝ) - 1) * ((lostRound run G δ S l).card : ℝ) +
        ((∑ v ∈ Stage1.poolL G π l, poolWeight run G δ l v : ℕ) : ℝ) +
        ((run.M G l : ℝ) - 1) * ((jvBadPorts run G δ S π l).card : ℝ) +
        ((RoundInput.ofPast run G δ S π l J).chosenRules.unpairedLegs.card : ℝ) +
        ((RoundInput.ofPast run G δ S π l J).chosenRules.payrd
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen : ℝ) +
        2 * (fnum (roundQuotient run G δ S π l J).edges : ℝ) := by
  classical
  have hM1n : 1 ≤ run.M G l := le_trans (by norm_num) (Stage1.two_pow_le_M G run l)
  have hMc : ((run.M G l - 1 : ℕ) : ℝ) = (run.M G l : ℝ) - 1 := by
    rw [Nat.cast_sub hM1n, Nat.cast_one]
  have hLJ := EG.liftJConsumerRun_univ V run G δ S π l J hl hlR hJ hI
  have hlift := hLJ.2.2
  -- `|Obj_l| = |paid| + |lifted|`
  have hlen : (roundOut run G δ S π l J).1.length =
      ((RoundInput.ofPast run G δ S π l J).chosenRules.paidEdges
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen).card +
        (((RoundInput.ofPast run G δ S π l J).chosenRules.dec
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen).flatMap
        ((RoundInput.ofPast run G δ S π l J).chosenRules.liftObj
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen)).length := by
    rw [roundOut_eq]
    unfold Rules.objs
    rw [List.length_append, List.length_map, length_toList]
  have hpaid := card_paidEdges_le (RoundInput.ofPast run G δ S π l J).chosenRules
    (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen
  have ha1 := card_Jlost_le hI
  have ha2 := card_paidPool_le (π := π) hJ hI
  have ha3 := card_paidJVBad_le hI
  have ha1' : ((RoundInput.ofPast run G δ S π l J).Jlost.card : ℝ) ≤
      ((lostRound run G δ S l).card : ℝ) * ((run.M G l - 1 : ℕ) : ℝ) := by
    exact_mod_cast ha1
  have ha3' : ((RoundInput.ofPast run G δ S π l J).paidJVBad.card : ℝ) ≤
      ((jvBadPorts run G δ S π l).card : ℝ) * ((run.M G l - 1 : ℕ) : ℝ) := by
    exact_mod_cast ha3
  have ha2' : ((RoundInput.ofPast run G δ S π l J).paidPool.card : ℝ) ≤
      ((∑ v ∈ Stage1.poolL G π l, poolWeight run G δ l v : ℕ) : ℝ) := by
    exact_mod_cast ha2
  rw [hMc] at ha1' ha3'
  have hpaid' : (((RoundInput.ofPast run G δ S π l J).chosenRules.paidEdges
      (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen).card : ℝ) ≤
      ((RoundInput.ofPast run G δ S π l J).Jlost.card : ℝ) +
        ((RoundInput.ofPast run G δ S π l J).paidPool.card : ℝ) +
        ((RoundInput.ofPast run G δ S π l J).paidJVBad.card : ℝ) +
        ((RoundInput.ofPast run G δ S π l J).chosenRules.unpairedLegs.card : ℝ) +
        ((RoundInput.ofPast run G δ S π l J).chosenRules.payrd
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen : ℝ) := by
    exact_mod_cast hpaid
  have hlift' : ((((RoundInput.ofPast run G δ S π l J).chosenRules.dec
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen).flatMap
        ((RoundInput.ofPast run G δ S π l J).chosenRules.liftObj
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen)).length : ℝ) ≤
      2 * (fnum (roundQuotient run G δ S π l J).edges : ℝ) := by
    exact_mod_cast hlift
  rw [hlen, Nat.cast_add]
  linarith

end EG.Quot
