module

public import EG.Proof.Chain.JSLCBound
public import EG.Spec.Chain.JSLC

/-!
# Proof of Lemma JS-LC with the J-interface of Lemma J⁺ (manuscript s6:lemJSLC, s6:lemJplus)

Probe unit P2J (probe P-2, part 2), proof round 1. `EG.jslc : EG.Spec.JSLCStatement`.

Assembly of the steps:
* Steps 1–2 (types; parity and the set `J_l`, J1 aggregated at hubs; eqJbound; J⁺):
  `EG.jslcStep2`, packed with the other inputs into the setting `JslcCtx` by `EG.exists_jslcCtx`
  (uses the declared inputs `EG.capPrePart` (s2:lemCap (ii)) and `EG.towerBLate`
  (s2:lemTower (b))).
* Steps 3–5 (realized beads; split): every component of `R_Y` is split into cherries at its
  centres ("pair the (evenly many) edges of `R_Y` at `h` arbitrarily into cherries"), and the
  cherries of `(Y,l)` are grouped greedily into groups of at most `K^JS_l` pairwise vertex-disjoint
  cherries (`exists_grouping`). Each group is a layered system with one cherry per layer and load
  `1`. (The manuscript applies the cherry split to giant components only and builds the system
  `𝒮_0(Y,l)` of the non-giant components by MED and EQ-LPT; for a non-giant pair `(Y,l)` all class-`Y`
  degrees are at most `2γ_l` (`JslcCtx.mY_le_of_not_isGiant`), so splitting every component costs
  at most `2γ_l + 2M_l` per ancestor, which Step 8's budget `ν_l · 5γ_l` absorbs.)
* Step 6 (joint routing, claims (a), (c), (d)): `exists_routes` (by `EG.jslcRouting`, COL(b)).
* Step 7 (HCC-P per system; the union): `exists_union` (by `EG.hccp`).
* Step 8 (the count): `JSLCBound.lean` (with `ν_l ≤ 2.74 n/P_{l−2}`, `P_{l−2} ≥ M_l^{13}`).
-/

public section

namespace EG

open EG.HB EG.Chain EG.Chain.JSLC

/-- [s6:lemJSLC] **Lemma JS-LC** with the J-interface of [s6:lemJplus] **Lemma J⁺**: proof. -/
theorem jslc : EG.Spec.JSLCStatement := by
  intro V _ G N0 Dstar run δ S l B hrh hδ hS hl hlR hB
  classical
  obtain ⟨J, R, C, hjb, hJP⟩ := exists_jslcCtx hrh hδ hS hl hlR hB
  obtain ⟨m, col, hg⟩ := exists_grouping C
  obtain ⟨rt, hr⟩ := exists_routes C hg
  obtain ⟨LentJS, D, hL, hdec, hcyc, hlen, hanc⟩ := exists_union (rt := rt) C hg hr
  refine ⟨J, LentJS, D, C.J_sub, ?_, hdec, hcyc, ?_, ?_, hjb, hJP⟩
  · intro e he
    obtain ⟨Y, hY, j, hj, he⟩ := hL e he
    exact Finset.mem_biUnion.2 ⟨Y, C.Ycl_lendGood hY,
      Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, he⟩⟩
  · -- Step 8
    set cl := Step2.classes run G δ S l
    set x : ℝ := (run.M G l : ℝ) with hxd
    have hM := one_le_M' (run := run) (G := G) (l := l)
    have hx : 1 ≤ x := by rw [hxd]; exact_mod_cast hM
    have hK : (Stage1.KJS G run l : ℝ) = x ^ 2 := by rw [KJS_eq]; push_cast; rfl
    have h1 : (D.length : ℝ) ≤ ∑ Y ∈ cl, ((used run G R col Y).card : ℝ) := by
      exact_mod_cast hlen
    have h2 : ∑ Y ∈ cl, ((used run G R col Y).card : ℝ) ≤
        ∑ Y ∈ cl, ((mY run G δ Y l : ℝ) + 2 * x + ((R Y).card : ℝ) / (Stage1.KJS G run l : ℝ)) :=
      Finset.sum_le_sum fun Y _ => card_used_le_real C hg Y
    have h3 : ∑ Y ∈ cl, ((mY run G δ Y l : ℝ) + 2 * x +
        ((R Y).card : ℝ) / (Stage1.KJS G run l : ℝ)) =
        ∑ Y ∈ cl, (mY run G δ Y l : ℝ) + (cl.card : ℝ) * (2 * x) +
          (∑ Y ∈ cl, ((R Y).card : ℝ)) / x ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_div, hK]
    have h4 := sum_mY_le C
    have h5 : (∑ Y ∈ cl, ((R Y).card : ℝ)) ≤ (G.card : ℝ) * x := by
      have := sum_card_R_le C
      have h' : ∑ Y ∈ cl, (R Y).card ≤ G.card * run.M G l :=
        this.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      rw [hxd]; exact_mod_cast h'
    have h6 : (∑ Y ∈ cl, ((R Y).card : ℝ)) / x ^ 2 ≤ (G.card : ℝ) * x / x ^ 2 :=
      div_le_div_of_nonneg_right h5 (by positivity)
    have hν : (cl.card : ℝ) ≤ 2.74 * (G.card : ℝ) / (run.P G (l - 2) : ℝ) := by
      have : (cl.card : ℝ) ≤ (run.nuAnc G l : ℝ) := by exact_mod_cast card_classes_le C
      exact this.trans C.towerNu
    have hp : x ^ 13 ≤ (run.P G (l - 2) : ℝ) := by rw [hxd]; exact_mod_cast C.towerM
    have hg0 : 0 ≤ ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l),
        (mY run G δ Y l : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hA := step8_arith (n := (G.card : ℝ)) (g := ∑ Y ∈ (run.ancestors G).filter
        (fun Y => IsGiant run G δ Y l), (mY run G δ Y l : ℝ)) (Nat.cast_nonneg _) hx hp hν
      (Nat.cast_nonneg _) gammaL_le_real hg0
    nlinarith
  · intro o ho
    obtain ⟨Y, hY, h⟩ := hanc o ho
    exact ⟨Y, C.Ycl_ancestors hY, h⟩

end EG
