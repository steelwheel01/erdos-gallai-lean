module

public import EG.Spec.Quot.Lift
public import EG.Proof.Quot.Lift

/-!
# Lemma JV-L (iv), the J-consumer, on vertex types of every universe (manuscript s7:lemLift)

`EG.Spec.LiftJConsumerStatement` and `EG.Spec.LiftJConsumerRunStatement` are stated on `Type`; the
s7b consumer s7:propCost quantifies over `V : Type u`. These are the same statements for
`V : Type u`, with the proofs of `EG.liftJConsumer` and `EG.liftJConsumerRun`
(`EG/Proof/Quot/Lift.lean`, unit P1) verbatim; the helper lemmas used there are
universe-polymorphic. The hypothesis `(RoundInput.ofPast …).Valid` of the run-level form is
discharged by `EG.Quot.ofPast_valid` (`EG/Lib/Quot/OfPastValid.lean`).
-/

public section

namespace EG

open EG.Quot EG.Spec

universe u

/-- [s7:lemLift] (iv), round level, for `V : Type u` (`EG.Spec.LiftJConsumerStatement`). -/
theorem liftJConsumer_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ ξ : Xi I.G I.M,
      (∀ e ∈ R.lentJV ξ, ∃ Y ∈ I.ancs, Y.1 + 2 ≤ I.l ∧ I.lendGood Y ∧ e ∈ I.ljv Y) ∧
      Chain.JC2 I.J (R.lentJV ξ) (R.objs ξ) ∧
      ((R.dec ξ).flatMap (R.liftObj ξ)).length ≤ 2 * fnum (R.Q ξ).edges := by
  intro V _ I hI R hR ξ
  have hD := (hR.dec ξ).1
  obtain ⟨-, -, hnd, hlen⟩ := Quot.Rules.liftDecomp_core hI hR ξ (R.dec ξ) hD
  refine ⟨Quot.Rules.lentJV_JC1 hI hR ξ, ?_, by rw [← (hR.dec ξ).2]; exact hlen⟩
  -- the edges of the lifted objects
  have hlift : ∀ g ∈ ((R.dec ξ).flatMap (R.liftObj ξ)).flatMap Obj.edges,
      ∃ c ∈ R.dec ξ, ∃ q ∈ c.edges, ∃ e, R.layerOf ξ q = some e ∧
        (g ∈ leItems e ∨ (c.isEdge = false ∧ R.IsJEdge ξ e g)) ∧
        g ∈ (R.liftObj ξ c).flatMap Obj.edges := by
    intro g hg
    rw [List.flatMap_assoc] at hg
    obtain ⟨c, hc, hg⟩ := List.mem_flatMap.1 hg
    obtain ⟨q, hq, e, hl, ho⟩ := (Rules.lift_member hI hR hD hc).2.2.1 g hg
    exact ⟨c, hc, q, hq, e, hl, ho, hg⟩
  have hObjs : (R.objs ξ).flatMap Obj.edges =
      (R.paidEdges ξ).toList ++ ((R.dec ξ).flatMap (R.liftObj ξ)).flatMap Obj.edges := by
    unfold Rules.objs
    rw [List.flatMap_append, Rules.flatMap_edges_map_edge]
  refine ⟨fun o ho => ?_, ?_, fun g => ?_⟩
  · -- well formed
    unfold Rules.objs at ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ho
      exact RoundInput.J_not_diag hI (Rules.paid_sub_J hI hR (Finset.mem_toList.1 hg))
    · obtain ⟨c, hc, ho⟩ := List.mem_flatMap.1 ho
      exact ((Rules.lift_member hI hR hD hc).1 o ho).1
  · -- pairwise edge-disjoint
    rw [hObjs, List.nodup_append]
    refine ⟨Finset.nodup_toList _, hnd, fun g hg g' hg' hgg => ?_⟩
    subst hgg
    have hp := Finset.mem_toList.1 hg
    obtain ⟨c, hc, q, hq, e, hl, ho, -⟩ := hlift g hg'
    have he := (Rules.layerOf_spec hl).1
    rcases ho with ho | ⟨-, en, hen, w, hw, rfl⟩
    · exact Rules.leItems_not_paid hI hR he ho hp
    · exact (Rules.jEdge_facts hI (Rules.leEnds_port hI hR he hen).1 hw).2.2.2.2
        (Rules.paid_sub_J hI hR hp)
  · -- the union is `J_l ∪ LentJV_l`
    rw [hObjs, List.mem_append, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe,
      Finset.mem_toList]
    constructor
    · rintro (hp | hg)
      · exact Or.inl (Rules.paid_sub_J hI hR hp)
      · obtain ⟨c, hc, q, hq, e, hl, ho, hgc⟩ := hlift g hg
        have he := (Rules.layerOf_spec hl).1
        rcases ho with ho | ⟨hce, hj⟩
        · exact Or.inl (Rules.leItems_J hI hR he ho)
        · right
          classical
          unfold Rules.lentJV
          obtain ⟨o, ho, hgo⟩ := List.mem_flatMap.1 hgc
          exact Finset.mem_filter.2 ⟨Rules.jEdge_mem_junctionEdges he hj, c, hc, hce, o, ho, hgo⟩
    · rintro (hJ | hL)
      · by_cases hlost : g ∈ I.Jlost
        · exact Or.inl ((Rules.mem_paidEdges).2 (Or.inl ((Rules.mem_paidA).2 (Or.inl hlost))))
        · rcases Rules.item_paid_or_layer hI hR (ξ := ξ) ((I.mem_items).2 ⟨hJ, hlost⟩) with
            hp | ⟨le, hle, hg⟩
          · exact Or.inl hp
          · right
            obtain ⟨q, hq⟩ := Rules.qEdge_isSome hI hR hle (R.rank ξ le)
            have hqQ : q ∈ (R.Q ξ).edges := (R.mem_qEdges).2 ⟨le, hle, hq⟩
            obtain ⟨c, hc, hqc⟩ := List.mem_flatMap.1 ((hD.2.2 q).2 (Finset.mem_coe.2 hqQ))
            have hgc := (Rules.lift_member hI hR hD hc).2.2.2 q hqc le
              (Rules.layerOf_eq hR hle hq) g hg
            rw [List.flatMap_assoc]
            exact List.mem_flatMap.2 ⟨c, hc, hgc⟩
      · right
        classical
        unfold Rules.lentJV at hL
        obtain ⟨-, c, hc, -, o, ho, hgo⟩ := Finset.mem_filter.1 hL
        exact List.mem_flatMap.2 ⟨o, List.mem_flatMap.2 ⟨c, hc, ho⟩, hgo⟩

/-- [s7:lemLift] (iv), run level, for `V : Type u` (`EG.Spec.LiftJConsumerRunStatement`): "Consequently the round step of Construction s7:consRound,
applied at every round `3 ≤ l ≤ R`, is a J-consumer: `Obj_l` and `LentJV_l` satisfy (JC1)–(JC3) of
Definition s6:defJconsumer. The objects of `Obj_l` other than paid single edges number at most
`2|Dec_l| = 2f(Q_l)`." (Conditional on `(RoundInput.ofPast …).Valid`, OBL-P1-1.) -/
theorem liftJConsumerRun_univ :
  ∀ (V : Type u) [DecidableEq V] (run : HB.Run V) (G : FGraph V) (δ : Chain.Designation V)
    (S : Chain.StageData V) (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V)),
    3 ≤ l → l ≤ run.R → Chain.JPlusProps run G δ S l J →
    (RoundInput.ofPast run G δ S π l J).Valid →
      Chain.JC1 run G S l (roundOut run G δ S π l J).2 ∧
      Chain.JC2 J (roundOut run G δ S π l J).2 (roundOut run G δ S π l J).1 ∧
      (((RoundInput.ofPast run G δ S π l J).chosenRules.dec
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen).flatMap
        ((RoundInput.ofPast run G δ S π l J).chosenRules.liftObj
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen)).length ≤
        2 * fnum (roundQuotient run G δ S π l J).edges := by
  intro V _ run G δ S π l J _ _ hJ hV
  have hR := RoundInput.chosenRules_valid hV
  obtain ⟨h1, h2, h3⟩ := liftJConsumer_univ V (RoundInput.ofPast run G δ S π l J) hV _ hR
    (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen
  refine ⟨?_, ?_, h3⟩
  · intro e he
    obtain ⟨Y, hY, hr, hg, hl⟩ := h1 e he
    have hY' : Y ∈ Chain.lendGoodAnc run G S l := by
      classical
      unfold Chain.lendGoodAnc
      exact Finset.mem_filter.2 ⟨hY, hr, hg⟩
    exact Finset.mem_biUnion.2 ⟨Y, hY', hl⟩
  · have hJ' := ofPast_J run G δ S π l hJ
    rw [hJ'] at h2
    exact h2

end EG
