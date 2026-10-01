module

public import EG.Spec.Quot.Lift
public import EG.Lib.Quot.Lift

/-!
# Proof of Lemma JV-L, the lift (manuscript s7:lemLift) — probe P-1, proof round 1

Unit P1, design note `formal/work/p2b/P1.md`. The lemmas are in `EG/Lib/Quot/Lift.lean`
(ownership of lifted edges, payments, segments of lifted cycles) and in the earlier files
`EG/Lib/Quot/{Items,Colour,Junction,E2,Quotient}.lean`.

Manuscript proof (s7.tex, proof of Lemma s7:lemLift), followed step by step:
* (i) "The first claim is (a2) … The claims about ports and fresh centres are Lemma
  s7:lemWellDef(i) together with the SDR of step (d). … Disjointness of the three roles is (J3)";
* (ii) PAR / HUB cycles: the vertices of the lifted closed walk are pairwise distinct
  (`EG.Quot.Rules.liftCycle_facts`), single edges lift to one or two items, and
  "Edge-disjointness": every lifted edge is owned by exactly one edge of `Q_l`
  (`EG.Quot.Rules.owned_unique`), which lies in exactly one member of `Dec`;
* (iii) items are paid or lie in exactly one edge of `Q_l`; a junction edge determines its end;
  its lent class is `LJV_{Y(u),l}`, the `H_Y` being edge-disjoint;
* (iv) (JC1) from (iii), (JC2) from (ii) and (iii), the count from (ii) for `Dec = Dec_l`.
-/

public section

namespace EG

open EG.Quot EG.Spec

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

theorem Quot.layerItems_eq (e : LayerEdge V) : layerItems e = leItems e := by
  rcases e with o | it <;> rfl

theorem Quot.mem_juncEnds {ξ : Xi I.G I.M} {en : REnd V} (h : en ∈ juncEnds R ξ) :
    ∃ e ∈ R.layerEdges ξ, en ∈ leEnds e := by
  unfold juncEnds at h
  rcases Finset.mem_union.1 h with h | h
  · obtain ⟨it, hit, rfl⟩ := Finset.mem_image.1 h
    exact ⟨.inr it, (Rules.inr_mem_layerEdges).2 hit, by simp [leEnds]⟩
  · obtain ⟨o, ho, h⟩ := Finset.mem_biUnion.1 h
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨.inl o, (Rules.inl_mem_layerEdges).2 ho, by cases b <;> simp [leEnds]⟩

theorem Quot.length_flatMap_le_two_mul {α β : Type*} (l : List α) (f : α → List β)
    (h : ∀ x ∈ l, (f x).length ≤ 2) : (l.flatMap f).length ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

/-- [s7:lemLift] (ii) for an arbitrary decomposition `Dec` of `E(Q_l)` (the core of
`EG.Spec.LiftDecompStatement`). -/
theorem Quot.Rules.liftDecomp_core (hI : I.Valid) (hR : R.Valid) (ξ : Xi I.G I.M)
    (Dec : List (Obj (QVert V))) (hD : IsDecomp ((R.Q ξ).edges : Set (Sym2 (QVert V))) Dec) :
    (∀ c ∈ Dec, c.isEdge = false →
        ∃ c' : List V, R.liftObj ξ c = [Obj.cycle c'] ∧ (Obj.cycle c').WF ∧
          ∀ e ∈ cycleEdges c', e ∈ I.G.edges) ∧
    (∀ c ∈ Dec, c.isEdge = true →
        1 ≤ (R.liftObj ξ c).length ∧ (R.liftObj ξ c).length ≤ 2 ∧
        ∀ o ∈ R.liftObj ξ c, o.isEdge = true ∧ o.WF ∧ ∀ e ∈ o.edges, e ∈ I.G.edges) ∧
    ((Dec.flatMap (R.liftObj ξ)).flatMap Obj.edges).Nodup ∧
    (Dec.flatMap (R.liftObj ξ)).length ≤ 2 * Dec.length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc hce
    rcases c with q | cv
    · simp [Obj.isEdge] at hce
    · refine ⟨R.liftCycle ξ cv, Rules.liftObj_cycle ξ cv, ?_⟩
      have h1 := (Rules.lift_member hI hR hD hc).1
      rw [Rules.liftObj_cycle] at h1
      exact h1 _ (List.mem_singleton_self _)
  · intro c hc hce
    rcases c with q | cv
    · have h1 := (Rules.lift_member hI hR hD hc).1
      obtain ⟨hWF, -, hmem⟩ := hD
      have hq : q ∈ (R.Q ξ).edges :=
        Finset.mem_coe.1 ((hmem q).1 (List.mem_flatMap.2 ⟨_, hc, by simp [Obj.edges]⟩))
      obtain ⟨e, hl⟩ := Rules.layerOf_isSome hq
      have hlift := Rules.liftObj_edge (R := R) hl
      refine ⟨?_, Rules.length_liftObj_le ξ _, fun o ho => ⟨?_, h1 o ho⟩⟩
      · rw [hlift, List.length_map]
        rcases e with o | it
        · cases o <;> simp [leItems, ParObj.edgeList]
        · simp [leItems]
      · rw [hlift] at ho
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 ho
        rfl
    · simp [Obj.isEdge] at hce
  · rw [List.flatMap_assoc]
    refine nodup_flatMap_of_owner Dec Obj.edges (fun c => (R.liftObj ξ c).flatMap Obj.edges)
      (fun g q => ∃ e, R.layerOf ξ q = some e ∧ R.Owned ξ e g) hD.2.1
      (fun c hc => (Rules.lift_member hI hR hD hc).2.1) (fun c hc g hg => ?_)
      (fun g q q' h h' => Rules.owner_unique hI hR h h')
    obtain ⟨q, hq, e, hl, ho⟩ := (Rules.lift_member hI hR hD hc).2.2.1 g hg
    exact ⟨q, hq, e, hl, ho.imp id (fun h => h.2)⟩
  · exact Quot.length_flatMap_le_two_mul Dec _ (fun c _ => Rules.length_liftObj_le ξ c)

/-- [s7:lemLift] (i) "`Live ∩ Pool_l = ∅`. Every port carries at most one PAR object of each PAR
colour and at most one coloured hub item of each HUB colour. Hence, although ports are not vertices
of `Q_l`, at most one edge of each sub-layer is an object or item with an end at a given port. Every
fresh centre is the middle of at most one cherry of each PAR colour. Hubs, fresh centres and ports
are pairwise disjoint." -/
theorem liftRoles : LiftRolesStatement := by
  intro V _ I hI R hR ξ
  refine ⟨?_, fun u κ => Rules.card_parObjs_end_colour_le hI hR u κ, ?_, ?_,
    fun x κ => Rules.card_parObjs_middle_colour_le hI hR x κ, hI.roles.1, hI.roles.2.1,
    hI.roles.2.2.2.1⟩
  · -- (a2)
    rw [Finset.disjoint_left]
    intro v hv hp
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.1 hv
    exact RoundInput.live_not_pool he (Sym2.mem_toFinset.1 hve) hp
  · -- the SDR of (d)
    intro u κ
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact Rules.hub_eq_of_port_colour hR ha.1 hb.1 (ha.2.1.trans hb.2.1.symm)
      (ha.2.2.trans hb.2.2.symm)
  · -- one edge of each sub-layer with an end at a given port
    intro u e he e' he' hu hu' hs heq
    rcases e with o | it <;> rcases e' with o' | it'
    · have ho := (Rules.mem_layerEdges_inl he).1
      have ho' := (Rules.mem_layerEdges_inl he').1
      obtain ⟨b, hb⟩ := hu
      obtain ⟨b', hb'⟩ := hu'
      cases h1 : R.parColour o with
      | none => simp [layerSubLayer, h1] at hs
      | some κ =>
        cases h2 : R.parColour o' with
        | none => simp [layerSubLayer, h1, h2] at heq
        | some κ' =>
          simp only [layerSubLayer, h1, h2, Option.map_some, Option.some.injEq,
            Prod.mk.injEq, true_and] at heq
          rw [← heq.1] at h2
          rw [Rules.parObj_eq_of_end_colour hI hR ho ho' (hb.trans hb'.symm) h1 h2]
    · cases h1 : R.parColour o <;> cases h2 : R.hubColour ξ.1 it' <;>
        simp [layerSubLayer, h1, h2] at hs heq
    · cases h1 : R.hubColour ξ.1 it <;> cases h2 : R.parColour o' <;>
        simp [layerSubLayer, h1, h2] at hs heq
    · have hit := (Rules.inr_mem_layerEdges).1 he
      have hit' := (Rules.inr_mem_layerEdges).1 he'
      simp only [layerHasPortEnd] at hu hu'
      simp only [layerSubLayer, Rules.hubColour_of_coloured hit, Rules.hubColour_of_coloured hit',
        Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at heq
      rw [Rules.hub_eq_of_port_colour hR hit hit' (hu.trans hu'.symm)
        (by rw [Rules.hubColour_of_coloured hit, Rules.hubColour_of_coloured hit', heq.1])]

/-- [s7:lemLift] (ii) "For *every* decomposition `Dec` of `E(Q_l)` into cycles and single edges,
the lift of each cycle of `Dec` is a cycle of `G`, and the lift of each single edge of `Dec`
consists of one or two single edges of `G`. The lifts of distinct members of `Dec` are pairwise
edge-disjoint. Hence the lift of `Dec` consists of at most `2|Dec|` pairwise edge-disjoint objects
of `G`." (The refutation target of probe P-1, a lifted cycle repeating a vertex, is excluded:
`(Obj.cycle c').WF` contains `c'.Nodup`.) -/
theorem liftDecomp : LiftDecompStatement := by
  intro V _ I hI R hR ξ Dec hD
  exact Quot.Rules.liftDecomp_core hI hR ξ Dec hD

/-- [s7:lemLift] (iii) "Every item is either paid or lies in exactly one edge of `Q_l`. Every
junction edge `uw` is the junction edge of at most one item-end, and that end is at `u`, never at
`w`. The edge `uw` lies in exactly one lent class, namely `LJV_{Y(u),l}`, where `Y(u)` is a
lend-good ancestor of round at most `l−2` […]. Junction edges lie in `E_r(Y)` for ancestors `Y` of
rounds `r ≤ l−2`, items lie in `E_l(Z)` for `Z ∈ Std_l`, and these edge sets are disjoint." -/
theorem liftAccounting : LiftAccountingStatement := by
  intro V _ I hI R hR ξ
  have endFacts : ∀ en ∈ juncEnds R ξ, en.port ∈ I.ports ∧ en.port ∉ I.pool := by
    intro en hen
    obtain ⟨e, he, hen'⟩ := Quot.mem_juncEnds hen
    exact Rules.leEnds_port hI hR he hen'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    by_cases hp : e ∈ R.paidEdges ξ
    · refine Or.inl ⟨hp, fun q _ hin => ?_⟩
      obtain ⟨le, hle, -, hg⟩ := hin
      rw [Quot.layerItems_eq] at hg
      exact Rules.leItems_not_paid hI hR hle hg hp
    · refine Or.inr ⟨hp, ?_⟩
      rcases Rules.item_paid_or_layer hI hR (ξ := ξ) he with h | ⟨le, hle, hg⟩
      · exact absurd h hp
      · obtain ⟨q, hq⟩ := Rules.qEdge_isSome hI hR hle (R.rank ξ le)
        refine ⟨q, ⟨(R.mem_qEdges).2 ⟨le, hle, hq⟩, le, hle, hq, by
          rw [Quot.layerItems_eq]; exact hg⟩, ?_⟩
        rintro q' ⟨-, le', hle', hq', hg'⟩
        rw [Quot.layerItems_eq] at hg'
        have := Rules.leItems_eq hI hR hle hle' hg hg'
        subst this
        exact Option.some.inj (hq'.symm.trans hq)
  · intro en hen en' hen' w w' hw hw' h
    exact Rules.end_eq_of_jEdge (endFacts en hen).2 (endFacts en' hen').2 hw hw' h
  · intro en hen w hw
    exact ⟨(endFacts en hen).1, (endFacts en hen).2, Rules.junction_pool hw⟩
  · intro en hen w hw
    have hu := (endFacts en hen).1
    obtain ⟨-, ha, hl, -, -⟩ := Rules.jEdge_facts hI hu hw
    refine ⟨ha, hl, fun Y hY hlY => ?_, hI.lendGood_ports _ hu, (hI.cls_round _ hu).2⟩
    by_contra hne
    exact Finset.disjoint_left.1 (hI.ljv_disj Y hY _ ha hne) hlY hl
  · rw [Finset.disjoint_left]
    intro g hg hJ
    obtain ⟨e, he, en, hen, w, hw, rfl⟩ := Rules.mem_junctionEdges hg
    exact (Rules.jEdge_facts hI (Rules.leEnds_port hI hR he hen).1 hw).2.2.2.2 hJ

/-- (JC1) in the form of the past: the edges of `LentJV_l` lie in the classes `LJV_{Y,l}` of the
lend-good ancestors of rounds `≤ l − 2`. -/
theorem Quot.Rules.lentJV_JC1 (hI : I.Valid) (hR : R.Valid) (ξ : Xi I.G I.M) :
    ∀ e ∈ R.lentJV ξ, ∃ Y ∈ I.ancs, Y.1 + 2 ≤ I.l ∧ I.lendGood Y ∧ e ∈ I.ljv Y := by
  intro g hg
  have hg' : g ∈ R.junctionEdges ξ := by
    classical
    unfold Rules.lentJV at hg
    exact (Finset.mem_filter.1 hg).1
  obtain ⟨e, he, en, hen, w, hw, rfl⟩ := Rules.mem_junctionEdges hg'
  have hu := (Rules.leEnds_port hI hR he hen).1
  obtain ⟨-, ha, hl, -, -⟩ := Rules.jEdge_facts hI hu hw
  exact ⟨_, ha, (hI.cls_round _ hu).2, hI.lendGood_ports _ hu, hl⟩

/-- [s7:lemLift] (iv), round level: "`Obj_l` and `LentJV_l` satisfy (JC1)–(JC3) of Definition
s6:defJconsumer. The objects of `Obj_l` other than paid single edges number at most
`2|Dec_l| = 2f(Q_l)`." -/
theorem liftJConsumer : LiftJConsumerStatement := by
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

/-- [s7:lemLift] (iv), run level: "Consequently the round step of Construction s7:consRound,
applied at every round `3 ≤ l ≤ R`, is a J-consumer: `Obj_l` and `LentJV_l` satisfy (JC1)–(JC3) of
Definition s6:defJconsumer. The objects of `Obj_l` other than paid single edges number at most
`2|Dec_l| = 2f(Q_l)`." (Conditional on `(RoundInput.ofPast …).Valid`, OBL-P1-1.) -/
theorem liftJConsumerRun : LiftJConsumerRunStatement := by
  intro V _ run G δ S π l J _ _ hJ hV
  have hR := RoundInput.chosenRules_valid hV
  obtain ⟨h1, h2, h3⟩ := liftJConsumer V (RoundInput.ofPast run G δ S π l J) hV _ hR
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
