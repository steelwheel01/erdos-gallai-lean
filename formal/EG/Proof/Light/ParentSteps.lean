module

public import EG.Spec.Light.ParentSteps
public import EG.Lib.Light.Trail
public import EG.Lib.Light.VisitCap

/-!
# Proofs of the abstract steps of Lemma parent side (s5:lemParent, Claim (transitions), Step 5)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.transitionClaim`
(`TransitionClaimStatement`), `EG.transitionCount` (`TransitionCountStatement`, a refutation
target of P-4) and `EG.visitCap` (`VisitCapStatement`, Step 4; list machinery in
`EG/Lib/Light/VisitCap.lean`). Library `EG/Lib/Light/Trail.lean`. Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.MTrail

universe u v w

/-- [s5:lemParent] Claim (transitions): "every transition consists of two distinct vertices of its
node `Y`." Proof as in the TeX: both vertices have the same parent (the trail is closed in the
quotient); if the two arcs differ they are vertex-disjoint; if they coincide (`k = 1`), the
transition consists of the two distinct ends of one arc. -/
theorem transitionClaim : EG.Spec.TransitionClaimStatement.{u, v, w} := by
  intro V β ι _ _ _ ends par W hW hdist hdisj t ht
  obtain ⟨_, hnd, hcl⟩ := hW
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_transitions.1 ht
    have hk : (j + 1) % W.length < W.length := Nat.mod_lt _ (by omega)
    set p := W[j] with hp
    set q := W[(j + 1) % W.length] with hq
    have hpW : p ∈ W := List.getElem_mem hj
    have hqW : q ∈ W := List.getElem_mem hk
    by_cases hpq : p.1 = q.1
    · -- the same arc: then the positions coincide (`k = 1`)
      have hidx : j = (j + 1) % W.length := by
        have h1 : (W.map Prod.fst)[j]'(by simpa using hj) =
            (W.map Prod.fst)[(j + 1) % W.length]'(by simpa using hk) := by
          simpa [List.getElem_map] using hpq
        exact (List.Nodup.getElem_inj_iff hnd).1 h1
      have hpq' : p = q := by
        simp only [hp, hq]
        congr 1
      rw [← hpq']
      exact oTgt_ne_oSrc ends p (hdist p hpW)
    · have h := hdisj p hpW q hqW hpq (oTgt ends p) (oTgt_mem_ends ends p)
      intro heq
      rcases oSrc_mem_ends ends q with h' | h'
      · exact h.1 (heq.trans h')
      · exact h.2 (heq.trans h')
  · have : (par t.1, par t.2) ∈ transitions (qEnds par ends) W := by
      rw [transitions_qEnds]; exact List.mem_map_of_mem ht
    exact hcl _ this

/-- [s5:lemParent] Step 5, "Each arc end lies in at most one transition" and "Counting": the
number of transitions containing `v`, over all trails and with multiplicity, is at most the number
of arcs of the trails having `v` as an end. -/
theorem transitionCount : EG.Spec.TransitionCountStatement.{u, v, w} := by
  intro V β ι _ _ _ ends par Ws _ hnd hdist v
  have key : ∀ Ws : List (List (ι × Bool)), (∀ a ∈ trailEdges Ws, (ends a).1 ≠ (ends a).2) →
      (Ws.flatMap (transitions ends)).countP (fun t => t.1 = v ∨ t.2 = v) ≤
        (trailEdges Ws).countP (fun a => (ends a).1 = v ∨ (ends a).2 = v) := by
    intro Ws hd
    induction Ws with
    | nil => simp [trailEdges]
    | cons W Ws ih =>
      have hte : trailEdges (W :: Ws) = W.map Prod.fst ++ trailEdges Ws := by
        simp [trailEdges]
      rw [hte] at hd
      rw [List.flatMap_cons, List.countP_append, hte, List.countP_append]
      have h1 := countP_transitions_le ends W
        (fun p hp => hd p.1 (List.mem_append_left _ (List.mem_map_of_mem hp))) v
      have h2 := ih (fun a ha => hd a (List.mem_append_right _ ha))
      omega
  refine (key Ws hdist).trans (le_of_eq ?_)
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext a
  simp

theorem trailEdges_eq_map_flatten {ι : Type*} (Ws : List (List (ι × Bool))) :
    trailEdges Ws = Ws.flatten.map Prod.fst := by
  induction Ws with
  | nil => rfl
  | cons W Ws ih => simp [trailEdges, List.flatMap_cons] at ih ⊢; rw [ih]

/-- The transitions of `W` at `Y` are its oriented edges ending (in the quotient) at `Y`. -/
theorem countP_transitions_node {V β ι : Type*} [DecidableEq β] (ends : ι → V × V) (par : V → β)
    (W : List (ι × Bool)) (Y : β) :
    (transitions ends W).countP (fun t => decide (par t.1 = Y)) =
      W.countP (fun p => decide (oTgt (qEnds par ends) p = Y)) := by
  have := congrArg (List.countP (fun x => decide (par x = Y))) (map_fst_transitions ends W)
  simp only [List.countP_map, Function.comp_def] at this
  rw [this]
  simp only [oTgt_qEnds]

theorem countP_flatMap_transitions_node {V β ι : Type*} [DecidableEq β] (ends : ι → V × V)
    (par : V → β) (Ws : List (List (ι × Bool))) (Y : β) :
    (Ws.flatMap (transitions ends)).countP (fun t => decide (par t.1 = Y)) =
      Ws.flatten.countP (fun p => decide (oTgt (qEnds par ends) p = Y)) := by
  induction Ws with
  | nil => rfl
  | cons W Ws ih =>
    rw [List.flatMap_cons, List.countP_append, ih, List.flatten_cons, List.countP_append,
      countP_transitions_node]

/-- [s5:lemParent] Step 4 (visit capping): "Process the nodes `Y` one after another in a fixed
order and split every current trail at the current node. … at the end every trail `𝒲` satisfies
`vis_Y(𝒲) ≤ T^sl_Y` for every `Y`. When `Y` is processed, the number of new trails is at most
`Σ_𝒲 vis_Y(𝒲)/T^sl_Y` … and `Σ_𝒲 vis_Y(𝒲)` … is not changed by any split." -/
theorem visitCap : EG.Spec.VisitCapStatement.{u, v, w} := by
  intro V β ι _ _ _ ends par cap Ws hcl _ hcap
  set E := qEnds par ends with hE
  set S : Finset β := ((Ws.flatMap (transitions ends)).map fun t => par t.1).toFinset with hS
  have hmemS : ∀ W ∈ Ws, ∀ p ∈ W, par (oTgt ends p) ∈ S := by
    intro W hW p hp
    rw [hS, List.mem_toFinset, List.mem_map]
    have : oTgt ends p ∈ (transitions ends W).map Prod.fst := by
      rw [map_fst_transitions]; exact List.mem_map_of_mem hp
    obtain ⟨t, ht, htp⟩ := List.mem_map.1 this
    exact ⟨t, List.mem_flatMap.2 ⟨W, hW, ht⟩, by rw [htp]⟩
  have hcapS : ∀ Y ∈ S.toList, 1 ≤ cap Y := by
    intro Y hY
    rw [Finset.mem_toList, hS, List.mem_toFinset, List.mem_map] at hY
    obtain ⟨t, ht, rfl⟩ := hY
    obtain ⟨W, hW, htW⟩ := List.mem_flatMap.1 ht
    exact hcap W hW t htW
  obtain ⟨Ws', hc', hf', hs', hq', hl'⟩ := MTrail.iterate E cap S.toList Ws hcl hcapS
  refine ⟨Ws', hc', ?_, fun W' hW' => ?_, fun W' hW' Y => ?_, ?_⟩
  · rw [trailEdges_eq_map_flatten, trailEdges_eq_map_flatten]; exact hf'.map _
  · obtain ⟨W, hW, hsub⟩ := hs' W' hW'
    exact ⟨W, hW, fun p hp => hsub.subset hp⟩
  · unfold vis
    rw [countP_transitions_node]
    by_cases hY : Y ∈ S
    · exact hq' W' hW' Y (Finset.mem_toList.2 hY)
    · rw [List.countP_eq_zero.2]
      · exact Nat.zero_le _
      · intro p hp
        obtain ⟨W, hW, hsub⟩ := hs' W' hW'
        have := hmemS W hW p (hsub.subset hp)
        simp only [hE, oTgt_qEnds, decide_eq_true_eq]
        intro h; rw [h] at this; exact hY this
  · refine hl'.trans (le_of_eq ?_)
    congr 1
    rw [Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [countP_flatMap_transitions_node]

end EG
