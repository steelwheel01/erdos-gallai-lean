module

public import EG.Lib.Vortex.TPVPhase
public import EG.Lib.Found.Fnum
public import EG.Lib.Found.Graph

/-!
# Closing the paths of one class (manuscript s4:lemTPV, proof, step (vi); s4:thmVXp, proof,
step (f))

Unit P3-s4. "For each `c ∈ [3]` the ends of the paths of `PathsQ_{j,c}` form a multiset of pairs of
distinct vertices in which every vertex lies in at most `t` pairs (P2, P4). By (G2) there are
pairwise edge-disjoint paths `Q' ⊆ R_{j,c}`, one for each `Q ∈ PathsQ_{j,c}`, joining the two ends
of `Q`, of length at most `2^{12}L^4`, with all inner vertices in `V_{j,c}`. … The inner vertices
of `Q'` avoid `V(Q)` by (P1), and `Q` has length at least `2` by (P3); so by observation (C),
`Q ∪ Q'` is a cycle, which is output."

`EG.TPVRun.close_class`: the output objects `D` of a class together with the closed cycles
`Q ∪ Q'` decompose the edges of `D` and `Q` plus a set `Conn` of connector edges of the class
graph, all of whose ends lie in `U_{j+1}` (`Up`), and the number of objects is `|D| + |Q|`.
-/

public section

namespace EG

namespace TPVRun

open List

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A vertex of a list is its first vertex, its last vertex, or an interior vertex. -/
theorem mem_ends_or_interior {p : List V} {v : V} (hv : v ∈ p) :
    p.head? = some v ∨ p.getLast? = some v ∨ v ∈ interior p := by
  match p, hv with
  | a :: t, hv =>
    rcases List.mem_cons.1 hv with rfl | hvt
    · exact Or.inl rfl
    · right
      have htne : t ≠ [] := List.ne_nil_of_mem hvt
      have hsplit := List.dropLast_append_getLast htne
      rw [← hsplit, List.mem_append, List.mem_singleton] at hvt
      rcases hvt with h | h
      · right; simpa [interior] using h
      · left
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a t)]
        rw [List.getLast_cons htne, h]

/-- The number of indices `i` of a list with `p l[i]` is `l.countP p`. -/
theorem card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i : Fin l.length => p l[i.1]).card = l.countP p := by
  rw [Finset.card_filter, Fin.sum_univ_fun_getElem (f := fun x => if p x then 1 else 0),
    PVStep.sum_map_ite_eq_countP]

/-- Distinct positions of a list with a duplicate-free `flatMap` have disjoint images. -/
theorem disjoint_of_nodup_flatMap {α β : Type*} {l : List α} {f : α → List β}
    (h : (l.flatMap f).Nodup) {i j : Fin l.length} (hij : i ≠ j) :
    (f l[i.1]).Disjoint (f l[j.1]) := by
  have hp := (List.nodup_flatMap.1 h).2
  rw [List.pairwise_iff_getElem] at hp
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
  · exact hp i.1 j.1 i.2 j.2 hlt
  · exact (hp j.1 i.1 j.2 i.2 hlt).symm

/-- [s4:lemTPV] proof, step (vi) (and s4:thmVXp, step (f)): closing the paths `Q` of one class
through the class graph `Gc` (`R_{j,c}`), which is `(ℓ,t)`-path connected through `Vc`
(`V_{j,c}`, (G2)). Hypotheses: the edges of the objects `D` and of the paths `Q` are the
duplicate-free list of the edge set `X`; (P1)–(P3) (`Q` avoids `Vc`, ends in `Up`, length
`≥ 2`); (P4) as `pec ≤ t`; `Vc ⊆ Up ⊆ V(Gc)`; every edge of `X` has an end outside `Up` (it
meets `W_j`). -/
theorem close_class {Gc : FGraph V} {ℓ t : ℝ} {Vc Up : Finset V}
    (hG : Gc.IsPathConnected ℓ t Vc)
    {D : List (Obj V)} {Q : List (List V)} {X : Finset (Sym2 V)}
    (hwf : ∀ o ∈ D, o.WF)
    (hnd : (D.flatMap Obj.edges ++ Q.flatMap walkEdges).Nodup)
    (hX : ∀ e, e ∈ D.flatMap Obj.edges ++ Q.flatMap walkEdges ↔ e ∈ X)
    (hQ : ∀ q ∈ Q, q.Nodup ∧ 2 ≤ pathLength q ∧ (∃ x ∈ Up, q.head? = some x) ∧
      (∃ y ∈ Up, q.getLast? = some y) ∧ ∀ x ∈ q, x ∉ Vc)
    (hUpV : Up ⊆ Gc.verts) (hVcUp : Vc ⊆ Up)
    (hpec : ∀ v, (pathEndCount Q v : ℝ) ≤ t)
    (hsep : ∀ e ∈ X, ∃ x ∈ e, x ∉ Up) :
    ∃ (Conn : Finset (Sym2 V)) (Dc : List (Obj V)),
      IsDecomp ((X ∪ Conn : Finset (Sym2 V)) : Set (Sym2 V)) Dc ∧ Disjoint X Conn ∧
      Conn ⊆ Gc.edges ∧ (∀ e ∈ Conn, ∀ v ∈ e, v ∈ Up) ∧ Dc.length = D.length + Q.length ∧
      Dc.countP Obj.isEdge = D.countP Obj.isEdge := by
  classical
  -- the ends of the paths
  have hxy : ∀ i : Fin Q.length, ∃ x y : V, x ∈ Up ∧ y ∈ Up ∧ Q[i.1].head? = some x ∧
      Q[i.1].getLast? = some y := by
    intro i
    obtain ⟨_, _, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, _⟩ := hQ _ (List.getElem_mem i.2)
    exact ⟨x, y, hx, hy, hx', hy'⟩
  choose xs ys hxU hyU hxs hys using hxy
  have hne : ∀ i, xs i ≠ ys i := by
    intro i hi
    obtain ⟨hnd', h2, _⟩ := hQ _ (List.getElem_mem i.2)
    have h2' : 2 ≤ Q[i.1].length := by simp only [pathLength] at h2; omega
    exact head?_ne_getLast?_of_nodup hnd' h2' (by rw [hxs i, hys i, hi])
  -- the connectors
  obtain ⟨Q', hQ', hdisj⟩ := hG.exists_paths (fun i : Fin Q.length => (xs i, ys i))
    (fun i => ⟨hUpV (hxU i), hUpV (hyU i), hne i⟩)
    (fun v => by
      refine le_trans (le_of_eq ?_) (hpec v)
      congr 1
      rw [pathEndCount, ← card_filter_fin_eq_countP]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxs, hys, Option.some.injEq])
  -- vertices of connectors lie in `Up`
  have hQ'Up : ∀ i, ∀ v ∈ Q' i, v ∈ Up := by
    intro i v hv
    obtain ⟨⟨_, _, _⟩, hh, hl⟩ := (hQ' i).1
    rcases mem_ends_or_interior hv with h | h | h
    · rw [hh] at h; rw [← Option.some.inj h]; exact hxU i
    · rw [hl] at h; rw [← Option.some.inj h]; exact hyU i
    · exact hVcUp ((hQ' i).2.1 v h)
  have hX' : ∀ e, e ∈ X → ∀ i, e ∉ walkEdges (Q' i) := by
    intro e he i he'
    obtain ⟨x, hx, hxU⟩ := hsep e he
    exact hxU (hQ'Up i x (mem_of_mem_walkEdges he' hx))
  -- the cycles
  have hcyc : ∀ i : Fin Q.length,
      (Obj.cycle (Q[i.1] ++ (interior (Q' i)).reverse)).WF ∧
      List.Perm (cycleEdges (Q[i.1] ++ (interior (Q' i)).reverse))
        (walkEdges Q[i.1] ++ walkEdges (Q' i)) := by
    intro i
    obtain ⟨hnd', h2, _, _, hav⟩ := hQ _ (List.getElem_mem i.2)
    obtain ⟨⟨_, hn, _⟩, hh, hl⟩ := (hQ' i).1
    exact closing_aux hnd' h2 (hxs i) (hys i) hn hh hl
      (fun v hv hvq => hav v hvq ((hQ' i).2.1 v hv))
  -- decompositions
  let Es : Fin Q.length → Set (Sym2 V) :=
    fun i => {e | e ∈ walkEdges Q[i.1] ∨ e ∈ walkEdges (Q' i)}
  have hEs : ∀ i ∈ List.finRange Q.length,
      IsDecomp (Es i) [Obj.cycle (Q[i.1] ++ (interior (Q' i)).reverse)] := by
    intro i _
    have hc := hcyc i
    have hwf' := hc.1
    simp only [Obj.WF] at hwf'
    refine (isDecomp_cycle hwf'.1 hwf'.2).congr ?_
    ext e
    simp only [Set.mem_ofPred_eq, Es]
    rw [hc.2.mem_iff, List.mem_append]
  have hEsd : (List.finRange Q.length).Pairwise fun i j => Disjoint (Es i) (Es j) := by
    refine (List.nodup_finRange Q.length).pairwise_of_forall_ne fun i _ j _ hij => ?_
    rw [Set.disjoint_left]
    rintro e (he | he) (he' | he')
    · have hQnd : (Q.flatMap walkEdges).Nodup := (List.nodup_append.1 hnd).2.1
      exact disjoint_of_nodup_flatMap hQnd hij he he'
    · refine hX' e ((hX e).1 ?_) j he'
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨_, List.getElem_mem i.2, he⟩)
    · refine hX' e ((hX e).1 ?_) i he
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨_, List.getElem_mem j.2, he'⟩)
    · exact hdisj i j hij he he'
  have hcycD := isDecomp_flatMap hEs hEsd
  have hDD : IsDecomp {e | e ∈ D.flatMap Obj.edges} D :=
    ⟨hwf, (List.nodup_append.1 hnd).1, fun e => Iff.rfl⟩
  let Conn : Finset (Sym2 V) := Finset.univ.biUnion fun i => (walkEdges (Q' i)).toFinset
  have hmemConn : ∀ e, e ∈ Conn ↔ ∃ i, e ∈ walkEdges (Q' i) := by
    intro e; simp [Conn]
  have hU : (⋃ i ∈ List.finRange Q.length, Es i) =
      {e | e ∈ Q.flatMap walkEdges} ∪ (Conn : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_iUnion, List.mem_finRange, exists_prop, true_and, Set.mem_union,
      Set.mem_ofPred_eq, Finset.mem_coe, hmemConn, Es]
    constructor
    · rintro ⟨i, he | he⟩
      · exact Or.inl (List.mem_flatMap.2 ⟨_, List.getElem_mem i.2, he⟩)
      · exact Or.inr ⟨i, he⟩
    · rintro (he | ⟨i, he⟩)
      · obtain ⟨q, hq, he⟩ := List.mem_flatMap.1 he
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
        exact ⟨⟨k, hk⟩, Or.inl he⟩
      · exact ⟨i, Or.inr he⟩
  have hdisjD : Disjoint {e | e ∈ D.flatMap Obj.edges} (⋃ i ∈ List.finRange Q.length, Es i) := by
    rw [hU, Set.disjoint_union_right]
    constructor
    · rw [Set.disjoint_left]
      intro e he he'
      exact List.disjoint_of_nodup_append hnd he he'
    · rw [Set.disjoint_left]
      intro e he he'
      obtain ⟨i, hi⟩ := (hmemConn e).1 he'
      exact hX' e ((hX e).1 (List.mem_append_left _ he)) i hi
  refine ⟨Conn, D ++ (List.finRange Q.length).flatMap fun i =>
      [Obj.cycle (Q[i.1] ++ (interior (Q' i)).reverse)], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hDD.append hcycD hdisjD).congr ?_
    rw [hU]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.coe_union, Finset.mem_coe]
    rw [← hX e, List.mem_append]
    tauto
  · rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨i, hi⟩ := (hmemConn e).1 he'
    exact hX' e he i hi
  · intro e he
    obtain ⟨i, hi⟩ := (hmemConn e).1 he
    exact (hQ' i).1.1.2.2 e hi
  · intro e he v hv
    obtain ⟨i, hi⟩ := (hmemConn e).1 he
    exact hQ'Up i v (mem_of_mem_walkEdges hi hv)
  · simp
  · rw [countP_isEdge_append, countP_isEdge_flatMap]
    simp [Obj.isEdge]

end TPVRun

end EG
