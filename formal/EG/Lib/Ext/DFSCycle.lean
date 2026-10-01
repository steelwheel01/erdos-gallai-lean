module

public import EG.Lib.Ext.DFS
public import EG.Lib.Found.Fnum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# A long cycle from a path in an expanding graph (for manuscript s1:citLem25)

The second half of the proof of [BM, Lemma 25] ([s1:citLem25]; design note
`formal/work/ext/lemma25.md`): a path `P` of `G` is split into consecutive segments
`X, Y, Z` (`|X| = x`, `|Y| = k`, `|Z| ≥ x`). If some vertex reachable from `X` through the
vertices off `P` is adjacent to `Z`, we close a cycle containing `Y`; otherwise a set `S` with
`|S| ≥ x`, `2|S| ≤ |G|` has `Nbr_G(S) ⊆ Y`, which contradicts expansion.

* `EG.DFS.cycle_of_chain`: a vertex list without repetitions, of length at least `3`, whose
  consecutive vertices and whose last and first vertices are adjacent, is a cycle of `G`;
* `EG.DFS.insideGraph G W`: the Mathlib graph of the edges of `G` inside `W`;
  `EG.DFS.exists_list_of_reachable` turns reachability in it into a list path;
* `EG.DFS.long_cycle_of_path`: the X/Y/Z argument.

This replaces [BM]'s "shortest path between `X` and `Z` in `G \ Y`" by the set `X*` of vertices
reachable from `X` through `V(G) \ V(P)`; no connectivity of `G` is used.
-/

public section


namespace EG

namespace DFS

variable {V : Type*} [DecidableEq V] {G : FGraph V}

omit [DecidableEq V] in
/-- A vertex list without repetitions, with at least three vertices, all of whose consecutive
pairs and whose last and first vertex are adjacent in `G`, is a cycle of `G`. -/
theorem cycle_of_chain {c : List V} (hnd : c.Nodup) (hlen : 3 ≤ c.length)
    (hch : c.IsChain G.Adj) (hclose : ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) :
    (Obj.cycle c).WF ∧ ∀ e ∈ cycleEdges c, e ∈ G.edges := by
  refine ⟨⟨hnd, hlen⟩, ?_⟩
  intro e he
  obtain ⟨i, hi, rfl⟩ := mem_cycleEdges.1 he
  by_cases h1 : i + 1 < c.length
  · have h2 := hch.getElem i h1
    simp only [Nat.mod_eq_of_lt h1]
    exact h2
  · have hi' : i + 1 = c.length := by omega
    have hmod : (i + 1) % c.length = 0 := by rw [hi', Nat.mod_self]
    simp only [hmod]
    have hlast : c.getLast? = some c[i] := by
      rw [List.getLast?_eq_getElem?]
      simp only [show c.length - 1 = i by omega]
      exact List.getElem?_eq_getElem hi
    have hhead : c.head? = some c[0] := by
      rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)
    exact hclose c[i] (by rw [hlast]; rfl) c[0] (by rw [hhead]; rfl)

/-- The graph (in the sense of Mathlib) of the edges of `G` with both ends in `W`. -/
def insideGraph (G : FGraph V) (W : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ W ∧ b ∈ W
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [DecidableEq V] in
theorem insideGraph_adj {W : Finset V} {a b : V} :
    (insideGraph G W).Adj a b ↔ G.Adj a b ∧ a ∈ W ∧ b ∈ W := Iff.rfl

omit [DecidableEq V] in
theorem support_subset_of_walk {W : Finset V} {a b : V} (q : (insideGraph G W).Walk a b)
    (ha : a ∈ W) : ∀ u ∈ q.support, u ∈ W := by
  induction q with
  | nil =>
    intro u hu
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    exact hu ▸ ha
  | cons h p ih =>
    intro u hu
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ha
    · exact ih h.2.2 u hu

/-- Reachability inside `W` gives a list path inside `W` (listed from `b` back to `a`). -/
theorem exists_list_of_reachable {W : Finset V} {a b : V} (ha : a ∈ W)
    (h : (insideGraph G W).Reachable a b) :
    ∃ R : List V, R.Nodup ∧ R.IsChain G.Adj ∧ (∀ r ∈ R, r ∈ W) ∧ R.head? = some b ∧
      R.getLast? = some a := by
  obtain ⟨q⟩ := h
  let p := q.toPath
  refine ⟨p.1.support.reverse, List.nodup_reverse.2 p.2.support_nodup, ?_, ?_, ?_, ?_⟩
  · rw [List.isChain_reverse]
    exact p.1.isChain_adj_support.imp (fun _ _ h => h.1.symm)
  · intro r hr
    rw [List.mem_reverse] at hr
    exact support_subset_of_walk p.1 ha r hr
  · rw [List.head?_reverse, List.getLast?_eq_some_getLast p.1.support_ne_nil,
      SimpleGraph.Walk.getLast_support]
  · rw [List.getLast?_reverse, List.head?_eq_some_head p.1.support_ne_nil,
      SimpleGraph.Walk.head_support]

omit [DecidableEq V] in
/-- The cycle-closing step: `P = A ++ B ++ C` a path of `G`, `x₀ ∈ A`, `z ∈ C`, and a list `R`
of vertices off `P` (possibly empty) such that `z, R, x₀` continue to a closed walk. Then
there is a cycle of `G` of length at least `|B| + 2`. -/
theorem exists_cycle_of_segment {A B C R : List V} {x₀ z : V}
    (hnd : (A ++ B ++ C).Nodup) (hch : (A ++ B ++ C).IsChain G.Adj)
    (hx₀ : x₀ ∈ A) (hz : z ∈ C) (hB : 1 ≤ B.length) (hRnd : R.Nodup) (hRch : R.IsChain G.Adj)
    (hRP : ∀ r ∈ R, r ∉ A ++ B ++ C) (hzR : ∀ b ∈ R.head?, G.Adj z b)
    (hclose : ∀ a ∈ (z :: R).getLast?, G.Adj a x₀) :
    ∃ c : List V, (Obj.cycle c).WF ∧ (∀ e ∈ cycleEdges c, e ∈ G.edges) ∧
      B.length + 2 ≤ c.length := by
  obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hx₀
  obtain ⟨C₁, C₂, rfl⟩ := List.append_of_mem hz
  set M : List V := x₀ :: (A₂ ++ B ++ C₁) with hM
  have hP : A₁ ++ x₀ :: A₂ ++ B ++ (C₁ ++ z :: C₂) = A₁ ++ (M ++ [z]) ++ C₂ := by
    simp [hM]
  rw [hP] at hnd hch hRP
  have hinf : (M ++ [z]) <:+: (A₁ ++ (M ++ [z]) ++ C₂) := ⟨A₁, C₂, rfl⟩
  have hMz_nd : (M ++ [z]).Nodup := hnd.sublist hinf.sublist
  have hMz_ch : (M ++ [z]).IsChain G.Adj := hch.infix hinf
  have hMz_ch' := List.isChain_append.1 hMz_ch
  have hRMz : ∀ r ∈ R, r ∉ M ++ [z] := by
    intro r hr hrm
    exact hRP r hr (List.mem_append_left _ (List.mem_append_right _ hrm))
  have hlen : B.length + 2 ≤ (M ++ z :: R).length := by
    rw [hM]; simp only [List.length_append, List.length_cons]; omega
  have hc_nd : (M ++ z :: R).Nodup := by
    rw [List.nodup_append]
    have h1 := List.nodup_append.1 hMz_nd
    refine ⟨h1.1, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun hzR' => hRMz z hzR' (List.mem_append_right _ (List.mem_singleton_self z)),
        hRnd⟩
    · intro a ha b hb hab
      subst hab
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h1.2.2 a ha a (List.mem_singleton_self a) rfl
      · exact hRMz a hb (List.mem_append_left _ ha)
  have hc_ch : (M ++ z :: R).IsChain G.Adj := by
    apply List.IsChain.append hMz_ch'.1 (hRch.cons hzR)
    intro a ha b hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact hMz_ch'.2.2 a ha _ (by simp)
  have hc_cl : ∀ a ∈ (M ++ z :: R).getLast?, ∀ b ∈ (M ++ z :: R).head?, G.Adj a b := by
    intro a ha b hb
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil z R)] at ha
    rw [hM] at hb
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact hclose a ha
  obtain ⟨hWF, hE⟩ := cycle_of_chain hc_nd (by omega) hc_ch hc_cl
  exact ⟨M ++ z :: R, hWF, hE, hlen⟩

omit [DecidableEq V] in
/-- Split a list at positions `x` and `x + k`. -/
theorem exists_split3 (P : List V) {x k : ℕ} (h : x + k ≤ P.length) :
    ∃ A B C : List V, P = A ++ B ++ C ∧ A.length = x ∧ B.length = k := by
  refine ⟨P.take x, (P.drop x).take k, (P.drop x).drop k, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · simp; omega
  · simp; omega

/-- [s1:citLem25] (proof in [BM]) The `X, Y, Z` step: "let `X, Y, Z` be sets of consecutive
vertices of `P` in that order which partition `V(P)` ... If `X` and `Z` are connected by some
path in `G \ Y`, then ... this gives a cycle containing each vertex in `Y` ... If `X` and `Z`
are not connected by a path in `G \ Y`, then ... By the expansion condition ... a
contradiction." Here `|X| = x`, `|Y| = k ≥ 1`, `|Z| ≥ x`, and the expansion hypothesis is
`k < |Nbr_G(S)|` for all `S ⊆ V(G)` with `x ≤ |S|` and `2|S| ≤ |G|`. The cycle has length at
least `k + 2`. -/
theorem long_cycle_of_path (P : List V) (hnd : P.Nodup) (hch : P.IsChain G.Adj)
    (hPV : ∀ v ∈ P, v ∈ G.verts) (x k : ℕ) (hk : 1 ≤ k) (hlen : x + k + x ≤ P.length)
    (hexp : ∀ S : Finset V, S ⊆ G.verts → x ≤ S.card → 2 * S.card ≤ G.card →
      k < (G.nbrSet S).card) :
    ∃ c : List V, (Obj.cycle c).WF ∧ (∀ e ∈ cycleEdges c, e ∈ G.edges) ∧ k + 2 ≤ c.length := by
  classical
  obtain ⟨A, B, C, rfl, hA, hB⟩ := exists_split3 P (x := x) (k := k) (by omega)
  have hC : x ≤ C.length := by simp at hlen; omega
  have hnd' := hnd
  rw [List.nodup_append, List.nodup_append] at hnd'
  obtain ⟨⟨hAnd, hBnd, hAB⟩, hCnd, hABC⟩ := hnd'
  set W : Finset V := G.verts.filter (fun v => v ∉ A ++ B ++ C) with hW
  set H := insideGraph G W with hH
  set Xs : Finset V := G.verts.filter (fun w => w ∈ A ∨
    (w ∈ W ∧ ∃ x₀ ∈ A, ∃ w₀ ∈ W, G.Adj x₀ w₀ ∧ H.Reachable w₀ w)) with hXs
  by_cases hcase : ∃ v ∈ Xs, ∃ z ∈ C, G.Adj v z
  · obtain ⟨v, hv, z, hz, hvz⟩ := hcase
    rw [hXs, Finset.mem_filter] at hv
    rcases hv.2 with hvA | ⟨-, x₀, hx₀, w₀, hw₀, hxw, hreach⟩
    · -- a chord of `P` from `X` to `Z`
      obtain ⟨c, h1, h2, h3⟩ := exists_cycle_of_segment (R := []) hnd hch hvA hz (by omega)
        List.nodup_nil List.IsChain.nil (by simp) (by simp) (by simpa using hvz.symm)
      exact ⟨c, h1, h2, by omega⟩
    · -- a path from `X` to `Z` through the vertices off `P`
      obtain ⟨R, hRnd, hRch, hRW, hRh, hRl⟩ := exists_list_of_reachable (G := G) hw₀ hreach
      have hRne : R ≠ [] := by rintro rfl; simp at hRh
      obtain ⟨c, h1, h2, h3⟩ := exists_cycle_of_segment hnd hch hx₀ hz (by omega) hRnd hRch
        (fun r hr hrP => by
          have := hRW r hr
          rw [hW, Finset.mem_filter] at this
          exact this.2 hrP)
        (fun b hb => by
          rw [hRh, Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact hvz.symm)
        (fun a ha => by
          rw [List.getLast?_cons, hRl] at ha
          simp only [Option.getD_some, Option.mem_def, Option.some.injEq] at ha
          subst ha
          exact hxw.symm)
      exact ⟨c, h1, h2, by omega⟩
  · exfalso
    push Not at hcase
    have hmemP : ∀ w, w ∈ A ++ B ++ C → w ∈ G.verts := hPV
    have hXsub : A.toFinset ⊆ Xs := by
      intro v hv
      rw [List.mem_toFinset] at hv
      rw [hXs, Finset.mem_filter]
      exact ⟨hmemP v (by simp [hv]), Or.inl hv⟩
    have hNXs : G.nbrSet Xs ⊆ B.toFinset := by
      intro w hw
      obtain ⟨hwV, hwXs, v, hvXs, hvw⟩ := FGraph.mem_nbrSet.1 hw
      by_cases hwP : w ∈ A ++ B ++ C
      · rw [List.mem_append, List.mem_append] at hwP
        rcases hwP with (hwA | hwB) | hwC
        · exact absurd (hXsub (List.mem_toFinset.2 hwA)) hwXs
        · exact List.mem_toFinset.2 hwB
        · exact absurd hvw (hcase v hvXs w hwC)
      · have hwW : w ∈ W := by rw [hW, Finset.mem_filter]; exact ⟨hwV, hwP⟩
        exfalso
        apply hwXs
        rw [hXs, Finset.mem_filter] at hvXs ⊢
        refine ⟨hwV, Or.inr ⟨hwW, ?_⟩⟩
        rcases hvXs.2 with hvA | ⟨hvW, x₀, hx₀, w₀, hw₀, hxw, hreach⟩
        · exact ⟨v, hvA, w, hwW, hvw, SimpleGraph.Reachable.refl w⟩
        · exact ⟨x₀, hx₀, w₀, hw₀, hxw,
            hreach.trans (SimpleGraph.Adj.reachable (G := H) ⟨hvw, hvW, hwW⟩)⟩
    set T : Finset V := G.verts \ (Xs ∪ B.toFinset) with hT
    have hNT : G.nbrSet T ⊆ B.toFinset := by
      intro w hw
      obtain ⟨hwV, hwT, t, htT, htw⟩ := FGraph.mem_nbrSet.1 hw
      have hw' : w ∈ Xs ∪ B.toFinset := by
        by_contra hc
        exact hwT (Finset.mem_sdiff.2 ⟨hwV, hc⟩)
      rcases Finset.mem_union.1 hw' with hwXs | hwB
      · exfalso
        have htV := (Finset.mem_sdiff.1 htT).1
        have htn := (Finset.mem_sdiff.1 htT).2
        have ht : t ∈ G.nbrSet Xs :=
          FGraph.mem_nbrSet.2 ⟨htV, fun h => htn (Finset.mem_union_left _ h), w, hwXs, htw.symm⟩
        exact htn (Finset.mem_union_right _ (hNXs ht))
      · exact hwB
    have hZT : C.toFinset ⊆ T := by
      intro z hz
      rw [List.mem_toFinset] at hz
      have hzV : z ∈ G.verts := hmemP z (by simp [hz])
      refine Finset.mem_sdiff.2 ⟨hzV, ?_⟩
      intro hz'
      rcases Finset.mem_union.1 hz' with hzXs | hzB
      · rw [hXs, Finset.mem_filter] at hzXs
        rcases hzXs.2 with hzA | ⟨hzW, -⟩
        · exact hABC z (List.mem_append_left _ hzA) z hz rfl
        · rw [hW, Finset.mem_filter] at hzW
          exact hzW.2 (by simp [hz])
      · exact hABC z (List.mem_append_right _ (List.mem_toFinset.1 hzB)) z hz rfl
    have hdisj : Disjoint Xs T :=
      Finset.disjoint_left.2 fun v hv hvT =>
        (Finset.mem_sdiff.1 hvT).2 (Finset.mem_union_left _ hv)
    have hsum : Xs.card + T.card ≤ G.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      apply Finset.card_le_card
      intro v hv
      rcases Finset.mem_union.1 hv with hv | hv
      · exact (Finset.mem_filter.1 hv).1
      · exact (Finset.mem_sdiff.1 hv).1
    have hAc : A.toFinset.card = x := by rw [List.toFinset_card_of_nodup hAnd, hA]
    have hBc : B.toFinset.card = k := by rw [List.toFinset_card_of_nodup hBnd, hB]
    have hCc : C.toFinset.card = C.length := List.toFinset_card_of_nodup hCnd
    by_cases hsmall : 2 * Xs.card ≤ G.card
    · have h1 := hexp Xs (Finset.filter_subset _ _)
        (hAc ▸ Finset.card_le_card hXsub) hsmall
      have h2 := Finset.card_le_card hNXs
      omega
    · have hle : x ≤ T.card := le_trans (by omega) (Finset.card_le_card hZT)
      have h1 := hexp T Finset.sdiff_subset hle (by omega)
      have h2 := Finset.card_le_card hNT
      omega

end DFS

end EG
