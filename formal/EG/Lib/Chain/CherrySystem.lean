module

public import EG.Lib.Chain.Cherry
public import EG.Lib.Chain.HCCP
public import EG.Lib.Found.Orient
public import EG.Lib.Found.Graph

/-!
# Layered systems of cherries (manuscript s6:lemJSLC, proof, Steps 5–7)

Probe unit P2J (probe P-2, part 2), proof round 1. A list `L = [c_0, …, c_{k−1}]` of pairwise
vertex-disjoint cherries `c_i = (h_i, u_i, u'_i)` is made into a layered system of depth `k` with
one cherry per layer ("Each cherry is a parity-clean cluster `({h},{u,u'},{hu,hu'})`. Its
orientation `u → h → u'` is admissible, with `exc(u) = +1`, `exc(u') = −1` and load `1`"; the
layering of Step 5 by Lemma EQ-LPT with unit loads, here with one unit per layer, so that no
padding is needed). The junction-`j` pair is `(u'_j, u_{j+1 mod k})` (the out-unit of layer `j` and
the in-unit of layer `j+1`, Step 6), joined by the path `Q j`.

`cherrySys L T Q` is the HCC-P data; `cherrySys_valid` checks the hypotheses of Lemma HCC-P
(Step 7: "(D) … (P) … (JC-P) …").
-/

public section

namespace EG.Chain.Cherry

variable {V : Type*} [DecidableEq V]

/-- A cherry `(h, u, u')` with three distinct vertices. -/
@[expose] def Good (c : V × V × V) : Prop := c.1 ≠ c.2.1 ∧ c.1 ≠ c.2.2 ∧ c.2.1 ≠ c.2.2

/-- The cluster `({h}, {u, u'}, {hu, hu'})` of a good cherry (junk: the empty cluster). -/
@[expose] noncomputable def cluster (c : V × V × V) : Cluster V := by
  classical
  exact if hc : Good c then
    { hubs := {c.1}
      ports := {c.2.1, c.2.2}
      beads := cEdges c
      disjoint := by
        rw [Finset.disjoint_singleton_left]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hc.1, hc.2.1⟩
      loopless := by
        intro e he
        unfold cEdges at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · rw [Sym2.mk_isDiag_iff]; exact hc.1
        · rw [Sym2.mk_isDiag_iff]; exact hc.2.1
      ends_mem := by
        intro e he v hv
        unfold cEdges at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl <;> rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
      no_hub_hub := by
        intro e he hall
        unfold cEdges at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hc.1 (Finset.mem_singleton.1 (hall _ (Sym2.mem_mk_right _ _))).symm
        · exact hc.2.1 (Finset.mem_singleton.1 (hall _ (Sym2.mem_mk_right _ _))).symm }
  else
    { hubs := ∅, ports := ∅, beads := ∅, disjoint := Finset.disjoint_empty_left _,
      loopless := by simp, ends_mem := by simp, no_hub_hub := by simp }

/-- The orientation `u → h → u'` of the cherry `(h, u, u')`. -/
@[expose] def orient (c : V × V × V) : Finset (V × V) := {(c.2.1, c.1), (c.1, c.2.2)}

variable {c : V × V × V}

theorem cluster_hubs (hc : Good c) : (cluster c).hubs = {c.1} := by
  unfold cluster; rw [dif_pos hc]

theorem cluster_ports (hc : Good c) : (cluster c).ports = {c.2.1, c.2.2} := by
  unfold cluster; rw [dif_pos hc]

theorem cluster_beads (hc : Good c) : (cluster c).beads = cEdges c := by
  unfold cluster; rw [dif_pos hc]

theorem cluster_verts (hc : Good c) : (cluster c).verts = cVerts c := by
  unfold Cluster.verts cVerts
  rw [cluster_hubs hc, cluster_ports hc]
  rfl

set_option linter.unusedSimpArgs false in
theorem outDeg_orient_fst (hc : Good c) : outDeg (orient c) c.2.1 = 1 := by
  simp [outDeg, orient, Finset.filter_insert, Finset.filter_singleton, hc.1, hc.2.1, hc.2.2, Ne.symm hc.1, Ne.symm hc.2.1, Ne.symm hc.2.2]

set_option linter.unusedSimpArgs false in
theorem inDeg_orient_fst (hc : Good c) : inDeg (orient c) c.2.1 = 0 := by
  simp [inDeg, orient, Finset.filter_insert, Finset.filter_singleton, hc.1, hc.2.1, hc.2.2, Ne.symm hc.1, Ne.symm hc.2.1, Ne.symm hc.2.2]

set_option linter.unusedSimpArgs false in
theorem outDeg_orient_snd (hc : Good c) : outDeg (orient c) c.2.2 = 0 := by
  simp [outDeg, orient, Finset.filter_insert, Finset.filter_singleton, hc.1, hc.2.1, hc.2.2, Ne.symm hc.1, Ne.symm hc.2.1, Ne.symm hc.2.2]

set_option linter.unusedSimpArgs false in
theorem inDeg_orient_snd (hc : Good c) : inDeg (orient c) c.2.2 = 1 := by
  simp [inDeg, orient, Finset.filter_insert, Finset.filter_singleton, hc.1, hc.2.1, hc.2.2, Ne.symm hc.1, Ne.symm hc.2.1, Ne.symm hc.2.2]

theorem exc_fst (hc : Good c) : exc (orient c) c.2.1 = 1 := by
  unfold exc; rw [outDeg_orient_fst hc, inDeg_orient_fst hc]; rfl

theorem exc_snd (hc : Good c) : exc (orient c) c.2.2 = -1 := by
  unfold exc; rw [outDeg_orient_snd hc, inDeg_orient_snd hc]; rfl

/-- "Its orientation `u → h → u'` is admissible". -/
theorem isAdmissible (hc : Good c) : (cluster c).IsAdmissible (orient c) := by
  have hne : s(c.1, c.2.1) ≠ s(c.1, c.2.2) := fun h => hc.2.2 (Sym2.congr_right.1 h)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    unfold orient at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Ne.symm hc.1
    · exact hc.2.1
  · intro a ha
    rw [cluster_beads hc]
    unfold orient at ha
    unfold cEdges
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl
    · exact Or.inl Sym2.eq_swap
    · exact Or.inr rfl
  · intro e he
    rw [cluster_beads hc] at he
    unfold cEdges at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    unfold orient
    rcases he with rfl | rfl
    · refine ⟨(c.2.1, c.1), ⟨by simp, Sym2.eq_swap⟩, ?_⟩
      rintro a ⟨ha, hae⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · rfl
      · exact absurd hae.symm hne
    · refine ⟨(c.1, c.2.2), ⟨by simp, rfl⟩, ?_⟩
      rintro a ⟨ha, hae⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact absurd (Sym2.eq_swap.symm.trans hae) hne
      · rfl
  · classical
    refine isAcyclic_of_potential
      (fun v => if v = c.2.1 then (0 : ℕ) else if v = c.1 then 1 else 2) ?_
    intro a ha
    unfold orient at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp [hc.1]
    · simp [hc.1, Ne.symm hc.2.2, Ne.symm hc.2.1]
  · intro h hh
    rw [cluster_hubs hc, Finset.mem_singleton] at hh
    subst hh
    have h1 := outDeg_orient_fst hc
    simp [outDeg, inDeg, orient, Finset.filter_insert, Finset.filter_singleton, hc.1, hc.2.1, hc.2.2, Ne.symm hc.1, Ne.symm hc.2.1, Ne.symm hc.2.2]

/-- "Each cherry is a parity-clean cluster": the centre has degree `2`. -/
theorem parityClean (hc : Good c) : (cluster c).ParityClean := by
  intro h hh
  rw [cluster_hubs hc, Finset.mem_singleton] at hh
  subst hh
  rw [cluster_beads hc]
  have : edgesAt (cEdges c) c.1 = cEdges c := by
    ext e
    rw [FGraph.mem_edgesAt]
    constructor
    · exact fun h => h.1
    · intro he
      refine ⟨he, ?_⟩
      unfold cEdges at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> exact Sym2.mem_mk_left _ _
  unfold degE
  rw [this]
  unfold cEdges
  rw [Finset.card_pair (fun h => hc.2.2 (Sym2.congr_right.1 h))]
  exact even_two

/-! ### The system -/

/-- The layered system of the list of cherries `L` (one cherry per layer, `lay i = i`), junction
sets `T j` and one path `Q j` per junction; no padding. -/
@[expose] noncomputable def cherrySys (L : List (V × V × V)) (T : ℕ → Finset V)
    (Q : ℕ → List V) : HccpData V where
  k := L.length
  N := L.length
  K i := cluster (L.get i)
  O i := orient (L.get i)
  lay i := i
  T j := T j.val
  pad _ := 0
  P j := [Q j.val]

variable {L : List (V × V × V)} {T : ℕ → Finset V} {Q : ℕ → List V}

theorem cherrySys_layP (hgood : ∀ c ∈ L, Good c) (j : Fin (cherrySys L T Q).k) :
    (cherrySys L T Q).layP j = {(L.get j).2.1, (L.get j).2.2} := by
  unfold HccpData.layP
  have : Finset.univ.filter (fun i : Fin (cherrySys L T Q).N => (cherrySys L T Q).lay i = j) =
      {(⟨j.val, j.2⟩ : Fin (cherrySys L T Q).N)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (congrArg Fin.val h)
    · intro h; exact Fin.ext (congrArg Fin.val h)
  rw [this, Finset.singleton_biUnion]
  exact cluster_ports (hgood _ (List.get_mem _ _))

theorem cherrySys_pexc (hgood : ∀ c ∈ L, Good c)
    (hD : ∀ i i' : Fin (cherrySys L T Q).N, i ≠ i' →
      Disjoint ((cherrySys L T Q).K i).verts ((cherrySys L T Q).K i').verts)
    (i : Fin (cherrySys L T Q).N) :
    (cherrySys L T Q).pexc (L.get i).2.1 = 1 ∧ (cherrySys L T Q).pexc (L.get i).2.2 = -1 := by
  have hg := hgood _ (List.get_mem L i)
  have h1 : (L.get i).2.1 ∈ ((cherrySys L T Q).K i).ports := by
    show (L.get i).2.1 ∈ (cluster (L.get i)).ports
    rw [cluster_ports hg]; simp
  have h2 : (L.get i).2.2 ∈ ((cherrySys L T Q).K i).ports := by
    show (L.get i).2.2 ∈ (cluster (L.get i)).ports
    rw [cluster_ports hg]; simp
  rw [(cherrySys L T Q).pexc_eq hD h1, (cherrySys L T Q).pexc_eq hD h2]
  exact ⟨exc_fst hg, exc_snd hg⟩

/-- [s6:lemJSLC] (proof, Step 7) the hypotheses of Lemma HCC-P for a system of pairwise
vertex-disjoint good cherries, one per layer, with junction sets `T j` and paths `Q j` from `u'_j`
to `u_{j+1 mod k}`. -/
theorem cherrySys_valid {G : FGraph V} (hL : L ≠ []) (hgood : ∀ c ∈ L, Good c)
    (hdisj : L.Pairwise (fun c c' => Disjoint (cVerts c) (cVerts c')))
    (hG : ∀ c ∈ L, cEdges c ⊆ G.edges)
    (hT : ∀ j j', j < L.length → j' < L.length → j ≠ j' → Disjoint (T j) (T j'))
    (hCT : ∀ c ∈ L, ∀ j < L.length, Disjoint (cVerts c) (T j))
    (hQ : ∀ (j : ℕ) (hj : j < L.length),
      IsPathBetween G.edges (L.get ⟨j, hj⟩).2.2
        (L.get ⟨(j + 1) % L.length, Nat.mod_lt _ (by omega)⟩).2.1 (Q j) ∧ IsThrough (T j) (Q j))
    (hQQ : ∀ j j', j < L.length → j' < L.length → j ≠ j' →
      Disjoint (walkEdges (Q j)).toFinset (walkEdges (Q j')).toFinset)
    (hQB : ∀ j < L.length, ∀ c ∈ L, Disjoint (walkEdges (Q j)).toFinset (cEdges c)) :
    (cherrySys L T Q).Valid G := by
  classical
  set S := cherrySys L T Q with hS
  have hk : S.k = L.length := rfl
  have hgi : ∀ i : Fin L.length, Good (L.get i) := fun i => hgood _ (List.get_mem L i)
  have hverts : ∀ i : Fin S.N, (S.K i).verts = cVerts (L.get i) := fun i => cluster_verts (hgi i)
  have hD : ∀ i i' : Fin S.N, i ≠ i' → Disjoint (S.K i).verts (S.K i').verts := by
    intro i i' hii
    rw [hverts, hverts]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hii) with h | h
    · exact List.Pairwise.rel_get_of_lt hdisj (a := i) (b := i') h
    · exact (List.Pairwise.rel_get_of_lt hdisj (a := i') (b := i) h).symm
  have hlayP := cherrySys_layP (T := T) (Q := Q) hgood
  have hpexc := cherrySys_pexc (T := T) (Q := Q) hgood hD
  have hsucc : ∀ j : Fin S.k, (S.succ j).val = (j.val + 1) % L.length := fun j => rfl
  have hcountH : ∀ (q : List V) (x : V),
      [q].countP (fun p => decide (p.head? = some x)) = if q.head? = some x then 1 else 0 := by
    intro q x; simp [List.countP_singleton]
  have hcountL : ∀ (q : List V) (x : V),
      [q].countP (fun p => decide (p.getLast? = some x)) =
        if q.getLast? = some x then 1 else 0 := by
    intro q x; simp [List.countP_singleton]
  refine ⟨?_, fun i => isAdmissible (hgi i), ?_, ?_, ?_, hD, ?_, fun i => parityClean (hgi i),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- k_pos
    show 1 ≤ L.length
    exact List.length_pos_iff.2 hL
  · -- beads_G
    intro i
    show (cluster (L.get i)).beads ⊆ G.edges
    rw [cluster_beads (hgi i)]
    exact hG _ (List.get_mem L i)
  · -- T_disj
    intro j j' hjj
    exact hT j j' j.2 j'.2 (Fin.val_ne_of_ne hjj)
  · -- pad_k1
    intro _ _ _ _; rfl
  · -- D_KT
    intro i j
    rw [hverts]
    exact hCT _ (List.get_mem L i) j j.2
  · -- path_G
    intro j p hp
    rw [List.mem_singleton.1 hp]
    exact (hQ j j.2).1.1
  · -- path_ends
    intro j p hp
    rw [List.mem_singleton.1 hp]
    obtain ⟨⟨-, h1, h2⟩, -⟩ := hQ j j.2
    refine ⟨⟨_, ?_, h1⟩, ⟨(L.get (S.succ j)).2.1, ?_, ?_⟩⟩
    · rw [hlayP]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [hlayP]; exact Finset.mem_insert_self _ _
    · rw [h2]; congr 3
  · -- path_T
    intro j p hp
    rw [List.mem_singleton.1 hp]
    exact (hQ j j.2).2
  · -- starts
    intro j u hu
    rw [hlayP] at hu
    obtain ⟨⟨-, h1, -⟩, -⟩ := hQ j j.2
    have hg := hgi j
    show [Q j.val].countP (fun p => decide (p.head? = some u)) = _
    rw [hcountH]
    unfold HccpData.demMinus
    rcases Finset.mem_insert.1 hu with rfl | hu
    · have : ¬ (Q j.val).head? = some (L.get j).2.1 := by
        rw [h1]; intro h; exact hg.2.2 (Option.some_inj.1 h).symm
      rw [if_neg this, (hpexc j).1]; rfl
    · have h1' : (Q j.val).head? = some (L.get j).2.2 := h1
      rw [Finset.mem_singleton.1 hu, (hpexc j).2, if_pos h1']; rfl
  · -- ends
    intro j v hv
    rw [hlayP] at hv
    obtain ⟨⟨-, -, h2⟩, -⟩ := hQ j j.2
    have h2' : (Q j.val).getLast? = some (L.get (S.succ j)).2.1 := by
      rw [h2]; congr 3
    have hg := hgi (S.succ j)
    show [Q j.val].countP (fun p => decide (p.getLast? = some v)) = _
    rw [hcountL]
    unfold HccpData.demPlus
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [if_pos h2', (hpexc (S.succ j)).1]; rfl
    · rw [Finset.mem_singleton.1 hv]
      have : ¬ (Q j.val).getLast? = some (L.get (S.succ j)).2.2 := by
        rw [h2']; intro h; exact hg.2.2 (Option.some_inj.1 h)
      rw [if_neg this, (hpexc (S.succ j)).2]; rfl
  · -- path_edisj
    intro j
    exact List.pairwise_singleton _ _
  · -- pp_disj
    intro j j' hjj
    have e1 : S.pathEdges j = (walkEdges (Q j.val)).toFinset := by
      unfold HccpData.pathEdges; simp [S, cherrySys]
    have e2 : S.pathEdges j' = (walkEdges (Q j'.val)).toFinset := by
      unfold HccpData.pathEdges; simp [S, cherrySys]
    rw [e1, e2]
    exact hQQ j j' j.2 j'.2 (Fin.val_ne_of_ne hjj)
  · -- pb_disj
    intro j i
    have e1 : S.pathEdges j = (walkEdges (Q j.val)).toFinset := by
      unfold HccpData.pathEdges; simp [S, cherrySys]
    rw [e1]
    show Disjoint _ (cluster (L.get i)).beads
    rw [cluster_beads (hgi i)]
    exact hQB j j.2 _ (List.get_mem L i)
  · -- bb_disj
    intro i i' hii
    have hv := hD i i' hii
    rw [hverts, hverts] at hv
    show Disjoint (cluster (L.get i)).beads (cluster (L.get i')).beads
    rw [cluster_beads (hgi i), cluster_beads (hgi i')]
    rw [Finset.disjoint_left]
    intro e he he'
    have hsub : ∀ c : V × V × V, ∀ e ∈ cEdges c, ∀ v ∈ e, v ∈ cVerts c := by
      intro c e he v hv
      unfold cEdges at he
      unfold cVerts
      simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
      rcases he with rfl | rfl <;> rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
    induction e using Sym2.ind with
    | _ x y =>
      exact Finset.disjoint_left.1 hv (hsub _ _ he x (Sym2.mem_mk_left _ _))
        (hsub _ _ he' x (Sym2.mem_mk_left _ _))

end EG.Chain.Cherry
