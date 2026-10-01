module

public import EG.Lib.HB.OVRound
public import EG.Lib.HB.CapAux

/-!
# Helpers for Proposition s2:propDegRec (manuscript s2:propDegRec)

Helper lemmas for `EG.Todo.DegRecKindsRound`, `EG.Todo.DegRecRound` (unit P3-s2).
* `STree.verts_nonempty`: every node of a split recursion on a non-empty graph is non-empty when
  every split has `U' ≠ ∅` and `V(H_ν) \ U' ≠ ∅` (so "a leaf with `q` vertices has fewer than
  `qP_l/2` edges" is meaningful: `q ≥ 1`);
* `STree.split_nonempty_of_isS0Rec`, `STree.split_nonempty_of_isTauRun`: these split conditions
  for an `s = 0` recursion and for a `τ`-run (witnesses have `1 ≤ |U| ≤ 2m/3`, `U' ⊆ U`, and
  `U' ≠ ∅` by the `τ`-rules, Lemma 14^τ (a));
* `two_card_edges_lt`: a loopless graph with `1 ≤ q < P` vertices has `2|E| < qP`.
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

namespace STree

theorem verts_nonempty : ∀ (t : STree V) (K : FGraph V), t.WF K → K.verts.Nonempty →
    (∀ a ∈ t.internalAddrs, (t.labelU a).Nonempty ∧
      ((t.graphAtD K a).verts \ t.labelU a).Nonempty) →
    ∀ a ∈ t.nodeAddrs, (t.graphAtD K a).verts.Nonempty := by
  intro t
  induction t with
  | nil => intro K _ hK _ a _; simpa using hK
  | node p l r ihl ihr =>
    intro K hwf hK hsplit a ha
    rw [wf_node_iff] at hwf
    have h0 := hsplit [] (by simp [internalAddrs_node])
    simp only [labelU_node_nil, graphAtD_node_nil] at h0
    rcases a with _ | ⟨b, a⟩
    · simpa using hK
    rw [mem_nodeAddrs_node_cons] at ha
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at ha
      simp only [graphAtD_node_false]
      refine ihl _ hwf.2.1 ?_ (fun a' ha' => ?_) a ha
      · obtain ⟨u, hu⟩ := h0.1
        exact ⟨u, by rw [splitFst_verts]; exact Finset.mem_inter.2 ⟨hwf.1.1 hu,
          Finset.mem_union_left _ hu⟩⟩
      · have := hsplit (false :: a') (by simpa using ha')
        simpa using this
    · simp only [↓reduceIte] at ha
      simp only [graphAtD_node_true]
      refine ihr _ hwf.2.2 ?_ (fun a' ha' => ?_) a ha
      · rw [splitSnd_verts]; exact h0.2
      · have := hsplit (true :: a') (by simpa using ha')
        simpa using this

theorem split_nonempty_of_isS0Rec {ε : ℝ} {t : STree V} {K : FGraph V} (ht : t.IsS0Rec ε K)
    {a : Addr} (ha : a ∈ t.internalAddrs) :
    (t.labelU a).Nonempty ∧ ((t.graphAtD K a).verts \ t.labelU a).Nonempty := by
  obtain ⟨U, F, hw, hl⟩ := ht.2 a ha
  rw [labelU_of_labelAt hl]
  show U.Nonempty ∧ ((t.graphAtD K a).verts \ U).Nonempty
  obtain ⟨hUV, -, hU1, hU2, -, -⟩ := hw
  refine ⟨Finset.card_pos.1 (by omega), ?_⟩
  rw [← Finset.card_pos, Finset.card_sdiff_of_subset hUV]
  have h1 : (1 : ℝ) ≤ U.card := by exact_mod_cast hU1
  have : (U.card : ℝ) < ((t.graphAtD K a).verts.card : ℝ) := by
    rw [FGraph.card_def] at hU2; linarith
  have : U.card < (t.graphAtD K a).verts.card := by exact_mod_cast this
  omega

theorem split_nonempty_of_isTauRun {ε τ : ℝ} {s : ℕ} {t : STree V} {K : FGraph V}
    (ht : t.IsTauRun ε s τ K)
    (hU' : ∀ a ∈ t.internalAddrs, (t.labelU a).Nonempty)
    {a : Addr} (ha : a ∈ t.internalAddrs) :
    (t.labelU a).Nonempty ∧ ((t.graphAtD K a).verts \ t.labelU a).Nonempty := by
  refine ⟨hU' a ha, ?_⟩
  obtain ⟨U, F, hw, hl⟩ := ht.2.2 a ha
  have hsub : t.labelU a ⊆ U := by
    rw [labelU_of_labelAt hl]; exact tauU1_subset _ _ _ _
  obtain ⟨hUV, -, hU1, hU2, -, -⟩ := hw
  have hcard : U.card < (t.graphAtD K a).verts.card := by
    have h1 : (1 : ℝ) ≤ U.card := by exact_mod_cast hU1
    have : (U.card : ℝ) < ((t.graphAtD K a).verts.card : ℝ) := by
      rw [FGraph.card_def] at hU2; linarith
    exact_mod_cast this
  obtain ⟨v, hv⟩ : ((t.graphAtD K a).verts \ U).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hUV]; omega
  rw [Finset.mem_sdiff] at hv
  exact ⟨v, Finset.mem_sdiff.2 ⟨hv.1, fun h => hv.2 (hsub h)⟩⟩

end STree

/-- A loopless graph with `1 ≤ q < P` vertices has `2|E| < qP` ("a leaf with `q < P_l` vertices
has at most `q(q-1)/2 < qP_l/2` edges"). -/
theorem two_card_edges_lt (X : FGraph V) {P : ℕ} (hq : 1 ≤ X.card) (hP : X.card < P) :
    2 * (X.edges.card : ℝ) < (X.card : ℝ) * P := by
  have hdeg : ∀ v ∈ X.verts, X.deg v ≤ X.card - 1 := by
    intro v hv
    have hsub : X.nbrs v ⊆ X.verts.erase v := by
      intro w hw
      exact Finset.mem_erase.2 ⟨fun h => X.self_not_mem_nbrs v (h ▸ hw),
        X.nbrs_subset_verts v hw⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hv] at this
    exact this
  have hsum : 2 * X.edges.card ≤ X.card * (X.card - 1) := by
    rw [← X.sum_deg_eq_two_mul_card_edges]
    calc ∑ v ∈ X.verts, X.deg v ≤ ∑ _v ∈ X.verts, (X.card - 1) := Finset.sum_le_sum hdeg
      _ = X.card * (X.card - 1) := by rw [Finset.sum_const, smul_eq_mul, FGraph.card_def]
  have h2 : X.card * (X.card - 1) < X.card * P :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  exact_mod_cast hsum.trans_lt h2

namespace Round

variable (H : FGraph V) (c : RoundChoice V)

/-- (R5) step (1): an edge of the part graph of a pre-part is assigned (it does not pass down). -/
theorem assign_ne_none_of_mem_partGraph (hv : Valid H c) {a : Addr} (ha : a ∈ prePartAddrs H c)
    {e : Sym2 V} (he : e ∈ (partGraph H c a).edges) : assign H c e ≠ none := by
  classical
  have hmem : a ∈ c.homeOrder := by
    rw [← List.mem_toFinset, hv.2.2.2.2.2]; exact ha
  have hsome : (c.homeOrder.find? (fun a => decide (a ∈ prePartAddrs H c ∧
      e ∈ (partGraph H c a).edges))).isSome := by
    rw [List.find?_isSome]
    exact ⟨a, hmem, by simp [ha, he]⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
  unfold assign
  rw [hb]
  simp

theorem partGraph_of_not_isLight {a : Addr} (hl : ¬ isLight H c a) : partGraph H c a = X0 H c a := by
  classical
  unfold partGraph; exact if_neg hl

theorem partGraph_of_isLight {a : Addr} (hl : isLight H c a) : partGraph H c a = X H c a := by
  classical
  unfold partGraph; exact if_pos hl

/-- An edge of `X^0_Z` with no end in `S_Z` is an edge of `X_Z`. -/
theorem mem_X_edges {a : Addr} {e : Sym2 V} (he : e ∈ (X0 H c a).edges)
    (hS : ∀ v ∈ guests H c a, v ∉ e) : e ∈ (X H c a).edges := by
  unfold X FGraph.deleteVerts
  rw [FGraph.mem_induce_edges]
  refine ⟨he, fun v hv => Finset.mem_sdiff.2 ⟨(X0 H c a).edge_verts e he v hv, fun h => hS v h hv⟩⟩

end Round

namespace Round

variable (H : FGraph V) (c : RoundChoice V)

theorem nbrs_X0_subset (a : Addr) (u : V) (hu : u ∈ Z0 H c a) :
    (X0 H c a).nbrs u ⊆ ((graph' H c).induce (Z0 H c a)).nbrs u := by
  intro w hw
  have hadj := FGraph.mem_nbrs.1 hw
  rw [FGraph.mem_nbrs, FGraph.induce_adj]
  exact ⟨(X0_le_graph' H c a).2 hadj, hu, hadj.mem_verts_right⟩

/-- Kind (c): "Every guest edge of `X^0_Z` joins some `u ∈ Z^0` to a vertex of `S_Z`, so it is
counted in `Σ_{u ∈ Z^0} |N_{X^0_Z}(u) ∩ S_Z|`; each term is at most `s_l/2` by (L2), since
`X^0_Z ⊆ G'_l[Z^0]`." -/
theorem card_guestEdges_le {a : Addr} (hL2 : isL2 H c a) :
    ((((X0 H c a).edges.filter (fun e => ∃ v ∈ guests H c a, v ∈ e)).card : ℕ) : ℝ) ≤
      ((Z0 H c a).card : ℝ) * (sOf (d H) : ℝ) / 2 := by
  have hsub : (X0 H c a).edges.filter (fun e => ∃ v ∈ guests H c a, v ∈ e) ⊆
      (Z0 H c a).biUnion (fun u => ((X0 H c a).nbrs u ∩ guests H c a).image
        (fun g => s(u, g))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heX, g, hg, hge⟩ := he
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hge
    have hu : u ∈ Z0 H c a := (X0 H c a).edge_verts _ heX u (Sym2.mem_mk_right g u)
    rw [Finset.mem_biUnion]
    refine ⟨u, hu, Finset.mem_image.2 ⟨g, Finset.mem_inter.2 ⟨?_, hg⟩, Sym2.eq_swap⟩⟩
    rw [FGraph.mem_nbrs, FGraph.adj_iff, Sym2.eq_swap]; exact heX
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := Z0 H c a)
    (t := fun u => ((X0 H c a).nbrs u ∩ guests H c a).image (fun g => s(u, g)))
  have h3 : ∀ u ∈ Z0 H c a, ((((X0 H c a).nbrs u ∩ guests H c a).image
      (fun g => s(u, g))).card : ℝ) ≤ (sOf (d H) : ℝ) / 2 := by
    intro u hu
    refine le_trans ?_ (hL2 u hu)
    have := Finset.card_image_le (s := (X0 H c a).nbrs u ∩ guests H c a) (f := fun g => s(u, g))
    have h4 : ((X0 H c a).nbrs u ∩ guests H c a).card ≤
        (((graph' H c).induce (Z0 H c a)).nbrs u ∩ guests H c a).card :=
      Finset.card_le_card (Finset.inter_subset_inter_right (nbrs_X0_subset H c a u hu))
    exact_mod_cast this.trans h4
  have h5 : (∑ u ∈ Z0 H c a, ((((X0 H c a).nbrs u ∩ guests H c a).image
      (fun g => s(u, g))).card : ℝ)) ≤ ∑ _u ∈ Z0 H c a, (sOf (d H) : ℝ) / 2 :=
    Finset.sum_le_sum h3
  rw [Finset.sum_const, nsmul_eq_mul] at h5
  have : ((((X0 H c a).edges.filter (fun e => ∃ v ∈ guests H c a, v ∈ e)).card : ℕ) : ℝ) ≤
      ∑ u ∈ Z0 H c a, ((((X0 H c a).nbrs u ∩ guests H c a).image (fun g => s(u, g))).card : ℝ) := by
    exact_mod_cast h1.trans h2
  linarith

end Round

end EG.HB
