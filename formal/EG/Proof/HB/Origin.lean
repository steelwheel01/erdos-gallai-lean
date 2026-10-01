module

public import EG.Spec.HB.Origin
public import EG.Lib.HB.SEP
public import EG.Lib.HB.GC
public import EG.Lib.HB.Run

/-!
# Proof of Proposition ORIGIN^τ (manuscript s2:propOrigin), parts (a), (b) and the final
paragraph

Unit P3B (probe P-3, part 2), proof round 1. Statements: `EG/Spec/HB/Origin.lean`. Design note
`formal/work/p2b/P3B.md`.

Argument (manuscript proof of s2:propOrigin, with the thin cut of s2:lemThinCut):
* an edge `e = ux` of `G'_r` with `u ∈ Y^0 \ Dup*_r` is, by SEP (i) on the two-level recursion
  (`STree.thinCut_edge`), either deleted there — then, since the first level deletes nothing
  (`Run.Valid.deleted_twoLevel`) and `u` lies in only one piece, deleted by the `τ`-run of the
  piece `𝒫` above `Y` — or an edge of the unique leaf containing `u`, which is `Y`
  (`origin_edge_cases`);
* a deleted edge has its other end outside the leaf of `u` (SEP (i), `STree.not_mem_leaf_of_mem_delAt`);
* an edge of `X^0_Y` that passes down at round `r` must be a guest–core edge of a light `Y`: for a
  standalone `Y`, or for a light `Y` and `x ∉ S_Y`, rule (R5) assigns it (`EG.HB.Round.assign_ne_none_*`);
* (b) is the thin cut (`STree.thinCut_lt`) on the `τ`-run of `𝒫` (only `τ_r > 0` is used);
* the final paragraph is rule (GC) (`Run.isGC_iff_eBetween`).
No hypothesis on `D_*` is used.
-/

public section

namespace EG

open EG.HB

namespace HB

variable {V : Type*} [DecidableEq V]

namespace STree

/-- An edge of a leaf graph is not deleted (SEP (i), count form). -/
theorem not_mem_deleted_of_mem_leaf (t : STree V) {H : FGraph V} {L : Addr}
    (hL : L ∈ t.leafAddrs) {e : Sym2 V} (heL : e ∈ (t.graphAtD H L).edges) :
    e ∉ t.deleted H := by
  intro hd
  have he : e ∈ H.edges := graphAtD_edges_subset t H L heL
  have hc := sep_count t he
  have h1 : 1 ≤ (t.leafAddrs.filter (fun L => e ∈ (t.graphAtD H L).edges)).card :=
    Finset.card_pos.2 ⟨L, Finset.mem_filter.2 ⟨hL, heL⟩⟩
  obtain ⟨a, ha, hea⟩ := mem_deleted_iff.1 hd
  have h2 : 1 ≤ (t.internalAddrs.filter (fun a => e ∈ t.delAt H a)).card :=
    Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, hea⟩⟩
  omega

/-- A deleted edge at a vertex `u ∉ Dup` of a leaf `L` has its other end outside `L`. -/
theorem not_mem_leaf_of_mem_deleted {t : STree V} {H : FGraph V} {L : Addr}
    (hL : L ∈ t.leafAddrs) {u x : V} (hu : u ∉ t.dup H) (huL : u ∈ (t.graphAtD H L).verts)
    (hd : s(u, x) ∈ t.deleted H) : x ∉ (t.graphAtD H L).verts := by
  intro hxL
  obtain ⟨a, ha, he⟩ := mem_deleted_iff.1 hd
  have hua := (mem_verts_of_mem_delAt t H he).1
  have haL := prefix_of_mem_of_not_mem_dup hu hL huL (internalAddrs_subset_nodeAddrs t ha) hua
  exact not_mem_leaf_of_mem_delAt ha hL haL he huL hxL

end STree

namespace Run

variable {run : Run V} {G : FGraph V}

theorem DupStar_of_isRound {l : ℕ} (hl : run.IsRound l) :
    run.DupStar G l = (run.twoLevel G l).dup (run.graph' G l) := if_pos hl

theorem X0_eq_graphAtD (l : ℕ) (a : Addr) :
    run.X0 G l a = (run.twoLevel G l).graphAtD (run.graph' G l) a := rfl

/-- `D_l ⊆ Dup*_l` at the run level. -/
theorem D_subset_DupStar' (l : ℕ) : run.D G l ⊆ run.DupStar G l := by
  by_cases hl : run.IsRound l
  · simp only [D, DupStar, if_pos hl]
    exact Round.D_subset_DupStar
  · simp [hl]

/-- The guests of a pre-part of a round lie in `Dup*`. -/
theorem guests_subset_DupStar {l : ℕ} (hl : run.IsRound l) (a : Addr) :
    run.guests G l a ⊆ run.DupStar G l := by
  intro v hv
  apply D_subset_DupStar' l
  simp only [D, if_pos hl]
  exact Round.guests_subset_D a hv

theorem guests_subset_Z0 (l : ℕ) (a : Addr) : run.guests G l a ⊆ run.Z0 G l a :=
  Round.guests_subset _ _ a

/-- An edge of `G_l`, `l > r`, is an edge of `G'_r` that passes down at round `r`. -/
theorem passes_of_mem_graph {r l : ℕ} (hr : run.IsRound r) (hrl : r < l) {e : Sym2 V}
    (he : e ∈ (run.graph G l).edges) :
    e ∈ (run.graph' G r).edges ∧ Round.assign (run.graph G r) (run.choice r) e = none := by
  have h1 : e ∈ (run.graph G (r + 1)).edges := graph_edges_subset_of_le run G hrl he
  rw [graph_succ_of_isRound run G hr, Round.next_edges] at h1
  exact (Round.mem_passed _ _).1 h1

/-- `τ_l ≥ 1` for every real `d` (`M ≥ 2^{40}`, so `Λ ≥ 40`, `s ≥ 1`). -/
theorem one_le_tauOf (d : ℝ) : 1 ≤ tauOf d := by
  have hM : (2 : ℝ) ^ 40 ≤ (MOf d : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have hM1 : (1 : ℝ) < (MOf d : ℝ) := lt_of_lt_of_le (by norm_num) hM
  have hL : (40 : ℝ) ≤ LamOf d := by
    unfold LamOf
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    have : (2 : ℝ) ^ (40 : ℝ) = (2 : ℝ) ^ (40 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
    rw [this]; exact hM
  have hs : 1 ≤ sOf d := by
    unfold sOf
    rw [Nat.one_le_ceil_iff]
    have : (1 : ℝ) ≤ LamOf d ^ sigmaC := one_le_pow₀ (by linarith)
    linarith
  unfold tauOf
  rw [Nat.one_le_ceil_iff]
  have hs' : (1 : ℝ) ≤ (sOf d : ℝ) := by exact_mod_cast hs
  have hl2 : (0 : ℝ) < Real.logb 2 (MOf d : ℝ) := Real.logb_pos (by norm_num) hM1
  positivity

theorem one_le_tau (l : ℕ) : 1 ≤ run.tau G l := one_le_tauOf _

/-- The case split of ORIGIN^τ (a): an edge `ux` of `G'_r` at `u ∈ Y^0 \ Dup*_r` is deleted by
the `τ`-run of the piece above `Y`, or it is an edge of `X^0_Y` not deleted by that `τ`-run. -/
theorem origin_edge_cases {Dstar : ℝ} (hv : run.Valid G Dstar) {r : ℕ} (hr : run.IsRound r)
    {a : Addr} (ha : a ∈ run.prePartAddrs G r) {u : V} (hu : u ∈ run.Z0 G r a)
    (hD : u ∉ run.DupStar G r) {x : V} (he : s(u, x) ∈ (run.graph' G r).edges) :
    s(u, x) ∈ (run.tauRun r (run.pieceOf r a)).deleted (run.piece G r (run.pieceOf r a)) ∨
      (s(u, x) ∈ (run.X0 G r a).edges ∧
        s(u, x) ∉ (run.tauRun r (run.pieceOf r a)).deleted
          (run.piece G r (run.pieceOf r a))) := by
  have hq := pieceOf_mem_bigPieceAddrs run G ha
  have hdel := Valid.deleted_twoLevel run G hv hr
  have hD' : u ∉ (run.twoLevel G r).dup (run.graph' G r) := by
    rwa [← DupStar_of_isRound hr]
  have huP : u ∈ (run.piece G r (run.pieceOf r a)).verts := by
    obtain ⟨b, -, hab, hX⟩ := exists_tauRun_leaf_of_mem_prePartAddrs run G ha
    have : run.Z0 G r a ⊆ (run.piece G r (run.pieceOf r a)).verts := by
      intro v hv'
      have hv'' : v ∈ (run.X0 G r a).verts := hv'
      rw [hX] at hv''
      exact STree.graphAtD_verts_subset _ _ _ hv''
    exact this hu
  rcases STree.thinCut_edge (run.twoLevel G r) hD' he (Sym2.mem_mk_left u x) with hd | hL
  · left
    rw [hdel, Finset.mem_biUnion] at hd
    obtain ⟨q', hq', hd'⟩ := hd
    have heP : s(u, x) ∈ (run.piece G r q').edges := STree.deleted_subset _ _ hd'
    have huq' : u ∈ (run.piece G r q').verts :=
      (run.piece G r q').edge_verts _ heP u (Sym2.mem_mk_left u x)
    have huG : u ∈ G.verts := Z0_subset_verts run G r a hu
    obtain ⟨q0, -, huniq⟩ := existsUnique_piece_of_notMem_DupStar run G hr huG hD
    have h1 := huniq q' ⟨bigPieceAddrs_subset run G r hq', huq'⟩
    have h2 := huniq (run.pieceOf r a) ⟨bigPieceAddrs_subset run G r hq, huP⟩
    rw [h2, ← h1]
    exact hd'
  · right
    obtain ⟨L, hL, huL, heL, huniq⟩ := hL
    have haL : a = L := huniq a (Round.prePartAddrs_subset_leafAddrs _ _
      (by rw [← prePartAddrs_of_isRound run G hr]; exact ha)) hu
    subst haL
    refine ⟨heL, fun hd => ?_⟩
    have hd2 : s(u, x) ∈ (run.twoLevel G r).deleted (run.graph' G r) := by
      rw [hdel, Finset.mem_biUnion]
      exact ⟨_, hq, hd⟩
    exact STree.not_mem_deleted_of_mem_leaf _ hL heL hd2

/-- (β) gives `x ∉ Y^0`: the other end of a deleted edge at `u ∈ Y^0 \ Dup*_r` lies outside the
leaf `Y^0` of the `τ`-run. -/
theorem notMem_Z0_of_deleted {r : ℕ} {a : Addr} (ha : a ∈ run.prePartAddrs G r) {u : V}
    (hu : u ∈ run.Z0 G r a) (hD : u ∉ run.DupStar G r) {x : V}
    (hd : s(u, x) ∈ (run.tauRun r (run.pieceOf r a)).deleted (run.piece G r (run.pieceOf r a))) :
    x ∉ run.Z0 G r a := by
  have hq := pieceOf_mem_bigPieceAddrs run G ha
  obtain ⟨b, hb, -, hX⟩ := exists_tauRun_leaf_of_mem_prePartAddrs run G ha
  have hD' : u ∉ (run.tauRun r (run.pieceOf r a)).dup (run.piece G r (run.pieceOf r a)) :=
    fun h => hD (tauRun_dup_subset_DupStar run G hq h)
  have hu' : u ∈ ((run.tauRun r (run.pieceOf r a)).graphAtD
      (run.piece G r (run.pieceOf r a)) b).verts := by
    rw [← hX]; exact hu
  intro hx
  have hx' : x ∈ ((run.tauRun r (run.pieceOf r a)).graphAtD
      (run.piece G r (run.pieceOf r a)) b).verts := by
    rw [← hX]; exact hx
  exact STree.not_mem_leaf_of_mem_deleted hb hD' hu' hd hx'

/-- An edge `ux` of `X^0_Y` (`u ∈ Y^0 \ Dup*_r`) that passes down at round `r` is a guest–core
edge of a light `Y`: `Y` is light and `x ∈ S_Y` ((R5) step (1)–(3)). -/
theorem isLight_and_mem_guests_of_passes {Dstar : ℝ} (hv : run.Valid G Dstar) {r : ℕ}
    (hr : run.IsRound r) {a : Addr} (ha : a ∈ run.prePartAddrs G r) {u : V}
    (hD : u ∉ run.DupStar G r) {x : V} (heX : s(u, x) ∈ (run.X0 G r a).edges)
    (hpass : Round.assign (run.graph G r) (run.choice r) (s(u, x)) = none) :
    run.isLight G r a ∧ x ∈ run.guests G r a := by
  classical
  have hvr := Valid.round run G hv hr
  have ha' : a ∈ Round.prePartAddrs (run.graph G r) (run.choice r) := by
    rw [← prePartAddrs_of_isRound run G hr]; exact ha
  have hsym : s(u, x) ∈ (run.Z0 G r a).sym2 := FGraph.edges_subset_sym2 heX
  have huZ : u ∈ run.Z0 G r a := Finset.mem_sym2_iff.1 hsym u (Sym2.mem_mk_left u x)
  have hxZ : x ∈ run.Z0 G r a := Finset.mem_sym2_iff.1 hsym x (Sym2.mem_mk_right u x)
  by_cases hl : run.isLight G r a
  · refine ⟨hl, ?_⟩
    by_contra hx
    have hug : u ∉ run.guests G r a := fun h => hD (guests_subset_DupStar hr a h)
    have hpv : s(u, x) ∈ (Round.partVerts (run.graph G r) (run.choice r) a).sym2 := by
      unfold Round.partVerts
      rw [if_pos (show Round.isLight _ _ a from hl)]
      rw [Finset.mem_sym2_iff]
      intro v hv'
      rcases Sym2.mem_iff.1 hv' with rfl | rfl
      · exact Finset.mem_sdiff.2 ⟨huZ, hug⟩
      · exact Finset.mem_sdiff.2 ⟨hxZ, hx⟩
    exact Round.assign_ne_none_of_mem_partVerts hvr ha' hpv hpass
  · exact absurd hpass (Round.assign_ne_none_of_not_isLight hvr ha' hl hsym)

end Run

end HB

open HB.Run in
/-- [s2:propOrigin] (a) "`u` lies in a unique `s = 0` piece `𝒫` and in a unique leaf of the
two-level recursion, namely `Y` (so `Y^0 ⊆ V(𝒫)`). Every edge `ux` of `G_{r+1}` is of exactly one
of the following two types: (β) … (α) … A standalone `Y` (GC-parts included) has no edges of type
(α). Since `E(G_l) ⊆ E(G_{r+1})` for `l > r`, the same classification applies to the edges `ux`
of `G_l`." -/
theorem originTypes : EG.Spec.OriginTypesStatement := by
  intro V _ G Dstar run hv r hr a ha u hu
  have hR : run.IsRound r := Finset.mem_Icc.1 hr
  obtain ⟨huZ, hD⟩ := Finset.mem_sdiff.1 hu
  have hq := Run.pieceOf_mem_bigPieceAddrs run G ha
  have hZP : run.Z0 G r a ⊆ (run.piece G r (run.pieceOf r a)).verts := by
    obtain ⟨b, -, -, hX⟩ := Run.exists_tauRun_leaf_of_mem_prePartAddrs run G ha
    intro v hv'
    have hv'' : v ∈ (run.X0 G r a).verts := hv'
    rw [hX] at hv''
    exact HB.STree.graphAtD_verts_subset _ _ _ hv''
  have huG : u ∈ G.verts := Run.Z0_subset_verts run G r a huZ
  obtain ⟨q0, -, huniq⟩ := Run.existsUnique_piece_of_notMem_DupStar run G hR huG hD
  have hq0 : run.pieceOf r a = q0 :=
    huniq _ ⟨Run.bigPieceAddrs_subset run G r hq, hZP huZ⟩
  -- classification of one edge
  have hclass : ∀ l : ℕ, r < l → ∀ x : V, s(u, x) ∈ (run.graph G l).edges →
      (run.OriginBeta G r a u x ∧ x ∈ (run.piece G r (run.pieceOf r a)).verts ∧
          ¬ run.OriginAlpha G r a u x) ∨
        (run.OriginAlpha G r a u x ∧ ¬ run.OriginBeta G r a u x ∧
          s(u, x) ∉ (run.tauRun r (run.pieceOf r a)).deleted
            (run.piece G r (run.pieceOf r a))) := by
    intro l hrl x hx
    obtain ⟨he', hpass⟩ := passes_of_mem_graph hR hrl hx
    rcases origin_edge_cases hv hR ha huZ hD he' with hd | ⟨heX, hnd⟩
    · left
      have hxZ := notMem_Z0_of_deleted ha huZ hD hd
      have heP : s(u, x) ∈ (run.piece G r (run.pieceOf r a)).edges :=
        HB.STree.deleted_subset _ _ hd
      refine ⟨⟨hxZ, hd⟩, (run.piece G r (run.pieceOf r a)).edge_verts _ heP x
        (Sym2.mem_mk_right u x), fun hα => hxZ (guests_subset_Z0 r a hα.2.1)⟩
    · right
      obtain ⟨hl, hxg⟩ := isLight_and_mem_guests_of_passes hv hR ha hD heX hpass
      exact ⟨⟨hl, hxg, heX⟩, fun hβ => hβ.1 (guests_subset_Z0 r a hxg), hnd⟩
  refine ⟨Run.bigPieceAddrs_subset run G r hq, fun q hq' => ⟨fun huq => ?_, fun h => ?_⟩,
    fun b hb => ⟨fun hub => ?_, fun h => h ▸ huZ⟩, hZP, hclass,
    fun hnl l _ x _ hα => hnl hα.1⟩
  · rw [hq0]; exact huniq q ⟨hq', huq⟩
  · rw [h]; exact hZP huZ
  · have hD' : u ∉ (run.twoLevel G r).dup (run.graph' G r) := by
      rwa [← Run.DupStar_of_isRound hR]
    have ha' : a ∈ (run.twoLevel G r).leafAddrs := Round.prePartAddrs_subset_leafAddrs _ _
      (by rw [← Run.prePartAddrs_of_isRound run G hR]; exact ha)
    exact HB.STree.eq_of_not_mem_dup hD' hb ha' hub huZ

open Classical in
/-- [s2:propOrigin] (b) "For every vertex `h` and every round `l > r`,
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l) is of type (β)} ≤ τ_r - 1`." -/
theorem originThin : EG.Spec.OriginThinStatement := by
  intro V _ G Dstar run hv r hr a ha h l hrl
  have hq := Run.pieceOf_mem_bigPieceAddrs run G ha
  obtain ⟨b, hb, -, hX⟩ := Run.exists_tauRun_leaf_of_mem_prePartAddrs run G ha
  set T := run.tauRun r (run.pieceOf r a)
  set P := run.piece G r (run.pieceOf r a)
  have hT := Run.Valid.isTauRun run G hv hq
  have hτ : (0 : ℝ) < (run.tau G r : ℝ) := by
    have := HB.Run.one_le_tau (run := run) (G := G) r
    exact_mod_cast this
  have hlt := HB.STree.thinCut_lt hτ (HB.STree.IsTauRun.tauLabels hT) hb h
  set S := (T.deleted P).filter (fun e => ∃ u ∈ (T.graphAtD P b).verts \ T.dup P, e = s(h, u))
  have hle : ((run.Z0 G r a \ run.DupStar G r).filter
      (fun u => s(h, u) ∈ (run.graph G l).edges ∧ run.OriginBeta G r a u h)).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun u => s(h, u)) ?_ ?_
    · intro u hu
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_sdiff] at hu
      obtain ⟨⟨huZ, hD⟩, -, -, hd⟩ := hu
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, S]
      refine ⟨by rw [Sym2.eq_swap]; exact hd, u, Finset.mem_sdiff.2 ⟨?_, ?_⟩, rfl⟩
      · rw [← hX]; exact huZ
      · exact fun h' => hD (Run.tauRun_dup_subset_DupStar run G hq h')
    · intro u _ v _ huv
      exact Sym2.congr_right.1 huv
  have : (S.card : ℝ) < run.tau G r := hlt
  have hS : S.card < run.tau G r := by exact_mod_cast this
  omega

open Classical in
/-- [s2:propOrigin] (final paragraph) "a guest `x` of a light `Y` is the guest end of fewer than
`θ^GC_r(Y^0)` edges of type (α) (Lemma [s2:lemGC](ii))". -/
theorem originGuestCap : EG.Spec.OriginGuestCapStatement := by
  intro V _ G Dstar run hv r hr a ha hl x hx l hrl
  have hR : run.IsRound r := Finset.mem_Icc.1 hr
  have hgc := (Run.isGC_iff_eBetween run G r a).1 hl.2.2 x hx
  refine lt_of_le_of_lt ?_ hgc
  rw [← FGraph.card_nbrs_inter_eq_eBetween]
  refine Finset.card_le_card (fun u hu => ?_)
  obtain ⟨hu1, -, hα⟩ := Finset.mem_filter.1 hu
  obtain ⟨huZ, hD⟩ := Finset.mem_sdiff.1 hu1
  refine Finset.mem_inter.2 ⟨FGraph.mem_nbrs.2 ?_, Finset.mem_sdiff.2 ⟨huZ, fun hg => ?_⟩⟩
  · show s(x, u) ∈ (run.X0 G r a).edges
    rw [Sym2.eq_swap]; exact hα.2.2
  · exact hD (HB.Run.guests_subset_DupStar hR a hg)

end EG
