module

public import EG.Proof.Chain.JSLCGroups

/-!
# JS-LC, Step 7: HCC-P for each cherry system (manuscript s6:lemJSLC, proof, Step 7)

Probe unit P2J (probe P-2, part 2), proof round 1. "Fix a system `𝒮` of `(Y,l)` of depth
`k = k_𝒮`. For `j < k` let `𝒫_j(𝒮)` be the paths of the joint-routing claim, part (d), for the
junction-`j` pairs of `𝒮` … We check the hypotheses of Lemma s6:lemHCCP for `𝒮` …
(D) The clusters of `𝒮` are pairwise vertex-disjoint: … vertex-disjoint cherries for a class.
Centres lie outside `V(Y)` and ports inside, so no vertex is both. Neither meets `⋃_j T_j(Y,l)`,
by part (e) of the joint-routing claim. The sets `T_j(Y,l)` are pairwise disjoint (Definition
s3:defCOL(iv)). (P) … centres of cherries have degree `2`. (JC-P) … The path families for distinct
`j` lie in distinct classes `LJS_{Y,l,j}`, which are disjoint. All of them lie in
`Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in `⋃_Z E_l(Z)`. These sets are disjoint …"
Then Lemma HCC-P (`EG.hccp`) gives one cycle per system (all loads are `1`).
-/

public section

namespace EG.Chain.JSLC

open EG.HB EG.Chain EG.Chain.Cherry

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)} {J : Finset (Sym2 V)}
  {R : PartId → Finset (Sym2 V)} {m : PartId → ℕ} {col : PartId → V × V × V → ℕ}
  {rt : ∀ Y j, usedJ run G R col Y j → List V}

/-- The specification of the routes (`exists_routes`). -/
@[expose] def RouteSpec (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V) (l : ℕ)
    (R : PartId → Finset (Sym2 V)) (col : PartId → V × V × V → ℕ)
    (rt : ∀ Y j, usedJ run G R col Y j → List V) : Prop :=
  ∀ Y j, Y ∈ Step2.classes run G δ S l → j < Stage1.KJS G run l →
    (∀ i, IsPathBetween (S.ljs Y l j) (pair run G R col Y j i).1 (pair run G R col Y j i).2
        (rt Y j i) ∧ IsThrough (Tj run G S Y l j) (rt Y j i)) ∧
    ∀ i i', i ≠ i' → (walkEdges (rt Y j i)).Disjoint (walkEdges (rt Y j i'))

theorem good_of_mem_chs (C : JslcCtx run G δ S l B J R) {Y : PartId} {c : V × V × V}
    (hc : c ∈ chs run G R Y) : Good c := by
  obtain ⟨-, -, hne, h0, h1, h2⟩ := cherry_spec (C.cherryHyp Y) hc
  exact ⟨fun h => h0 (h ▸ h1), fun h => h0 (h ▸ h2), hne⟩

/-- A cherry avoids every junction set `T_j(Y,l)` (claim (e)). -/
theorem cVerts_disjoint_Tj (C : JslcCtx run G δ S l B J R) {Y : PartId} {c : V × V × V}
    (hc : c ∈ chs run G R Y) (j : ℕ) : Disjoint (cVerts c) (Tj run G S Y l j) := by
  have hH := C.cherryHyp Y
  obtain ⟨e1, e2, -, h0, -, -⟩ := cherry_spec hH hc
  have hport : ∀ u, s(c.1, u) ∈ R Y → u ∉ Tj run G S Y l j := by
    intro u he
    obtain ⟨a, -, hu, hY, -⟩ := C.port_of he h0
    rw [← hY]
    exact notMem_Tj_of_mem_qs run G δ S hu j
  rw [Finset.disjoint_left]
  intro v hv hvT
  unfold cVerts at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact h0 (Finset.filter_subset _ _ hvT)
  · exact hport _ e1 hvT
  · exact hport _ e2 hvT

theorem Qs_eq {Y : PartId} {i j : ℕ} (h : i ∈ usedJ run G R col Y j) :
    Qs run G R col rt Y i j = rt Y j ⟨i, h⟩ := by
  unfold Qs; rw [dif_pos h]

theorem mem_usedJ {Y : PartId} {i j : ℕ} (hi : i ∈ used run G R col Y)
    (hj : j < (lst run G R col Y i).length) : i ∈ usedJ run G R col Y j :=
  Finset.mem_filter.2 ⟨hi, hj⟩

/-- The paths of a system lie in the class `LJS_{Y,l,j}`. -/
theorem walkEdges_Qs_subset (hr : RouteSpec run G δ S l R col rt) {Y : PartId}
    (hY : Y ∈ Step2.classes run G δ S l) {i j : ℕ} (hi : i ∈ used run G R col Y)
    (hj : j < (lst run G R col Y i).length) (hjK : j < Stage1.KJS G run l) :
    ∀ e ∈ walkEdges (Qs run G R col rt Y i j), e ∈ S.ljs Y l j := by
  intro e he
  rw [Qs_eq (mem_usedJ hi hj)] at he
  exact ((hr Y j hY hjK).1 _).1.1.2.2 e he

/-- [s6:lemJSLC] (proof, Step 7) the hypotheses of Lemma HCC-P for the system of the group `i` of
`(Y,l)`. -/
theorem sys_valid (C : JslcCtx run G δ S l B J R) (hg : GroupSpec run G l R δ m col)
    (hr : RouteSpec run G δ S l R col rt) {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l)
    {i : ℕ} (hi : i ∈ used run G R col Y) : (sys run G S l R col rt Y i).Valid G := by
  have hH := C.cherryHyp Y
  have hlen := length_lst_le hg Y i
  have hmem : ∀ c ∈ lst run G R col Y i, c ∈ chs run G R Y := fun c hc => (mem_lst.1 hc).1
  have hYa := C.Ycl_ancestors hY
  refine cherrySys_valid (lst_ne_nil hi) (fun c hc => good_of_mem_chs C (hmem c hc))
    (lst_pairwise hg Y i) (fun c hc => (cEdges_subset hH (hmem c hc)).trans (C.R_subset_edges Y))
    (fun j j' _ _ hjj => Tj_disjoint run G S Y l hjj)
    (fun c hc j _ => cVerts_disjoint_Tj C (hmem c hc) j) ?_ ?_ ?_
  · intro j hj
    rw [Qs_eq (mem_usedJ hi hj)]
    obtain ⟨hp, hT⟩ := (hr Y j hY (lt_of_lt_of_le hj hlen)).1 ⟨i, mem_usedJ hi hj⟩
    exact ⟨hp.mono (C.hS.ljs_subset_graph_edges Y l j), hT⟩
  · intro j j' hj hj' hjj
    rw [Finset.disjoint_left]
    intro e he he'
    have h1 := walkEdges_Qs_subset hr hY hi hj (lt_of_lt_of_le hj hlen) e (List.mem_toFinset.1 he)
    have h2 := walkEdges_Qs_subset hr hY hi hj' (lt_of_lt_of_le hj' hlen) e
      (List.mem_toFinset.1 he')
    exact Finset.disjoint_left.1 (C.hS.ljs_disj Y l j l j' (by simpa using hjj)) h1 h2
  · intro j hj c hc
    rw [Finset.disjoint_left]
    intro e he he'
    have h1 := walkEdges_Qs_subset hr hY hi hj (lt_of_lt_of_le hj hlen) e (List.mem_toFinset.1 he)
    exact Finset.disjoint_left.1 (C.disjoint_ljs_R hYa j Y) h1 (cEdges_subset hH (hmem c hc) he')

/-! ### Beads and path edges of a system -/

theorem sys_beads (C : JslcCtx run G δ S l B J R) {Y : PartId} {i : ℕ} :
    (sys run G S l R col rt Y i).beads = (grp run G R col Y i).biUnion cEdges := by
  ext e
  rw [HccpData.mem_beads, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx⟩
    have hc := List.get_mem (lst run G R col Y i) x
    have hgood := good_of_mem_chs C (mem_lst.1 hc).1
    refine ⟨_, Finset.mem_toList.1 hc, ?_⟩
    have : (sys run G S l R col rt Y i).K x = cluster ((lst run G R col Y i).get x) := rfl
    rw [this, cluster_beads hgood] at hx
    exact hx
  · rintro ⟨c, hc, he⟩
    have hcl : c ∈ lst run G R col Y i := Finset.mem_toList.2 hc
    obtain ⟨x, hx⟩ := List.get_of_mem hcl
    refine ⟨x, ?_⟩
    have : (sys run G S l R col rt Y i).K x = cluster ((lst run G R col Y i).get x) := rfl
    rw [this, hx, cluster_beads (good_of_mem_chs C (mem_lst.1 hcl).1)]
    exact he

theorem sys_pathEdges {Y : PartId} {i : ℕ} (j : Fin (sys run G S l R col rt Y i).k) :
    (sys run G S l R col rt Y i).pathEdges j = (walkEdges (Qs run G R col rt Y i j.val)).toFinset := by
  unfold HccpData.pathEdges
  simp [sys, cherrySys]

theorem sys_k {Y : PartId} {i : ℕ} :
    (sys run G S l R col rt Y i).k = (lst run G R col Y i).length := rfl

/-- The path edges of the system of group `i` at junction `j` lie in `LJS_{Y,l,j}`, `j < K^JS_l`. -/
theorem sys_pathEdges_subset (hg : GroupSpec run G l R δ m col) (hr : RouteSpec run G δ S l R col rt)
    {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l) {i : ℕ} (hi : i ∈ used run G R col Y)
    (j : Fin (sys run G S l R col rt Y i).k) :
    (sys run G S l R col rt Y i).pathEdges j ⊆ S.ljs Y l j.val ∧ j.val < Stage1.KJS G run l := by
  have hlen := length_lst_le hg Y i
  have hj : j.val < (lst run G R col Y i).length := j.2
  refine ⟨?_, lt_of_lt_of_le hj hlen⟩
  rw [sys_pathEdges]
  intro e he
  exact walkEdges_Qs_subset hr hY hi hj (lt_of_lt_of_le hj hlen) e (List.mem_toFinset.1 he)

/-- [s6:lemHCCP] applied to one cherry system: sets `F_j ⊆ E(𝒫_j)` and at most one cycle
decomposing its beads together with `⋃_j F_j`. -/
theorem exists_sys_decomp (C : JslcCtx run G δ S l B J R) (hg : GroupSpec run G l R δ m col)
    (hr : RouteSpec run G δ S l R col rt) {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l)
    {i : ℕ} (hi : i ∈ used run G R col Y) :
    ∃ (F : Fin (sys run G S l R col rt Y i).k → Finset (Sym2 V)) (D : List (Obj V)),
      (∀ j, F j ⊆ (sys run G S l R col rt Y i).pathEdges j) ∧
      IsDecomp (((sys run G S l R col rt Y i).beads ∪ Finset.univ.biUnion F : Finset (Sym2 V)) :
        Set (Sym2 V)) D ∧ D.length ≤ 1 ∧ ∀ o ∈ D, ∃ c : List V, o = Obj.cycle c := by
  have hv := sys_valid C hg hr hY hi
  obtain ⟨Φ, hΦ, F, hF, D, hD, hDl, hDc⟩ := EG.hccp V G _ hv
  have hk : 0 < (sys run G S l R col rt Y i).k := by
    rw [sys_k]; exact List.length_pos_iff.2 (lst_ne_nil hi)
  have hΦ1 : Φ = 1 := by
    rw [← (hΦ ⟨0, hk⟩).2]; rfl
  refine ⟨F, D, fun j => (hF j).1, hD, hΦ1 ▸ hDl, fun o ho => ?_⟩
  obtain ⟨c, hc, -⟩ := hDc o ho
  exact ⟨c, hc⟩

end EG.Chain.JSLC
