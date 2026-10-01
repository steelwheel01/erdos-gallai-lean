module

public import EG.Proof.Chain.JSLCStep2
public import EG.Proof.Chain.JSLCRouting
public import EG.Proof.Chain.JSLCStep7
public import EG.Proof.Chain.HCCP
public import EG.Proof.HB.TowerBLate
public import EG.Lib.Chain.CherrySystem
public import EG.Lib.Gamma.Full

/-!
# JS-LC, Steps 3–8: the setting after Step 2 (manuscript s6:lemJSLC, proof)

Probe unit P2J (probe P-2, part 2), proof round 1. `JslcCtx run G δ S l B J R` bundles what
Steps 3–8 read: the output `J_l`, `R_Y` of Step 2 (`EG.jslcStep2`), the hypotheses of JS-LC, the
Step-1 fact from Lemma EL (`EG.jslcTypes`), Lemma s2:lemCap(ii) (`EG.capPrePart`, declared input),
the Step-7 disjointness (`EG.jslcStep7Disj`) and Lemma s2:lemTower(b) (`EG.towerBLate`, declared
input). `jslcCtx_of` builds it from the hypotheses of `EG.Spec.JSLCStatement`.

Basic facts on the realized beads `R_Y` (Step 3): "Every edge of `R_Y` joins a port (a class-`Y`
port `u` of some `Q*_Z`, with `u ∈ V(Y) \ ⋃_j T_j(Y,l)`) to a centre (a vertex outside `V(Y)`).
The degree of a centre `h` in `R_Y` is at most `d_{Y,l}(h) ≤ m_{Y,l}`. The degree of a port `u` in
`R_Y` is at most `deg_{E_l(Z_u)}(u) ≤ M_l − 1`."
-/

public section

namespace EG.Chain.JSLC

open EG.HB EG.Chain EG.Chain.Cherry

variable {V : Type*} [DecidableEq V]

/-- The setting of Steps 3–8 of the proof of JS-LC. -/
structure JslcCtx (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V) (l : ℕ)
    (B : Addr → Finset (Sym2 V)) (J : Finset (Sym2 V)) (R : PartId → Finset (Sym2 V)) : Prop where
  l3 : 3 ≤ l
  lR : l ≤ run.R
  hδ : IsDesignation run G δ
  hS : S.Coherent run G
  hB : ∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ qs run G δ S l a, u ∈ e
  J_sub : J ⊆ (run.Std G l).biUnion B
  R_sub : ∀ Y, R Y ⊆ (run.Std G l).biUnion B
  cover : ∀ e ∈ (run.Std G l).biUnion B, e ∈ J ∨ ∃ Y, e ∈ R Y
  disjJR : ∀ Y, Disjoint J (R Y)
  disjRR : ∀ Y Y', Y ≠ Y' → Disjoint (R Y) (R Y')
  struct : ∀ Y, ∀ e ∈ R Y, ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
    ∃ h u, e = s(h, u) ∧ u ∈ qs run G δ S l a ∧ δ l u = Y ∧ h ∉ run.ancVerts G Y
  even : ∀ Y, ∀ h ∉ run.ancVerts G Y, Even (degE (R Y) h)
  el : ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a, ∀ h : V, s(h, u) ∈ run.E G l a →
    h ∉ run.ancVerts G (δ l u)
  cap : ∀ a ∈ run.Std G l, ∀ v : V, degE (run.E G l a) v ≤ run.M G l - 1
  s7E : ∀ Y ∈ run.ancestors G, ∀ j, ∀ a ∈ run.Std G l, Disjoint (S.ljs Y l j) (run.E G l a)
  s7Y : ∀ Y ∈ run.ancestors G, ∀ Y' ∈ run.ancestors G, Y ≠ Y' → ∀ j j',
    Disjoint (S.ljs Y l j) (S.ljs Y' l j')
  towerM : run.M G l ^ 13 ≤ run.P G (l - 2)
  towerNu : (run.nuAnc G l : ℝ) ≤ 2.74 * (G.card : ℝ) / (run.P G (l - 2) : ℝ)

variable {run : Run V} {G : FGraph V} {δ : Designation V} {S : StageData V} {l : ℕ}
  {B : Addr → Finset (Sym2 V)} {J : Finset (Sym2 V)} {R : PartId → Finset (Sym2 V)}

namespace JslcCtx

variable (C : JslcCtx run G δ S l B J R)
include C

theorem mem_E_of_mem_B {a : Addr} (ha : a ∈ run.Std G l) {e : Sym2 V} (he : e ∈ B a) :
    e ∈ run.E G l a := (C.hB a ha).1 he

theorem Bu_subset_edges : (run.Std G l).biUnion B ⊆ G.edges := by
  intro e he
  obtain ⟨a, ha, heB⟩ := Finset.mem_biUnion.1 he
  exact E_subset_edges run G l a (C.mem_E_of_mem_B ha heB)

theorem R_subset_edges (Y : PartId) : R Y ⊆ G.edges := (C.R_sub Y).trans C.Bu_subset_edges

theorem port_mem_ancVerts {a : Addr} (ha : a ∈ run.Std G l) {u : V}
    (hu : u ∈ qs run G δ S l a) : u ∈ run.ancVerts G (δ l u) :=
  C.hδ.mem_ancVerts C.l3 ha (qs_subset_classed run G δ S l a hu)

/-- The edge `hu ∈ R_Y` with `h ∉ V(Y)`: `u` is a class-`Y` port in `Q*_Z` and `hu ∈ E_l(Z)`. -/
theorem port_of {Y : PartId} {h u : V} (he : s(h, u) ∈ R Y) (hh : h ∉ run.ancVerts G Y) :
    ∃ a ∈ run.Std G l, u ∈ qs run G δ S l a ∧ δ l u = Y ∧ s(h, u) ∈ run.E G l a := by
  obtain ⟨a, ha, heE, h', u', heq, hu', hY, -⟩ := C.struct Y _ he
  rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, ha, hu', hY, heE⟩
  · exact absurd (hY ▸ C.port_mem_ancVerts ha hu') hh

/-- The hypotheses of the cherry split for `R_Y` with `W = V(Y)`. -/
theorem cherryHyp (Y : PartId) : Cherry.Hyp (R Y) (run.ancVerts G Y) where
  split e he := by
    obtain ⟨a, ha, -, h, u, heq, hu, hY, hh⟩ := C.struct Y e he
    exact ⟨h, u, heq, hh, hY ▸ C.port_mem_ancVerts ha hu⟩
  even := C.even Y

/-- "The degree of a port `u` in `R_Y` is at most `deg_{E_l(Z_u)}(u) ≤ M_l − 1`." -/
theorem degE_port_le (Y : PartId) {u : V} (hu : u ∈ run.ancVerts G Y) :
    degE (R Y) u ≤ run.M G l - 1 := by
  by_cases hne : (edgesAt (R Y) u).Nonempty
  · obtain ⟨e0, he0⟩ := hne
    obtain ⟨he0R, hue0⟩ := FGraph.mem_edgesAt.1 he0
    -- `u` is the port of `e0`
    have hport : ∀ e ∈ R Y, u ∈ e → ∃ a ∈ run.Std G l, u ∈ qs run G δ S l a ∧
        e ∈ run.E G l a := by
      intro e he hue
      obtain ⟨a, ha, heE, h, u', heq, hu', hY, hh⟩ := C.struct Y e he
      rw [heq] at hue
      rcases Sym2.mem_iff.1 hue with rfl | rfl
      · exact absurd hu hh
      · exact ⟨a, ha, hu', heq ▸ heE⟩
    obtain ⟨a0, ha0, hu0, -⟩ := hport e0 he0R hue0
    have hsub : edgesAt (R Y) u ⊆ edgesAt (run.E G l a0) u := by
      intro e he
      obtain ⟨heR, hue⟩ := FGraph.mem_edgesAt.1 he
      obtain ⟨a, ha, hua, heE⟩ := hport e heR hue
      have : a = a0 := eq_of_mem_classed run G ha ha0 (qs_subset_classed run G δ S l a hua)
        (qs_subset_classed run G δ S l a0 hu0)
      subst this
      exact FGraph.mem_edgesAt.2 ⟨heE, hue⟩
    exact (Finset.card_le_card hsub).trans (C.cap a0 ha0 u)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold degE; rw [hne]; exact Nat.zero_le _

/-- "The degree of a centre `h` in `R_Y` is at most `d_{Y,l}(h) ≤ m_{Y,l}`." -/
theorem degE_centre_le (Y : PartId) {h : V} (hh : h ∉ run.ancVerts G Y) :
    degE (R Y) h ≤ mY run G δ Y l := by
  by_cases hne : (edgesAt (R Y) h).Nonempty
  · obtain ⟨e0, he0⟩ := hne
    obtain ⟨he0R, hhe0⟩ := FGraph.mem_edgesAt.1 he0
    have hG : h ∈ G.verts := G.edge_verts e0 (C.R_subset_edges Y he0R) h hhe0
    refine le_trans ?_ (classDeg_le_mY run G δ hG)
    unfold classDeg degE
    refine Finset.card_le_card fun e he => ?_
    obtain ⟨heR, hhe⟩ := FGraph.mem_edgesAt.1 he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hhe
    obtain ⟨a, ha, hw, hY, heE⟩ := C.port_of heR hh
    exact Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2
      ⟨heE, w, qs_subset_classed run G δ S l a hw, rfl, hY⟩⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold degE; rw [hne]; exact Nat.zero_le _

/-- The classes of round `l`. -/
noncomputable abbrev Ycl : Finset PartId := Step2.classes run G δ S l

theorem mem_Ycl_of_mem {Y : PartId} {e : Sym2 V} (he : e ∈ R Y) : Y ∈ Step2.classes run G δ S l := by
  obtain ⟨a, ha, -, -, u, -, hu, hY, -⟩ := C.struct Y e he
  exact Step2.mem_classes.2 ⟨a, ha, u, hu, hY⟩

theorem Ycl_lendGood {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l) :
    Y ∈ lendGoodAnc run G S l := by
  obtain ⟨a, ha, u, hu, rfl⟩ := Step2.mem_classes.1 hY
  exact mem_lendGoodAnc_of_mem_qs run G S C.hδ ha hu

theorem Ycl_ancestors {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l) :
    Y ∈ run.ancestors G := by
  classical
  have := C.Ycl_lendGood hY
  unfold lendGoodAnc at this
  exact (Finset.mem_filter.1 this).1

theorem Ycl_round {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l) : Y.1 + 2 ≤ l := by
  have := C.Ycl_lendGood hY
  classical
  unfold lendGoodAnc at this
  exact (Finset.mem_filter.1 this).2.1

/-- `R_Y ⊆ ⋃_Z E_l(Z)`: an edge of `R_Y` lies in some `E_l(Z)`. -/
theorem R_mem_E {Y : PartId} {e : Sym2 V} (he : e ∈ R Y) : ∃ a ∈ run.Std G l, e ∈ run.E G l a := by
  obtain ⟨a, ha, heE, -⟩ := C.struct Y e he
  exact ⟨a, ha, heE⟩

/-- The lent classes are disjoint from the realized beads (Step 7: "All of them lie in
`Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in `⋃_Z E_l(Z)`"). -/
theorem disjoint_ljs_R {Y : PartId} (hY : Y ∈ run.ancestors G) (j : ℕ) (Y' : PartId) :
    Disjoint (S.ljs Y l j) (R Y') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, ha, heE⟩ := C.R_mem_E he'
  exact Finset.disjoint_left.1 (C.s7E Y hY j a ha) he heE

theorem disjoint_ljs_Bu {Y : PartId} (hY : Y ∈ run.ancestors G) (j : ℕ) :
    Disjoint (S.ljs Y l j) ((run.Std G l).biUnion B) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, ha, heB⟩ := Finset.mem_biUnion.1 he'
  exact Finset.disjoint_left.1 (C.s7E Y hY j a ha) he (C.mem_E_of_mem_B ha heB)

/-- `|⋃_Z B_Z| ≤ n (M_l − 1)` ("Each port has at most `M_l − 1` beads"): every edge of `B_Z` has
an end in `Q*_Z`, and a classed port has degree at most `M_l − 1` in `⋃_Z B_Z`. -/
theorem card_Bu_le : ((run.Std G l).biUnion B).card ≤ G.card * (run.M G l - 1) := by
  classical
  set Bu := (run.Std G l).biUnion B
  set Q := (qsRound run G δ S l).filter (fun u => u ∈ G.verts)
  have hsub : Bu ⊆ Q.biUnion (edgesAt Bu) := by
    intro e he
    obtain ⟨a, ha, heB⟩ := Finset.mem_biUnion.1 he
    obtain ⟨u, hu, hue⟩ := (C.hB a ha).2 e heB
    have huG : u ∈ G.verts := G.edge_verts e (C.Bu_subset_edges he) u hue
    exact Finset.mem_biUnion.2 ⟨u, Finset.mem_filter.2 ⟨(mem_qsRound run G δ S).2 ⟨a, ha, hu⟩,
      huG⟩, FGraph.mem_edgesAt.2 ⟨he, hue⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have h1 : ∀ u ∈ Q, (edgesAt Bu u).card ≤ run.M G l - 1 := by
    intro u hu
    obtain ⟨a, ha, hu⟩ := (mem_qsRound run G δ S).1 (Finset.mem_filter.1 hu).1
    have huc := qs_subset_classed run G δ S l a hu
    refine le_trans (Finset.card_le_card fun e he => ?_) (C.cap a ha u)
    obtain ⟨heB, hue⟩ := FGraph.mem_edgesAt.1 he
    obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.1 heB
    have heE := C.mem_E_of_mem_B hb heb
    have : b = a := eq_of_mem_Z0_of_notMem_D run G (Std_subset_prePartAddrs run G l hb)
      (Std_subset_prePartAddrs run G l ha)
      (Run.partVerts_subset_Z0 run G l b (Run.mem_partVerts_of_mem_E run G heE hue))
      (classed_subset_Z0 run G l a huc)
      (not_mem_D_of_mem_ports run G (classed_subset_ports run G l a huc))
    subst this
    exact FGraph.mem_edgesAt.2 ⟨heE, hue⟩
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  unfold FGraph.card
  exact Finset.card_le_card (fun u hu => (Finset.mem_filter.1 hu).2)

/-- For a non-giant pair `(Y,l)`, `m_{Y,l} ≤ 2γ_l`: all class-`Y` edges at `h` lie in `Bead_{Y,l}`
(Lemma EL) and in one component of it. -/
theorem mY_le_of_not_isGiant {Y : PartId} (hng : ¬ IsGiant run G δ Y l) :
    mY run G δ Y l ≤ 2 * gammaL run G l := by
  classical
  unfold mY
  refine Finset.sup_le fun h _ => ?_
  by_cases hne : (classDeg run G δ Y l h) = 0
  · rw [hne]; exact Nat.zero_le _
  · -- all class-`Y` edges at `h` lie in the component of `h` in `Bead_{Y,l}`
    set Bd := Bead run G δ Y l
    set Cc := (edgeGraph Bd).connectedComponentMk h
    have hsub : ((run.Std G l).biUnion (fun a => (run.E G l a).filter
        (fun e => ∃ u ∈ run.classed G l a, e = s(h, u) ∧ δ l u = Y))) ⊆ compEdges Bd Cc := by
      intro e he
      obtain ⟨a, ha, heE, u, hu, rfl, hY⟩ := (mem_classDeg_set run G δ).1 he
      have hbead : s(h, u) ∈ Bd := by
        unfold Bd Bead
        refine Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2 ⟨heE, h, u, rfl, hu, hY, ?_⟩⟩
        by_cases hc : h ∈ run.classed G l a
        · right
          intro hhY
          exact C.el a ha u hu h heE (hY ▸ hhY ▸ C.hδ.mem_ancVerts C.l3 ha hc)
        · exact Or.inl hc
      exact mem_compEdges_of_mem_of_mk rfl hbead (Sym2.mem_mk_left _ _)
    have hcomp : Cc ∈ edgeComps Bd := by
      obtain ⟨e, he⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
      have := hsub he
      obtain ⟨heB, hall⟩ := mem_compEdges.1 this
      obtain ⟨a, ha, heE, u, hu, rfl, hY⟩ := (mem_classDeg_set run G δ).1 he
      rw [mem_edgeComps]
      refine ⟨h, ?_, rfl⟩
      unfold edgeVerts
      exact Finset.mem_biUnion.2 ⟨_, heB, by simp⟩
    have hle : (compEdges Bd Cc).card ≤ 2 * gammaL run G l := by
      by_contra hlt
      exact hng ⟨Cc, hcomp, by show 2 * gammaL run G l < (compEdges Bd Cc).card; omega⟩
    unfold classDeg
    exact (Finset.card_le_card hsub).trans hle

end JslcCtx

end EG.Chain.JSLC

namespace EG

open EG.HB EG.Chain EG.Chain.JSLC

/-- The setting of Steps 3–8 from the hypotheses of JS-LC, with `J_l`, `R_Y` from Step 2. -/
theorem exists_jslcCtx {V : Type*} [DecidableEq V] {G : FGraph V} {N0 Dstar : ℝ} {run : Run V}
    {δ : Designation V} {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)}
    (hrh : RunHyp N0 Dstar G run) (hδ : IsDesignation run G δ) (hS : S.Coherent run G)
    (hl : 3 ≤ l) (hlR : l ≤ run.R)
    (hB : ∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ qs run G δ S l a, u ∈ e) :
    ∃ (J : Finset (Sym2 V)) (R : PartId → Finset (Sym2 V)), JslcCtx run G δ S l B J R ∧
      (J.card : ℝ) ≤ jBound run G δ S l ∧ JPlusProps run G δ S l J := by
  have hΓ : Gamma2a Dstar := hrh.gamma2a
  have hrun : run.Valid G Dstar := hrh.2.2.2.2.2
  obtain ⟨J, R, hJ, hR, hcov, hJR, hRR, hst, hev, -, -, hjb, hJP⟩ :=
    EG.jslcStep2 V G Dstar run δ S l B hΓ hrun hδ hl hlR hB
  have H := step2Hyp_of (S := S) hΓ hrun hδ hl hlR hB
  obtain ⟨h7E, h7Y, -, -, -⟩ := EG.jslcStep7Disj V G Dstar run S l hrun hS
  obtain ⟨hTM, hTnu⟩ := EG.towerBLate V G Dstar run hrh.1.1 hrun hrh.2.2.2.2.1 l hl hlR
  exact ⟨J, R, ⟨hl, hlR, hδ, hS, hB, hJ, hR, hcov, hJR, hRR, hst, hev, H.el, H.cap, h7E, h7Y,
    hTM, hTnu⟩, hjb, hJP⟩

end EG
