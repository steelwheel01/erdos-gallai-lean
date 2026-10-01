module

public import EG.Defs.Light.Stages
public import EG.Lib.Stage1.Zones
public import EG.Lib.Found.Graph

/-!
# API for the stage-2 statuses of light parts (`EG/Defs/Light/Stages.lean`, s5:defStages)

* `vm_eq`, `vb_eq` (`rfl`: the manuscript formulas `⌈L_Y^6⌉`, `⌈2^7 L_Y^2 vm_Y⌉`), `AY_spec`
  (the fixed family is a Lemma-HB family whenever one exists);
* light-part facts of the run: `X_verts_of_isLight` (`V(X_Y) = V(Y)`), `ancGraph_eq_X_of_isLight`
  (`H_Y = X_Y`), `E_subset_sym2` (`E_l(Z)` lies inside `V(Z)`);
* the statuses: `demoted_iff_of_isLight` (the list of [s5:defStages]), `parentBad_iff_of_isLight`
  (the explicit triples `(l, c, σ)`), `not_parentBad_of_R_lt` ("If `r ≥ R-1` … never
  parent-bad"), `mem_Bad`, `goodParent_iff_not_mem_Bad`, `not_goodParent_of_demoted`
  ([s5:lemDemoted] (1));
* `Rt`, `Pl`, `parU`: membership, `Rt_subset`, `Pl_subset`, `disjoint_Rt_Pl`, `Rt_union_Pl`
  (`Z = Rt(Z) ⊔ Pl(Z)`), `Rt_eq_empty_of_le_two` ("if `l ≤ 2` there is no round `≤ l-2`, so
  `Rt(Z) = ∅`"), `parU_spec`, `parU_isSome_iff`, `mem_Rt_iff_parU` (`par(v)` is defined exactly on
  `Rt(Z)`);
* zones: `not_mem_Zone_of_zonePhase_ne` (a vertex whose round-`l` phase is not `c` lies in no
  round-`l` phase-`c` zone: the step "(b)" of the proof of [s5:lemChild]);
* arcs: `mem_arcEdges`, `mem_bundleEdges`, per part `ArcSys.mem_verts` (every vertex of an arc
  of `Z` lies in `Z`, (F-d)), `ArcSys.head_ne_getLast` (two distinct ends), `ArcSys.nil`, and the
  same for `ArcHyp` (`ArcHyp_iff`, `ArcHyp.mem_verts`, `ArcHyp.head_ne_getLast`, `ArcHyp.nil`).
-/

public section

namespace EG.Light

open EG.HB EG.Stage1 Finset

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-! ### `vm`, `vb`, `A_Y` -/

theorem vm_eq (Y : PartId) : vm G run Y = ⌈run.LY G Y ^ 6⌉₊ := rfl

theorem vb_eq (Y : PartId) :
    vb G run Y = ⌈(2 : ℝ) ^ 7 * run.LY G Y ^ 2 * (vm G run Y : ℝ)⌉₊ := rfl

/-- The fixed family `A_Y` is a Lemma-HB family for `X_Y`, `vm_Y`, `vb_Y` whenever such a family
exists (its existence under Γ and validity is Lemma [s3:lemHB], a Spec). -/
theorem AY_spec (Y : PartId)
    (h : ∃ A, IsHBFamily (run.X G Y.1 Y.2) (vm G run Y) (vb G run Y) A) :
    IsHBFamily (run.X G Y.1 Y.2) (vm G run Y) (vb G run Y) (AY G run Y) :=
  Classical.epsilon_spec h

/-! ### Light parts of the run -/

theorem isLight_of_mem_lightParts {Y : PartId} (hY : Y ∈ run.lightParts G) :
    run.isLight G Y.1 Y.2 := by
  classical
  exact (Finset.mem_filter.1 hY).2

theorem X_verts_of_isLight {Y : PartId} (h : run.isLight G Y.1 Y.2) :
    (run.X G Y.1 Y.2).verts = run.ancVerts G Y := by
  classical
  have h' : Round.isLight (run.graph G Y.1) (run.choice Y.1) Y.2 := h
  simp only [Run.X, Run.ancVerts, Run.partVerts, Round.X_verts, Round.partVerts]
  rw [if_pos h']

theorem ancGraph_eq_X_of_isLight {Y : PartId} (h : run.isLight G Y.1 Y.2) :
    run.ancGraph G Y = run.X G Y.1 Y.2 := by
  classical
  have h' : Round.isLight (run.graph G Y.1) (run.choice Y.1) Y.2 := h
  simp only [Run.ancGraph, Run.partGraph, Round.partGraph, Run.X]
  rw [if_pos h']

/-- Every edge of `E_l(Z)` has both ends in `V(Z)` (s2:propStructure (iii), from the definition
of the assignment (R5)). -/
theorem E_subset_sym2 (l : ℕ) (a : Addr) : run.E G l a ⊆ (run.partVerts G l a).sym2 := by
  unfold Run.E
  split_ifs
  · exact Round.E_subset_sym2 _ _ a
  · exact Finset.empty_subset _

theorem mem_partVerts_of_mem_E {l : ℕ} {a : Addr} {e : Sym2 V} (he : e ∈ run.E G l a) {v : V}
    (hv : v ∈ e) : v ∈ run.partVerts G l a :=
  Finset.mem_sym2_iff.1 (E_subset_sym2 l a he) v hv

/-! ### Statuses -/

theorem demoted_iff (ω : Outcome G run) (Y : PartId) :
    demoted ω Y ↔ ¬ E1 ω Y ∨ ¬ COLa G run Y (ω.cOutAt Y) := Iff.rfl

/-- [s5:defStages] for a light part: "(E1) fails for `Y` …, or one of `Own_Y`, `Lend_Y` is not a
`(2^{-6}, s_r/8)`-expander on `Y`, or some lent class of `Y` is not a
`(2^{-6}, s_r/(16 k_lend(Y)))`-expander, or some own class of `Y` is not a
`(2^{-6}, s_r/(16 k_own))`-expander". -/
theorem demoted_iff_of_isLight (ω : Outcome G run) {Y : PartId} (hY : run.isLight G Y.1 Y.2) :
    demoted ω Y ↔ ¬ E1 ω Y ∨
      ¬ ((Own G run Y (ω.colAt Y)).IsExpander (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 8) ∧
        (Lend G run Y (ω.colAt Y)).IsExpander (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 8) ∧
        (∀ i ∈ lentIdx G run Y, (lentClass G run Y (ω.colAt Y) i).IsExpander (2 ^ (-6 : ℤ))
          ((run.s G Y.1 : ℝ) / (16 * klend G run Y))) ∧
        (∀ o : Fin (kown G run Y), (ownClass G run Y (ω.colAt Y) o).IsExpander (2 ^ (-6 : ℤ))
          ((run.s G Y.1 : ℝ) / (16 * kown G run Y)))) := by
  rw [demoted_iff, COLa_iff_of_isLight G run hY]
  rfl

/-- [s5:defStages] for a light part: "`Y` is parent-bad if for some `(l,c,σ)` with
`r+2 ≤ l ≤ R`, `c ∈ [4]`, `σ ∈ [T^sl_Y]`, the class `LU_{Y,l,c,σ}` is not
`(2^{12} L_Y^4, t_Y)`-path connected through `Zone_{Y,l,c,σ}`" (`σ` `0`-based). -/
theorem parentBad_iff_of_isLight (ω : Outcome G run) {Y : PartId}
    (hY : run.isLight G Y.1 Y.2) :
    parentBad ω Y ↔ ∃ (l : ℕ) (c : Fin 4) (σ : ℕ), Y.1 + 2 ≤ l ∧ l ≤ run.R ∧
      σ < Tslot G run Y ∧
      ¬ (LU G run Y (ω.colAt Y) l c σ).IsPathConnected (2 ^ 12 * run.LY G Y ^ 4)
          (tY G run Y : ℝ) (Zone G run ω.zone Y (LentTag.U l c σ)) := by
  unfold parentBad COLc
  push Not
  constructor
  · rintro ⟨i, hi, hn⟩
    obtain ⟨-, l, c, σ, rfl, hl, hσ⟩ := mem_IU.1 hi
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 hl
    exact ⟨l, c, σ, hl1, hl2, hσ, hn⟩
  · rintro ⟨l, c, σ, hl1, hl2, hσ, hn⟩
    exact ⟨LentTag.U l c σ, mem_IU.2 ⟨hY, l, c, σ, rfl, Finset.mem_Icc.2 ⟨hl1, hl2⟩, hσ⟩,
      hn⟩

/-- [s5:defStages] "If `r ≥ R-1`, the family `I^U` of `Y` is empty …, so `Y` … is never
parent-bad." -/
theorem not_parentBad_of_R_lt (ω : Outcome G run) {Y : PartId} (hY : run.R < Y.1 + 2) :
    ¬ parentBad ω Y := by
  unfold parentBad COLc
  push Not
  intro i hi
  obtain ⟨-, l, c, σ, rfl, hl, -⟩ := mem_IU.1 hi
  have := (lateRounds_eq_empty_iff run).2 hY
  rw [this] at hl
  simp at hl

/-- Standalone ancestors are never parent-bad (their family `I^U` is empty). -/
theorem not_parentBad_of_not_isLight (ω : Outcome G run) {Y : PartId}
    (hY : ¬ run.isLight G Y.1 Y.2) : ¬ parentBad ω Y := by
  unfold parentBad COLc
  push Not
  intro i hi
  rw [IU_eq_empty_of_not_isLight hY] at hi
  simp at hi

theorem mem_Bad (ω : Outcome G run) {Y : PartId} :
    Y ∈ Bad ω ↔ Y ∈ run.lightParts G ∧ (demoted ω Y ∨ parentBad ω Y) := by
  classical
  unfold Bad
  rw [Finset.mem_filter]

theorem Bad_subset_lightParts (ω : Outcome G run) : Bad ω ⊆ run.lightParts G := by
  classical
  exact Finset.filter_subset _ _

theorem goodParent_iff_not_mem_Bad (ω : Outcome G run) {Y : PartId} :
    goodParent ω Y ↔ Y ∈ run.lightParts G ∧ Y ∉ Bad ω := by
  rw [mem_Bad, goodParent]
  tauto

/-- [s5:lemDemoted] (1) "A demoted part lies in `Bad`, so it is not a good parent". -/
theorem not_goodParent_of_demoted (ω : Outcome G run) {Y : PartId} (h : demoted ω Y) :
    ¬ goodParent ω Y :=
  fun hg => hg.2.1 h

theorem mem_goodParents (ω : Outcome G run) {l : ℕ} {Y : PartId} :
    Y ∈ goodParents ω l ↔ goodParent ω Y ∧ Y.1 + 2 ≤ l := by
  classical
  unfold goodParents
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩

theorem goodParents_eq_empty_of_le_two (ω : Outcome G run) {l : ℕ} (hl : l ≤ 2) :
    goodParents ω l = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro Y hY
  obtain ⟨hg, hr⟩ := (mem_goodParents ω).1 hY
  have := Run.isRound_of_mem_parts run G (Finset.mem_filter.1 hg.1).1
  have := this.1
  omega

/-! ### `Rt`, `Pl`, `par` -/

theorem mem_Rt (ω : Outcome G run) {Z : PartId} {v : V} :
    v ∈ Rt ω Z ↔ v ∈ run.ancVerts G Z ∧
      ∃ Y, goodParent ω Y ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y := by
  classical
  unfold Rt
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hv, Y, hY, hvY⟩
    exact ⟨hv, Y, ((mem_goodParents ω).1 hY).1, ((mem_goodParents ω).1 hY).2, hvY⟩
  · rintro ⟨hv, Y, hg, hr, hvY⟩
    exact ⟨hv, Y, (mem_goodParents ω).2 ⟨hg, hr⟩, hvY⟩

theorem mem_Pl (ω : Outcome G run) {Z : PartId} {v : V} :
    v ∈ Pl ω Z ↔ v ∈ run.ancVerts G Z ∧ v ∉ Rt ω Z := by
  unfold Pl
  rw [Finset.mem_sdiff]

theorem Rt_subset (ω : Outcome G run) (Z : PartId) : Rt ω Z ⊆ run.ancVerts G Z := by
  classical
  exact Finset.filter_subset _ _

theorem Pl_subset (ω : Outcome G run) (Z : PartId) : Pl ω Z ⊆ run.ancVerts G Z :=
  Finset.sdiff_subset

theorem disjoint_Rt_Pl (ω : Outcome G run) (Z : PartId) : Disjoint (Rt ω Z) (Pl ω Z) :=
  Finset.disjoint_sdiff

/-- [s5:lemChild] "`Rt(Z) ⊔ Pl(Z) = Z` by definition". -/
theorem Rt_union_Pl (ω : Outcome G run) (Z : PartId) : Rt ω Z ∪ Pl ω Z = run.ancVerts G Z :=
  Finset.union_sdiff_of_subset (Rt_subset ω Z)

/-- [s5:lemChild] (d) "If `l ≤ 2` there is no round `≤ l-2`, so `Rt(Z) = ∅`." -/
theorem Rt_eq_empty_of_le_two (ω : Outcome G run) {Z : PartId} (hZ : Z.1 ≤ 2) : Rt ω Z = ∅ := by
  classical
  unfold Rt
  rw [goodParents_eq_empty_of_le_two ω hZ]
  simp

theorem Pl_eq_of_le_two (ω : Outcome G run) {Z : PartId} (hZ : Z.1 ≤ 2) :
    Pl ω Z = run.ancVerts G Z := by
  rw [Pl, Rt_eq_empty_of_le_two ω hZ, Finset.sdiff_empty]

theorem parU_isSome_iff (ω : Outcome G run) (l : ℕ) (v : V) :
    (parU ω l v).isSome ↔ ∃ Y, goodParent ω Y ∧ Y.1 + 2 ≤ l ∧ v ∈ run.ancVerts G Y := by
  classical
  unfold parU
  split_ifs with h
  · simp only [Option.isSome_some, true_iff]
    obtain ⟨Y, hY⟩ := h
    rw [Finset.mem_filter] at hY
    exact ⟨Y, ((mem_goodParents ω).1 hY.1).1, ((mem_goodParents ω).1 hY.1).2, hY.2⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨Y, hg, hr, hv⟩
    exact h ⟨Y, Finset.mem_filter.2 ⟨(mem_goodParents ω).2 ⟨hg, hr⟩, hv⟩⟩

/-- [s5:defStages] `par(v)` is "the good parent of the smallest round `≤ l-2` that contains `v`":
if `parU ω l v = some Y` then `Y` is a good parent of round `≤ l - 2` containing `v`, of smallest
round among these. -/
theorem parU_spec (ω : Outcome G run) {l : ℕ} {v : V} {Y : PartId} (h : parU ω l v = some Y) :
    goodParent ω Y ∧ Y.1 + 2 ≤ l ∧ v ∈ run.ancVerts G Y ∧
      ∀ Y', goodParent ω Y' → Y'.1 + 2 ≤ l → v ∈ run.ancVerts G Y' → Y.1 ≤ Y'.1 := by
  classical
  unfold parU at h
  split_ifs at h with hne
  obtain rfl := Option.some.inj h
  -- existence of a minimiser
  have hex : ∃ Y : PartId, Y ∈ goodParents ω l ∧ v ∈ run.ancVerts G Y ∧
      ∀ Y' ∈ goodParents ω l, v ∈ run.ancVerts G Y' → Y.1 ≤ Y'.1 := by
    obtain ⟨Y, hY, hmin⟩ := ((goodParents ω l).filter fun Y => v ∈ run.ancVerts G Y).exists_min_image
      Prod.fst hne
    rw [Finset.mem_filter] at hY
    exact ⟨Y, hY.1, hY.2, fun Y' hY' hv' => hmin Y' (Finset.mem_filter.2 ⟨hY', hv'⟩)⟩
  obtain ⟨h1, h2, h3⟩ := Classical.epsilon_spec hex
  refine ⟨((mem_goodParents ω).1 h1).1, ((mem_goodParents ω).1 h1).2, h2, ?_⟩
  intro Y' hg hr hv
  exact h3 Y' ((mem_goodParents ω).2 ⟨hg, hr⟩) hv

/-- `par(v)` is defined exactly on `Rt(Z)`: for `v ∈ V(Z)`, `v ∈ Rt(Z)` iff `parU ω (r(Z)) v`
is `some _`. -/
theorem mem_Rt_iff_parU (ω : Outcome G run) {Z : PartId} {v : V} :
    v ∈ Rt ω Z ↔ v ∈ run.ancVerts G Z ∧ (parU ω Z.1 v).isSome := by
  rw [mem_Rt, parU_isSome_iff]

/-! ### Zones and arcs -/

/-- A vertex that does not carry a round-`l` zone of phase `c` lies in no round-`l` phase-`c` zone
(for every assignment of zone labels; the step "(b)" of the proof of [s5:lemChild]: "If `x` lay in
a round-`l` phase-`c` zone `Zone_{Y,l,c,σ}`, then `x` would carry a round-`l` zone of phase `c`,
i.e. `ext(x) = c`"). -/
theorem not_mem_Zone_of_zonePhase_ne (ζ : ↥G.verts → Option ZIdx) {l : ℕ} {c : Fin 4} {x : V}
    (h : zonePhase ζ l x ≠ some c) (Y : PartId) (σ : ℕ) :
    x ∉ Zone G run ζ Y (LentTag.U l c σ) := by
  intro hx
  exact h ((zonePhase_eq_some_iff ζ l x c).2 ⟨Y, σ, (mem_Zone.1 hx).2⟩)

theorem mem_arcEdges {as : List (Arc V)} {e : Sym2 V} :
    e ∈ arcEdges as ↔ ∃ a ∈ as, e ∈ walkEdges a.1 := by
  simp [arcEdges]

theorem mem_bundleEdges (ω : Outcome G run) {l : ℕ} {arcs : PartId → List (Arc V)} {c : Fin 4}
    {e : Sym2 V} :
    e ∈ bundleEdges ω l arcs c ↔
      ∃ Z ∈ childParts ω l, ∃ a ∈ arcs Z, a.2 = c ∧ e ∈ walkEdges a.1 := by
  simp only [bundleEdges, Finset.mem_biUnion, mem_arcEdges, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨Z, hZ, a, ⟨ha, hc⟩, he⟩
    exact ⟨Z, hZ, a, ha, hc, he⟩
  · rintro ⟨Z, hZ, a, ha, hc, he⟩
    exact ⟨Z, hZ, a, ⟨ha, hc⟩, he⟩

theorem mem_childParts (ω : Outcome G run) {l : ℕ} {Z : PartId} :
    Z ∈ childParts ω l ↔ Z ∈ run.lightParts G ∧ Z.1 = l ∧ ¬ demoted ω Z := by
  classical
  unfold childParts
  rw [Finset.mem_filter]

/-- (F-d) "every vertex of an arc of `Z` lies in `Z` (its edges lie in `H_0(Z) ⊆ E_l(Z)`)", per
part. -/
theorem ArcSys.mem_verts {ω : Outcome G run} {Z : PartId} {H0 : Finset (Sym2 V)}
    {as : List (Arc V)} (hH0 : H0Adm ω Z H0) (h : ArcSys ω Z H0 as) {a : Arc V} (ha : a ∈ as)
    {x : V} (hx : x ∈ a.1) : x ∈ run.ancVerts G Z := by
  obtain ⟨-, harc, -⟩ := h
  obtain ⟨hp, hlen, -⟩ := harc a ha
  have h2 : 2 ≤ a.1.length := by unfold pathLength at hlen; omega
  obtain ⟨e, he, hxe⟩ := exists_mem_walkEdges_of_mem h2 hx
  have heE : e ∈ run.E G Z.1 Z.2 := hH0.2 (hp.edges_mem he)
  exact mem_partVerts_of_mem_E heE hxe

/-- (F-d) "every arc of `Z` is a path with at least one edge, hence with two distinct ends", per
part. -/
theorem ArcSys.head_ne_getLast {ω : Outcome G run} {Z : PartId} {H0 : Finset (Sym2 V)}
    {as : List (Arc V)} (h : ArcSys ω Z H0 as) {a : Arc V} (ha : a ∈ as) {x y : V}
    (hx : a.1.head? = some x) (hy : a.1.getLast? = some y) : x ≠ y := by
  obtain ⟨-, harc, -⟩ := h
  obtain ⟨hp, hlen, -⟩ := harc a ha
  obtain ⟨p, c⟩ := a
  simp only at hp hlen hx hy
  have h2 : 2 ≤ p.length := by unfold pathLength at hlen; omega
  match p, h2, hx, hy, hp with
  | u :: w :: t, _, hx, hy, hp =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    intro hxy
    subst hxy
    have hnd := hp.nodup
    rw [List.getLast?_eq_some_getLast (by simp)] at hy
    have hmem : (u :: w :: t).getLast (by simp) ∈ w :: t := by
      rw [List.getLast_cons (by simp)]
      exact List.getLast_mem _
    rw [Option.some.injEq] at hy
    rw [hy] at hmem
    exact (List.nodup_cons.1 hnd).1 hmem

/-- No arcs at all satisfy [s5:lemChild] (b)–(d), for every `H_0`. -/
theorem ArcSys.nil (ω : Outcome G run) (Z : PartId) (H0 : Finset (Sym2 V)) :
    ArcSys ω Z H0 [] := by
  refine ⟨by simp, by simp, by simp, ?_, fun _ => rfl⟩
  intro x
  simp [pathEndCount]

/-- `ArcHyp` is the per-part predicate `H0Adm ∧ ArcSys` over the non-demoted light parts of round
`l` (definitional). -/
theorem ArcHyp_iff {ω : Outcome G run} {l : ℕ} {H0 : PartId → Finset (Sym2 V)}
    {arcs : PartId → List (Arc V)} :
    ArcHyp ω l H0 arcs ↔ ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z) ∧ ArcSys ω Z (H0 Z) (arcs Z) :=
  Iff.rfl

/-- (F-d) "every vertex of an arc of `Z` lies in `Z` (its edges lie in `H_0(Z) ⊆ E_l(Z)`)". -/
theorem ArcHyp.mem_verts {ω : Outcome G run} {l : ℕ} {H0 : PartId → Finset (Sym2 V)}
    {arcs : PartId → List (Arc V)} (h : ArcHyp ω l H0 arcs) {Z : PartId}
    (hZ : Z ∈ childParts ω l) {a : Arc V} (ha : a ∈ arcs Z) {x : V} (hx : x ∈ a.1) :
    x ∈ run.ancVerts G Z :=
  (h Z hZ).2.mem_verts (h Z hZ).1 ha hx

/-- (F-d) "every arc of `Z` is a path with at least one edge, hence with two distinct ends". -/
theorem ArcHyp.head_ne_getLast {ω : Outcome G run} {l : ℕ} {H0 : PartId → Finset (Sym2 V)}
    {arcs : PartId → List (Arc V)} (h : ArcHyp ω l H0 arcs) {Z : PartId}
    (hZ : Z ∈ childParts ω l) {a : Arc V} (ha : a ∈ arcs Z) {x y : V}
    (hx : a.1.head? = some x) (hy : a.1.getLast? = some y) : x ≠ y :=
  (h Z hZ).2.head_ne_getLast ha hx hy

/-- No arcs at all are admissible, given the conditions `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`. -/
theorem ArcHyp.nil {ω : Outcome G run} {l : ℕ} {H0 : PartId → Finset (Sym2 V)}
    (hH0 : ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z)) :
    ArcHyp ω l H0 (fun _ => []) :=
  fun Z hZ => ⟨hH0 Z hZ, ArcSys.nil ω Z (H0 Z)⟩

/-! ### The child data -/

@[simp] theorem childData_Z (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).Z = run.ancVerts G Z := rfl

@[simp] theorem childData_O (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).O = run.X G Z.1 Z.2 := rfl

@[simp] theorem childData_A (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).A = AY G run Z := rfl

@[simp] theorem childData_Rt (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).Rt = Rt ω Z := rfl

@[simp] theorem childData_Pl (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).Pl = Pl ω Z := rfl

@[simp] theorem childData_ext (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).ext = fun v => zonePhase ω.zone Z.1 v := rfl

/-- The own-class index `J_Z` of the colouring is the Lemma-PV index `pvJ |Z|` of the child data
(definitionally: the own classes are passed with no cast). -/
theorem childData_J (ω : Outcome G run) (Z : PartId) :
    JY G run Z = Vortex.pvJ (childData ω Z).Z.card := rfl

@[simp] theorem childData_R (ω : Outcome G run) (Z : PartId) (j : Fin (JY G run Z)) (c : Fin 4) :
    (childData ω Z).R (j, c) = ownR G run Z (ω.colAt Z) j c := rfl

@[simp] theorem childData_M (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).M = ownM G run Z (ω.colAt Z) := rfl

/-- [s5:lemChild] "(E1'). For `u ∈ Z` we have `ext(u) = *` iff `u` carries no round-`l` zone.
Since `Z` is not demoted, (E1) holds for `Z`; its instance at the round `l = r(Z)` of `Z` states
that for every `w ∈ Z` … `#{u ∈ A_Z(w) : wu ∈ M_Z, ext(u) = *} ≥ L^5/8`": (E1) at `l = r(Z)` in
terms of the child data. -/
theorem E1_childData (ω : Outcome G run) {Z : PartId} (h : E1 ω Z) (hR : Z.1 ≤ run.R) {w : V}
    (hw : w ∈ (childData ω Z).Z) :
    run.LY G Z ^ 5 / 8 ≤ ((((childData ω Z).A w).filter fun u =>
      s(w, u) ∈ (childData ω Z).M.edges ∧ (childData ω Z).ext u = none).card : ℝ) :=
  h Z.1 (Finset.mem_Icc.2 ⟨le_rfl, hR⟩) w hw

end EG.Light
