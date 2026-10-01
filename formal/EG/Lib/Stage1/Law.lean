module

public import EG.Defs.Stage1.Law
public import EG.Lib.Stage1.COL
public import EG.Lib.Stage1.Zones
public import EG.Lib.Stage1.Pool

/-!
# API for the stage-1 law (s7:defSchedule stage 1; TRIAGE §2.7)

`EG.Stage1.law G run` is the image of the product `pi (coordLaw G run)` over the coordinates
`Coord G run` under `Outcome.ofCoords`. This file provides:
* the bijection: `toCoords_ofCoords`, `ofCoords_toCoords`;
* the two general principles (functions of disjoint sets of coordinates):
  `indepFun_of_dependsOn` and `iIndepFun_of_dependsOn`;
* marginals: `map_col` (component (1a) of the ancestor `Y` has law `colouringLaw G run Y`),
  `map_js` ((1c) of `Y`: `jsLaw G run Y`), `map_cOut` (the lending data of `Y`: `colLaw G run Y`,
  the form consumed by the lemCOL Specs), `map_cOutAt`, `map_zone` (`zoneLaw`), `map_pool`
  (`poolLaw`);
* independence ([s7:defSchedule] "four mutually independent families", [s3:defCOL]
  "Consequently: …", [s5:lemZones] (iv), [s7:defPool]): `indepFun_col_js` ("the labels are
  independent of the colours"), `iIndepFun_cOut` ("The data of distinct ancestors are
  independent"), `iIndepFun_col_edges` ("colours of distinct edges are independent"),
  `indepFun_cOut_zone` / `indepFun_cOutAt_zone` (the zones are independent of the lending data of
  every ancestor; the joint form consumed by s3:lemCOL (c)), `indepFun_colJS_zone` ([s5:lemZones]
  (iv)), `indepFun_rest_pool` (the pool labels are independent of all other stage-1 data),
  `iIndepFun_zone`, `iIndepFun_pool` (per-vertex independence);
* support: `law_w`, `mem_supp_law_iff` (an outcome has positive weight iff every coordinate is in
  the support of its law), `col_mem_supp_colouringLaw`, `COLg_of_mem_supp_law` ([s3:lemCOL] (g)
  holds for every outcome of positive weight), `zone_mem_supp` (a zone label is `none` or an
  available `(Y, i)` with `i ∈ I^U(Y)`), `Zone_eq_empty_of_not_mem_IU`, `lightParts_of_zone_eq`,
  `pool_mem_supp` (a pool label is `⊥` or in `poolIdx`), `zonePhase_eq_some_iff_mem_Zone`
  ([s5:defZones] "Equivalently, …");
* per-edge marginal `map_col_apply`, and the per-vertex mixed shapes `iIndepFun_edge_pool`
  ([s7:lemCand] (i)) and `iIndepFun_edge_zone` ([s5:lemE1] (a)).
-/

public section

namespace EG.Stage1

open EG.HB EG.FinDist Finset

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-! ### The bijection with the coordinates -/

@[simp] theorem Outcome.toCoords_ofCoords (f : (c : Coord G run) → CoordVal G run c) :
    (Outcome.ofCoords f).toCoords = f := by
  funext c
  rcases c with p | v | p | v <;> rfl

@[simp] theorem Outcome.ofCoords_toCoords (ω : Outcome G run) : Outcome.ofCoords ω.toCoords = ω := by
  cases ω
  rfl

theorem Outcome.cOutAt_of_mem (ω : Outcome G run) {Y : PartId} (h : Y ∈ run.ancestors G) :
    ω.cOutAt Y = ω.cOut ⟨Y, h⟩ := by
  simp [Outcome.cOutAt, Outcome.colAt, Outcome.jsAt, Outcome.cOut, h]

/-- `T_j(Y,l)` in terms of the JS labels read by `Outcome.labAt`. -/
theorem Outcome.mem_Tj_iff (ω : Outcome G run) {Y : PartId} {l j : ℕ} {y : V} :
    y ∈ Tj G run Y (ω.jsAt Y) l j ↔ y ∈ run.ancVerts G Y ∧ ω.labAt Y l y = some j := by
  simp only [Tj, Finset.mem_filter, Outcome.labAt]
  constructor
  · rintro ⟨hy, hs, h⟩
    exact ⟨hy, by rw [dif_pos hs]; exact h⟩
  · rintro ⟨hy, h⟩
    by_cases hs : (l, y) ∈ jsSites G run Y
    · rw [dif_pos hs] at h
      exact ⟨hy, hs, h⟩
    · rw [dif_neg hs] at h
      exact absurd h (by simp)

variable (G run)

theorem law_eq : law G run = (FinDist.pi (coordLaw G run)).map Outcome.ofCoords := rfl

/-! ### Functions of disjoint sets of coordinates -/

/-- Functions of disjoint sets of stage-1 coordinates are independent: if `X` depends only on the
coordinates in `p` and `Y` only on the others, then `X` and `Y` are independent under the stage-1
law. -/
theorem indepFun_of_dependsOn (p : Coord G run → Prop) {γ δ : Type*}
    {X : Outcome G run → γ} {Y : Outcome G run → δ}
    (hX : ∀ ω ω' : Outcome G run, (∀ c, p c → ω.toCoords c = ω'.toCoords c) → X ω = X ω')
    (hY : ∀ ω ω' : Outcome G run, (∀ c, ¬ p c → ω.toCoords c = ω'.toCoords c) → Y ω = Y ω') :
    (law G run).IndepFun X Y := by
  classical
  rw [law_eq, indepFun_map_iff]
  intro A B
  refine prob_pi_inter_of_dependsOn _ p ?_ ?_
  · intro f g h hf
    simp only [Set.mem_preimage] at hf ⊢
    rw [← hX (Outcome.ofCoords f) (Outcome.ofCoords g) (by simpa using h)]
    exact hf
  · intro f g h hf
    simp only [Set.mem_preimage] at hf ⊢
    rw [← hY (Outcome.ofCoords f) (Outcome.ofCoords g) (by simpa using h)]
    exact hf

/-- Functions of pairwise disjoint blocks of stage-1 coordinates are mutually independent. -/
theorem iIndepFun_of_dependsOn {U : Type*} {β : U → Type*} (B : U → Set (Coord G run))
    (hB : Pairwise fun u v => Disjoint (B u) (B v)) (X : ∀ u, Outcome G run → β u)
    (hX : ∀ u (ω ω' : Outcome G run), (∀ c ∈ B u, ω.toCoords c = ω'.toCoords c) →
      X u ω = X u ω') :
    (law G run).iIndepFun X := by
  rw [law_eq, iIndepFun_map_iff]
  exact iIndepFun_pi_of_dependsOn _ B hB (fun u f => X u (Outcome.ofCoords f))
    fun u f f' h => hX u _ _ (by simpa using h)

/-- The law of a function of a block of coordinates, as a product over the block. -/
theorem map_eq_pi_of_dependsOn {U : Type*} [Fintype U] {β : U → Type*}
    (B : U → Set (Coord G run)) (hB : Pairwise fun u v => Disjoint (B u) (B v))
    (X : ∀ u, Outcome G run → β u)
    (hX : ∀ u (ω ω' : Outcome G run), (∀ c ∈ B u, ω.toCoords c = ω'.toCoords c) →
      X u ω = X u ω') :
    (law G run).map (fun ω u => X u ω) = FinDist.pi fun u => (law G run).map (X u) := by
  exact (iIndepFun_iff_map_eq_pi _).1 (iIndepFun_of_dependsOn G run B hB X hX)

/-- The law of one coordinate. -/
theorem map_toCoords_apply (c : Coord G run) :
    (law G run).map (fun ω => ω.toCoords c) = coordLaw G run c := by
  rw [law_eq, FinDist.map_map]
  have : ((fun ω : Outcome G run => ω.toCoords c) ∘ Outcome.ofCoords) = fun f => f c := by
    funext f; simp
  rw [this, map_eval_pi]

/-! ### Marginals -/

/-- The weight of an outcome is the product weight of its coordinates. -/
theorem law_w (ω : Outcome G run) :
    (law G run).w ω = (FinDist.pi (coordLaw G run)).w ω.toCoords := by
  rw [law_eq, map_w]
  have : (Outcome.ofCoords ⁻¹' {ω} : Set _) = {ω.toCoords} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  rw [this, prob_singleton]

/-- The support of the stage-1 law: an outcome has positive weight iff each of its coordinates is
in the support of its law (TRIAGE §2.7: fixed-outcome statements quantify over this support). -/
theorem mem_supp_law_iff (ω : Outcome G run) :
    ω ∈ (law G run).supp ↔ ∀ c, ω.toCoords c ∈ (coordLaw G run c).supp := by
  rw [mem_supp, law_w G run ω, ← mem_supp, mem_supp_pi]


/-- Component (1a) of the ancestor `Y` has law `colouringLaw G run Y` (independent triples on the
edges of `H_Y`). -/
theorem map_col (Y : ↥(run.ancestors G)) :
    (law G run).map (fun ω => ω.col Y) = colouringLaw G run Y := by
  have h := map_eq_pi_of_dependsOn G run
    (fun e : ↥(run.ancGraph G Y).edges => ({Sum.inl ⟨Y, e⟩} : Set (Coord G run)))
    (fun e e' hee' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inl.injEq, Sigma.mk.inj_iff,
        heq_eq_eq, true_and]
      exact hee')
    (fun e ω => ω.toCoords (Sum.inl ⟨Y, e⟩)) (fun e ω ω' h => h _ (Set.mem_singleton _))
  simp only [map_toCoords_apply] at h
  exact h

/-- The colour of one edge of `H_Y` has law `edgeLaw G run Y` ([s3:defCOL] (i)–(iii)). -/
theorem map_col_apply (Y : ↥(run.ancestors G)) (e : ↥(run.ancGraph G Y).edges) :
    (law G run).map (fun ω => ω.col Y e) = edgeLaw G run Y :=
  map_toCoords_apply G run (Sum.inl ⟨Y, e⟩)

/-- Component (1c) of the ancestor `Y` has law `jsLaw G run Y`. -/
theorem map_js (Y : ↥(run.ancestors G)) :
    (law G run).map (fun ω => ω.js Y) = jsLaw G run Y := by
  have h := map_eq_pi_of_dependsOn G run
    (fun s : ↥(jsSites G run Y) => ({Sum.inr (Sum.inr (Sum.inl ⟨Y, s⟩))} : Set (Coord G run)))
    (fun s s' hss' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inr.injEq, Sum.inl.injEq,
        Sigma.mk.inj_iff, heq_eq_eq, true_and]
      exact hss')
    (fun s ω => ω.toCoords (Sum.inr (Sum.inr (Sum.inl ⟨Y, s⟩)))) (fun s ω ω' h => h _ (Set.mem_singleton _))
  simp only [map_toCoords_apply] at h
  exact h

/-- Component (1b) has law `zoneLaw G run`. -/
theorem map_zone : (law G run).map Outcome.zone = zoneLaw G run := by
  have h := map_eq_pi_of_dependsOn G run
    (fun v : ↥G.verts => ({Sum.inr (Sum.inl v)} : Set (Coord G run)))
    (fun v v' hvv' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inr.injEq, Sum.inl.injEq]
      exact hvv')
    (fun v ω => ω.toCoords (Sum.inr (Sum.inl v))) (fun v ω ω' h => h _ (Set.mem_singleton _))
  simp only [map_toCoords_apply] at h
  exact h

/-- Component (1d) has law `poolLaw G run`. -/
theorem map_pool : (law G run).map Outcome.pool = poolLaw G run := by
  have h := map_eq_pi_of_dependsOn G run
    (fun v : ↥G.verts => ({Sum.inr (Sum.inr (Sum.inr v))} : Set (Coord G run)))
    (fun v v' hvv' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inr.injEq]
      exact hvv')
    (fun v ω => ω.toCoords (Sum.inr (Sum.inr (Sum.inr v)))) (fun v ω ω' h => h _ (Set.mem_singleton _))
  simp only [map_toCoords_apply] at h
  exact h

/-! ### Independence -/

/-- [s3:defCOL] "the labels are independent of the colours": (1a) and (1c) are independent. -/
theorem indepFun_col_js : (law G run).IndepFun Outcome.col Outcome.js :=
  indepFun_of_dependsOn G run (fun c => c.isLeft)
    (fun ω ω' h => by
      cases ω; cases ω'
      funext Y e
      exact h (Sum.inl ⟨Y, e⟩) rfl)
    (fun ω ω' h => by
      cases ω; cases ω'
      funext Y s
      exact h (Sum.inr (Sum.inr (Sum.inl ⟨Y, s⟩))) (by simp))

/-- The colouring and the JS labels of one ancestor are independent. -/
theorem indepFun_col_js_apply (Y : ↥(run.ancestors G)) :
    (law G run).IndepFun (fun ω => ω.col Y) (fun ω => ω.js Y) :=
  (indepFun_col_js G run).comp (fun c => c Y) (fun j => j Y)

/-- [s3:defCOL] the law of the stage-1 lending data of the ancestor `Y` is `colLaw G run Y` (the
form in which the lemCOL Specs consume it). -/
theorem map_cOut (Y : ↥(run.ancestors G)) :
    (law G run).map (fun ω => ω.cOut Y) = colLaw G run Y := by
  have h := (indepFun_iff_map_eq_prod _).1 (indepFun_col_js_apply G run Y)
  rw [map_col, map_js] at h
  exact h

theorem map_cOutAt {Y : PartId} (hY : Y ∈ run.ancestors G) :
    (law G run).map (fun ω => ω.cOutAt Y) = colLaw G run Y := by
  have : (fun ω : Outcome G run => ω.cOutAt Y) = fun ω => ω.cOut ⟨Y, hY⟩ := by
    funext ω; exact ω.cOutAt_of_mem hY
  rw [this]
  exact map_cOut G run ⟨Y, hY⟩

/-- [s3:defCOL] "The data of distinct ancestors are independent". -/
theorem iIndepFun_cOut :
    (law G run).iIndepFun fun (Y : ↥(run.ancestors G)) (ω : Outcome G run) => ω.cOut Y := by
  refine iIndepFun_of_dependsOn G run
    (fun Y => {c | match c with
      | Sum.inl p => p.1 = Y
      | Sum.inr (Sum.inr (Sum.inl p)) => p.1 = Y
      | _ => False}) ?_ _ ?_
  · intro Y Y' hYY'
    show Disjoint _ _
    rw [Set.disjoint_left]
    rintro (p | v | p | v) h1 h2
    · exact hYY' (h1.symm.trans h2)
    · exact h1.elim
    · exact hYY' (h1.symm.trans h2)
    · exact h1.elim
  · intro Y ω ω' h
    cases ω; cases ω'
    simp only [Outcome.cOut, Prod.mk.injEq]
    constructor
    · funext e
      exact h (Sum.inl ⟨Y, e⟩) rfl
    · funext s
      exact h (Sum.inr (Sum.inr (Sum.inl ⟨Y, s⟩))) rfl

/-- [s3:defCOL] "colours of distinct edges are independent" (the edge triples of `H_Y`). -/
theorem iIndepFun_col_edges (Y : ↥(run.ancestors G)) :
    (law G run).iIndepFun fun (e : ↥(run.ancGraph G Y).edges) (ω : Outcome G run) => ω.col Y e :=
  iIndepFun_of_dependsOn G run (fun e => {Sum.inl ⟨Y, e⟩})
    (fun e e' hee' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inl.injEq, Sigma.mk.inj_iff,
        heq_eq_eq, true_and]
      exact hee')
    _ (fun e ω ω' h => by cases ω; cases ω'; exact h _ (Set.mem_singleton _))

/-- [s5:defZones] "Independently for every vertex `v` of `G`": the zone labels are mutually
independent. -/
theorem iIndepFun_zone :
    (law G run).iIndepFun fun (v : ↥G.verts) (ω : Outcome G run) => ω.zone v :=
  iIndepFun_of_dependsOn G run (fun v => {Sum.inr (Sum.inl v)})
    (fun v v' hvv' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inr.injEq, Sum.inl.injEq]
      exact hvv')
    _ (fun v ω ω' h => by cases ω; cases ω'; exact h _ (Set.mem_singleton _))

/-- [s7:defPool] "Every vertex `v` of `G` independently draws a pool label". -/
theorem iIndepFun_pool :
    (law G run).iIndepFun fun (v : ↥G.verts) (ω : Outcome G run) => ω.pool v :=
  iIndepFun_of_dependsOn G run (fun v => {Sum.inr (Sum.inr (Sum.inr v))})
    (fun v v' hvv' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inr.injEq]
      exact hvv')
    _ (fun v ω ω' h => by cases ω; cases ω'; exact h _ (Set.mem_singleton _))

/-- [s5:lemZones] (iv) "The family of all zones is independent of the colourings (i)–(iii) and of
the JS labels (iv) of Definition [s3:defCOL]": (1a) and (1c) jointly are independent of (1b). -/
theorem indepFun_colJS_zone :
    (law G run).IndepFun (fun ω => (ω.col, ω.js)) Outcome.zone :=
  indepFun_of_dependsOn G run
    (fun c => match c with
      | Sum.inr (Sum.inl _) => False
      | _ => True)
    (fun ω ω' h => by
      cases ω; cases ω'
      simp only [Prod.mk.injEq]
      constructor
      · funext Y e; exact h (Sum.inl ⟨Y, e⟩) trivial
      · funext Y s; exact h (Sum.inr (Sum.inr (Sum.inl ⟨Y, s⟩))) trivial)
    (fun ω ω' h => by
      cases ω; cases ω'
      funext v
      exact h (Sum.inr (Sum.inl v)) (fun h => h))

/-- The zones are independent of the stage-1 lending data of every ancestor `Y` (the joint
independence required by [s3:lemCOL] (c) for the zone family of `Y`, [s5:lemE1] (c)). -/
theorem indepFun_cOut_zone (Y : ↥(run.ancestors G)) :
    (law G run).IndepFun (fun ω => ω.cOut Y) Outcome.zone :=
  (indepFun_colJS_zone G run).comp (fun p => (p.1 Y, p.2 Y)) id

theorem indepFun_cOutAt_zone (Y : PartId) :
    (law G run).IndepFun (fun ω => ω.cOutAt Y) Outcome.zone := by
  by_cases hY : Y ∈ run.ancestors G
  · have : (fun ω : Outcome G run => ω.cOutAt Y) = fun ω => ω.cOut ⟨Y, hY⟩ := by
      funext ω; exact ω.cOutAt_of_mem hY
    rw [this]
    exact indepFun_cOut_zone G run ⟨Y, hY⟩
  · refine indepFun_of_dependsOn G run (fun _ => False) (fun ω ω' _ => ?_) (fun ω ω' h => ?_)
    · simp [Outcome.cOutAt, Outcome.colAt, Outcome.jsAt, hY]
    · cases ω; cases ω'
      funext v
      exact h (Sum.inr (Sum.inl v)) (fun h => h)

/-- [s7:defPool] "They are independent of all other stage-1 data, in particular of the colourings
and labels of Definition [s3:defCOL]": (1d) is independent of (1a), (1b), (1c) jointly. -/
theorem indepFun_rest_pool :
    (law G run).IndepFun (fun ω => (ω.col, ω.zone, ω.js)) Outcome.pool :=
  indepFun_of_dependsOn G run
    (fun c => match c with
      | Sum.inr (Sum.inr (Sum.inr _)) => False
      | _ => True)
    (fun ω ω' h => by
      cases ω; cases ω'
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · funext Y e; exact h (Sum.inl ⟨Y, e⟩) trivial
      · funext v; exact h (Sum.inr (Sum.inl v)) trivial
      · funext Y s; exact h (Sum.inr (Sum.inr (Sum.inl ⟨Y, s⟩))) trivial)
    (fun ω ω' h => by
      cases ω; cases ω'
      funext v
      exact h (Sum.inr (Sum.inr (Sum.inr v))) (fun h => h))

/-- The pool labels are independent of the stage-1 lending data of an ancestor `Y` (used by
[s7:lemCand] (i)). -/
theorem indepFun_cOut_pool (Y : ↥(run.ancestors G)) :
    (law G run).IndepFun (fun ω => ω.cOut Y) Outcome.pool :=
  (indepFun_rest_pool G run).comp (fun p => (p.1 Y, p.2.2 Y)) id

/-! ### Support -/

theorem col_mem_supp_colouringLaw {ω : Outcome G run} (hω : ω ∈ (law G run).supp)
    (Y : ↥(run.ancestors G)) : ω.col Y ∈ (colouringLaw G run Y).supp := by
  rw [← map_col G run Y, mem_supp, map_w]
  refine (lt_of_lt_of_le ((mem_supp_iff_pos _).1 hω) ?_).ne'
  rw [← prob_singleton]
  exact prob_mono _ (fun ω' h => by simp only [Set.mem_singleton_iff] at h; subst h; rfl)

/-- [s3:lemCOL] (g) (partition facts) holds for every ancestor at every stage-1 outcome of
positive weight. -/
theorem COLg_of_mem_supp_law {ω : Outcome G run} (hω : ω ∈ (law G run).supp)
    {Y : PartId} (hY : Y ∈ run.ancestors G) : COLg G run Y (ω.cOutAt Y) := by
  rw [ω.cOutAt_of_mem hY]
  exact COLg_of_mem_supp G run Y (col_mem_supp_colouringLaw G run hω ⟨Y, hY⟩)

/-- On the support, the zone label of `v` is `none` or an available `(Y, i)`: `Y` is a light
part containing `v` with `r(Y) ≤ R-2` (`Y ∈ availParts G run v`) and the sublabel is a U-index
(`i ∈ IU G run Y`) ([s5:defZones]). -/
theorem zone_mem_supp {ω : Outcome G run} (hω : ω ∈ (law G run).supp) (v : ↥G.verts) :
    ω.zone v = none ∨
      ∃ Y i, ω.zone v = some (Y, i) ∧ Y ∈ availParts G run v ∧ i ∈ IU G run Y := by
  have h := (mem_supp_law_iff G run ω).1 hω (Sum.inr (Sum.inl v))
  change ω.zone v ∈ (zoneLabelLaw G run v).supp at h
  rw [mem_supp] at h
  unfold zoneLabelLaw at h
  split_ifs at h with hg
  · rcases ho : ω.zone v with _ | ⟨Y, i⟩
    · exact Or.inl rfl
    · right
      refine ⟨Y, i, rfl, ?_⟩
      rw [ho] at h
      change zoneWeight G run v (some (Y, i)) ≠ 0 at h
      by_contra hn
      apply h
      simp only [zoneWeight]
      rw [if_neg hn]
  · left
    by_contra hn
    exact h (dirac_w_of_ne hn)

/-- On the support, a zone with a sublabel outside `I^U(Y)` is empty. -/
theorem Zone_eq_empty_of_not_mem_IU {ω : Outcome G run} (hω : ω ∈ (law G run).supp)
    {Y : PartId} {i : LentTag} (hi : i ∉ IU G run Y) : Zone G run ω.zone Y i = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  rw [mem_Zone] at hv
  obtain ⟨-, hz⟩ := hv
  unfold zoneOf at hz
  split_ifs at hz with hvG
  rcases zone_mem_supp G run hω ⟨v, hvG⟩ with h0 | ⟨Y', i', h1, -, hi'⟩
  · rw [h0] at hz; cases hz
  · rw [h1] at hz
    cases hz
    exact hi hi'

/-- On the support, a pool label is `⊥` or an admissible `(l, r)` ([s7:defPool]). -/
theorem pool_mem_supp {ω : Outcome G run} (hω : ω ∈ (law G run).supp) (v : ↥G.verts) :
    ω.pool v = none ∨ ∃ l r, ω.pool v = some (l, r) ∧ (l, r) ∈ poolIdx run := by
  have h := (mem_supp_law_iff G run ω).1 hω (Sum.inr (Sum.inr (Sum.inr v)))
  change ω.pool v ∈ (poolLabelLaw G run).supp at h
  rw [mem_supp] at h
  unfold poolLabelLaw at h
  split_ifs at h with hg
  · rcases ho : ω.pool v with _ | ⟨l, r⟩
    · exact Or.inl rfl
    · right
      refine ⟨l, r, rfl, ?_⟩
      rw [ho] at h
      change plabWeight G run (some (l, r)) ≠ 0 at h
      by_contra hn
      apply h
      simp only [plabWeight]
      rw [if_neg hn]
  · left
    by_contra hn
    exact h (dirac_w_of_ne hn)

/-- [s5:defZones] "Equivalently, `v` carries a round-`l` zone of phase `c` iff
`v ∈ Zone_{Y,l,c,σ}` for some light part `Y` and some `σ`" (on the support, where
`Zone ⊆ V(Y)` loses nothing; `Y` is light by `zone_mem_supp`). -/
theorem zonePhase_eq_some_iff_mem_Zone {ω : Outcome G run} (hω : ω ∈ (law G run).supp)
    (l : ℕ) (v : V) (c : Fin 4) :
    zonePhase ω.zone l v = some c ↔ ∃ Y σ, v ∈ Zone G run ω.zone Y (LentTag.U l c σ) := by
  rw [zonePhase_eq_some_iff]
  constructor
  · rintro ⟨Y, σ, h⟩
    refine ⟨Y, σ, ?_⟩
    rw [mem_Zone]
    refine ⟨?_, h⟩
    unfold zoneOf at h
    split_ifs at h with hv
    rcases zone_mem_supp G run hω ⟨v, hv⟩ with h0 | ⟨Y', i', h1, hY', -⟩
    · rw [h0] at h; cases h
    · rw [h1] at h
      cases h
      exact (Finset.mem_filter.1 hY').2.1
  · rintro ⟨Y, σ, h⟩
    exact ⟨Y, σ, (mem_Zone.1 h).2⟩

/-- On the support, a vertex with a zone label `(Y, i)` has `Y` light (the "light part `Y`" of
[s5:defZones]). -/
theorem lightParts_of_zone_eq {ω : Outcome G run} (hω : ω ∈ (law G run).supp) {v : ↥G.verts}
    {Y : PartId} {i : LentTag} (h : ω.zone v = some (Y, i)) : Y ∈ run.lightParts G := by
  rcases zone_mem_supp G run hω v with h0 | ⟨Y', i', h1, hY', -⟩
  · rw [h0] at h; cases h
  · rw [h1] at h
    cases h
    exact (Finset.mem_filter.1 hY').1

/-! ### Per-vertex mixed independence shapes -/

/-- [s7:lemCand] (i): the pairs (colour of `uw`, pool label of `w`) are mutually independent over
the neighbours `w` of `u` in `H_Y`. -/
theorem iIndepFun_edge_pool (Y : ↥(run.ancestors G)) (u : V) :
    (law G run).iIndepFun
      (fun (w : {w : ↥G.verts // s(u, (w : V)) ∈ (run.ancGraph G Y).edges}) (ω : Outcome G run) =>
        (ω.col Y ⟨s(u, (w.1 : V)), w.2⟩, ω.pool w.1)) := by
  refine iIndepFun_of_dependsOn G run
    (fun w => {Sum.inl ⟨Y, ⟨s(u, (w.1 : V)), w.2⟩⟩, Sum.inr (Sum.inr (Sum.inr w.1))}) ?_ _ ?_
  · intro w w' hww'
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Sigma.mk.inj_iff, heq_eq_eq,
        true_and, Subtype.mk.injEq, Sym2.eq_iff] at h
    · apply hww'
      rcases h with h | ⟨h1, h2⟩
      · exact Subtype.ext (Subtype.ext h)
      · exact Subtype.ext (Subtype.ext (h2.trans h1))
    · exact hww' (Subtype.ext h)
  · intro w ω ω' h
    cases ω; cases ω'
    simp only [Prod.mk.injEq]
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩

/-- [s5:lemE1] (a): the pairs (colour of `wu`, zone label of `u`) are mutually independent over
the neighbours `u` of `w` in `H_Y`. -/
theorem iIndepFun_edge_zone (Y : ↥(run.ancestors G)) (w : V) :
    (law G run).iIndepFun
      (fun (u : {u : ↥G.verts // s(w, (u : V)) ∈ (run.ancGraph G Y).edges}) (ω : Outcome G run) =>
        (ω.col Y ⟨s(w, (u.1 : V)), u.2⟩, ω.zone u.1)) := by
  refine iIndepFun_of_dependsOn G run
    (fun u => {Sum.inl ⟨Y, ⟨s(w, (u.1 : V)), u.2⟩⟩, Sum.inr (Sum.inl u.1)}) ?_ _ ?_
  · intro u u' huu'
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Sigma.mk.inj_iff, heq_eq_eq,
        true_and, Subtype.mk.injEq, Sym2.eq_iff] at h
    · apply huu'
      rcases h with h | ⟨h1, h2⟩
      · exact Subtype.ext (Subtype.ext h)
      · exact Subtype.ext (Subtype.ext (h2.trans h1))
    · exact huu' (Subtype.ext h)
  · intro u ω ω' h
    cases ω; cases ω'
    simp only [Prod.mk.injEq]
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩

end EG.Stage1
