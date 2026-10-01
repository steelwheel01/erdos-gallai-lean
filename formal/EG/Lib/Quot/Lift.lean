module

public import EG.Lib.Quot.Quotient

/-!
# The lift of the quotient (manuscript s7:consRound (h), s7:lemLift) — probe P-1, proof round 1

Unit P1, design note `formal/work/p2b/P1.md`. Lemmas for the proof of Lemma [s7:lemLift]
(`EG/Proof/Quot/Lift.lean`):
* the items (`leItems`), ends (`leEnds`) and middle (`leMiddle`) of a layer edge; an edge of `G`
  is *owned* by the layer edge `e` (`Owned`) if it is an item of `e` or the junction edge of an end
  of `e`; under validity every edge is owned by at most one layer edge (`owned_unique`): "So `uw`
  determines the end at `u`, hence the item, the edge of `Q_l` and the member of `Dec`";
* items are paid or lie in a layer edge, and never both (`item_paid_or_layer`,
  `leItems_not_paid`);
* the lift of one edge `ab` of a cycle of `Q_l` (`walk_owned`), the vertex facts of a segment
  (`interior_*`), and the lift of a cycle (`liftCycle_*`): "all vertices of the closed walk are
  pairwise distinct. Consecutive vertices are adjacent in `G`".
-/

public section

namespace EG.Quot

open Finset

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

/-- The J-edges (items) of a layer edge. -/
@[expose] def leItems : LayerEdge V → List (Sym2 V)
  | .inl o => o.edgeList
  | .inr it => [s(it.1, it.2)]

/-- The ends of a layer edge that receive junctions. -/
@[expose] def leEnds : LayerEdge V → List (REnd V)
  | .inl o => [.par o false, .par o true]
  | .inr it => [.hub it.1 it.2]

/-- The middle of a layer edge (the middle of a cherry). -/
@[expose] def leMiddle : LayerEdge V → Option V
  | .inl o => o.middle
  | .inr _ => none

theorem leEnds_inj {e e' : LayerEdge V} {en : REnd V} (h : en ∈ leEnds e) (h' : en ∈ leEnds e') :
    e = e' := by
  rcases e with o | ⟨a, b⟩ <;> rcases e' with o' | ⟨a', b'⟩ <;>
    simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at h h' <;>
    aesop

namespace Rules

/-- The kind and the colour of a layer edge. -/
@[expose] noncomputable def leColour (R : Rules I) (ξ : Xi I.G I.M) :
    LayerEdge V → Option (Bool × ℕ)
  | .inl o => (R.parColour o).map (fun κ => (false, κ))
  | .inr it => (R.hubColour ξ.1 it).map (fun κ => (true, κ))

/-- `g` is the junction edge `s(port, junction)` of an end of the layer edge `e`. -/
@[expose] def IsJEdge (R : Rules I) (ξ : Xi I.G I.M) (e : LayerEdge V) (g : Sym2 V) : Prop :=
  ∃ en ∈ leEnds e, ∃ w, R.junction ξ en = some w ∧ g = s(en.port, w)

/-- The edge `g` of `G` is owned by the layer edge `e`: an item of `e` or a junction edge of an
end of `e`. -/
@[expose] def Owned (R : Rules I) (ξ : Xi I.G I.M) (e : LayerEdge V) (g : Sym2 V) : Prop :=
  g ∈ leItems e ∨ R.IsJEdge ξ e g

/-- The part of the lift of a cycle contributed by its edge `ab` after `a`. -/
@[expose] noncomputable def segT (R : Rules I) (ξ : Xi I.G I.M) (a b : QVert V) : List V :=
  match R.layerOf ξ s(a, b) with
  | some e => R.interior ξ e a.2
  | none => []

/-- The lift of the cycle `cv` of `Q_l` (the vertex list of `R.liftObj ξ (.cycle cv)`). -/
@[expose] noncomputable def liftCycle (R : Rules I) (ξ : Xi I.G I.M) (cv : List (QVert V)) :
    List V :=
  (List.zip cv (cv.rotate 1)).flatMap (fun ab => ab.1.2 :: R.segT ξ ab.1 ab.2)

theorem liftObj_cycle (ξ : Xi I.G I.M) (cv : List (QVert V)) :
    R.liftObj ξ (.cycle cv) = [Obj.cycle (R.liftCycle ξ cv)] := rfl

theorem segT_of_layerOf {ξ : Xi I.G I.M} {a b : QVert V} {e : LayerEdge V}
    (h : R.layerOf ξ s(a, b) = some e) : R.segT ξ a b = R.interior ξ e a.2 := by
  simp [segT, h]

theorem liftObj_edge {ξ : Xi I.G I.M} {q : Sym2 (QVert V)} {e : LayerEdge V}
    (h : R.layerOf ξ q = some e) : R.liftObj ξ (.edge q) = (leItems e).map Obj.edge := by
  rcases e with o | it <;> simp [liftObj, h, leItems]

theorem length_liftObj_le (ξ : Xi I.G I.M) (c : Obj (QVert V)) : (R.liftObj ξ c).length ≤ 2 := by
  rcases c with q | cv
  · simp only [liftObj]
    split
    · rename_i o _
      cases o <;> simp [ParObj.edgeList]
    · simp
    · simp
  · simp [liftObj]

/-! ## Membership in the layer edges -/

theorem mem_layerEdges_inl {ξ : Xi I.G I.M} {o : ParObj V} (h : Sum.inl o ∈ R.layerEdges ξ) :
    o ∈ R.parObjs ∧ ¬ R.Looped ξ o :=
  (mem_unpaidPar).1 ((inl_mem_layerEdges).1 h)

theorem mem_layerEdges_inr {ξ : Xi I.G I.M} {it : V × V} (h : Sum.inr it ∈ R.layerEdges ξ) :
    it ∈ I.hubItems ∧ R.SDRExists ξ.1 it.2 :=
  (mem_colouredHub).1 ((inr_mem_layerEdges).1 h)

/-- The `Q`-edge of a layer edge: the tags of its ends carry the kind and colour of the layer edge
and the rank. -/
theorem qEdge_mem_colour {ξ : Xi I.G I.M} {ι : ℕ} {e : LayerEdge V} {q : Sym2 (QVert V)}
    (h : R.qEdge ξ ι e = some q) {x : QVert V} (hx : x ∈ q) :
    R.leColour ξ e = some (x.1.1, x.1.2.1) ∧ x.1.2.2.1 = ι := by
  rcases e with o | it
  · obtain ⟨κ, w₁, w₂, hκ, -, -, -, rfl⟩ := qEdge_par_iff.1 h
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> simp [leColour, hκ, parTag]
  · obtain ⟨κ, w, hκ, -, rfl⟩ := qEdge_hub_iff.1 h
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> simp [leColour, hκ, hubTag]

/-- The sides of the ends of a `Q`-edge: a junction copy is a copy of a pooled vertex, a hub copy
is a copy of a hub that is not pooled. -/
theorem qEdge_mem_side {ξ : Xi I.G I.M} {ι : ℕ} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    {q : Sym2 (QVert V)} (h : R.qEdge ξ ι e = some q) {x : QVert V} (hx : x ∈ q) :
    (x.1.2.2.2 = false → x.2 ∈ I.pool) ∧ (x.1.2.2.2 = true → x.2 ∈ I.hubs ∧ x.2 ∉ I.pool) := by
  rcases e with o | it
  · obtain ⟨κ, w₁, w₂, -, h1, h2, -, rfl⟩ := qEdge_par_iff.1 h
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact ⟨fun _ => junction_pool h1, fun h => by simp [parTag] at h⟩
    · exact ⟨fun _ => junction_pool h2, fun h => by simp [parTag] at h⟩
  · obtain ⟨κ, w, -, hw, rfl⟩ := qEdge_hub_iff.1 h
    have hH := (mem_layerEdges_inr he).1
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact ⟨fun h => by simp [hubTag] at h,
        fun _ => ⟨RoundInput.hubItems_hub hH, RoundInput.hubItems_hub_not_pool hH⟩⟩
    · exact ⟨fun _ => junction_pool hw, fun h => by simp [hubTag] at h⟩

/-! ## Facts under validity -/

variable (hI : I.Valid) (hR : R.Valid)
include hI hR

theorem leColour_isSome {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) :
    ∃ c, R.leColour ξ e = some c := by
  rcases e with o | it
  · obtain ⟨κ, -, hκ⟩ := parColour_some hI hR (mem_layerEdges_inl he).1
    exact ⟨(false, κ), by simp [leColour, hκ]⟩
  · exact ⟨(true, R.sdr ξ.1 it), by
      simp [leColour, hubColour_of_coloured ((inr_mem_layerEdges).1 he)]⟩

/-- Every layer edge has a `Q`-edge in every rank. -/
theorem qEdge_isSome {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) (ι : ℕ) :
    ∃ q, R.qEdge ξ ι e = some q := by
  rcases e with o | it
  · obtain ⟨ho, hnl⟩ := mem_layerEdges_inl he
    obtain ⟨κ, -, hκ⟩ := parColour_some hI hR ho
    obtain ⟨w₁, h1⟩ := junction_par_some hI hR ξ ho false
    obtain ⟨w₂, h2⟩ := junction_par_some hI hR ξ ho true
    have hne : w₁ ≠ w₂ := fun heq => hnl ⟨w₁, h1, heq ▸ h2⟩
    exact ⟨_, qEdge_par_iff.2 ⟨κ, w₁, w₂, hκ, h1, h2, hne, rfl⟩⟩
  · have hit := (inr_mem_layerEdges).1 he
    obtain ⟨w, hw⟩ := junction_hub_some hI hR ξ hit
    exact ⟨_, qEdge_hub_iff.2 ⟨_, w, hubColour_of_coloured hit, hw, rfl⟩⟩

/-- Ends of layer edges are at ports, which are not pooled and not hubs. -/
theorem leEnds_port {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) {en : REnd V}
    (hen : en ∈ leEnds e) : en.port ∈ I.ports ∧ en.port ∉ I.pool := by
  rcases e with o | it
  · have ho := (mem_layerEdges_inl he).1
    simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at hen
    rcases hen with rfl | rfl <;>
      exact ⟨parObj_end_port hI hR ho _, parObj_end_not_pool hI hR ho _⟩
  · have hH := (mem_layerEdges_inr he).1
    simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at hen
    subst hen
    exact ⟨RoundInput.hubItems_port hH, RoundInput.hubItems_port_not_pool hH⟩

/-- The items of a layer edge are live. -/
theorem leItems_live {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) {g : Sym2 V}
    (hg : g ∈ leItems e) : g ∈ I.live := by
  rcases e with o | it
  · exact parObj_edge_live hI hR (mem_layerEdges_inl he).1 hg
  · simp only [leItems, List.mem_singleton] at hg
    subst hg
    exact RoundInput.hubItems_live hI (mem_layerEdges_inr he).1

theorem leItems_J {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) {g : Sym2 V}
    (hg : g ∈ leItems e) : g ∈ I.J :=
  RoundInput.live_mem_J (leItems_live hI hR he hg)

theorem leItems_nodup {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) :
    (leItems e).Nodup := by
  rcases e with o | it
  · have hne := parObj_ends_ne hI hR (mem_layerEdges_inl he).1
    cases o with
    | par u v => simp [leItems, ParObj.edgeList]
    | cherry x u u' =>
      simp [ParObj.endAt] at hne
      simp only [leItems, ParObj.edgeList, List.nodup_cons, List.mem_singleton, Sym2.eq_iff,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
      rintro (⟨-, h⟩ | ⟨h1, h2⟩)
      · exact hne h
      · exact hne (h2.trans h1)
  · simp [leItems]

/-- An item lies in at most one layer edge. -/
theorem leItems_eq {ξ : Xi I.G I.M} {e e' : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    (he' : e' ∈ R.layerEdges ξ) {g : Sym2 V} (hg : g ∈ leItems e) (hg' : g ∈ leItems e') :
    e = e' := by
  rcases e with o | it <;> rcases e' with o' | it'
  · rw [parObj_eq_of_edge hI hR (mem_layerEdges_inl he).1 (mem_layerEdges_inl he').1 hg hg']
  · exfalso
    simp only [leItems, List.mem_singleton] at hg'
    subst hg'
    have hJ := RoundInput.hubItems_Jhub (mem_layerEdges_inr he').1
    rcases parObj_edge_type hI hR (mem_layerEdges_inl he).1 hg with h | h
    · exact RoundInput.Jhub_not_Jpar hI hJ h
    · exact RoundInput.Jhub_not_Jfr hI hJ h
  · exfalso
    simp only [leItems, List.mem_singleton] at hg
    subst hg
    have hJ := RoundInput.hubItems_Jhub (mem_layerEdges_inr he).1
    rcases parObj_edge_type hI hR (mem_layerEdges_inl he').1 hg' with h | h
    · exact RoundInput.Jhub_not_Jpar hI hJ h
    · exact RoundInput.Jhub_not_Jfr hI hJ h
  · simp only [leItems, List.mem_singleton] at hg hg'
    rw [RoundInput.hubItems_edge_inj (mem_layerEdges_inr he).1 (mem_layerEdges_inr he').1 hI
      (hg.symm.trans hg')]

omit hR in
/-- A junction edge at a port lies in the class `LJV_{Y(u),l}`, which is an ancestor's; it is an
edge of `G` and not a J-edge. -/
theorem jEdge_facts {ξ : Xi I.G I.M} {en : REnd V} (hu : en.port ∈ I.ports) {w : V}
    (hw : R.junction ξ en = some w) :
    w ∈ I.pool ∧ I.cls en.port ∈ I.ancs ∧ s(en.port, w) ∈ I.ljv (I.cls en.port) ∧
      s(en.port, w) ∈ I.G.edges ∧ s(en.port, w) ∉ I.J := by
  obtain ⟨hp, -, hl⟩ := mem_cand (junction_mem_cand hw)
  have ha := hI.cls_anc _ hu
  exact ⟨hp, ha, hl, (hI.ljv_in _ ha _ hl).1,
    fun hJ => Finset.disjoint_left.1 (hI.ljv_J _ ha) hl hJ⟩

omit hI hR in
/-- A junction edge determines its end (the port is not pooled, the junction is pooled, and the
junctions at one port are distinct). -/
theorem end_eq_of_jEdge {ξ : Xi I.G I.M} {en en' : REnd V} (hu : en.port ∉ I.pool)
    (hu' : en'.port ∉ I.pool) {w w' : V} (hw : R.junction ξ en = some w)
    (hw' : R.junction ξ en' = some w') (h : s(en.port, w) = s(en'.port, w')) : en = en' := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, -⟩
  · subst h2
    exact junction_inj h1 hw hw'
  · exact absurd (h1 ▸ junction_pool hw') hu

/-- Every edge of `G` is owned by at most one layer edge. -/
theorem owned_unique {ξ : Xi I.G I.M} {e e' : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    (he' : e' ∈ R.layerEdges ξ) {g : Sym2 V} (hg : R.Owned ξ e g) (hg' : R.Owned ξ e' g) :
    e = e' := by
  rcases hg with hg | ⟨en, hen, w, hw, rfl⟩ <;> rcases hg' with hg' | ⟨en', hen', w', hw', hg'⟩
  · exact leItems_eq hI hR he he' hg hg'
  · exact absurd (leItems_J hI hR he hg)
      (hg' ▸ (jEdge_facts hI (leEnds_port hI hR he' hen').1 hw').2.2.2.2)
  · exact absurd (leItems_J hI hR he' hg')
      ((jEdge_facts hI (leEnds_port hI hR he hen).1 hw).2.2.2.2)
  · have := end_eq_of_jEdge (leEnds_port hI hR he hen).2 (leEnds_port hI hR he' hen').2 hw hw' hg'
    subst this
    exact leEnds_inj hen hen'

/-- Owned edges are edges of `G`. -/
theorem owned_mem_edges {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) {g : Sym2 V}
    (hg : R.Owned ξ e g) : g ∈ I.G.edges := by
  rcases hg with hg | ⟨en, hen, w, hw, rfl⟩
  · exact RoundInput.J_mem_edges hI (leItems_J hI hR he hg)
  · exact (jEdge_facts hI (leEnds_port hI hR he hen).1 hw).2.2.2.1

omit hI hR in
/-- The junction edges of the ends of layer edges are the junction edges of (e). -/
theorem jEdge_mem_junctionEdges {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    {g : Sym2 V} (hg : R.IsJEdge ξ e g) : g ∈ R.junctionEdges ξ := by
  obtain ⟨en, hen, w, hw, rfl⟩ := hg
  unfold junctionEdges
  rw [Finset.mem_union]
  rcases e with o | it
  · right
    simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at hen
    refine Finset.mem_biUnion.2 ⟨o, (inl_mem_layerEdges).1 he, ?_⟩
    rcases hen with rfl | rfl
    · exact Finset.mem_biUnion.2 ⟨false, Finset.mem_univ _,
        Finset.mem_image.2 ⟨w, by simp [hw], rfl⟩⟩
    · exact Finset.mem_biUnion.2 ⟨true, Finset.mem_univ _,
        Finset.mem_image.2 ⟨w, by simp [hw], rfl⟩⟩
  · left
    simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at hen
    subst hen
    exact Finset.mem_biUnion.2 ⟨it, (inr_mem_layerEdges).1 he,
      Finset.mem_image.2 ⟨w, by simp [hw], rfl⟩⟩

/-! ## Payments -/

omit hI in
theorem mem_unpairedLegs {g : Sym2 V} (hg : g ∈ R.unpairedLegs) :
    ∃ x ∈ I.fresh, ∃ u, leftover (R.pairing x) = some u ∧ u ∈ I.frPorts x ∧ g = s(x, u) := by
  unfold unpairedLegs at hg
  obtain ⟨x, hx, hg⟩ := Finset.mem_biUnion.1 hg
  cases hl : leftover (R.pairing x) with
  | none => simp [hl] at hg
  | some u =>
    simp only [hl, Option.map_some, Option.toFinset_some, Finset.mem_singleton] at hg
    refine ⟨x, hx, u, hl, ?_, hg⟩
    rw [← (hR.pairing x hx).2]
    exact List.mem_toFinset.2 (mem_of_leftover hl)

omit hI hR in
theorem mem_sdrPaid {L : Lists I.G I.M} {g : Sym2 V} :
    g ∈ R.sdrPaid L ↔ ∃ it ∈ I.hubItems, ¬ R.SDRExists L it.2 ∧ g = s(it.1, it.2) := by
  classical
  unfold sdrPaid
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨it, ⟨h1, h2⟩, rfl⟩; exact ⟨it, h1, h2, rfl⟩
  · rintro ⟨it, h1, h2, rfl⟩; exact ⟨it, ⟨h1, h2⟩, rfl⟩

omit hI hR in
theorem mem_loopPaid {ξ : Xi I.G I.M} {g : Sym2 V} :
    g ∈ R.loopPaid ξ ↔ ∃ o ∈ R.parObjs, R.Looped ξ o ∧ g ∈ o.edgeList := by
  classical
  unfold loopPaid
  simp only [Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨o, ⟨h1, h2⟩, h3⟩; exact ⟨o, h1, h2, h3⟩
  · rintro ⟨o, h1, h2, h3⟩; exact ⟨o, ⟨h1, h2⟩, h3⟩

omit hI hR in
theorem mem_paidEdges {ξ : Xi I.G I.M} {g : Sym2 V} :
    g ∈ R.paidEdges ξ ↔ g ∈ I.paidA ∨ g ∈ R.unpairedLegs ∨ g ∈ R.sdrPaid ξ.1 ∨
      g ∈ R.loopPaid ξ := by
  simp [paidEdges, or_assoc]

omit hI hR in
theorem mem_paidA {g : Sym2 V} : g ∈ I.paidA ↔ g ∈ I.Jlost ∨ g ∈ I.paidPool ∨ g ∈ I.paidJVBad := by
  simp [RoundInput.paidA, or_assoc]

omit hI hR in
theorem paidA_sub_J {g : Sym2 V} (hg : g ∈ I.paidA) : g ∈ I.J := by
  classical
  rcases (mem_paidA).1 hg with h | h | h
  · exact RoundInput.mem_J.2 (Or.inl h)
  · unfold RoundInput.paidPool at h
    exact ((I.mem_items).1 (Finset.mem_filter.1 h).1).1
  · unfold RoundInput.paidJVBad at h
    exact ((I.mem_items).1 (Finset.mem_filter.1 h).1).1

/-- Paid edges are J-edges. -/
theorem paid_sub_J {ξ : Xi I.G I.M} {g : Sym2 V} (hg : g ∈ R.paidEdges ξ) : g ∈ I.J := by
  rcases (mem_paidEdges).1 hg with h | h | h | h
  · exact paidA_sub_J h
  · obtain ⟨x, -, u, -, hu, rfl⟩ := mem_unpairedLegs hR h
    exact RoundInput.Jfr_sub_J ((I.mem_frPorts).1 hu).2.2
  · obtain ⟨it, hit, -, rfl⟩ := (mem_sdrPaid).1 h
    exact RoundInput.Jhub_sub_J (RoundInput.hubItems_Jhub hit)
  · obtain ⟨o, ho, -, hg⟩ := (mem_loopPaid).1 h
    exact parObj_edge_J hI hR ho hg

/-- Items of layer edges are not paid. -/
theorem leItems_not_paid {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    {g : Sym2 V} (hg : g ∈ leItems e) : g ∉ R.paidEdges ξ := by
  have hlive := leItems_live hI hR he hg
  intro hp
  rcases (mem_paidEdges).1 hp with h | h | h | h
  · have hl := (I.mem_live).1 hlive
    rcases (mem_paidA).1 h with h | h | h
    · exact ((I.mem_items).1 hl.1).2 h
    · exact hl.2.1 h
    · exact hl.2.2 h
  · obtain ⟨x, hx, u, hlo, hu, rfl⟩ := mem_unpairedLegs hR h
    have hu' := (I.mem_frPorts).1 hu
    rcases e with o | it
    · have ho := (mem_layerEdges_inl he).1
      rcases (R.mem_parObjs).1 ho with h1 | h1
      · obtain ⟨e0, he0, rfl⟩ := (mem_parObjsPar).1 h1
        simp only [leItems, ParObj.edgeList, List.mem_singleton, mk_out] at hg
        exact RoundInput.Jfr_not_Jpar hI hu'.2.2 (hg ▸ ((I.mem_parItems).1 he0).2)
      · obtain ⟨x', hx', p, hp', rfl⟩ := (R.mem_cherries).1 h1
        obtain ⟨-, hp1, hp2⟩ := cherry_facts hI hR hx' hp'
        simp only [leItems, ParObj.edgeList, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | hg
        · obtain ⟨rfl, rfl⟩ := RoundInput.fr_edge_inj hI hx hx' hu'.1 ((I.mem_frPorts).1 hp1).1 hg
          exact not_mem_pairUp_of_leftover (hR.pairing x hx).1 hlo ⟨p, hp', Or.inl rfl⟩
        · obtain ⟨rfl, rfl⟩ := RoundInput.fr_edge_inj hI hx hx' hu'.1 ((I.mem_frPorts).1 hp2).1 hg
          exact not_mem_pairUp_of_leftover (hR.pairing x hx).1 hlo ⟨p, hp', Or.inr rfl⟩
    · simp only [leItems, List.mem_singleton] at hg
      exact RoundInput.Jhub_not_Jfr hI
        (hg ▸ RoundInput.hubItems_Jhub (mem_layerEdges_inr he).1) hu'.2.2
  · obtain ⟨it', hit', hns, rfl⟩ := (mem_sdrPaid).1 h
    rcases e with o | it
    · rcases parObj_edge_type hI hR (mem_layerEdges_inl he).1 hg with h' | h'
      · exact RoundInput.Jhub_not_Jpar hI (RoundInput.hubItems_Jhub hit') h'
      · exact RoundInput.Jhub_not_Jfr hI (RoundInput.hubItems_Jhub hit') h'
    · simp only [leItems, List.mem_singleton] at hg
      have hit := mem_layerEdges_inr he
      rw [RoundInput.hubItems_edge_inj hit.1 hit' hI hg.symm] at hit
      exact hns hit.2
  · obtain ⟨o', ho', hlo, hg'⟩ := (mem_loopPaid).1 h
    rcases e with o | it
    · have ho := mem_layerEdges_inl he
      rw [parObj_eq_of_edge hI hR ho.1 ho' hg hg'] at ho
      exact ho.2 hlo
    · simp only [leItems, List.mem_singleton] at hg
      subst hg
      have hJ := RoundInput.hubItems_Jhub (mem_layerEdges_inr he).1
      rcases parObj_edge_type hI hR ho' hg' with h' | h'
      · exact RoundInput.Jhub_not_Jpar hI hJ h'
      · exact RoundInput.Jhub_not_Jfr hI hJ h'

omit hI hR in
/-- A PAR object is paid in (e3) or it is a layer edge. -/
theorem parObj_paid_or_layer {ξ : Xi I.G I.M} {o : ParObj V} (ho : o ∈ R.parObjs) {g : Sym2 V}
    (hg : g ∈ o.edgeList) : g ∈ R.paidEdges ξ ∨ ∃ le ∈ R.layerEdges ξ, g ∈ leItems le := by
  by_cases hl : R.Looped ξ o
  · exact Or.inl ((mem_paidEdges).2 (Or.inr (Or.inr (Or.inr ((mem_loopPaid).2 ⟨o, ho, hl, hg⟩)))))
  · exact Or.inr ⟨.inl o, (inl_mem_layerEdges).2 ((mem_unpaidPar).2 ⟨ho, hl⟩), hg⟩

/-- Every item is paid, or it is an item of a layer edge. -/
theorem item_paid_or_layer {ξ : Xi I.G I.M} {g : Sym2 V} (hg : g ∈ I.items) :
    g ∈ R.paidEdges ξ ∨ ∃ le ∈ R.layerEdges ξ, g ∈ leItems le := by
  by_cases hl : g ∈ I.live
  · have hJ := RoundInput.live_mem_J hl
    rcases (RoundInput.mem_J).1 hJ with h | h | h | h
    · exact absurd h ((I.mem_items).1 hg).2
    · obtain ⟨hh, hhm, u, hu, rfl⟩ := hI.hub_typed _ h
      have hit : (hh, u) ∈ I.hubItems := (I.mem_hubItems).2 ⟨hhm, hu, hl, h⟩
      by_cases hs : R.SDRExists ξ.1 u
      · exact Or.inr ⟨.inr (hh, u), (inr_mem_layerEdges).2 ((mem_colouredHub).2 ⟨hit, hs⟩),
          by simp [leItems]⟩
      · exact Or.inl ((mem_paidEdges).2 (Or.inr (Or.inr (Or.inl
          ((mem_sdrPaid).2 ⟨(hh, u), hit, hs, rfl⟩)))))
    · obtain ⟨x, hx, u, hu, rfl⟩ := hI.fr_typed _ h
      have hfr : u ∈ I.frPorts x := (I.mem_frPorts).2 ⟨hu, hl, h⟩
      have hmem : u ∈ R.pairing x := by
        rw [← List.mem_toFinset, (hR.pairing x hx).2]; exact hfr
      rcases mem_pairUp_or_leftover hmem with ⟨p, hp, hup⟩ | hlo
      · have ho : ParObj.cherry x p.1 p.2 ∈ R.parObjs :=
          (R.mem_parObjs).2 (Or.inr ((R.mem_cherries).2 ⟨x, hx, p, hp, rfl⟩))
        refine parObj_paid_or_layer ho ?_
        rcases hup with rfl | rfl <;> simp [ParObj.edgeList]
      · refine Or.inl ((mem_paidEdges).2 (Or.inr (Or.inl ?_)))
        unfold unpairedLegs
        exact Finset.mem_biUnion.2 ⟨x, hx, by simp [hlo]⟩
    · have hpi : g ∈ I.parItems := (I.mem_parItems).2 ⟨hl, h⟩
      have ho : ParObj.par (_root_.Quot.out g).1 (_root_.Quot.out g).2 ∈ R.parObjs :=
        (R.mem_parObjs).2 (Or.inl ((mem_parObjsPar).2 ⟨g, hpi, rfl⟩))
      exact parObj_paid_or_layer ho (by simp [ParObj.edgeList, mk_out])
  · have hp : g ∈ I.paidPool ∨ g ∈ I.paidJVBad := by
      by_contra hc
      push Not at hc
      exact hl ((I.mem_live).2 ⟨hg, hc.1, hc.2⟩)
    exact Or.inl ((mem_paidEdges).2 (Or.inl ((mem_paidA).2 (Or.inr hp))))

/-! ## The interior of a segment of a lifted cycle -/

omit hI hR in
theorem mem_interior {ξ : Xi I.G I.M} {e : LayerEdge V} {a v : V} (hv : v ∈ R.interior ξ e a) :
    (∃ en ∈ leEnds e, en.port = v) ∨ leMiddle e = some v := by
  rcases e with o | it
  · have key : v = o.endAt false ∨ o.middle = some v ∨ v = o.endAt true := by
      simp only [interior] at hv
      split_ifs at hv <;>
        simp only [List.mem_cons, List.mem_append, Option.mem_toList, List.mem_singleton,
          List.not_mem_nil, or_false] at hv <;> tauto
    rcases key with rfl | h | rfl
    · exact Or.inl ⟨.par o false, by simp [leEnds], rfl⟩
    · exact Or.inr h
    · exact Or.inl ⟨.par o true, by simp [leEnds], rfl⟩
  · simp only [interior, List.mem_singleton] at hv
    exact Or.inl ⟨.hub it.1 it.2, by simp [leEnds], hv.symm⟩

omit hI hR in
theorem two_le_length_seg (ξ : Xi I.G I.M) (e : LayerEdge V) (a : V) :
    2 ≤ (a :: R.interior ξ e a).length := by
  rcases e with o | it
  · simp only [interior]; split_ifs <;> simp
  · simp [interior]

/-- The vertices of the interior of a layer edge are ports or fresh centres: live, so not pooled,
and not hubs. -/
theorem interior_vert {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) {a v : V}
    (hv : v ∈ R.interior ξ e a) : v ∉ I.pool ∧ v ∉ I.hubs := by
  rcases mem_interior hv with ⟨en, hen, rfl⟩ | hm
  · obtain ⟨hp, hnp⟩ := leEnds_port hI hR he hen
    exact ⟨hnp, RoundInput.port_not_hub hI hp⟩
  · rcases e with o | it
    · obtain ⟨hf, hnp⟩ := parObj_middle hI hR (mem_layerEdges_inl he).1 hm
      exact ⟨hnp, RoundInput.fresh_not_hub hI hf⟩
    · simp [leMiddle] at hm

theorem interior_nodup {ξ : Xi I.G I.M} {e : LayerEdge V} (he : e ∈ R.layerEdges ξ) (a : V) :
    (R.interior ξ e a).Nodup := by
  rcases e with o | it
  · have ho := (mem_layerEdges_inl he).1
    have hne := parObj_ends_ne hI hR ho
    have hp := parObj_end_port hI hR ho
    cases o with
    | par u v =>
      simp [ParObj.endAt] at hne
      simp only [interior]
      split_ifs <;> simp [ParObj.endAt, ParObj.middle, hne, Ne.symm hne]
    | cherry x u u' =>
      have hx := (parObj_middle hI hR ho rfl).1
      have h1 : x ≠ u := RoundInput.fresh_ne_port hI hx (hp false)
      have h2 : x ≠ u' := RoundInput.fresh_ne_port hI hx (hp true)
      simp [ParObj.endAt] at hne
      simp only [interior]
      split_ifs <;> simp [ParObj.endAt, ParObj.middle, hne, Ne.symm hne, h1, h2, Ne.symm h1,
        Ne.symm h2]
  · simp [interior]

omit hI hR in
theorem parColour_of_leColour {ξ : Xi I.G I.M} {o o' : ParObj V} {κ : ℕ}
    (h : R.parColour o = some κ) (hc : R.leColour ξ (.inl o) = R.leColour ξ (.inl o')) :
    R.parColour o' = some κ := by
  simp only [leColour, h, Option.map_some] at hc
  cases h' : R.parColour o' with
  | none => simp [h'] at hc
  | some κ' =>
    simp only [h', Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at hc
    rw [hc]

omit hI hR in
theorem leColour_inl_fst {ξ : Xi I.G I.M} {o : ParObj V} {c : Bool × ℕ}
    (h : R.leColour ξ (.inl o) = some c) : c.1 = false := by
  simp only [leColour, Option.map_eq_some_iff] at h
  obtain ⟨κ, -, rfl⟩ := h; rfl

omit hI hR in
theorem leColour_inr_fst {ξ : Xi I.G I.M} {it : V × V} {c : Bool × ℕ}
    (h : R.leColour ξ (.inr it) = some c) : c.1 = true := by
  simp only [leColour, Option.map_eq_some_iff] at h
  obtain ⟨κ, -, rfl⟩ := h; rfl

/-- Distinct layer edges of the same kind and colour have disjoint interiors (the ports of distinct
objects or items of one colour are distinct, the middles of distinct cherries of one colour are
distinct, and no port is a middle). -/
theorem interior_disjoint {ξ : Xi I.G I.M} {e e' : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    (he' : e' ∈ R.layerEdges ξ) (hne : e ≠ e') (hc : R.leColour ξ e = R.leColour ξ e') (a a' : V) :
    List.Disjoint (R.interior ξ e a) (R.interior ξ e' a') := by
  intro v hv hv'
  have portMid : ∀ {f f' : LayerEdge V}, f ∈ R.layerEdges ξ → f' ∈ R.layerEdges ξ →
      ∀ en ∈ leEnds f, leMiddle f' = some en.port → False := by
    intro f f' hf hf' en hen hm
    rcases f' with o' | it'
    · exact RoundInput.fresh_ne_port hI (parObj_middle hI hR (mem_layerEdges_inl hf').1 hm).1
        (leEnds_port hI hR hf hen).1 rfl
    · simp [leMiddle] at hm
  obtain ⟨c, hc1⟩ := leColour_isSome hI hR he
  have hc2 : R.leColour ξ e' = some c := hc ▸ hc1
  rcases mem_interior hv with ⟨en, hen, rfl⟩ | hm <;>
    rcases mem_interior hv' with ⟨en', hen', hp⟩ | hm'
  · rcases e with o | it <;> rcases e' with o' | it'
    · simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at hen hen'
      have ho := (mem_layerEdges_inl he).1
      have ho' := (mem_layerEdges_inl he').1
      obtain ⟨κ, -, hκ⟩ := parColour_some hI hR ho
      have hκ' : R.parColour o' = some κ := parColour_of_leColour hκ hc
      apply hne
      rcases hen with rfl | rfl <;> rcases hen' with rfl | rfl <;>
        exact congrArg _ (parObj_eq_of_end_colour hI hR ho ho' hp.symm hκ hκ')
    · have := (leColour_inl_fst hc1).symm.trans (leColour_inr_fst hc2); cases this
    · have := (leColour_inr_fst hc1).symm.trans (leColour_inl_fst hc2); cases this
    · simp only [leEnds, List.mem_cons, List.not_mem_nil, or_false] at hen hen'
      subst hen hen'
      have hit := (inr_mem_layerEdges).1 he
      have hit' := (inr_mem_layerEdges).1 he'
      exact hne (congrArg _ (hub_eq_of_port_colour hR hit hit' hp.symm (by
        simpa [leColour, hubColour_of_coloured hit, hubColour_of_coloured hit'] using hc)))
  · exact portMid he he' en hen hm'
  · exact portMid he' he en' hen' (hp ▸ hm)
  · rcases e with o | it <;> rcases e' with o' | it'
    · have ho := (mem_layerEdges_inl he).1
      have ho' := (mem_layerEdges_inl he').1
      obtain ⟨κ, -, hκ⟩ := parColour_some hI hR ho
      have hκ' : R.parColour o' = some κ := parColour_of_leColour hκ hc
      exact hne (congrArg _ (parObj_eq_of_middle_colour hI hR ho ho' hm hm' hκ hκ'))
    all_goals simp [leMiddle] at hm hm'

/-! ## The lift of one edge of a cycle -/

omit hI hR in
/-- A walk `x a … b y` through the list `m` from `a` to `b`. -/
theorem walkEdges_cons_append (x : V) (m : List V) (hm : m ≠ []) (y : V) :
    walkEdges (x :: m ++ [y]) = s(x, m.head hm) :: (walkEdges m ++ [s(m.getLast hm, y)]) := by
  obtain ⟨a, m', rfl⟩ := List.exists_cons_of_ne_nil hm
  rw [List.cons_append, List.cons_append, walkEdges_cons_cons, ← List.cons_append,
    walkEdges_concat, List.getLast?_eq_getLast hm]
  simp

omit hI hR in
/-- The walk through a PAR object from its end `β` to its other end uses exactly its J-edges. -/
theorem mem_walkEdges_par (o : ParObj V) (β : Bool) {g : Sym2 V} :
    g ∈ walkEdges (o.endAt β :: (o.middle.toList ++ [o.endAt (!β)])) ↔ g ∈ o.edgeList := by
  cases o <;> cases β <;>
    simp [ParObj.endAt, ParObj.middle, ParObj.edgeList, Sym2.eq_swap, or_comm]

omit hI hR in
theorem walk_par (ξ : Xi I.G I.M) (o : ParObj V) (β : Bool) {x y : V}
    (hx : R.junction ξ (.par o β) = some x) (hy : R.junction ξ (.par o (!β)) = some y) :
    (∀ g ∈ walkEdges (x :: (o.endAt β :: (o.middle.toList ++ [o.endAt (!β)])) ++ [y]),
      R.Owned ξ (.inl o) g) ∧
    (∀ g ∈ o.edgeList,
      g ∈ walkEdges (x :: (o.endAt β :: (o.middle.toList ++ [o.endAt (!β)])) ++ [y])) := by
  rw [walkEdges_cons_append x _ (List.cons_ne_nil _ _) y]
  have hl : (o.endAt β :: (o.middle.toList ++ [o.endAt (!β)])).getLast (List.cons_ne_nil _ _) =
      o.endAt (!β) := by
    simp
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · simp only [List.head_cons, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      hl] at hg
    rcases hg with rfl | hg | rfl
    · refine Or.inr ⟨.par o β, by cases β <;> simp [leEnds], x, hx, Sym2.eq_swap⟩
    · exact Or.inl ((mem_walkEdges_par o β).1 hg)
    · refine Or.inr ⟨.par o (!β), by cases β <;> simp [leEnds], y, hy, ?_⟩
      simp [REnd.port]
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((mem_walkEdges_par o β).2 hg))

omit hI hR in
/-- The lift of the edge `ab` of a cycle of `Q_l` (entered at `a`, left at `b`): every edge of the
walk `a (interior) b` is owned by the layer edge of `ab`, and every item of that layer edge is an
edge of the walk. -/
theorem walk_owned {ξ : Xi I.G I.M} {e : LayerEdge V} {ι : ℕ} {a b : QVert V}
    (hq : R.qEdge ξ ι e = some s(a, b)) :
    (∀ g ∈ walkEdges (a.2 :: R.interior ξ e a.2 ++ [b.2]), R.Owned ξ e g) ∧
    (∀ g ∈ leItems e, g ∈ walkEdges (a.2 :: R.interior ξ e a.2 ++ [b.2])) := by
  rcases e with o | it
  · obtain ⟨κ, w₁, w₂, -, h1, h2, hne, hq'⟩ := qEdge_par_iff.1 hq
    rcases Sym2.eq_iff.1 hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hi : R.interior ξ (.inl o) w₁ = o.endAt false :: (o.middle.toList ++ [o.endAt true]) := by
        simp [interior, h1]
      rw [hi]
      exact walk_par ξ o false h1 h2
    · have hi : R.interior ξ (.inl o) w₂ = o.endAt true :: (o.middle.toList ++ [o.endAt false]) := by
        simp [interior, h1, hne]
      rw [hi]
      exact walk_par ξ o true h2 h1
  · obtain ⟨κ, w, -, hw, hq'⟩ := qEdge_hub_iff.1 hq
    have hj : R.IsJEdge ξ (.inr it) s(it.2, w) :=
      ⟨.hub it.1 it.2, by simp [leEnds], w, hw, rfl⟩
    have hi : s(it.1, it.2) ∈ leItems (Sum.inr it : LayerEdge V) := by simp [leItems]
    rcases Sym2.eq_iff.1 hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [interior, List.cons_append, List.nil_append, walkEdges_cons_cons,
        walkEdges_singleton, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨?_, ?_⟩
      · rintro g (rfl | rfl)
        · exact Or.inl hi
        · exact Or.inr hj
      · intro g hg; simp only [leItems, List.mem_singleton] at hg; exact Or.inl hg
    · simp only [interior, List.cons_append, List.nil_append, walkEdges_cons_cons,
        walkEdges_singleton, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨?_, ?_⟩
      · rintro g (rfl | rfl)
        · exact Or.inr (Sym2.eq_swap ▸ hj)
        · exact Or.inl (Sym2.eq_swap ▸ hi)
      · intro g hg; simp only [leItems, List.mem_singleton] at hg
        exact Or.inr (hg.trans Sym2.eq_swap)

/-! ## The lift of a cycle -/

omit hI hR in
theorem zip_facts {ξ : Xi I.G I.M} {cv : List (QVert V)}
    (hQ : ∀ q ∈ cycleEdges cv, q ∈ (R.Q ξ).edges) {p : QVert V × QVert V}
    (hp : p ∈ List.zip cv (cv.rotate 1)) :
    ∃ e, R.layerOf ξ s(p.1, p.2) = some e ∧ e ∈ R.layerEdges ξ ∧
      R.qEdge ξ (R.rank ξ e) e = some s(p.1, p.2) := by
  have hq : s(p.1, p.2) ∈ cycleEdges cv := by
    rw [cycleEdges_eq_map_zip]; exact List.mem_map_of_mem hp
  obtain ⟨e, he⟩ := layerOf_isSome (hQ _ hq)
  exact ⟨e, he, layerOf_spec he⟩

omit hI hR in
theorem mem_zip_fst {cv : List (QVert V)} {p : QVert V × QVert V}
    (hp : p ∈ List.zip cv (cv.rotate 1)) : p.1 ∈ cv :=
  (List.of_mem_zip (a := p.1) (b := p.2) hp).1

/-- [s7:lemLift] (ii) "all vertices of the closed walk … are pairwise distinct. Consecutive
vertices are adjacent in `G`": the lift of a cycle of `Q_l` is a cycle of `G` with at least three
(in fact `≥ 6`) pairwise distinct vertices; its edges are owned by the layer edges of the edges of
the cycle, and it contains every item of those layer edges. -/
theorem liftCycle_facts {ξ : Xi I.G I.M} {cv : List (QVert V)} (hnd : cv.Nodup)
    (h3 : 3 ≤ cv.length) (hQ : ∀ q ∈ cycleEdges cv, q ∈ (R.Q ξ).edges) :
    (R.liftCycle ξ cv).Nodup ∧ 3 ≤ (R.liftCycle ξ cv).length ∧
    (∀ g ∈ cycleEdges (R.liftCycle ξ cv), ∃ q ∈ cycleEdges cv, ∃ e,
      R.layerOf ξ q = some e ∧ R.Owned ξ e g) ∧
    (∀ q ∈ cycleEdges cv, ∀ e, R.layerOf ξ q = some e → ∀ g ∈ leItems e,
      g ∈ cycleEdges (R.liftCycle ξ cv)) := by
  set Z := List.zip cv (cv.rotate 1) with hZ
  have hEdges : cycleEdges (R.liftCycle ξ cv) =
      Z.flatMap (fun p => walkEdges (p.1.2 :: R.segT ξ p.1 p.2 ++ [p.2.2])) :=
    cycleEdges_flatMap_zip (fun x : QVert V => x.2) (R.segT ξ) cv
  -- the tag `(kind, colour, rank)` is constant along the cycle
  let tg : QVert V → Bool × ℕ × ℕ := fun x => (x.1.1, x.1.2.1, x.1.2.2.1)
  have hstep : ∀ p ∈ Z, tg p.1 = tg p.2 := by
    intro p hp
    obtain ⟨e, -, -, hq⟩ := zip_facts hQ hp
    have h1 := qEdge_mem_colour hq (Sym2.mem_mk_left p.1 p.2)
    have h2 := qEdge_mem_colour hq (Sym2.mem_mk_right p.1 p.2)
    have hc := h1.1.symm.trans h2.1
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    simp only [tg, hc.1, hc.2, h1.2, h2.2]
  have htg : ∀ x ∈ cv, ∀ y ∈ cv, tg x = tg y := fun x hx y hy =>
    (forall_eq_of_zip_rotate_one tg hstep hx y hy).symm
  -- the sides of the vertices of the cycle
  have hside : ∀ x ∈ cv, (x.1.2.2.2 = false → x.2 ∈ I.pool) ∧
      (x.1.2.2.2 = true → x.2 ∈ I.hubs ∧ x.2 ∉ I.pool) := by
    intro x hx
    rw [← map_fst_zip_rotate cv] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e, -, he, hq⟩ := zip_facts hQ hp
    exact qEdge_mem_side he hq (Sym2.mem_mk_left _ _)
  have hdist : ∀ x ∈ cv, ∀ y ∈ cv, x ≠ y → x.2 ≠ y.2 := by
    intro x hx y hy hxy h2
    have ht := htg x hx y hy
    have sx := hside x hx
    have sy := hside y hy
    obtain ⟨⟨k, c, r, sd⟩, v⟩ := x
    obtain ⟨⟨k', c', r', sd'⟩, v'⟩ := y
    simp only [tg, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl⟩ := ht
    simp only at h2 sx sy
    subst h2
    cases sd <;> cases sd'
    · exact hxy rfl
    · exact (sy.2 rfl).2 (sx.1 rfl)
    · exact (sx.2 rfl).2 (sy.1 rfl)
    · exact hxy rfl
  -- the segments
  have hseg : ∀ p ∈ Z, ∃ e, e ∈ R.layerEdges ξ ∧ R.qEdge ξ (R.rank ξ e) e = some s(p.1, p.2) ∧
      R.segT ξ p.1 p.2 = R.interior ξ e p.1.2 := by
    intro p hp
    obtain ⟨e, hl, he, hq⟩ := zip_facts hQ hp
    exact ⟨e, he, hq, segT_of_layerOf hl⟩
  have hhead : ∀ p ∈ Z, ∀ e ∈ R.layerEdges ξ, p.1.2 ∉ R.interior ξ e p.1.2 ∧
      ∀ a, p.1.2 ∉ R.interior ξ e a := by
    intro p hp e he
    have hs := hside p.1 (mem_zip_fst hp)
    have key : ∀ a, p.1.2 ∉ R.interior ξ e a := by
      intro a hv
      have hvi := interior_vert hI hR he hv
      cases h : p.1.1.2.2.2
      · exact hvi.1 (hs.1 h)
      · exact hvi.2 (hs.2 h).1
    exact ⟨key _, key⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the vertices are pairwise distinct
    unfold liftCycle
    rw [← hZ]
    refine List.nodup_flatMap.2 ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨e, he, -, hs⟩ := hseg p hp
      rw [hs, List.nodup_cons]
      exact ⟨(hhead p hp e he).1, interior_nodup hI hR he _⟩
    · have hP1 : Z.Pairwise (fun p p' => p.1 ≠ p'.1) := by
        have h := hnd
        rw [← map_fst_zip_rotate cv, List.Nodup, List.pairwise_map] at h
        exact h
      have hP2 : Z.Pairwise (fun p p' => s(p.1, p.2) ≠ s(p'.1, p'.2)) := by
        have h := nodup_cycleEdges hnd h3
        rw [cycleEdges_eq_map_zip, List.Nodup, List.pairwise_map] at h
        exact h
      refine (hP1.and hP2).imp_of_mem (fun {p p'} hp hp' hne => ?_)
      obtain ⟨e, he, hq, hs⟩ := hseg p hp
      obtain ⟨e', he', hq', hs'⟩ := hseg p' hp'
      intro v hv hv'
      simp only [hs, hs', List.mem_cons] at hv hv'
      rcases hv with rfl | hv <;> rcases hv' with hv' | hv'
      · exact hdist _ (mem_zip_fst hp) _ (mem_zip_fst hp') hne.1 hv'
      · exact (hhead p hp e' he').2 _ hv'
      · exact (hhead p' hp' e he).2 _ (hv' ▸ hv)
      · have hee : e ≠ e' := by
          rintro rfl
          exact hne.2 (Option.some.inj (hq.symm.trans hq'))
        have hc : R.leColour ξ e = R.leColour ξ e' := by
          rw [(qEdge_mem_colour hq (Sym2.mem_mk_left _ _)).1,
            (qEdge_mem_colour hq' (Sym2.mem_mk_left _ _)).1]
          have := htg _ (mem_zip_fst hp) _ (mem_zip_fst hp')
          simp only [tg, Prod.mk.injEq] at this
          rw [this.1, this.2.1]
        exact interior_disjoint hI hR he he' hee hc _ _ hv hv'
  · -- at least three vertices
    unfold liftCycle
    rw [← hZ]
    have h2 := two_mul_le_length_flatMap (l := Z)
      (F := fun p => p.1.2 :: R.segT ξ p.1 p.2) (fun p hp => by
        obtain ⟨e, -, -, hs⟩ := hseg p hp
        simp only [hs]
        exact two_le_length_seg ξ e _)
    rw [length_zip_rotate] at h2
    omega
  · -- every edge is owned by the layer edge of an edge of the cycle
    intro g hg
    rw [hEdges] at hg
    obtain ⟨p, hp, hg⟩ := List.mem_flatMap.1 hg
    obtain ⟨e, hl, he, hq⟩ := zip_facts hQ hp
    rw [segT_of_layerOf hl] at hg
    refine ⟨s(p.1, p.2), ?_, e, hl, (walk_owned hq).1 g hg⟩
    rw [cycleEdges_eq_map_zip]; exact List.mem_map_of_mem hp
  · -- every item of the layer edge of an edge of the cycle is on the lift
    intro q hq e hl g hg
    rw [cycleEdges_eq_map_zip] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    rw [hEdges]
    refine List.mem_flatMap.2 ⟨p, hp, ?_⟩
    rw [segT_of_layerOf hl]
    exact (walk_owned (layerOf_spec hl).2).2 g hg

/-! ## The lift of a member of a decomposition -/

omit hI hR in
theorem flatMap_edges_map_edge {W : Type*} (l : List (Sym2 W)) :
    (l.map Obj.edge).flatMap Obj.edges = l := by
  induction l with
  | nil => rfl
  | cons g t ih => simp [Obj.edges, ih]

omit hI hR in
/-- Every junction edge of (e) is the junction edge of an end of a layer edge. -/
theorem mem_junctionEdges {ξ : Xi I.G I.M} {g : Sym2 V} (hg : g ∈ R.junctionEdges ξ) :
    ∃ e ∈ R.layerEdges ξ, R.IsJEdge ξ e g := by
  unfold junctionEdges at hg
  rcases Finset.mem_union.1 hg with hg | hg
  · obtain ⟨it, hit, hg⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hg
    exact ⟨.inr it, (inr_mem_layerEdges).2 hit, .hub it.1 it.2, by simp [leEnds], w,
      Option.mem_toFinset.1 hw, rfl⟩
  · obtain ⟨o, ho, hg⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨b, -, hg⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hg
    exact ⟨.inl o, (inl_mem_layerEdges).2 ho, .par o b, by cases b <;> simp [leEnds], w,
      Option.mem_toFinset.1 hw, rfl⟩

/-- The owner of an edge of a lifted object is unique: the edge of `Q_l` whose layer edge owns
it. -/
theorem owner_unique {ξ : Xi I.G I.M} {g : Sym2 V} {q q' : Sym2 (QVert V)}
    (h : ∃ e, R.layerOf ξ q = some e ∧ R.Owned ξ e g)
    (h' : ∃ e, R.layerOf ξ q' = some e ∧ R.Owned ξ e g) : q = q' := by
  obtain ⟨e, hl, ho⟩ := h
  obtain ⟨e', hl', ho'⟩ := h'
  obtain ⟨he, hq⟩ := layerOf_spec hl
  obtain ⟨he', hq'⟩ := layerOf_spec hl'
  have := owned_unique hI hR he he' ho ho'
  subst this
  exact Option.some.inj (hq.symm.trans hq')

/-- [s7:lemLift] (ii) for one member `c` of a decomposition of `E(Q_l)`: its lifted objects are
well formed objects of `G`, their edges are duplicate free, each is owned by (the layer edge of)
an edge of `c`, junction edges occur only for cycles, and every item of the layer edge of an edge
of `c` is used. -/
theorem lift_member {ξ : Xi I.G I.M} {Dec : List (Obj (QVert V))}
    (hD : IsDecomp ((R.Q ξ).edges : Set (Sym2 (QVert V))) Dec) {c : Obj (QVert V)}
    (hc : c ∈ Dec) :
    (∀ o ∈ R.liftObj ξ c, o.WF ∧ ∀ g ∈ o.edges, g ∈ I.G.edges) ∧
    ((R.liftObj ξ c).flatMap Obj.edges).Nodup ∧
    (∀ g ∈ (R.liftObj ξ c).flatMap Obj.edges, ∃ q ∈ c.edges, ∃ e, R.layerOf ξ q = some e ∧
      (g ∈ leItems e ∨ (c.isEdge = false ∧ R.IsJEdge ξ e g))) ∧
    (∀ q ∈ c.edges, ∀ e, R.layerOf ξ q = some e → ∀ g ∈ leItems e,
      g ∈ (R.liftObj ξ c).flatMap Obj.edges) := by
  obtain ⟨hWF, -, hmem⟩ := hD
  have hQ : ∀ q ∈ c.edges, q ∈ (R.Q ξ).edges := fun q hq =>
    Finset.mem_coe.1 ((hmem q).1 (List.mem_flatMap.2 ⟨c, hc, hq⟩))
  rcases c with q | cv
  · have hq : q ∈ (R.Q ξ).edges := hQ q (by simp [Obj.edges])
    obtain ⟨e, hl⟩ := layerOf_isSome hq
    have he := (layerOf_spec hl).1
    rw [liftObj_edge hl, flatMap_edges_map_edge]
    refine ⟨fun o ho => ?_, leItems_nodup hI hR he, fun g hg => ⟨q, by simp [Obj.edges], e, hl,
      Or.inl hg⟩, fun q' hq' e' hl' g hg => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ho
      have hJ := leItems_J hI hR he hg
      exact ⟨RoundInput.J_not_diag hI hJ, fun g' hg' => by
        simp only [Obj.edges, List.mem_singleton] at hg'
        exact hg' ▸ RoundInput.J_mem_edges hI hJ⟩
    · simp only [Obj.edges, List.mem_singleton] at hq'
      subst hq'
      rw [hl] at hl'
      cases hl'
      exact hg
  · obtain ⟨hnd, h3⟩ := hWF _ hc
    have hQ' : ∀ q ∈ cycleEdges cv, q ∈ (R.Q ξ).edges := hQ
    obtain ⟨f1, f2, f3, f4⟩ := liftCycle_facts hI hR hnd h3 hQ'
    rw [liftObj_cycle]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Obj.edges, List.mem_singleton,
      forall_eq]
    refine ⟨⟨⟨f1, f2⟩, fun g hg => ?_⟩, nodup_cycleEdges f1 f2, fun g hg => ?_, f4⟩
    · obtain ⟨q, -, e, hl, ho⟩ := f3 g hg
      exact owned_mem_edges hI hR (layerOf_spec hl).1 ho
    · obtain ⟨q, hq, e, hl, ho⟩ := f3 g hg
      exact ⟨q, hq, e, hl, ho.imp id (fun h => ⟨rfl, h⟩)⟩

end Rules

/-! ## Duplicate-free concatenations with owners -/

omit [DecidableEq V] in
/-- If every element of `F c` has an owner in `E c`, owners are unique, and the lists `E c` are
pairwise disjoint and duplicate free, then the concatenation of the `F c` is duplicate free as soon
as each `F c` is. -/
theorem nodup_flatMap_of_owner {α β γ : Type*} (D : List α) (E : α → List γ) (F : α → List β)
    (Own : β → γ → Prop) (hE : (D.flatMap E).Nodup) (hF : ∀ c ∈ D, (F c).Nodup)
    (hown : ∀ c ∈ D, ∀ y ∈ F c, ∃ q ∈ E c, Own y q)
    (huniq : ∀ y q q', Own y q → Own y q' → q = q') : (D.flatMap F).Nodup := by
  refine List.nodup_flatMap.2 ⟨hF, ?_⟩
  refine (List.nodup_flatMap.1 hE).2.imp_of_mem (fun {c c'} hc hc' hdis => ?_)
  intro y hy hy'
  obtain ⟨q, hq, ho⟩ := hown c hc y hy
  obtain ⟨q', hq', ho'⟩ := hown c' hc' y hy'
  exact hdis hq (huniq y q q' ho ho' ▸ hq')

end EG.Quot
