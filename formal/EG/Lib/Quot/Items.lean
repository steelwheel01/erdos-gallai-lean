module

public import EG.Lib.Quot.ListAux

/-!
# Items, PAR objects and hub items of the round step (probe P-1, stage 3)

Facts about the objects of [s7:consRound] (a)–(d) under `RoundInput.Valid` / `Rules.Valid`, used by
the proofs of s7:lemWellDef, s7:lemSimple, s7:lemMULT, s7:lemLift (unit P1, design note
`formal/work/p2b/P1.md`):
* the four J-classes are pairwise disjoint and typed (`Jhub_not_Jfr`, …), J-edges are not loops;
* live vertices are not pooled; hubs and ports of live hub items;
* the PAR objects: their ends are distinct live ports, their middles live fresh centres; the
  J-edge of a PAR object at an end (`jAt`) determines the object;
* counting at a vertex: at most `deg_J(u)` PAR objects with an end at `u`, hub items at `u`, ends
  in `E'(u)`; at most `deg_J(x)` cherries with middle `x` ([s7:lemWellDef] proof: "By (J2) …, every
  port carries at most `M_l − 1` J-edges, hence at most `M_l − 1` live items").
-/

public section

namespace EG.Quot

open Finset

variable {V : Type*} [DecidableEq V]

namespace RoundInput

variable {I : RoundInput V}

/-! ## The J-classes -/

theorem mem_J {e : Sym2 V} : e ∈ I.J ↔ e ∈ I.Jlost ∨ e ∈ I.Jhub ∨ e ∈ I.Jfr ∨ e ∈ I.Jpar := by
  simp [RoundInput.J, or_assoc]

theorem Jhub_sub_J {e : Sym2 V} (h : e ∈ I.Jhub) : e ∈ I.J := mem_J.2 (Or.inr (Or.inl h))
theorem Jfr_sub_J {e : Sym2 V} (h : e ∈ I.Jfr) : e ∈ I.J := mem_J.2 (Or.inr (Or.inr (Or.inl h)))
theorem Jpar_sub_J {e : Sym2 V} (h : e ∈ I.Jpar) : e ∈ I.J := mem_J.2 (Or.inr (Or.inr (Or.inr h)))

variable (hI : I.Valid)
include hI

theorem hub_ne_port {h u : V} (hh : h ∈ I.hubs) (hu : u ∈ I.ports) : h ≠ u :=
  fun e => Finset.disjoint_left.1 hI.roles.2.1 hh (e ▸ hu)

theorem fresh_ne_port {x u : V} (hx : x ∈ I.fresh) (hu : u ∈ I.ports) : x ≠ u :=
  fun e => Finset.disjoint_left.1 hI.roles.2.2.2.1 hx (e ▸ hu)

theorem hub_ne_fresh {h x : V} (hh : h ∈ I.hubs) (hx : x ∈ I.fresh) : h ≠ x :=
  fun e => Finset.disjoint_left.1 hI.roles.1 hh (e ▸ hx)

theorem port_not_hub {u : V} (hu : u ∈ I.ports) : u ∉ I.hubs :=
  fun hh => hub_ne_port hI hh hu rfl

theorem fresh_not_hub {x : V} (hx : x ∈ I.fresh) : x ∉ I.hubs :=
  fun hh => hub_ne_fresh hI hh hx rfl

theorem J_not_diag {e : Sym2 V} (he : e ∈ I.J) : ¬ e.IsDiag :=
  I.G.loopless e (hI.J_sub he)

theorem J_mem_edges {e : Sym2 V} (he : e ∈ I.J) : e ∈ I.G.edges := hI.J_sub he

theorem Jhub_not_Jfr {e : Sym2 V} (h1 : e ∈ I.Jhub) (h2 : e ∈ I.Jfr) : False := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hI.hub_typed _ h1
  obtain ⟨x, hx, u', hu', he⟩ := hI.fr_typed _ h2
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hub_ne_fresh hI hh hx rfl
  · exact hub_ne_port hI hh hu' rfl

theorem Jhub_not_Jpar {e : Sym2 V} (h1 : e ∈ I.Jhub) (h2 : e ∈ I.Jpar) : False := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hI.hub_typed _ h1
  obtain ⟨p, hp, q, hq, he⟩ := hI.par_typed _ h2
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hub_ne_port hI hh hp rfl
  · exact hub_ne_port hI hh hq rfl

theorem Jfr_not_Jpar {e : Sym2 V} (h1 : e ∈ I.Jfr) (h2 : e ∈ I.Jpar) : False := by
  obtain ⟨x, hx, u, hu, rfl⟩ := hI.fr_typed _ h1
  obtain ⟨p, hp, q, hq, he⟩ := hI.par_typed _ h2
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fresh_ne_port hI hx hp rfl
  · exact fresh_ne_port hI hx hq rfl

theorem Jpar_port {e : Sym2 V} (he : e ∈ I.Jpar) {v : V} (hv : v ∈ e) : v ∈ I.ports := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hI.par_typed e he
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · exact hp
  · exact hq

/-- A `J^fr`-edge `xu` determines its fresh centre and its port. -/
theorem fr_edge_inj {x x' u u' : V} (hx : x ∈ I.fresh) (hx' : x' ∈ I.fresh) (hu : u ∈ I.ports)
    (hu' : u' ∈ I.ports) (h : s(x, u) = s(x', u')) : x = x' ∧ u = u' := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h1 (fresh_ne_port hI hx hu')

/-- A hub edge `hu` determines its hub and its port. -/
theorem hub_edge_inj {h h' u u' : V} (hh : h ∈ I.hubs) (hh' : h' ∈ I.hubs) (hu : u ∈ I.ports)
    (hu' : u' ∈ I.ports) (e : s(h, u) = s(h', u')) : h = h' ∧ u = u' := by
  rcases Sym2.eq_iff.1 e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h1 (hub_ne_port hI hh hu')

omit hI in
/-- Live vertices are not pooled ((a2)). -/
theorem live_not_pool {e : Sym2 V} (he : e ∈ I.live) {v : V} (hv : v ∈ e) : v ∉ I.pool :=
  I.not_mem_pool_of_mem_live he hv

omit hI in
theorem live_mem_J {e : Sym2 V} (he : e ∈ I.live) : e ∈ I.J :=
  (I.mem_items).1 (I.live_subset_items he) |>.1

omit hI in
/-- A port of a live item is JV-good. -/
theorem not_jvBad_of_live {e : Sym2 V} (he : e ∈ I.live) {u : V} (hu : u ∈ e)
    (hp : u ∈ I.ports) : ¬ I.jvBad u := by
  classical
  intro hb
  have h := (I.mem_live).1 he
  apply h.2.2
  simp only [paidJVBad, Finset.mem_filter]
  exact ⟨h.1, u, hu, hp, hb⟩

/-- A port of a live item has at least `Hcd` candidates ([s7:lemCand] (iv)). -/
theorem Hcd_le_cand_of_live {e : Sym2 V} (he : e ∈ I.live) {u : V} (hu : u ∈ e)
    (hp : u ∈ I.ports) : I.Hcd ≤ ((I.cand u).card : ℝ) :=
  hI.good_cand u hp (not_jvBad_of_live he hu hp)

/-! ## Hub items -/

theorem hubItems_live {it : V × V} (h : it ∈ I.hubItems) : s(it.1, it.2) ∈ I.live :=
  ((I.mem_hubItems).1 h).2.2.1

omit hI in
theorem hubItems_hub {it : V × V} (h : it ∈ I.hubItems) : it.1 ∈ I.hubs :=
  ((I.mem_hubItems).1 h).1

omit hI in
theorem hubItems_port {it : V × V} (h : it ∈ I.hubItems) : it.2 ∈ I.ports :=
  ((I.mem_hubItems).1 h).2.1

omit hI in
theorem hubItems_Jhub {it : V × V} (h : it ∈ I.hubItems) : s(it.1, it.2) ∈ I.Jhub :=
  ((I.mem_hubItems).1 h).2.2.2

omit hI in
theorem hubItems_hub_not_pool {it : V × V} (h : it ∈ I.hubItems) : it.1 ∉ I.pool :=
  live_not_pool (((I.mem_hubItems).1 h).2.2.1) (Sym2.mem_mk_left _ _)

omit hI in
theorem hubItems_port_not_pool {it : V × V} (h : it ∈ I.hubItems) : it.2 ∉ I.pool :=
  live_not_pool (((I.mem_hubItems).1 h).2.2.1) (Sym2.mem_mk_right _ _)

omit hI in
theorem hubItems_edge_inj {it it' : V × V} (h : it ∈ I.hubItems) (h' : it' ∈ I.hubItems)
    (hI : I.Valid) (e : s(it.1, it.2) = s(it'.1, it'.2)) : it = it' := by
  obtain ⟨h1, h2⟩ := hub_edge_inj hI (hubItems_hub h) (hubItems_hub h') (hubItems_port h)
    (hubItems_port h') e
  exact Prod.ext h1 h2

/-- The live hub items at `u` are at most `deg_J(u)`. -/
theorem card_hubItemsAt_le (u : V) : (I.hubItemsAt u).card ≤ degE I.J u := by
  unfold degE edgesAt
  refine Finset.card_le_card_of_injOn (fun it => s(it.1, it.2)) ?_ ?_
  · intro it hit
    rw [Finset.mem_coe, I.mem_hubItemsAt] at hit
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Jhub_sub_J (hubItems_Jhub hit.1), ?_⟩
    rw [← hit.2]; exact Sym2.mem_mk_right _ _
  · intro it hit it' hit' e
    rw [Finset.mem_coe, I.mem_hubItemsAt] at hit hit'
    exact hubItems_edge_inj hit.1 hit'.1 hI e

/-- Hub items at a port: at most `M_l − 1`. -/
theorem card_hubItemsAt_le_M {u : V} (hu : u ∈ I.ports) : (I.hubItemsAt u).card ≤ I.M - 1 :=
  (card_hubItemsAt_le hI u).trans (hI.J2 u (port_not_hub hI hu))

end RoundInput

/-! ## PAR objects -/

namespace ParObj

variable {W : Type*}

theorem Conflict.symm {o o' : ParObj W} (h : Conflict o o') : Conflict o' o := by
  rcases h with ⟨b, b', h⟩ | ⟨x, h1, h2⟩
  · exact Or.inl ⟨b', b, h.symm⟩
  · exact Or.inr ⟨x, h2, h1⟩

/-- The J-edge of a PAR object at its end `b`: its `J^par` edge, or the leg `x u` of a cherry. -/
def jAt : ParObj W → Bool → Sym2 W
  | par u v, _ => s(u, v)
  | cherry x u u', b => s(x, if b then u' else u)

theorem endAt_mem_jAt (o : ParObj W) (b : Bool) : o.endAt b ∈ o.jAt b := by
  cases o <;> cases b <;> simp [endAt, jAt]

theorem jAt_mem_edgeList (o : ParObj W) (b : Bool) : o.jAt b ∈ o.edgeList := by
  cases o <;> cases b <;> simp [jAt, edgeList]

theorem mem_edgeList {o : ParObj W} {e : Sym2 W} : e ∈ o.edgeList ↔ ∃ b, e = o.jAt b := by
  cases o <;> simp [edgeList, jAt]

theorem endAt_eq_iff (o : ParObj W) (b : Bool) (v : W) :
    o.endAt b = v ↔ (b = false ∧ o.endAt false = v) ∨ (b = true ∧ o.endAt true = v) := by
  cases b <;> simp

end ParObj

namespace Rules

variable {I : RoundInput V} (R : Rules I)

theorem mem_parObjsPar {o : ParObj V} :
    o ∈ parObjsPar I ↔ ∃ e ∈ I.parItems, o = ParObj.par (_root_.Quot.out e).1
      (_root_.Quot.out e).2 := by
  simp [parObjsPar, eq_comm]

theorem mem_cherries {o : ParObj V} :
    o ∈ R.cherries ↔ ∃ x ∈ I.fresh, ∃ p ∈ pairUp (R.pairing x), o = ParObj.cherry x p.1 p.2 := by
  simp [cherries, eq_comm]

theorem mem_parObjs {o : ParObj V} :
    o ∈ R.parObjs ↔ o ∈ parObjsPar I ∨ o ∈ R.cherries := by
  simp [parObjs]

theorem mk_out (e : Sym2 V) : s((_root_.Quot.out e).1, (_root_.Quot.out e).2) = e := by
  conv_rhs => rw [← Quot.out_eq e]

variable {R} (hI : I.Valid) (hR : R.Valid)
include hI hR

/-- The cherry `u–x–u'` of a pair of the pairing list at `x`: `xu`, `xu'` are live `J^fr` items,
`u ≠ u'` are ports. -/
theorem cherry_facts {x : V} (hx : x ∈ I.fresh) {p : V × V} (hp : p ∈ pairUp (R.pairing x)) :
    p.1 ≠ p.2 ∧ p.1 ∈ I.frPorts x ∧ p.2 ∈ I.frPorts x := by
  have hnd := (hR.pairing x hx).1
  have hmem := mem_of_mem_pairUp hp
  have hset := (hR.pairing x hx).2
  refine ⟨pairUp_ne hnd hp, ?_, ?_⟩
  · rw [← hset]; exact List.mem_toFinset.2 hmem.1
  · rw [← hset]; exact List.mem_toFinset.2 hmem.2

/-- Facts on a PAR object `o`: the J-edge at each end is a live item of `J^par ∪ J^fr` containing
the end, the ends are distinct ports, the middle (if any) is a fresh centre, and the J-edges of
`o` are exactly the `jAt o b`. -/
theorem parObj_facts {o : ParObj V} (ho : o ∈ R.parObjs) :
    (∀ b, o.jAt b ∈ I.live) ∧ (∀ b, o.jAt b ∈ I.Jpar ∨ o.jAt b ∈ I.Jfr) ∧
    (∀ b, o.endAt b ∈ I.ports) ∧ o.endAt false ≠ o.endAt true ∧
    (∀ x, o.middle = some x → x ∈ I.fresh ∧ ∀ b, x ∈ o.jAt b) := by
  rcases (R.mem_parObjs).1 ho with ho | ho
  · obtain ⟨e, he, rfl⟩ := (mem_parObjsPar).1 ho
    have he' := (I.mem_parItems).1 he
    have hj : ∀ b, (ParObj.par (_root_.Quot.out e).1 (_root_.Quot.out e).2).jAt b = e :=
      fun b => mk_out e
    obtain ⟨p, hp, q, hq, hpq⟩ := hI.par_typed e he'.2
    have hends : (_root_.Quot.out e).1 ∈ I.ports ∧ (_root_.Quot.out e).2 ∈ I.ports := by
      have := mk_out e
      rw [hpq] at this
      have hv : ∀ v ∈ e, v ∈ I.ports := by
        intro v hv
        rw [hpq] at hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hp
        · exact hq
      have m1 := Sym2.mem_mk_left (_root_.Quot.out e).1 (_root_.Quot.out e).2
      have m2 := Sym2.mem_mk_right (_root_.Quot.out e).1 (_root_.Quot.out e).2
      rw [mk_out] at m1 m2
      exact ⟨hv _ m1, hv _ m2⟩
    refine ⟨fun b => by rw [hj]; exact he'.1, fun b => by rw [hj]; exact Or.inl he'.2,
      fun b => by cases b <;> simp [ParObj.endAt, hends.1, hends.2], ?_, ?_⟩
    · intro h
      apply RoundInput.J_not_diag hI (RoundInput.live_mem_J he'.1)
      rw [← mk_out e, Sym2.mk_isDiag_iff]
      simpa [ParObj.endAt] using h
    · intro x hx; simp [ParObj.middle] at hx
  · obtain ⟨x, hx, p, hp, rfl⟩ := (R.mem_cherries).1 ho
    obtain ⟨hne, h1, h2⟩ := cherry_facts hI hR hx hp
    have h1' := (I.mem_frPorts).1 h1
    have h2' := (I.mem_frPorts).1 h2
    refine ⟨fun b => by cases b <;> simp [ParObj.jAt, h1'.2.1, h2'.2.1],
      fun b => by cases b <;> simp [ParObj.jAt, h1'.2.2, h2'.2.2],
      fun b => by cases b <;> simp [ParObj.endAt, h1'.1, h2'.1], by simpa [ParObj.endAt] using hne,
      ?_⟩
    intro y hy
    simp only [ParObj.middle, Option.some.injEq] at hy
    subst hy
    exact ⟨hx, fun b => by cases b <;> simp [ParObj.jAt]⟩

theorem parObj_end_port {o : ParObj V} (ho : o ∈ R.parObjs) (b : Bool) : o.endAt b ∈ I.ports :=
  (parObj_facts hI hR ho).2.2.1 b

theorem parObj_ends_ne {o : ParObj V} (ho : o ∈ R.parObjs) : o.endAt false ≠ o.endAt true :=
  (parObj_facts hI hR ho).2.2.2.1

theorem parObj_end_inj {o : ParObj V} (ho : o ∈ R.parObjs) {b b' : Bool}
    (h : o.endAt b = o.endAt b') : b = b' := by
  have hne := parObj_ends_ne hI hR ho
  cases b <;> cases b'
  · rfl
  · exact absurd h hne
  · exact absurd h.symm hne
  · rfl

theorem parObj_end_live {o : ParObj V} (ho : o ∈ R.parObjs) (b : Bool) :
    ∃ e ∈ I.live, o.endAt b ∈ e :=
  ⟨o.jAt b, (parObj_facts hI hR ho).1 b, ParObj.endAt_mem_jAt o b⟩

theorem parObj_end_not_pool {o : ParObj V} (ho : o ∈ R.parObjs) (b : Bool) :
    o.endAt b ∉ I.pool :=
  RoundInput.live_not_pool ((parObj_facts hI hR ho).1 b) (ParObj.endAt_mem_jAt o b)

theorem parObj_middle {o : ParObj V} (ho : o ∈ R.parObjs) {x : V} (hx : o.middle = some x) :
    x ∈ I.fresh ∧ x ∉ I.pool := by
  obtain ⟨h1, h2⟩ := (parObj_facts hI hR ho).2.2.2.2 x hx
  exact ⟨h1, RoundInput.live_not_pool ((parObj_facts hI hR ho).1 false) (h2 false)⟩

theorem parObj_edge_live {o : ParObj V} (ho : o ∈ R.parObjs) {e : Sym2 V}
    (he : e ∈ o.edgeList) : e ∈ I.live := by
  obtain ⟨b, rfl⟩ := ParObj.mem_edgeList.1 he
  exact (parObj_facts hI hR ho).1 b

theorem parObj_edge_J {o : ParObj V} (ho : o ∈ R.parObjs) {e : Sym2 V}
    (he : e ∈ o.edgeList) : e ∈ I.J :=
  RoundInput.live_mem_J (parObj_edge_live hI hR ho he)

theorem parObj_edge_type {o : ParObj V} (ho : o ∈ R.parObjs) {e : Sym2 V}
    (he : e ∈ o.edgeList) : e ∈ I.Jpar ∨ e ∈ I.Jfr := by
  obtain ⟨b, rfl⟩ := ParObj.mem_edgeList.1 he
  exact (parObj_facts hI hR ho).2.1 b

/-- A J-edge lies in at most one PAR object. -/
theorem parObj_eq_of_edge {o o' : ParObj V} (ho : o ∈ R.parObjs) (ho' : o' ∈ R.parObjs)
    {e : Sym2 V} (he : e ∈ o.edgeList) (he' : e ∈ o'.edgeList) : o = o' := by
  rcases (R.mem_parObjs).1 ho with h1 | h1 <;> rcases (R.mem_parObjs).1 ho' with h2 | h2
  · obtain ⟨e1, -, rfl⟩ := (mem_parObjsPar).1 h1
    obtain ⟨e2, -, rfl⟩ := (mem_parObjsPar).1 h2
    simp only [ParObj.edgeList, List.mem_singleton] at he he'
    rw [mk_out] at he he'
    rw [← he, ← he']
  · exfalso
    obtain ⟨e1, he1, rfl⟩ := (mem_parObjsPar).1 h1
    simp only [ParObj.edgeList, List.mem_singleton] at he
    rw [mk_out] at he
    subst he
    obtain ⟨x, hx, p, -, rfl⟩ := (R.mem_cherries).1 h2
    obtain ⟨b, hb⟩ := ParObj.mem_edgeList.1 he'
    have hxe : x ∈ e := hb ▸ ((parObj_facts hI hR ho').2.2.2.2 x rfl).2 b
    exact RoundInput.fresh_ne_port hI hx (RoundInput.Jpar_port hI ((I.mem_parItems).1 he1).2 hxe)
      rfl
  · exfalso
    obtain ⟨e2, he2, rfl⟩ := (mem_parObjsPar).1 h2
    simp only [ParObj.edgeList, List.mem_singleton] at he'
    rw [mk_out] at he'
    subst he'
    obtain ⟨x, hx, p, -, rfl⟩ := (R.mem_cherries).1 h1
    obtain ⟨b, hb⟩ := ParObj.mem_edgeList.1 he
    have hxe : x ∈ e := hb ▸ ((parObj_facts hI hR ho).2.2.2.2 x rfl).2 b
    exact RoundInput.fresh_ne_port hI hx (RoundInput.Jpar_port hI ((I.mem_parItems).1 he2).2 hxe)
      rfl
  · obtain ⟨x, hx, p, hp, rfl⟩ := (R.mem_cherries).1 h1
    obtain ⟨x', hx', p', hp', rfl⟩ := (R.mem_cherries).1 h2
    obtain ⟨b, hb⟩ := ParObj.mem_edgeList.1 he
    obtain ⟨b', hb'⟩ := ParObj.mem_edgeList.1 he'
    have hu := parObj_end_port hI hR ho b
    have hu' := parObj_end_port hI hR ho' b'
    simp only [ParObj.jAt] at hb hb'
    simp only [ParObj.endAt] at hu hu'
    obtain ⟨rfl, hy⟩ := RoundInput.fr_edge_inj hI hx hx' hu hu' (hb.symm.trans hb')
    have hnd := (hR.pairing x hx).1
    have := pairUp_unique hnd hp hp' (x := if b then p.2 else p.1)
      (by cases b <;> simp) (by rw [hy]; cases b' <;> simp)
    rw [this]

/-- Two PAR objects with an end at the same vertex `u`, with the same J-edge there, are equal. -/
theorem parObj_eq_of_jAt {o o' : ParObj V} (ho : o ∈ R.parObjs) (ho' : o' ∈ R.parObjs)
    {b b' : Bool} (h : o.jAt b = o'.jAt b') : o = o' :=
  parObj_eq_of_edge hI hR ho ho' (ParObj.jAt_mem_edgeList o b)
    (h ▸ ParObj.jAt_mem_edgeList o' b')

/-- At most `deg_J(u)` PAR objects have an end at `u`. -/
theorem card_parObjs_end_le (u : V) :
    (R.parObjs.filter (fun o => ∃ b, o.endAt b = u)).card ≤ degE I.J u := by
  classical
  unfold degE edgesAt
  refine Finset.card_le_card_of_injOn
    (fun o => if o.endAt false = u then o.jAt false else o.jAt true) ?_ ?_
  · intro o ho
    rw [Finset.mem_coe, Finset.mem_filter] at ho
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨b, hb⟩ := ho.2
    have hJ : ∀ b, o.jAt b ∈ I.J := fun b =>
      RoundInput.live_mem_J ((parObj_facts hI hR ho.1).1 b)
    dsimp only
    split_ifs with h
    · exact ⟨hJ false, h ▸ ParObj.endAt_mem_jAt o false⟩
    · have : b = true := by cases b <;> simp_all
      subst this
      exact ⟨hJ true, hb ▸ ParObj.endAt_mem_jAt o true⟩
  · intro o ho o' ho' e
    rw [Finset.mem_coe, Finset.mem_filter] at ho ho'
    dsimp only at e
    split_ifs at e
    all_goals exact parObj_eq_of_jAt hI hR ho.1 ho'.1 e

/-- At most `deg_J(x)` cherries have middle `x`. -/
theorem card_parObjs_middle_le (x : V) :
    (R.parObjs.filter (fun o => o.middle = some x)).card ≤ degE I.J x := by
  unfold degE edgesAt
  refine Finset.card_le_card_of_injOn (fun o => o.jAt false) ?_ ?_
  · intro o ho
    rw [Finset.mem_coe, Finset.mem_filter] at ho
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨RoundInput.live_mem_J ((parObj_facts hI hR ho.1).1 false),
      ((parObj_facts hI hR ho.1).2.2.2.2 x ho.2).2 false⟩
  · intro o ho o' ho' e
    rw [Finset.mem_coe, Finset.mem_filter] at ho ho'
    exact parObj_eq_of_jAt hI hR ho.1 ho'.1 e

theorem card_parObjs_end_le_M {u : V} (hu : u ∈ I.ports) :
    (R.parObjs.filter (fun o => ∃ b, o.endAt b = u)).card ≤ I.M - 1 :=
  (card_parObjs_end_le hI hR u).trans (hI.J2 u (RoundInput.port_not_hub hI hu))

theorem card_parObjs_middle_le_M (x : V) :
    (R.parObjs.filter (fun o => o.middle = some x)).card ≤ I.M - 1 := by
  by_cases hx : x ∈ I.fresh
  · exact (card_parObjs_middle_le hI hR x).trans (hI.J2 x (RoundInput.fresh_not_hub hI hx))
  · rw [Finset.card_eq_zero.2]
    · exact Nat.zero_le _
    · rw [Finset.filter_eq_empty_iff]
      intro o ho hm
      exact hx (parObj_middle hI hR ho hm).1

end Rules

end EG.Quot
