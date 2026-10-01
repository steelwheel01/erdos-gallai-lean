module

public import EG.Lib.Chain.PairUp
public import EG.Lib.Found.Components

/-!
# The cherry split (manuscript s6:lemJSLC, proof, Step 5)

Probe unit P2J (probe P-2, part 2), proof round 1. Generic form: `R` is an edge set, `W` a vertex
set (`W = V(Y)`), every edge of `R` joins a *centre* `h ∉ W` to a *port* `u ∈ W`, and every centre
has even degree in `R`.

"At every centre `h` …, pair the (evenly many) edges of `R_Y` at `h` arbitrarily into *cherries*
`{hu, hu'}`, written `u`–`h`–`u'`. Since `G` is simple, `u ≠ u'`. … Every edge … lies in exactly
one cherry. Two cherries *conflict* if they share a vertex. A centre is never an end of a cherry,
because centres lie outside `V(Y)` and ends inside. A cherry at `h` conflicts with at most
`deg_{R_Y}(h)/2 − 1` other cherries at `h`. Each of its two ends `u` has at most `M_l − 1` edges in
`R_Y`, each in at most one cherry …"

A cherry is a triple `(h, u, u')` (centre, first end, second end); its edges are `hu`, `hu'`.
-/

public section

namespace EG.Chain.Cherry

variable {V : Type*} [DecidableEq V] (R : Finset (Sym2 V)) (W : Finset V)

/-- The centres: vertices of `R` outside `W`. -/
@[expose] noncomputable def centres : Finset V := (edgeVerts R).filter (fun h => h ∉ W)

/-- The `R`-neighbours of `h`. -/
@[expose] noncomputable def nbr (h : V) : Finset V := (edgeVerts R).filter (fun u => s(h, u) ∈ R)

/-- The chosen pairing of the `R`-neighbours of `h` (when their number is even). -/
@[expose] noncomputable def pairsAt (h : V) : Finset (V × V) :=
  if hev : Even (nbr R h).card then (exists_pairing (nbr R h) hev).choose else ∅

/-- The cherries `(h, u, u')`: `h` a centre and `(u, u')` a pair of its neighbours. -/
@[expose] noncomputable def cherries : Finset (V × V × V) :=
  (centres R W).biUnion (fun h => (pairsAt R h).image (fun p => (h, p.1, p.2)))

/-- The two edges `hu`, `hu'` of the cherry `(h, u, u')`. -/
@[expose] def cEdges (c : V × V × V) : Finset (Sym2 V) := {s(c.1, c.2.1), s(c.1, c.2.2)}

/-- The three vertices of the cherry `(h, u, u')`. -/
@[expose] def cVerts (c : V × V × V) : Finset V := {c.1, c.2.1, c.2.2}

/-- Two cherries conflict if they share a vertex. -/
@[expose] def Conf (c c' : V × V × V) : Prop := ¬ Disjoint (cVerts c) (cVerts c')

instance : DecidableRel (Conf (V := V)) := fun c c' => by unfold Conf; infer_instance

theorem conf_symm {c c' : V × V × V} (h : Conf c c') : Conf c' c := fun h' => h h'.symm

variable {R W}

theorem mem_nbr {h u : V} : u ∈ nbr R h ↔ s(h, u) ∈ R := by
  unfold nbr
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hu
    refine ⟨?_, hu⟩
    unfold edgeVerts
    exact Finset.mem_biUnion.2 ⟨_, hu, by simp⟩

theorem card_nbr (h : V) : (nbr R h).card = degE R h := by
  unfold degE
  refine Finset.card_bij (fun u _ => s(h, u)) ?_ ?_ ?_
  · intro u hu
    exact FGraph.mem_edgesAt.2 ⟨mem_nbr.1 hu, Sym2.mem_mk_left _ _⟩
  · intro u _ u' _ huu
    exact Sym2.congr_right.1 huu
  · intro e he
    obtain ⟨heR, hhe⟩ := FGraph.mem_edgesAt.1 he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hhe
    exact ⟨w, mem_nbr.2 heR, rfl⟩

theorem pairsAt_spec {h : V} (hev : Even (degE R h)) :
    (∀ p ∈ pairsAt R h, p.1 ∈ nbr R h ∧ p.2 ∈ nbr R h ∧ p.1 ≠ p.2) ∧
      ∀ x ∈ nbr R h, ∃! p, p ∈ pairsAt R h ∧ (p.1 = x ∨ p.2 = x) := by
  have hev' : Even (nbr R h).card := by rw [card_nbr]; exact hev
  unfold pairsAt
  rw [dif_pos hev']
  exact (exists_pairing (nbr R h) hev').choose_spec

theorem mem_cherries {c : V × V × V} :
    c ∈ cherries R W ↔ c.1 ∈ centres R W ∧ (c.2.1, c.2.2) ∈ pairsAt R c.1 := by
  unfold cherries
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, p, hp, rfl⟩
    exact ⟨hh, hp⟩
  · rintro ⟨hh, hp⟩
    exact ⟨c.1, hh, (c.2.1, c.2.2), hp, rfl⟩

theorem mem_centres {h : V} : h ∈ centres R W ↔ h ∈ edgeVerts R ∧ h ∉ W := by
  unfold centres; rw [Finset.mem_filter]

/-- The hypotheses of the cherry split: every edge joins a centre outside `W` to a port in `W`,
and every centre has even degree. -/
structure Hyp (R : Finset (Sym2 V)) (W : Finset V) : Prop where
  split : ∀ e ∈ R, ∃ h u, e = s(h, u) ∧ h ∉ W ∧ u ∈ W
  even : ∀ h ∉ W, Even (degE R h)

variable (hR : Hyp R W)
include hR

/-- The edge `hu` with `h ∉ W`: `u ∈ W`. -/
theorem port_mem {h u : V} (he : s(h, u) ∈ R) (hh : h ∉ W) : u ∈ W := by
  obtain ⟨h', u', heq, hh', hu'⟩ := hR.split _ he
  rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hu'
  · exact absurd hu' hh

theorem cherry_spec {c : V × V × V} (hc : c ∈ cherries R W) :
    s(c.1, c.2.1) ∈ R ∧ s(c.1, c.2.2) ∈ R ∧ c.2.1 ≠ c.2.2 ∧ c.1 ∉ W ∧ c.2.1 ∈ W ∧ c.2.2 ∈ W := by
  obtain ⟨hh, hp⟩ := mem_cherries.1 hc
  obtain ⟨-, hhW⟩ := mem_centres.1 hh
  obtain ⟨h1, h2, h3⟩ := (pairsAt_spec (hR.even _ hhW)).1 _ hp
  have e1 := mem_nbr.1 h1
  have e2 := mem_nbr.1 h2
  exact ⟨e1, e2, h3, hhW, port_mem hR e1 hhW, port_mem hR e2 hhW⟩

theorem cEdges_subset {c : V × V × V} (hc : c ∈ cherries R W) : cEdges c ⊆ R := by
  obtain ⟨e1, e2, -⟩ := cherry_spec hR hc
  intro e he
  unfold cEdges at he
  rcases Finset.mem_insert.1 he with rfl | he
  · exact e1
  · rw [Finset.mem_singleton.1 he]; exact e2

/-- The centre and the port of an edge of a cherry. -/
theorem mem_cEdges {c : V × V × V} (hc : c ∈ cherries R W) {h x : V} (hh : h ∉ W)
    (he : s(h, x) ∈ cEdges c) : h = c.1 ∧ (x = c.2.1 ∨ x = c.2.2) := by
  obtain ⟨-, -, -, hcW, h1W, h2W⟩ := cherry_spec hR hc
  unfold cEdges at he
  rcases Finset.mem_insert.1 he with he | he
  · rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact absurd (h1 ▸ h1W) hh
  · rcases Sym2.eq_iff.1 (Finset.mem_singleton.1 he) with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact ⟨h1, Or.inr h2⟩
    · exact absurd (h1 ▸ h2W) hh

/-- "Every edge … lies in exactly one cherry": existence. -/
theorem exists_cherry {e : Sym2 V} (he : e ∈ R) : ∃ c ∈ cherries R W, e ∈ cEdges c := by
  obtain ⟨h, u, rfl, hh, hu⟩ := hR.split e he
  have hcen : h ∈ centres R W := mem_centres.2 ⟨by
    unfold edgeVerts; exact Finset.mem_biUnion.2 ⟨_, he, by simp⟩, hh⟩
  obtain ⟨p, ⟨hp, hpu⟩, -⟩ := (pairsAt_spec (hR.even h hh)).2 u (mem_nbr.2 he)
  refine ⟨(h, p.1, p.2), mem_cherries.2 ⟨hcen, hp⟩, ?_⟩
  unfold cEdges
  rcases hpu with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- "Every edge … lies in exactly one cherry": uniqueness. -/
theorem eq_of_mem_cEdges {c c' : V × V × V} (hc : c ∈ cherries R W) (hc' : c' ∈ cherries R W)
    {e : Sym2 V} (he : e ∈ cEdges c) (he' : e ∈ cEdges c') : c = c' := by
  obtain ⟨-, -, -, hcW, h1W, h2W⟩ := cherry_spec hR hc
  have hx : ∃ x, e = s(c.1, x) ∧ (x = c.2.1 ∨ x = c.2.2) := by
    unfold cEdges at he
    rcases Finset.mem_insert.1 he with he | he
    · exact ⟨c.2.1, he, Or.inl rfl⟩
    · exact ⟨c.2.2, Finset.mem_singleton.1 he, Or.inr rfl⟩
  obtain ⟨x, rfl, hx⟩ := hx
  obtain ⟨hcc, hx'⟩ := mem_cEdges hR hc' hcW he'
  obtain ⟨hh, hp⟩ := mem_cherries.1 hc
  obtain ⟨hh', hp'⟩ := mem_cherries.1 hc'
  obtain ⟨-, hhW⟩ := mem_centres.1 hh
  have hxn : x ∈ nbr R c.1 := by
    rcases hx with rfl | rfl
    · exact ((pairsAt_spec (hR.even _ hhW)).1 _ hp).1
    · exact ((pairsAt_spec (hR.even _ hhW)).1 _ hp).2.1
  obtain ⟨q, -, hq⟩ := (pairsAt_spec (hR.even _ hhW)).2 x hxn
  have e1 : (c.2.1, c.2.2) = q := hq _ ⟨hp, by rcases hx with rfl | rfl <;> simp⟩
  have e2 : (c'.2.1, c'.2.2) = q := hq _ ⟨hcc ▸ hp', by rcases hx' with rfl | rfl <;> simp⟩
  have := e1.trans e2.symm
  simp only [Prod.mk.injEq] at this
  exact Prod.ext hcc (Prod.ext this.1 this.2)

/-- `R` is the union of the edge sets of its cherries. -/
theorem biUnion_cEdges : (cherries R W).biUnion cEdges = R := by
  ext e
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, he⟩; exact cEdges_subset hR hc he
  · intro he; exact exists_cherry hR he

theorem disjoint_cEdges {c c' : V × V × V} (hc : c ∈ cherries R W) (hc' : c' ∈ cherries R W)
    (hne : c ≠ c') : Disjoint (cEdges c) (cEdges c') := by
  rw [Finset.disjoint_left]
  intro e he he'
  exact hne (eq_of_mem_cEdges hR hc hc' he he')

/-- The number of cherries is at most `|R|`. -/
theorem card_cherries_le : (cherries R W).card ≤ R.card := by
  refine Finset.card_le_card_of_injOn (fun c => s(c.1, c.2.1)) ?_ ?_
  · intro c hc
    exact Finset.mem_coe.2 (cherry_spec hR (Finset.mem_coe.1 hc)).1
  · intro c hc c' hc' heq
    have h1 : s(c.1, c.2.1) ∈ cEdges c := by unfold cEdges; exact Finset.mem_insert_self _ _
    have h2 : s(c'.1, c'.2.1) ∈ cEdges c' := by unfold cEdges; exact Finset.mem_insert_self _ _
    simp only at heq
    rw [← heq] at h2
    exact eq_of_mem_cEdges hR (Finset.mem_coe.1 hc) (Finset.mem_coe.1 hc') h1 h2

/-- A port `x ∈ W` is an end of at most `deg_R(x)` cherries ("each in at most one cherry"). -/
theorem card_cherries_port_le (x : V) :
    ((cherries R W).filter (fun c => c.2.1 = x ∨ c.2.2 = x)).card ≤ degE R x := by
  unfold degE
  refine Finset.card_le_card_of_injOn (fun c => s(c.1, x)) ?_ ?_
  · intro c hc
    obtain ⟨hc, hx⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
    obtain ⟨e1, e2, -⟩ := cherry_spec hR hc
    refine Finset.mem_coe.2 (FGraph.mem_edgesAt.2 ⟨?_, Sym2.mem_mk_right _ _⟩)
    rcases hx with rfl | rfl
    · exact e1
    · exact e2
  · intro c hc c' hc' heq
    obtain ⟨hc, hx⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
    obtain ⟨hc', hx'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc')
    have h1 : s(c.1, x) ∈ cEdges c := by
      unfold cEdges; rcases hx with rfl | rfl <;> simp
    have h2 : s(c'.1, x) ∈ cEdges c' := by
      unfold cEdges; rcases hx' with rfl | rfl <;> simp
    simp only at heq
    rw [← heq] at h2
    exact eq_of_mem_cEdges hR hc hc' h1 h2

/-- A centre `h` carries at most `deg_R(h)` cherries. -/
theorem card_cherries_centre_le (h : V) :
    ((cherries R W).filter (fun c => c.1 = h)).card ≤ degE R h := by
  unfold degE
  refine Finset.card_le_card_of_injOn (fun c => s(h, c.2.1)) ?_ ?_
  · intro c hc
    obtain ⟨hc1, hch⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
    have := (cherry_spec hR hc1).1
    rw [hch] at this
    exact Finset.mem_coe.2 (FGraph.mem_edgesAt.2 ⟨this, Sym2.mem_mk_left _ _⟩)
  · intro c hc c' hc' heq
    obtain ⟨hc1, hch⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
    obtain ⟨hc', hh⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc')
    have h1 : s(c.1, c.2.1) ∈ cEdges c := by unfold cEdges; simp
    have h2 : s(c'.1, c'.2.1) ∈ cEdges c' := by unfold cEdges; simp
    simp only at heq
    rw [hh, ← heq, ← hch] at h2
    exact eq_of_mem_cEdges hR hc1 hc' h1 h2

/-- The conflict degree of a cherry `(h, u, u')`: at most `deg(h) + deg(u) + deg(u')`. -/
theorem card_conf_le {c : V × V × V} (hc : c ∈ cherries R W) :
    ((cherries R W).filter (fun c' => c' ≠ c ∧ Conf c c')).card ≤
      degE R c.1 + degE R c.2.1 + degE R c.2.2 := by
  obtain ⟨-, -, -, hcW, h1W, h2W⟩ := cherry_spec hR hc
  have hsub : (cherries R W).filter (fun c' => c' ≠ c ∧ Conf c c') ⊆
      ((cherries R W).filter (fun c' => c'.1 = c.1)) ∪
      ((cherries R W).filter (fun c' => c'.2.1 = c.2.1 ∨ c'.2.2 = c.2.1)) ∪
      ((cherries R W).filter (fun c' => c'.2.1 = c.2.2 ∨ c'.2.2 = c.2.2)) := by
    intro c' hc'
    obtain ⟨hc', -, hconf⟩ := Finset.mem_filter.1 hc'
    obtain ⟨-, -, -, hcW', h1W', h2W'⟩ := cherry_spec hR hc'
    unfold Conf at hconf
    rw [Finset.not_disjoint_iff] at hconf
    obtain ⟨v, hv, hv'⟩ := hconf
    unfold cVerts at hv hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hv with rfl | rfl | rfl
    · rcases hv' with h | h | h
      · exact Or.inl (Or.inl ⟨hc', h.symm⟩)
      · exact absurd (h ▸ h1W') hcW
      · exact absurd (h ▸ h2W') hcW
    · rcases hv' with h | h | h
      · exact absurd (h ▸ h1W) hcW'
      · exact Or.inl (Or.inr ⟨hc', Or.inl h.symm⟩)
      · exact Or.inl (Or.inr ⟨hc', Or.inr h.symm⟩)
    · rcases hv' with h | h | h
      · exact absurd (h ▸ h2W) hcW'
      · exact Or.inr ⟨hc', Or.inl h.symm⟩
      · exact Or.inr ⟨hc', Or.inr h.symm⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := card_cherries_centre_le hR c.1
  have h2 := card_cherries_port_le hR c.2.1
  have h3 := card_cherries_port_le hR c.2.2
  have h4 := Finset.card_union_le ((cherries R W).filter (fun c' => c'.1 = c.1))
    ((cherries R W).filter (fun c' => c'.2.1 = c.2.1 ∨ c'.2.2 = c.2.1))
  omega

end EG.Chain.Cherry
