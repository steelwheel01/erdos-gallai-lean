module

public import EG.Proof.Light.ParentSteps
public import EG.Proof.Light.ArcClassEuler
public import EG.Proof.Light.ConnectorCycle
public import EG.Lib.Light.ChainAux

/-!
# The chaining engine of Lemma parent side for one phase (s5:lemParent, Steps 1–9, abstract)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1. `EG.PEngine.engine` is the proof
of Lemma parent side for one round `l` and one phase `c`, stated abstractly (as the step Specs of
`EG/Spec/Light/ParentSteps.lean`): the arcs `a ∈ arcSet` (paths `arcPath a` with ends `ends a`,
class `cls a < ncl`), the parent map `par`, the nodes `Nd`, and for every node `Y` and slot
`σ < Tsl Y` a class `LUg Y σ` (a graph on `VY Y`) that is `(ℓ_Y, t_Y)`-path connected through the
zone `Zn Y σ`. The hypotheses are the facts (F-a)–(F-d) and Step 0 of the TeX proof as used in
Steps 1–8; the run-level instantiation is `EG.lemParent` (`EG/Proof/Light/Parent.lean`).

Steps: 2–3 `EG.arcClassEuler` per class; 4 `EG.visitCap` with capacities `T^sl_Y`; 5 slots
(`EG.MTrail.slot`) and the multiplicity count (`EG.transitionCount`, `M_l − 1 ≤ t_Y` as the
hypothesis `hmult`); 6 routing (the path connectivity, one family per `(Y, σ)`); 7 the cycles
(`EG.connectorCycle`); 8 exact cover; 9 the object count. Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

namespace PEngine

open EG.MTrail

variable {V β ι : Type*} [DecidableEq V] [DecidableEq β] [DecidableEq ι]

/-- The edges of all arcs. -/
def arcEdgeSet (arcSet : Finset ι) (arcPath : ι → List V) : Finset (Sym2 V) :=
  arcSet.biUnion fun a => (walkEdges (arcPath a)).toFinset

theorem mem_arcEdgeSet {arcSet : Finset ι} {arcPath : ι → List V} {e : Sym2 V} :
    e ∈ arcEdgeSet arcSet arcPath ↔ ∃ a ∈ arcSet, e ∈ walkEdges (arcPath a) := by
  simp [arcEdgeSet]

/-- A nodup list of length `≥ 2`: its ends are distinct. -/
theorem ends_ne {p : List V} {x y : V} (hp : p.Nodup) (h2 : 2 ≤ p.length) (hx : p.head? = some x)
    (hy : p.getLast? = some y) : x ≠ y := by
  intro hxy
  have := head?_ne_getLast?_of_nodup hp h2
  rw [hx, hy, hxy] at this
  exact this rfl

theorem mem_of_head? {p : List V} {x : V} (h : p.head? = some x) : x ∈ p :=
  List.mem_of_mem_head? h

theorem mem_of_getLast? {p : List V} {x : V} (h : p.getLast? = some x) : x ∈ p :=
  List.mem_of_getLast? h

theorem two_le_of_head_last {l : List V} {a b : V} (ha : l.head? = some a)
    (hb : l.getLast? = some b) (hab : a ≠ b) : 2 ≤ l.length := by
  match l with
  | [] => simp at ha
  | [c] =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at ha hb
    exact absurd (ha.symm.trans hb) hab
  | _ :: _ :: _ => simp

theorem nodup_interior {l : List V} (h : l.Nodup) : (interior l).Nodup :=
  h.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _))

theorem mem_of_mem_interior {l : List V} {x : V} (h : x ∈ interior l) : x ∈ l :=
  ((List.dropLast_sublist _).trans (List.tail_sublist _)).subset h

theorem flatMap_map_edge (l : List (Sym2 V)) : (l.map Obj.edge).flatMap Obj.edges = l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [List.flatMap_cons, Obj.edges, ih]

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]; simp

theorem length_flatMap_transitions (ends : ι → V × V) (L : List (List (ι × Bool))) :
    (L.flatMap (transitions ends)).length = (trailEdges L).length := by
  induction L with
  | nil => rfl
  | cons W L ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_transitions]
    simp [trailEdges]

section Engine

variable (arcSet : Finset ι) (arcPath : ι → List V) (ends : ι → V × V) (cls : ι → ℕ) (ncl : ℕ)
  (par : V → β) (Nd : Finset β) (Tsl : β → ℕ) (tm ℓ : β → ℝ) (LUg : β → ℕ → FGraph V)
  (Zn : β → ℕ → Finset V) (VY : β → Finset V) (K : ℕ) (Tmin : ℝ)

/-- The hypotheses of the engine: Step 0 of the proof of [s5:lemParent] (facts (F-a)–(F-d)) and
the properties of the good parents used in Steps 5–8. -/
structure Hyp : Prop where
  hpath : ∀ a ∈ arcSet, (arcPath a).Nodup ∧ 2 ≤ (arcPath a).length
  hends : ∀ a ∈ arcSet, (arcPath a).head? = some (ends a).1 ∧ (arcPath a).getLast? = some (ends a).2
  hcls : ∀ a ∈ arcSet, cls a < ncl
  hvd : ∀ a ∈ arcSet, ∀ b ∈ arcSet, cls a = cls b → a ≠ b → ∀ x ∈ arcPath a, x ∉ arcPath b
  hed : ∀ a ∈ arcSet, ∀ b ∈ arcSet, a ≠ b → (walkEdges (arcPath a)).Disjoint (walkEdges (arcPath b))
  hlen : ∀ a ∈ arcSet, (walkEdges (arcPath a)).length ≤ K
  hpar : ∀ a ∈ arcSet, par (ends a).1 ∈ Nd ∧ par (ends a).2 ∈ Nd ∧
    (ends a).1 ∈ VY (par (ends a).1) ∧ (ends a).2 ∈ VY (par (ends a).2)
  hmult : ∀ v, ((arcSet.filter fun a => (ends a).1 = v ∨ (ends a).2 = v).card : ℝ) ≤ tm (par v)
  htm : ∀ Y ∈ Nd, 0 ≤ tm Y
  hTmin : 1 ≤ Tmin
  hTsl : ∀ Y ∈ Nd, Tmin ≤ (Tsl Y : ℝ)
  hLUv : ∀ Y ∈ Nd, ∀ σ < Tsl Y, (LUg Y σ).verts = VY Y
  hPC : ∀ Y ∈ Nd, ∀ σ < Tsl Y, (LUg Y σ).IsPathConnected (ℓ Y) (tm Y) (Zn Y σ)
  hZdis : ∀ Y ∈ Nd, ∀ σ < Tsl Y, ∀ Y' ∈ Nd, ∀ σ' < Tsl Y', (Y, σ) ≠ (Y', σ') →
    Disjoint (Zn Y σ) (Zn Y' σ')
  hZarc : ∀ a ∈ arcSet, ∀ x ∈ arcPath a, ∀ Y ∈ Nd, ∀ σ < Tsl Y, x ∉ Zn Y σ
  hLUdis : ∀ Y ∈ Nd, ∀ σ < Tsl Y, ∀ Y' ∈ Nd, ∀ σ' < Tsl Y', (Y, σ) ≠ (Y', σ') →
    Disjoint (LUg Y σ).edges (LUg Y' σ').edges
  hLUarc : ∀ a ∈ arcSet, ∀ e ∈ walkEdges (arcPath a), ∀ Y ∈ Nd, ∀ σ < Tsl Y, e ∉ (LUg Y σ).edges

end Engine


universe uV uβ uι

/-- [s5:lemParent] for one round and one phase, abstract form (module docstring). -/
theorem engine {V : Type uV} {β : Type uβ} {ι : Type uι} [DecidableEq V] [DecidableEq β]
    [DecidableEq ι]
    (arcSet : Finset ι) (arcPath : ι → List V) (ends : ι → V × V) (cls : ι → ℕ) (ncl : ℕ)
    (par : V → β) (Nd : Finset β) (Tsl : β → ℕ) (tm ℓ : β → ℝ) (LUg : β → ℕ → FGraph V)
    (Zn : β → ℕ → Finset V) (VY : β → Finset V) (K : ℕ) (Tmin : ℝ)
    (h : Hyp arcSet arcPath ends cls ncl par Nd Tsl tm ℓ LUg Zn VY K Tmin) :
    ∃ (LentU : Finset (Sym2 V)) (D : List (Obj V)) (extra : ℕ),
      Disjoint LentU (arcEdgeSet arcSet arcPath) ∧
      IsDecomp ((arcEdgeSet arcSet arcPath ∪ LentU : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      (∀ e ∈ LentU, ∃ Y ∈ Nd, ∃ σ < Tsl Y, ∃ p : List V,
        IsPathIn (LUg Y σ).edges p ∧ IsThrough (Zn Y σ) p ∧ e ∈ walkEdges p) ∧
      D.length ≤ ncl * (Nd.card * (K + 1)) + extra ∧
      (extra : ℝ) ≤ (arcSet.card : ℝ) / Tmin := by
  classical
  set E := qEnds par ends with hE
  -- Steps 1–3: the classes, their `T`-joins and Euler trails
  set A : ℕ → Finset ι := fun i => arcSet.filter fun a => cls a = i with hA
  have hAsub : ∀ i, A i ⊆ arcSet := fun i => Finset.filter_subset _ _
  have hApar : ∀ i, ∀ a ∈ A i, par (ends a).1 ∈ Nd ∧ par (ends a).2 ∈ Nd := fun i a ha =>
    ⟨(h.hpar a (hAsub i ha)).1, (h.hpar a (hAsub i ha)).2.1⟩
  choose T Ws hTA hTc hWsl hWscl hWsnd hWsmem using fun i =>
    arcClassEuler.{uV, uβ, uι} V β ι (A i) ends par Nd (hApar i)
  -- the node of every transition is a good parent (`∈ Nd`)
  have hnodeNd : ∀ i, ∀ W ∈ Ws i, ∀ p ∈ W, par (oTgt ends p) ∈ Nd := by
    intro i W hW p hp
    have hpA : p.1 ∈ A i := ((hWsmem i p.1).1 (List.mem_flatMap.2 ⟨W, hW,
      List.mem_map_of_mem hp⟩)).1
    rcases oTgt_mem_ends ends p with h1 | h1 <;> rw [h1]
    · exact (hApar i p.1 hpA).1
    · exact (hApar i p.1 hpA).2
  have hTmin0 : (0 : ℝ) < Tmin := lt_of_lt_of_le one_pos h.hTmin
  have hTsl1 : ∀ Y ∈ Nd, 1 ≤ Tsl Y := fun Y hY => by
    have := h.hTsl Y hY; have := h.hTmin; exact_mod_cast (show (1 : ℝ) ≤ Tsl Y by linarith)
  have hcap1 : ∀ i, ∀ W ∈ Ws i, ∀ t ∈ transitions ends W, 1 ≤ Tsl (par t.1) := by
    intro i W hW t ht
    obtain ⟨j, hj, rfl⟩ := mem_transitions.1 ht
    exact hTsl1 _ (hnodeNd i W hW _ (List.getElem_mem hj))
  -- Step 4: visit capping
  choose Ws' hWs'cl hWs'perm hWs'sub hWs'vis hWs'len using fun i =>
    visitCap.{uV, uβ, uι} V β ι ends par Tsl (Ws i) (hWscl i) (hWsnd i) (hcap1 i)
  -- the final trails
  set FT := (List.range ncl).flatMap Ws' with hFT
  have hFTcl : ∀ W ∈ FT, IsClosedTrail E W := by
    intro W hW; obtain ⟨i, -, hWi⟩ := List.mem_flatMap.1 hW; exact hWs'cl i W hWi
  have hTE : ∀ i a, a ∈ trailEdges (Ws' i) ↔ a ∈ A i ∧ a ∉ T i := fun i a =>
    ((hWs'perm i).mem_iff).trans (hWsmem i a)
  have hFTcls : ∀ W ∈ FT, ∃ i, ∀ p ∈ W, p.1 ∈ A i ∧ p.1 ∉ T i := by
    intro W hW
    obtain ⟨i, -, hWi⟩ := List.mem_flatMap.1 hW
    exact ⟨i, fun p hp => (hTE i p.1).1 (List.mem_flatMap.2 ⟨W, hWi, List.mem_map_of_mem hp⟩)⟩
  have hFTnd : (trailEdges FT).Nodup := by
    rw [trailEdges_flatMap, List.nodup_flatMap]
    refine ⟨fun i _ => (hWs'perm i).nodup_iff.2 (hWsnd i), ?_⟩
    refine (List.nodup_range).pairwise_of_forall_ne fun i _ j _ hij => ?_
    rw [Function.onFun, List.disjoint_left]
    intro a ha hb
    have h1 := ((hTE i a).1 ha).1
    have h2 := ((hTE j a).1 hb).1
    exact hij ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
  have hFTmem : ∀ a, a ∈ trailEdges FT ↔ a ∈ arcSet ∧ a ∉ T (cls a) := by
    intro a
    rw [trailEdges_flatMap, List.mem_flatMap]
    constructor
    · rintro ⟨i, -, ha⟩
      obtain ⟨h1, h2⟩ := (hTE i a).1 ha
      obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
      subst h4
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨cls a, List.mem_range.2 (h.hcls a h1),
        (hTE _ a).2 ⟨Finset.mem_filter.2 ⟨h1, rfl⟩, h2⟩⟩
  have hFTarc : ∀ W ∈ FT, ∀ p ∈ W, p.1 ∈ arcSet := fun W hW p hp =>
    ((hFTmem p.1).1 (List.mem_flatMap.2 ⟨W, hW, List.mem_map_of_mem hp⟩)).1
  have hdist : ∀ a ∈ arcSet, (ends a).1 ≠ (ends a).2 := fun a ha =>
    ends_ne (h.hpath a ha).1 (h.hpath a ha).2 (h.hends a ha).1 (h.hends a ha).2
  have hFTWs' : ∀ W ∈ FT, ∃ i, W ∈ Ws' i := fun W hW => by
    obtain ⟨i, -, hWi⟩ := List.mem_flatMap.1 hW; exact ⟨i, hWi⟩
  have hFTlen : FT.length = ((List.range ncl).map fun i => (Ws' i).length).sum := by
    rw [hFT, List.length_flatMap]
  clear_value FT
  -- Step 5: positions, nodes and slots
  let pt : Pos FT → ι × Bool := fun x => FT[x.1.1][x.2.1]
  let nx : Pos FT → ι × Bool := fun x =>
    FT[x.1.1][(x.2.1 + 1) % FT[x.1.1].length]'(Nat.mod_lt _
      (lt_of_le_of_lt (Nat.zero_le _) x.2.isLt))
  let nd : Pos FT → β := fun x => par (oTgt ends (pt x))
  let sl : Pos FT → ℕ := fun x => slot (fun p => par (oTgt ends p)) FT[x.1.1] x.2.1 (nd x)
  let pr : Pos FT → V × V := fun x => (oTgt ends (pt x), oSrc ends (nx x))
  have hWmem : ∀ x : Pos FT, FT[x.1.1] ∈ FT := fun x => List.getElem_mem _
  have hptmem : ∀ x : Pos FT, pt x ∈ FT[x.1.1] := fun x => List.getElem_mem _
  have hnxmem : ∀ x : Pos FT, nx x ∈ FT[x.1.1] := fun x => List.getElem_mem _
  have hprmem : ∀ x : Pos FT, pr x ∈ transitions ends FT[x.1.1] := fun x =>
    mem_transitions.2 ⟨x.2.1, x.2.isLt, rfl⟩
  have hclaim : ∀ x : Pos FT, (pr x).1 ≠ (pr x).2 ∧ par (pr x).1 = par (pr x).2 := by
    intro x
    refine transitionClaim.{uV, uβ, uι} V β ι ends par FT[x.1.1] (hFTcl _ (hWmem x))
      (fun p hp => hdist p.1 (hFTarc _ (hWmem x) p hp)) ?_ (pr x) (hprmem x)
    intro p hp q hq hpq y hy
    obtain ⟨i, hi⟩ := hFTcls _ (hWmem x)
    have hpA := (hi p hp).1
    have hqA := (hi q hq).1
    have hpa := hAsub i hpA
    have hqa := hAsub i hqA
    have hcl : cls p.1 = cls q.1 := (Finset.mem_filter.1 hpA).2.trans (Finset.mem_filter.1 hqA).2.symm
    have hy' : y ∈ arcPath p.1 := by
      rcases hy with rfl | rfl
      · exact mem_of_head? (h.hends p.1 hpa).1
      · exact mem_of_getLast? (h.hends p.1 hpa).2
    have hvd := h.hvd p.1 hpa q.1 hqa hcl hpq y hy'
    exact ⟨fun h' => hvd (h' ▸ mem_of_head? (h.hends q.1 hqa).1),
      fun h' => hvd (h' ▸ mem_of_getLast? (h.hends q.1 hqa).2)⟩
  have hndNd : ∀ x : Pos FT, nd x ∈ Nd := by
    intro x
    have ha := hFTarc _ (hWmem x) (pt x) (hptmem x)
    show par (oTgt ends (pt x)) ∈ Nd
    rcases oTgt_mem_ends ends (pt x) with h1 | h1 <;> rw [h1]
    · exact (h.hpar _ ha).1
    · exact (h.hpar _ ha).2.1
  have hprVY : ∀ x : Pos FT, (pr x).1 ∈ VY (nd x) ∧ (pr x).2 ∈ VY (nd x) := by
    intro x
    have ha := hFTarc _ (hWmem x) (pt x) (hptmem x)
    have hb := hFTarc _ (hWmem x) (nx x) (hnxmem x)
    have hpar2 : par (pr x).2 = nd x := (hclaim x).2.symm
    refine ⟨?_, ?_⟩
    · show oTgt ends (pt x) ∈ VY (par (oTgt ends (pt x)))
      rcases oTgt_mem_ends ends (pt x) with h1 | h1 <;> rw [h1]
      · exact (h.hpar _ ha).2.2.1
      · exact (h.hpar _ ha).2.2.2
    · rw [← hpar2]
      show oSrc ends (nx x) ∈ VY (par (oSrc ends (nx x)))
      rcases oSrc_mem_ends ends (nx x) with h1 | h1 <;> rw [h1]
      · exact (h.hpar _ hb).2.2.1
      · exact (h.hpar _ hb).2.2.2
  have hslTsl : ∀ x : Pos FT, sl x < Tsl (nd x) := by
    intro x
    obtain ⟨i, hWi⟩ := hFTWs' _ (hWmem x)
    have hv := hWs'vis i _ hWi (nd x)
    unfold vis at hv
    rw [countP_transitions_node] at hv
    simp only [oTgt_qEnds] at hv
    exact lt_of_lt_of_le (slot_lt _ _ _ x.2.isLt) hv
  -- Step 5, counting: every vertex lies in at most `t_Y` of the pairs at its node
  have hmultPos : ∀ v, ((Finset.univ.filter fun x : Pos FT => (pr x).1 = v ∨ (pr x).2 = v).card : ℝ)
      ≤ tm (par v) := by
    intro v
    have h1 := card_pos_filter ends FT (fun t => t.1 = v ∨ t.2 = v)
    have h2 := transitionCount.{uV, uβ, uι} V β ι ends par FT hFTcl hFTnd
      (fun a ha => hdist a ((hFTmem a).1 ha).1) v
    have h3 : ((trailEdges FT).toFinset.filter fun a => (ends a).1 = v ∨ (ends a).2 = v) ⊆
        arcSet.filter fun a => (ends a).1 = v ∨ (ends a).2 = v := by
      intro a ha
      rw [Finset.mem_filter, List.mem_toFinset] at ha
      exact Finset.mem_filter.2 ⟨((hFTmem a).1 ha.1).1, ha.2⟩
    have h4 := Finset.card_le_card h3
    have h5 : (Finset.univ.filter fun x : Pos FT => (pr x).1 = v ∨ (pr x).2 = v).card ≤
        (arcSet.filter fun a => (ends a).1 = v ∨ (ends a).2 = v).card := by
      rw [show (Finset.univ.filter fun x : Pos FT => (pr x).1 = v ∨ (pr x).2 = v) =
        (Finset.univ.filter fun x : Pos FT => (oTgt ends FT[x.1.1][x.2.1],
          oSrc ends (FT[x.1.1][(x.2.1 + 1) % FT[x.1.1].length]'(Nat.mod_lt _
            (lt_of_le_of_lt (Nat.zero_le _) x.2.isLt)))).1 = v ∨ (oTgt ends FT[x.1.1][x.2.1],
          oSrc ends (FT[x.1.1][(x.2.1 + 1) % FT[x.1.1].length]'(Nat.mod_lt _
            (lt_of_le_of_lt (Nat.zero_le _) x.2.isLt)))).2 = v) from rfl, h1]
      exact h2.trans h4
    exact (by exact_mod_cast h5 : ((Finset.univ.filter fun x : Pos FT =>
      (pr x).1 = v ∨ (pr x).2 = v).card : ℝ) ≤ _).trans (h.hmult v)
  -- Step 6: routing, one family per `(Y, σ)`
  have hroute : ∀ (Y : β) (σ : ℕ), ∃ Q : {x : Pos FT // nd x = Y ∧ sl x = σ} → List V,
      Y ∈ Nd → σ < Tsl Y →
        (∀ y, IsPathBetween (LUg Y σ).edges (pr y.1).1 (pr y.1).2 (Q y) ∧
          IsThrough (Zn Y σ) (Q y)) ∧
        ∀ y y', y ≠ y' → (walkEdges (Q y)).Disjoint (walkEdges (Q y')) := by
    intro Y σ
    by_cases hYσ : Y ∈ Nd ∧ σ < Tsl Y
    · have hP : ∀ y : {x : Pos FT // nd x = Y ∧ sl x = σ}, (pr y.1).1 ∈ (LUg Y σ).verts ∧
          (pr y.1).2 ∈ (LUg Y σ).verts ∧ (pr y.1).1 ≠ (pr y.1).2 := by
        intro y
        rw [h.hLUv Y hYσ.1 σ hYσ.2]
        have h1 := hprVY y.1
        rw [y.2.1] at h1
        exact ⟨h1.1, h1.2, (hclaim y.1).1⟩
      have hT : ∀ v : V, ((Finset.univ.filter fun y : {x : Pos FT // nd x = Y ∧ sl x = σ} =>
          (pr y.1).1 = v ∨ (pr y.1).2 = v).card : ℝ) ≤ tm Y := by
        intro v
        by_cases hv : ∃ x : Pos FT, nd x = Y ∧ ((pr x).1 = v ∨ (pr x).2 = v)
        · obtain ⟨x0, hx0, hx0v⟩ := hv
          have hpv : par v = Y := by
            rcases hx0v with h' | h'
            · rw [← h', ← hx0]
            · rw [← h', ← hx0]; exact (hclaim x0).2.symm
          refine le_trans ?_ ((hmultPos v).trans (le_of_eq (by rw [hpv])))
          have hc := Finset.card_le_card_of_injOn
            (s := Finset.univ.filter fun y : {x : Pos FT // nd x = Y ∧ sl x = σ} =>
              (pr y.1).1 = v ∨ (pr y.1).2 = v)
            (t := Finset.univ.filter fun x : Pos FT => (pr x).1 = v ∨ (pr x).2 = v)
            (fun y => y.1)
            (fun y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩)
            (fun y _ y' _ hyy => Subtype.ext hyy)
          exact_mod_cast hc
        · push Not at hv
          rw [Finset.card_eq_zero.2]
          · simpa using h.htm Y hYσ.1
          · rw [Finset.filter_eq_empty_iff]
            intro y _
            have := hv y.1 y.2.1
            tauto
      obtain ⟨Q, hQ, hQd⟩ := (h.hPC Y hYσ.1 σ hYσ.2).exists_paths
        (fun y : {x : Pos FT // nd x = Y ∧ sl x = σ} => pr y.1) hP hT
      exact ⟨Q, fun _ _ => ⟨fun y => ⟨(hQ y).1, (hQ y).2.1⟩, hQd⟩⟩
    · exact ⟨fun _ => [], fun h1 h2 => absurd ⟨h1, h2⟩ hYσ⟩
  choose Q hQ using hroute
  let conn : Pos FT → List V := fun x => Q (nd x) (sl x) ⟨x, rfl, rfl⟩
  have hconn : ∀ x, IsPathBetween (LUg (nd x) (sl x)).edges (pr x).1 (pr x).2 (conn x) ∧
      IsThrough (Zn (nd x) (sl x)) (conn x) := fun x =>
    (hQ (nd x) (sl x) (hndNd x) (hslTsl x)).1 ⟨x, rfl, rfl⟩
  have hQcast : ∀ (Y Y' : β) (σ σ' : ℕ) (hY : Y = Y') (hσ : σ = σ') (x : Pos FT)
      (h1 : nd x = Y ∧ sl x = σ) (h2 : nd x = Y' ∧ sl x = σ'), Q Y σ ⟨x, h1⟩ = Q Y' σ' ⟨x, h2⟩ := by
    intro Y Y' σ σ' hY hσ x h1 h2
    subst hY; subst hσ; rfl
  have hconnd : ∀ x x', x ≠ x' → (walkEdges (conn x)).Disjoint (walkEdges (conn x')) := by
    intro x x' hxx
    by_cases hs : nd x = nd x' ∧ sl x = sl x'
    · have e : conn x' = Q (nd x) (sl x) ⟨x', hs.1.symm, hs.2.symm⟩ :=
        hQcast _ _ _ _ hs.1.symm hs.2.symm x' _ _
      rw [e]
      exact (hQ (nd x) (sl x) (hndNd x) (hslTsl x)).2 ⟨x, rfl, rfl⟩ ⟨x', hs.1.symm, hs.2.symm⟩
        (fun h' => hxx (congrArg Subtype.val h'))
    · have hne : (nd x, sl x) ≠ (nd x', sl x') := fun h' => hs (Prod.mk.inj h')
      have hd := h.hLUdis _ (hndNd x) _ (hslTsl x) _ (hndNd x') _ (hslTsl x') hne
      rw [List.disjoint_left]
      intro e he he'
      exact Finset.disjoint_left.1 hd ((hconn x).1.1.2.2 e he) ((hconn x').1.1.2.2 e he')
  -- distinct positions of one trail carry distinct arcs of one class
  have hposarc : ∀ (k : Fin FT.length) (i j : Fin (FT.get k).length), i ≠ j →
      ((FT.get k).get i).1 ≠ ((FT.get k).get j).1 := by
    intro k i j hij he
    have hnd := (hFTcl _ (List.getElem_mem k.2)).2.1
    have : ((FT.get k).map Prod.fst)[i.1]'(by simp) = ((FT.get k).map Prod.fst)[j.1]'(by simp) := by
      simpa using he
    exact hij (Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this))
  have hposcls : ∀ (k : Fin FT.length) (i j : Fin (FT.get k).length),
      cls ((FT.get k).get i).1 = cls ((FT.get k).get j).1 := by
    intro k i j
    obtain ⟨c, hc⟩ := hFTcls _ (List.getElem_mem k.2)
    exact (Finset.mem_filter.1 (hc _ (List.getElem_mem i.2)).1).2.trans
      (Finset.mem_filter.1 (hc _ (List.getElem_mem j.2)).1).2.symm
  -- Step 7: the cycles
  let segs : Fin FT.length → List (List V × List V) := fun k =>
    List.ofFn fun j : Fin (FT.get k).length => (orient arcPath ((FT.get k).get j), conn ⟨k, j⟩)
  let C : Fin FT.length → List V := fun k => (segs k).flatMap fun s => s.1 ++ interior s.2
  have hsegs : ∀ k (j : ℕ) (hj : j < (segs k).length), (segs k)[j] =
      (orient arcPath ((FT.get k).get ⟨j, by simpa [segs] using hj⟩),
        conn ⟨k, ⟨j, by simpa [segs] using hj⟩⟩) := by
    intro k j hj
    simp [segs, List.getElem_ofFn]
  have hlensegs : ∀ k, (segs k).length = (FT.get k).length := fun k => by simp [segs]
  have hcyc : ∀ k, (Obj.cycle (C k)).WF ∧ (cycleEdges (C k)).Perm
      ((segs k).flatMap fun s => walkEdges s.1 ++ walkEdges s.2) := by
    intro k
    have hWk := hFTcl _ (List.getElem_mem k.2)
    have harcW : ∀ j : Fin (FT.get k).length, ((FT.get k).get j).1 ∈ arcSet := fun j =>
      hFTarc _ (List.getElem_mem k.2) _ (List.getElem_mem j.2)
    refine connectorCycle.{uV} V (segs k) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h0
      have := congrArg List.length h0
      rw [hlensegs] at this
      exact hWk.1 (List.eq_nil_of_length_eq_zero this)
    · intro s hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hs
      have hp := h.hpath _ (harcW j)
      have hc := hconn ⟨k, j⟩
      refine ⟨orient_nodup.2 hp.1, by rw [length_orient]; exact hp.2, hc.1.1.2.1, ?_⟩
      exact two_le_of_head_last hc.1.2.1 hc.1.2.2 (hclaim ⟨k, j⟩).1
    · intro p hp
      obtain ⟨j, hj, rfl⟩ := mem_zip_rotate.1 hp
      rw [hsegs, hsegs]
      have hj' : j < (FT.get k).length := by rwa [hlensegs] at hj
      have hc := hconn ⟨k, ⟨j, hj'⟩⟩
      have ha := h.hends _ (harcW ⟨j, hj'⟩)
      have hjm : (j + 1) % (segs k).length < (FT.get k).length := by
        rw [hlensegs]; exact Nat.mod_lt _ (by omega)
      have hb := h.hends _ (harcW ⟨(j + 1) % (segs k).length, hjm⟩)
      refine ⟨?_, ?_⟩
      · rw [hc.1.2.1, orient_getLast? ha.1 ha.2]; rfl
      · rw [hc.1.2.2, orient_head? hb.1 hb.2]
        simp only [hlensegs]; rfl
    · -- the arcs of a trail are pairwise vertex-disjoint
      have e : (segs k).flatMap Prod.fst =
          (List.ofFn fun j : Fin (FT.get k).length => orient arcPath ((FT.get k).get j)).flatten := by
        simp only [segs, List.flatMap, List.map_ofFn]
        rfl
      rw [e, List.nodup_flatten]
      refine ⟨fun l hl => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
        exact orient_nodup.2 (h.hpath _ (harcW j)).1
      · rw [List.disjoint_left]
        intro x hx hx'
        rw [mem_orient] at hx hx'
        exact h.hvd _ (harcW i) _ (harcW j) (hposcls k i j) (hposarc k i j (ne_of_lt hij)) x hx hx'
    · -- the connector interiors are pairwise disjoint
      have e : ((segs k).flatMap fun s => interior s.2) =
          (List.ofFn fun j : Fin (FT.get k).length => interior (conn ⟨k, j⟩)).flatten := by
        simp only [segs, List.flatMap, List.map_ofFn]
        rfl
      rw [e, List.nodup_flatten]
      refine ⟨fun l hl => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
        exact nodup_interior (hconn ⟨k, j⟩).1.1.2.1
      · rw [List.disjoint_left]
        intro x hx hx'
        have hz := (hconn ⟨k, i⟩).2 x hx
        have hz' := (hconn ⟨k, j⟩).2 x hx'
        have hne : (nd ⟨k, i⟩, sl ⟨k, i⟩) ≠ (nd ⟨k, j⟩, sl ⟨k, j⟩) := by
          intro he
          obtain ⟨h1, h2⟩ := Prod.mk.inj he
          have := slot_lt_slot (fun p => par (oTgt ends p)) (FT.get k) i.2 j.2 hij h1
          exact absurd h2 (ne_of_lt this)
        exact Finset.disjoint_left.1 (h.hZdis _ (hndNd _) _ (hslTsl _) _ (hndNd _) _ (hslTsl _) hne)
          hz hz'
    · -- interiors avoid the arcs
      intro s hs s' hs' x hx hx'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hs
      obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hs'
      exact h.hZarc _ (harcW j') x (mem_orient.1 hx') _ (hndNd ⟨k, j⟩) _ (hslTsl ⟨k, j⟩)
        ((hconn ⟨k, j⟩).2 x hx)
    · -- arc edges are not connector edges
      rw [List.disjoint_left]
      intro e he he'
      obtain ⟨s, hs, hes⟩ := List.mem_flatMap.1 he
      obtain ⟨s', hs', hes'⟩ := List.mem_flatMap.1 he'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hs
      obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hs'
      have he1 : e ∈ walkEdges (arcPath ((FT.get k).get j).1) :=
        (walkEdges_orient_perm arcPath _).subset hes
      exact h.hLUarc _ (harcW j) e he1 _ (hndNd ⟨k, j'⟩) _ (hslTsl ⟨k, j'⟩)
        ((hconn ⟨k, j'⟩).1.1.2.2 e hes')
  -- Step 8: the objects and the exact cover
  let singles : List (Obj V) := (List.range ncl).flatMap fun i =>
    (T i).toList.flatMap fun a => (walkEdges (arcPath a)).map Obj.edge
  let cycles : List (Obj V) := List.ofFn fun k : Fin FT.length => Obj.cycle (C k)
  let LentU : Finset (Sym2 V) := Finset.univ.biUnion fun x : Pos FT => (walkEdges (conn x)).toFinset
  let Tl : List ι := (List.range ncl).flatMap fun i => (T i).toList
  let posL : List (Pos FT) := (List.finRange FT.length).flatMap fun k =>
    (List.finRange (FT.get k).length).map fun j => (⟨k, j⟩ : Pos FT)
  let g : ι → List (Sym2 V) := fun a => walkEdges (arcPath a)
  let hc : Pos FT → List (Sym2 V) := fun x => walkEdges (conn x)
  have hsingles : singles.flatMap Obj.edges = Tl.flatMap g := by
    simp only [singles, Tl, g, List.flatMap_assoc, flatMap_map_edge]
  have hcycles : (cycles.flatMap Obj.edges).Perm ((trailEdges FT).flatMap g ++ posL.flatMap hc) := by
    have e1 : cycles.flatMap Obj.edges = (List.finRange FT.length).flatMap fun k => cycleEdges (C k) := by
      simp only [cycles, List.ofFn_eq_map, List.flatMap_map, Obj.edges]
    rw [e1]
    have e2 : ∀ k : Fin FT.length, (cycleEdges (C k)).Perm
        ((((FT.get k).map Prod.fst).flatMap g) ++
          ((List.finRange (FT.get k).length).flatMap fun j => hc ⟨k, j⟩)) := by
      intro k
      refine (hcyc k).2.trans ((ConnCyc.flatMap_append_perm _ _ _).trans ?_)
      refine List.Perm.append ?_ ?_
      · have : (segs k).flatMap (fun s => walkEdges s.1) =
            (List.finRange (FT.get k).length).flatMap fun j => walkEdges (orient arcPath ((FT.get k).get j)) := by
          simp only [segs, List.ofFn_eq_map, List.flatMap_map]
        rw [this]
        refine (List.Perm.flatMap_left _ fun j _ => walkEdges_orient_perm arcPath _).trans ?_
        rw [← List.flatMap_map (fun j => (FT.get k).get j) (fun p => g p.1), List.map_get_finRange,
          List.flatMap_map]
      · simp only [segs, List.ofFn_eq_map, List.flatMap_map]
        exact List.Perm.refl _
    refine (List.Perm.flatMap_left _ fun k _ => e2 k).trans ?_
    refine (ConnCyc.flatMap_append_perm _ _ _).trans (List.Perm.append ?_ ?_)
    · have : (List.finRange FT.length).flatMap (fun k => ((FT.get k).map Prod.fst).flatMap g) =
          (trailEdges FT).flatMap g := by
        rw [← List.flatMap_map (fun k => FT.get k) (fun W => (W.map Prod.fst).flatMap g),
          List.map_get_finRange]
        simp only [trailEdges, List.flatMap_assoc]
      rw [this]
    · simp only [posL, List.flatMap_assoc, List.flatMap_map]
      exact List.Perm.refl _
  -- the arcs: the `T`-arcs and the arcs of the final trails are all the arcs, once
  have hTlmem : ∀ a, a ∈ Tl ↔ a ∈ arcSet ∧ a ∈ T (cls a) := by
    intro a
    simp only [Tl, List.mem_flatMap, List.mem_range, Finset.mem_toList]
    constructor
    · rintro ⟨i, -, ha⟩
      have := Finset.mem_filter.1 (hTA i ha)
      rw [this.2]; exact ⟨this.1, ha⟩
    · rintro ⟨h1, h2⟩; exact ⟨cls a, h.hcls a h1, h2⟩
  have hTlnd : Tl.Nodup := by
    simp only [Tl]
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => Finset.nodup_toList _, ?_⟩
    refine (List.nodup_range).pairwise_of_forall_ne fun i _ j _ hij => ?_
    rw [Function.onFun, List.disjoint_left]
    intro a ha hb
    rw [Finset.mem_toList] at ha hb
    exact hij ((Finset.mem_filter.1 (hTA i ha)).2.symm.trans (Finset.mem_filter.1 (hTA j hb)).2)
  have harcperm : (Tl ++ trailEdges FT).Perm arcSet.toList := by
    rw [List.perm_ext_iff_of_nodup _ (Finset.nodup_toList _)]
    · intro a
      rw [List.mem_append, hTlmem, hFTmem, Finset.mem_toList]
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
      · intro ha; by_cases hT : a ∈ T (cls a)
        · exact Or.inl ⟨ha, hT⟩
        · exact Or.inr ⟨ha, hT⟩
    · rw [List.nodup_append]
      refine ⟨hTlnd, hFTnd, fun a ha b hb hab => ?_⟩
      subst hab
      exact ((hFTmem a).1 hb).2 ((hTlmem a).1 ha).2
  have hposperm : posL.Perm (Finset.univ : Finset (Pos FT)).toList := by
    rw [List.perm_ext_iff_of_nodup _ (Finset.nodup_toList _)]
    · intro x
      simp only [posL, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
        Finset.mem_toList, Finset.mem_univ, iff_true]
      exact ⟨x.1, x.2, rfl⟩
    · simp only [posL]
      rw [List.nodup_flatMap]
      refine ⟨fun k _ => (List.nodup_finRange _).map fun j j' h' => by
        simpa using h', ?_⟩
      refine (List.nodup_finRange _).pairwise_of_forall_ne fun k _ k' _ hkk => ?_
      rw [Function.onFun, List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_map, List.mem_finRange, true_and] at hx hx'
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨j', hj'⟩ := hx'
      exact hkk (congrArg Sigma.fst hj').symm
  -- the edge lists
  set arcList := arcSet.toList.flatMap g with harcList
  set connList := (Finset.univ : Finset (Pos FT)).toList.flatMap hc with hconnList
  have hDperm : ((singles ++ cycles).flatMap Obj.edges).Perm (arcList ++ connList) := by
    rw [List.flatMap_append, hsingles]
    refine (List.Perm.append_left _ hcycles).trans ?_
    rw [← List.append_assoc, ← List.flatMap_append]
    exact List.Perm.append (harcperm.flatMap_right g) (hposperm.flatMap_right hc)
  have harcnd : arcList.Nodup := by
    rw [harcList, List.nodup_flatMap]
    refine ⟨fun a ha => nodup_walkEdges (h.hpath a (Finset.mem_toList.1 ha)).1, ?_⟩
    exact (Finset.nodup_toList _).pairwise_of_forall_ne fun a ha b hb hab =>
      h.hed a (Finset.mem_toList.1 ha) b (Finset.mem_toList.1 hb) hab
  have hconnnd : connList.Nodup := by
    rw [hconnList, List.nodup_flatMap]
    refine ⟨fun x _ => nodup_walkEdges (hconn x).1.1.2.1, ?_⟩
    exact (Finset.nodup_toList _).pairwise_of_forall_ne fun x _ x' _ hxx => hconnd x x' hxx
  have hmemarc : ∀ e, e ∈ arcList ↔ e ∈ arcEdgeSet arcSet arcPath := by
    intro e
    rw [harcList, List.mem_flatMap, mem_arcEdgeSet]
    simp only [Finset.mem_toList, g]
  have hmemconn : ∀ e, e ∈ connList ↔ e ∈ LentU := by
    intro e
    rw [hconnList, List.mem_flatMap]
    simp only [Finset.mem_toList, Finset.mem_univ, true_and, LentU, Finset.mem_biUnion,
      List.mem_toFinset, hc]
  have hdisj : Disjoint LentU (arcEdgeSet arcSet arcPath) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨a, ha, hea⟩ := mem_arcEdgeSet.1 he'
    obtain ⟨x, -, hex⟩ := Finset.mem_biUnion.1 he
    exact h.hLUarc a ha e hea _ (hndNd x) _ (hslTsl x) ((hconn x).1.1.2.2 e (List.mem_toFinset.1 hex))
  -- Step 9: counting
  let ex : ℕ → ℕ := fun i => (Ws' i).length - (Ws i).length
  refine ⟨LentU, singles ++ cycles, ∑ i ∈ Finset.range ncl, ex i, hdisj, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- well-formed objects
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · simp only [singles, List.mem_flatMap, List.mem_range, Finset.mem_toList, List.mem_map] at ho
      obtain ⟨i, -, a, ha, e, he, rfl⟩ := ho
      exact not_isDiag_of_mem_walkEdges (h.hpath a (hAsub i (hTA i ha))).1 he
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ho
      exact (hcyc k).1
  · -- every edge once
    refine hDperm.nodup_iff.2 (List.nodup_append.2 ⟨harcnd, hconnnd, fun e he e' he' hee => ?_⟩)
    subst hee
    exact Finset.disjoint_left.1 hdisj ((hmemconn e).1 he') ((hmemarc e).1 he)
  · -- exactly the edges of the bundle and of `LentU`
    intro e
    rw [hDperm.mem_iff, List.mem_append, hmemarc, hmemconn, Finset.coe_union, Set.mem_union,
      Finset.mem_coe, Finset.mem_coe]
  · -- the connectors
    intro e he
    obtain ⟨x, -, hex⟩ := Finset.mem_biUnion.1 he
    exact ⟨nd x, hndNd x, sl x, hslTsl x, conn x, (hconn x).1.1, (hconn x).2,
      List.mem_toFinset.1 hex⟩
  · -- the number of objects
    have hs : singles.length = ∑ i ∈ Finset.range ncl,
        ((T i).toList.flatMap fun a => (walkEdges (arcPath a)).map Obj.edge).length := by
      simp only [singles, List.length_flatMap]
      exact sum_map_range _ ncl
    have hcl : cycles.length = ∑ i ∈ Finset.range ncl, (Ws' i).length := by
      simp only [cycles, List.length_ofFn]
      rw [hFTlen]
      exact sum_map_range _ ncl
    rw [List.length_append, hs, hcl, ← Finset.sum_add_distrib]
    have hterm : ∀ i ∈ Finset.range ncl,
        ((T i).toList.flatMap fun a => (walkEdges (arcPath a)).map Obj.edge).length +
          (Ws' i).length ≤ Nd.card * (K + 1) + ex i := by
      intro i _
      have h1 : ((T i).toList.flatMap fun a => (walkEdges (arcPath a)).map Obj.edge).length ≤
          (Nd.card - 1) * K := by
        rw [List.length_flatMap]
        refine (List.sum_le_card_nsmul _ K ?_).trans ?_
        · intro n hn
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hn
          rw [List.length_map]
          exact h.hlen a (hAsub i (hTA i (Finset.mem_toList.1 ha)))
        · rw [List.length_map, Finset.length_toList, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hTc i)
      have h2 : (Ws' i).length ≤ Nd.card + ex i := by
        have := hWsl i; simp only [ex]; omega
      have h3 : (Nd.card - 1) * K + Nd.card ≤ Nd.card * (K + 1) := by
        have : (Nd.card - 1) * K ≤ Nd.card * K := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        rw [Nat.mul_succ]; omega
      omega
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  · -- the visit-capping pieces
    have hA : ∑ i ∈ Finset.range ncl, (A i).card = arcSet.card :=
      (Finset.card_eq_sum_card_fiberwise fun a ha => Finset.mem_range.2 (h.hcls a ha)).symm
    have hterm : ∀ i ∈ Finset.range ncl, ((ex i : ℕ) : ℝ) ≤ ((A i).card : ℝ) / Tmin := by
      intro i _
      set S := (((Ws i).flatMap (transitions ends)).map fun t => par t.1).toFinset with hS
      have hSNd : ∀ Y ∈ S, Y ∈ Nd := by
        intro Y hY
        rw [hS, List.mem_toFinset, List.mem_map] at hY
        obtain ⟨t, ht, rfl⟩ := hY
        obtain ⟨W, hW, htW⟩ := List.mem_flatMap.1 ht
        obtain ⟨j, hj, rfl⟩ := mem_transitions.1 htW
        exact hnodeNd i W hW _ (List.getElem_mem hj)
      have hsum : ∑ Y ∈ S, ((((Ws i).flatMap (transitions ends)).countP
            fun t => par t.1 = Y : ℕ) : ℝ) / (Tsl Y : ℝ) ≤
          (((trailEdges (Ws i)).length : ℕ) : ℝ) / Tmin := by
        calc _ ≤ ∑ Y ∈ S, ((((Ws i).flatMap (transitions ends)).countP
              fun t => par t.1 = Y : ℕ) : ℝ) / Tmin := by
              refine Finset.sum_le_sum fun Y hY => ?_
              exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hTmin0 (h.hTsl Y (hSNd Y hY))
          _ = (((trailEdges (Ws i)).length : ℕ) : ℝ) / Tmin := by
              rw [← Finset.sum_div, ← Nat.cast_sum, sum_countP_fiber (fun t : V × V => par t.1) S _
                (fun t ht => by rw [hS, List.mem_toFinset]; exact List.mem_map_of_mem ht),
                length_flatMap_transitions]
      have hlenA : (trailEdges (Ws i)).length ≤ (A i).card := by
        rw [← List.toFinset_card_of_nodup (hWsnd i)]
        exact Finset.card_le_card fun a ha => ((hWsmem i a).1 (List.mem_toFinset.1 ha)).1
      have hlenA' : (((trailEdges (Ws i)).length : ℕ) : ℝ) / Tmin ≤ ((A i).card : ℝ) / Tmin :=
        div_le_div_of_nonneg_right (by exact_mod_cast hlenA) hTmin0.le
      have hW := hWs'len i
      simp only [ex]
      by_cases hle : (Ws i).length ≤ (Ws' i).length
      · rw [Nat.cast_sub hle]
        linarith
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
        positivity
    rw [Nat.cast_sum]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_div, ← Nat.cast_sum, hA]


end PEngine

end EG
