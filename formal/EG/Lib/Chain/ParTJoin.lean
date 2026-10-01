module

public import EG.Lib.Found.Components
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# T-joins in a finite edge set (for Lemma PAR, manuscript s6:lemPAR)

Probe unit P2E (probe P-2, part 1), proof round 1.

`EG.exists_tJoin`: let `E` be a finite edge set and `T` a finite vertex set such that, for every
vertex `z`, the number of vertices of `T` reachable from `z` in `(V(E), E)` is even (every
component contains an even number of vertices of `T`). Then some `J ⊆ E` has `deg_J(v)` odd
exactly for `v ∈ T`.

This replaces the manuscript's use of Cited result [s1:citEuler] (a) ("By Cited result
s1:citEuler, a spanning tree of the connected graph `C'` contains a `T`-join"): instead of a
spanning tree, `J` is built by induction on `|T|` as the symmetric difference of paths joining
pairs of vertices of `T` in the same component (a path from `x` to `y ≠ x` has odd degree exactly
at `x` and `y`, Mathlib `SimpleGraph.Walk.IsTrail.even_countP_edges_iff`). So the probe's proof of
Lemma PAR does not use the declared input `EG.eulerTreeTJoin`.
-/

public section

namespace EG

variable {V : Type*} [DecidableEq V]

theorem degE_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    degE (A ∪ B) v = degE A v + degE B v := by
  unfold degE edgesAt
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem degE_sdiff_add_inter (A B : Finset (Sym2 V)) (v : V) :
    degE (A \ B) v + degE (A ∩ B) v = degE A v := by
  unfold degE edgesAt
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
    (Finset.disjoint_sdiff_inter A B)), ← Finset.filter_union, Finset.sdiff_union_inter]

/-- Degrees of a symmetric difference `(A ∖ B) ∪ (B ∖ A)`:
`deg_{A∆B}(v) + 2 deg_{A∩B}(v) = deg_A(v) + deg_B(v)`. -/
theorem degE_symmDiff_add (A B : Finset (Sym2 V)) (v : V) :
    degE ((A \ B) ∪ (B \ A)) v + 2 * degE (A ∩ B) v = degE A v + degE B v := by
  rw [degE_union_of_disjoint (disjoint_sdiff_sdiff) v]
  have h1 := degE_sdiff_add_inter A B v
  have h2 := degE_sdiff_add_inter B A v
  rw [Finset.inter_comm] at h2
  omega

/-- The degree in the edge set of a trail is the number of its edges at `v`. -/
theorem degE_edges_toFinset {G : SimpleGraph V} {x y : V} {p : G.Walk x y} (hp : p.IsTrail)
    (v : V) : degE p.edges.toFinset v = p.edges.countP (fun e => v ∈ e) := by
  unfold degE edgesAt
  rw [List.filter_toFinset, List.toFinset_card_of_nodup (hp.edges_nodup.filter _),
    List.countP_eq_length_filter]

omit [DecidableEq V] in
/-- The edges of a walk of `edgeGraph E` lie in `E`. -/
theorem mem_of_mem_edges_edgeGraph {E : Finset (Sym2 V)} {x y : V} (p : (edgeGraph E).Walk x y)
    {e : Sym2 V} (he : e ∈ p.edges) : e ∈ E := by
  have := p.edges_subset_edgeSet he
  rw [edgeSet_edgeGraph] at this
  exact this.1

/-- A path of `edgeGraph E` from `x` to `y ≠ x`: its edge set lies in `E` and has odd degree
exactly at `x` and `y`. -/
theorem exists_path_edges {E : Finset (Sym2 V)} {x y : V} (hxy : x ≠ y)
    (h : (edgeGraph E).Reachable x y) :
    ∃ P ⊆ E, ∀ v, Odd (degE P v) ↔ (v = x ∨ v = y) := by
  obtain ⟨q⟩ := h
  set p := q.bypass
  have hp : p.IsPath := q.bypass_isPath
  refine ⟨p.edges.toFinset, fun e he => mem_of_mem_edges_edgeGraph p (List.mem_toFinset.1 he),
    fun v => ?_⟩
  rw [degE_edges_toFinset hp.isTrail, ← Nat.not_even_iff_odd,
    hp.isTrail.even_countP_edges_iff v]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (fun _ => h')
  · rintro h h'
    rcases h with rfl | rfl
    · exact (h' hxy).1 rfl
    · exact (h' hxy).2 rfl

/-- [s6:lemPAR] (proof, "The partition") T-joins: if every component of `(V(E), E)` contains an
even number of vertices of `T`, then some `J ⊆ E` has odd degree exactly at the vertices of `T`
(replacing "a spanning tree of the connected graph `C'` contains a `T`-join", Cited result
[s1:citEuler] (a)). -/
theorem exists_tJoin (E : Finset (Sym2 V)) [DecidableRel (edgeGraph E).Reachable] :
    ∀ (n : ℕ) (T : Finset V), T.card = n →
      (∀ z, Even (T.filter (fun t => (edgeGraph E).Reachable z t)).card) →
      ∃ J ⊆ E, ∀ v, Odd (degE J v) ↔ v ∈ T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hTn hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · refine ⟨∅, Finset.empty_subset _, fun v => ?_⟩
      simp [degE, edgesAt]
    -- a second vertex `y` of `T` in the component of `x`
    obtain ⟨y, hyT, hyx, hxy⟩ : ∃ y ∈ T, y ≠ x ∧ (edgeGraph E).Reachable x y := by
      by_contra hno
      push Not at hno
      have hfilt : T.filter (fun t => (edgeGraph E).Reachable x t) = {x} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨ht, hr⟩
          by_contra hne
          exact hno t ht hne hr
        · rintro rfl
          exact ⟨hx, SimpleGraph.Reachable.refl _⟩
      have := hT x
      rw [hfilt, Finset.card_singleton] at this
      exact (Nat.not_even_one) this
    set T' := (T.erase x).erase y with hT'
    have hyT' : y ∈ T.erase x := Finset.mem_erase.2 ⟨hyx, hyT⟩
    have hcard : T'.card + 2 = T.card := by
      rw [hT', Finset.card_erase_of_mem hyT', Finset.card_erase_of_mem hx]
      have : 2 ≤ T.card := by
        have h2 : ({x, y} : Finset V) ⊆ T := by
          intro t ht
          rcases Finset.mem_insert.1 ht with rfl | ht
          · exact hx
          · rw [Finset.mem_singleton.1 ht]; exact hyT
        have := Finset.card_le_card h2
        rwa [Finset.card_pair (Ne.symm hyx)] at this
      omega
    have hT'even : ∀ z, Even (T'.filter (fun t => (edgeGraph E).Reachable z t)).card := by
      intro z
      by_cases hzx : (edgeGraph E).Reachable z x
      · have hzy : (edgeGraph E).Reachable z y := hzx.trans hxy
        have hsub : T'.filter (fun t => (edgeGraph E).Reachable z t) =
            ((T.filter (fun t => (edgeGraph E).Reachable z t)).erase x).erase y := by
          ext t
          simp only [hT', Finset.mem_filter, Finset.mem_erase]
          tauto
        have hx' : x ∈ T.filter (fun t => (edgeGraph E).Reachable z t) :=
          Finset.mem_filter.2 ⟨hx, hzx⟩
        have hy' : y ∈ (T.filter (fun t => (edgeGraph E).Reachable z t)).erase x :=
          Finset.mem_erase.2 ⟨hyx, Finset.mem_filter.2 ⟨hyT, hzy⟩⟩
        rw [hsub, Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx']
        obtain ⟨r, hr⟩ := hT z
        have : 2 ≤ (T.filter (fun t => (edgeGraph E).Reachable z t)).card := by
          have := Finset.card_erase_of_mem hx'
          have := Finset.card_pos.2 ⟨y, hy'⟩
          omega
        exact ⟨r - 1, by omega⟩
      · have hzy : ¬ (edgeGraph E).Reachable z y := fun h => hzx (h.trans hxy.symm)
        have hsub : T'.filter (fun t => (edgeGraph E).Reachable z t) =
            T.filter (fun t => (edgeGraph E).Reachable z t) := by
          ext t
          simp only [hT', Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨⟨-, -, ht⟩, hr⟩; exact ⟨ht, hr⟩
          · rintro ⟨ht, hr⟩
            refine ⟨⟨?_, ?_, ht⟩, hr⟩
            · rintro rfl; exact hzy hr
            · rintro rfl; exact hzx hr
        rw [hsub]
        exact hT z
    obtain ⟨J', hJ'E, hJ'⟩ := ih T'.card (by omega) T' rfl hT'even
    obtain ⟨P, hPE, hP⟩ := exists_path_edges (Ne.symm hyx) hxy
    refine ⟨(J' \ P) ∪ (P \ J'), ?_, fun v => ?_⟩
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · exact hJ'E (Finset.mem_sdiff.1 he).1
      · exact hPE (Finset.mem_sdiff.1 he).1
    · have hdeg := degE_symmDiff_add J' P v
      have h1 := hJ' v
      have h2 := hP v
      have hmem : v ∈ T ↔ (v ∈ T' ↔ ¬ (v = x ∨ v = y)) := by
        simp only [hT', Finset.mem_erase]
        constructor
        · intro hv
          constructor
          · rintro ⟨hvy, hvx, -⟩ h
            rcases h with rfl | rfl
            · exact hvx rfl
            · exact hvy rfl
          · intro h
            exact ⟨fun h' => h (Or.inr h'), fun h' => h (Or.inl h'), hv⟩
        · intro h
          by_cases hv : v = x ∨ v = y
          · rcases hv with rfl | rfl
            · exact hx
            · exact hyT
          · exact (h.2 hv).2.2
      rw [hmem, ← h1, ← h2]
      have e1 : Odd (degE ((J' \ P) ∪ (P \ J')) v) ↔ Odd (degE J' v + degE P v) := by
        rw [← hdeg, Nat.odd_add]
        simp
      rw [e1, Nat.odd_add, ← Nat.not_odd_iff_even]

end EG
