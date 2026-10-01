import EG.Proof.Chain.Gate

/-! Unit tests for `EG.Defs.Orient` and a sanity instance of Lemma GATE (`EG.gate`,
[s6:lemGATE]): the cyclically oriented triangle with `𝒲` one arc. Also non-vacuity of the
hypotheses and negative tests of the definitions. -/

namespace EGTest

open EG

/-! ## Definitions -/

example : cycleArcs [0, 1, 2] = [((0 : ℕ), 1), (1, 2), (2, 0)] := by decide
example : cycleArcs [(5 : ℕ)] = [(5, 5)] := by decide

/-! ## The cyclically oriented triangle on `Fin 3` -/

/-- The triangle `K₃` on `Fin 3`. -/
def K3 : FGraph (Fin 3) := FGraph.ofEdges Finset.univ {s(0, 1), s(1, 2), s(2, 0)}

/-- Its edge set `F = E(K₃)`. -/
def F3 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(1, 2), s(2, 0)}

/-- The cyclic orientation `0 → 1 → 2 → 0`. -/
def A3 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 2), (2, 0)}

/-- `𝒲`: the single arc `0 → 1`. -/
def W3 : Finset (Fin 3 × Fin 3) := {(0, 1)}

theorem F3_sub : F3 ⊆ K3.edges := by decide

theorem A3_orientation : IsOrientation F3 A3 := by
  refine ⟨by decide, by decide, ?_⟩
  intro e he
  simp only [F3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · refine ⟨(0, 1), ⟨by decide, rfl⟩, ?_⟩
    rintro a ⟨ha, hae⟩
    revert a; decide
  · refine ⟨(1, 2), ⟨by decide, rfl⟩, ?_⟩
    rintro a ⟨ha, hae⟩
    revert a; decide
  · refine ⟨(2, 0), ⟨by decide, rfl⟩, ?_⟩
    rintro a ⟨ha, hae⟩
    revert a; decide

theorem A3_balanced : IsBalanced A3 := by
  unfold IsBalanced outDeg inDeg; decide

theorem W3_sub : W3 ⊆ A3 := by decide

/-- A potential increasing along the two arcs `1 → 2 → 0` of `A₃ - 𝒲`. -/
def pot3 (i : Fin 3) : ℕ := (i.val + 2) % 3

theorem A3_sdiff_W3_acyclic : IsAcyclic (A3 \ W3) :=
  isAcyclic_of_potential pot3 (by decide)

/-- The full cyclic triangle is not acyclic: `0 1 2` is a directed cycle. -/
theorem A3_not_acyclic : ¬ IsAcyclic A3 := fun h => h [0, 1, 2] (by decide)

/-- The acyclicity hypothesis of GATE has teeth: it fails on the triangle for `𝒲 = ∅`. -/
example : ¬ IsAcyclic (A3 \ ∅) := by simpa using A3_not_acyclic

/-- GATE on the triangle: `F₃` decomposes into at most `|𝒲| = 1` cycles of `K₃`, and (since
`F₃ ≠ ∅`) into exactly one. -/
example : ∃ D : List (Obj (Fin 3)), IsDecomp (F3 : Set (Sym2 (Fin 3))) D ∧ D.length = 1 ∧
    ∀ o ∈ D, (∃ c, o = Obj.cycle c) ∧ ∀ e ∈ o.edges, e ∈ K3.edges := by
  obtain ⟨D, hD, hlen, hcyc⟩ :=
    gate (Fin 3) K3 F3 A3 W3 F3_sub A3_orientation A3_balanced W3_sub A3_sdiff_W3_acyclic
  refine ⟨D, hD, ?_, hcyc⟩
  have h1 : W3.card = 1 := by decide
  have hne : D ≠ [] := by
    rintro rfl
    have := (hD.2.2 s(0, 1)).2 (by simp [F3])
    simp at this
  have : 0 < D.length := List.length_pos_iff.2 hne
  omega

/-- The precise form on the triangle. -/
example : ∃ cs : List (List (Fin 3)), cs.length ≤ 1 ∧
    ∀ a, a ∈ cs.flatMap cycleArcs ↔ a ∈ A3 := by
  obtain ⟨cs, -, -, hmem, hlen⟩ :=
    gate_precise (Fin 3) K3 F3 A3 W3 F3_sub A3_orientation A3_balanced W3_sub A3_sdiff_W3_acyclic
  exact ⟨cs, by simpa [W3] using hlen, hmem⟩

/-- The combined form: the decomposition together with the directed cycles behind it. -/
example : ∃ cs : List (List (Fin 3)), IsDecomp (F3 : Set (Sym2 (Fin 3))) (cs.map Obj.cycle) ∧
    cs.length ≤ 1 ∧ ∀ c ∈ cs, IsDirCycle A3 c ∧ ∃ w ∈ W3, w ∈ cycleArcs c := by
  obtain ⟨cs, hD, hlen, hcs⟩ :=
    gate_with_cycles K3 F3 A3 W3 F3_sub A3_orientation A3_balanced W3_sub A3_sdiff_W3_acyclic
  exact ⟨cs, hD, by simpa [W3] using hlen, fun c hc => ⟨(hcs c hc).1, (hcs c hc).2.2.2⟩⟩

/-! ## Directed paths, sources, potentials, building orientations -/

example : walkArcs [0, 1, 2] = [((0 : ℕ), 1), (1, 2)] := by decide
example : IsDirPathIn A3 [0, 1, 2] := by decide
example : IsDirPathIn A3 [2] := by decide
/-- The arc `0 → 2` is not in `A₃` (only `2 → 0` is). -/
example : ¬ IsDirPathIn A3 [0, 2] := by decide
/-- A repeated vertex is not a directed path. -/
example : ¬ IsDirPathIn A3 [0, 1, 2, 0] := by decide

/-- `A₃ - 𝒲 = {1 → 2, 2 → 0}` has a source (namely `1`). -/
example : ∃ v, inDeg (A3 \ W3) v = 0 ∧ 0 < outDeg (A3 \ W3) v :=
  A3_sdiff_W3_acyclic.exists_source (by decide)

/-- `A₃ - 𝒲` has a numbering `Fin 3 → {1, 2, 3}` increasing along its arcs. -/
example : ∃ f : Fin 3 → ℕ, Set.InjOn f (Finset.univ : Finset (Fin 3)) ∧
    (∀ v ∈ (Finset.univ : Finset (Fin 3)), 1 ≤ f v ∧ f v ≤ 3) ∧ ∀ a ∈ A3 \ W3, f a.1 < f a.2 :=
  A3_sdiff_W3_acyclic.exists_potential Finset.univ (by simp)

/-- A digraph with a directed cycle has no potential. -/
example : ¬ ∃ f : Fin 3 → ℕ, ∀ a ∈ A3, f a.1 < f a.2 :=
  fun h => A3_not_acyclic (isAcyclic_iff_exists_potential.2 h)

/-- The two triangles `0 1 2` and `0 3 4` of the bowtie on `Fin 5`, cyclically oriented, as a union
of orientations of disjoint edge sets (built with `IsOrientation.of_subset_edges`, which supplies
looplessness from the simplicity of `G`). -/
def Bow : FGraph (Fin 5) :=
  FGraph.ofEdges Finset.univ {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 0)}

theorem bow_orient₁ : IsOrientation ({s(0, 1), s(1, 2), s(2, 0)} : Finset (Sym2 (Fin 5)))
    {(0, 1), (1, 2), (2, 0)} := by
  refine IsOrientation.of_subset_edges (G := Bow) (by decide) (by decide) ?_
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨(0, 1), ⟨by decide, rfl⟩, by rintro a ⟨ha, hae⟩; revert a; decide⟩
  · exact ⟨(1, 2), ⟨by decide, rfl⟩, by rintro a ⟨ha, hae⟩; revert a; decide⟩
  · exact ⟨(2, 0), ⟨by decide, rfl⟩, by rintro a ⟨ha, hae⟩; revert a; decide⟩

theorem bow_orient₂ : IsOrientation ({s(0, 3), s(3, 4), s(4, 0)} : Finset (Sym2 (Fin 5)))
    {(0, 3), (3, 4), (4, 0)} := by
  refine IsOrientation.of_subset_edges (G := Bow) (by decide) (by decide) ?_
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨(0, 3), ⟨by decide, rfl⟩, by rintro a ⟨ha, hae⟩; revert a; decide⟩
  · exact ⟨(3, 4), ⟨by decide, rfl⟩, by rintro a ⟨ha, hae⟩; revert a; decide⟩
  · exact ⟨(4, 0), ⟨by decide, rfl⟩, by rintro a ⟨ha, hae⟩; revert a; decide⟩

/-- GATE on the bowtie with `𝒲 = {0 → 1, 0 → 3}`: at most two cycles. -/
example : ∃ D : List (Obj (Fin 5)),
    IsDecomp (({s(0, 1), s(1, 2), s(2, 0)} ∪ {s(0, 3), s(3, 4), s(4, 0)} :
      Finset (Sym2 (Fin 5))) : Set (Sym2 (Fin 5))) D ∧ D.length ≤ 2 := by
  have hA := bow_orient₁.union bow_orient₂ (by decide)
  have hbal : IsBalanced (({(0, 1), (1, 2), (2, 0)} : Finset (Fin 5 × Fin 5)) ∪
      {(0, 3), (3, 4), (4, 0)}) := by
    unfold IsBalanced outDeg inDeg; decide
  have hacyc : IsAcyclic ((({(0, 1), (1, 2), (2, 0)} : Finset (Fin 5 × Fin 5)) ∪
      {(0, 3), (3, 4), (4, 0)}) \ {(0, 1), (0, 3)}) :=
    isAcyclic_of_potential (fun i : Fin 5 => ((i.val + 4) % 5 : ℕ)) (by decide)
  obtain ⟨D, hD, hlen, -⟩ := gate (Fin 5) Bow _ _ _ (by decide) hA hbal (by decide) hacyc
  exact ⟨D, hD, by simpa using hlen⟩

/-! ## Helpers for MED and HCC-P (fix round 2) -/

/-- The warning of the `IsDirPathIn` docstring: `[v]` is a directed path of every arc set. -/
example : IsDirPathIn (∅ : Finset (Fin 3 × Fin 3)) [2] := by decide

/-- `arcVerts` unfolds downstream (it is exposed) and has a membership lemma. -/
example : arcVerts A3 = Finset.univ := by decide
example : (2 : Fin 3) ∈ arcVerts A3 := by
  rw [mem_arcVerts]
  exact ⟨(1, 2), by decide, Or.inr rfl⟩

/-- `d⁺ + d⁻ = deg_F` on the triangle. -/
example : outDeg A3 0 + inDeg A3 0 = 2 := by
  rw [A3_orientation.outDeg_add_inDeg]
  decide

/-- The orientation of the path `0 1 2` from its first to its last vertex. -/
example : IsOrientation ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) {(0, 1), (1, 2)} := by
  have h := isOrientation_walkArcs (p := [(0 : Fin 3), 1, 2]) (by decide)
  have h1 : (walkEdges [(0 : Fin 3), 1, 2]).toFinset = {s(0, 1), s(1, 2)} := by decide
  have h2 : (walkArcs [(0 : Fin 3), 1, 2]).toFinset = {(0, 1), (1, 2)} := by decide
  rwa [h1, h2] at h

/-- A directed path of an orientation is a path of the oriented edge set. -/
example : IsPathIn F3 [0, 1, 2] := IsDirPathIn.isPathIn (by decide) A3_orientation.mem

/-- The directed triangle started at the head `1` of the `𝒲`-arc `0 → 1`: the directed path
`1 2 0` followed by the arc `0 → 1`. -/
example : ∃ n t, [(0 : Fin 3), 1, 2].rotate n = 1 :: t ∧
    (1 :: t).getLast (List.cons_ne_nil _ _) = 0 ∧ IsDirPathIn A3 (1 :: t) := by
  obtain ⟨n, t, h1, h2, -, h4⟩ :=
    IsDirCycle.exists_rotate_eq_cons_of_mem (A := A3) (c := [0, 1, 2]) (by decide)
      (a := (0, 1)) (by decide)
  exact ⟨n, t, h1, h2, h4⟩

/-- Cancellation on the directed triangle has to delete a cycle. -/
example : ∃ cs : List (List (Fin 3)), cs ≠ [] ∧ (∀ c ∈ cs, IsDirCycle A3 c) ∧
    IsAcyclic (A3 \ (cs.flatMap cycleArcs).toFinset) := by
  obtain ⟨cs, hcs, -, hac⟩ := exists_cancel_dirCycles A3
  refine ⟨cs, ?_, hcs, hac⟩
  rintro rfl
  exact A3_not_acyclic (by simpa using hac)

/-! ## Negative tests -/

/-- Two antiparallel arcs are not an orientation of the single edge `01` (each edge receives
exactly one direction). -/
example : ¬ IsOrientation ({s(0, 1)} : Finset (Sym2 (Fin 3))) {(0, 1), (1, 0)} := by
  intro h
  exact h.not_mem_swap (u := 0) (v := 1) (by decide) (by decide)

/-- A loop is not an orientation of anything. -/
example (F : Finset (Sym2 (Fin 3))) : ¬ IsOrientation F {(0, 0)} :=
  fun h => h.loopless (0, 0) (by decide) rfl

/-- An arc set must orient every edge of `F`. -/
example : ¬ IsOrientation F3 {(0, 1), (1, 2)} := by
  intro h
  obtain ⟨a, ⟨ha, hae⟩, -⟩ := h.existsUnique s(2, 0) (by decide)
  revert a; decide

/-- A directed path is not balanced. -/
example : ¬ IsBalanced ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)) := by
  unfold IsBalanced outDeg inDeg; decide

/-- A repeated vertex is not a directed cycle. -/
example : ¬ IsDirCycle A3 [0, 1, 2, 0, 1, 2] := by decide

end EGTest
