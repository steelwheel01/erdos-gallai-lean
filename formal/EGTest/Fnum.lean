import EG.Lib.Found.Fnum
import EG.Lib.Found.FGraphFnum
import EG.Lib.Found.FnumMain

/-!
Unit tests for `EG.fnum` / `EG.fmax` (plan §8 Q1: definition unit tests for [s1:defObject]):
f(∅) = 0, f(single edge) = 1, f(K₃) = 1, f(star with k edges) = k for every k,
f(two disjoint triangles) = 2, f(K₄) = 3 (a value strictly between the trivial bounds, where
cycles exist but cannot all be used), the loop convention, f(2) = 1, iterated unions of
decompositions (s6:lemHCCglob), the `FGraph` lemmas, counting single edges (`Obj.isEdge`), and
the link between `fmax` and the internal main theorem (`EG.Lib.Found.FnumMain`).
-/

namespace EGTest.Fnum

open EG

/-! ### f(∅) = 0 -/

example : fnum (∅ : Finset (Sym2 ℕ)) = 0 := fnum_empty

/-- f(∅) = 0 straight from the definition (the empty list decomposes the empty set). -/
example : fnum (∅ : Finset (Sym2 ℕ)) = 0 := by
  unfold fnum
  apply Nat.sInf_eq_zero.2
  left
  exact ⟨[], by simpa using (isDecomp_nil : IsDecomp (∅ : Set (Sym2 ℕ)) []), rfl⟩

example : fnum (⊥ : SimpleGraph (Fin 5)).edgeFinset = 0 := by simp

/-! ### A single edge -/

example : fnum ({s(0, 1)} : Finset (Sym2 ℕ)) = 1 := fnum_singleton (by simp)

/-- K₂ as a `SimpleGraph`. -/
example : fnum (⊤ : SimpleGraph (Fin 2)).edgeFinset = 1 := by
  have : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  rw [this]
  exact fnum_singleton (by decide)

/-! ### K₃ -/

theorem fnum_K3 : fnum ({s(0, 1), s(1, 2), s(2, 0)} : Finset (Sym2 ℕ)) = 1 := by
  have : ({s(0, 1), s(1, 2), s(2, 0)} : Finset (Sym2 ℕ)) = (cycleEdges [0, 1, 2]).toFinset := by
    decide
  rw [this]
  exact fnum_cycleEdges (by decide) (by decide)

/-- K₃ as a `SimpleGraph`. -/
example : fnum (⊤ : SimpleGraph (Fin 3)).edgeFinset = 1 := by
  have : (⊤ : SimpleGraph (Fin 3)).edgeFinset = (cycleEdges [0, 1, 2]).toFinset := by decide
  rw [this]
  exact fnum_cycleEdges (by decide) (by decide)

/-- The triangle is not the sum of its edges: its optimal decomposition has one object. -/
example : ∃ D : List (Obj ℕ), IsDecomp ({s(0, 1), s(1, 2), s(2, 0)} : Set (Sym2 ℕ)) D ∧
    D.length = 1 := by
  refine ⟨[Obj.cycle [0, 1, 2]], ?_, rfl⟩
  refine ⟨fun o ho => ?_, by decide, fun e => ?_⟩
  · simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨by decide, by decide⟩
  · simp [cycleEdges]

/-! ### Stars -/

theorem star_injective : Function.Injective fun i : ℕ => s(0, i + 1) :=
  fun i j h => by simpa using h

/-- The star with centre `0` and leaves `1, …, k`. -/
def star (k : ℕ) : Finset (Sym2 ℕ) :=
  (Finset.range k).map ⟨fun i => s(0, i + 1), star_injective⟩

theorem card_star (k : ℕ) : (star k).card = k := by simp [star]

/-- f(star with k edges) = k, for every k. -/
theorem fnum_star (k : ℕ) : fnum (star k) = k := by
  rw [fnum_eq_card_of_forall_mem (v₀ := 0), card_star]
  · intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 he
    simp
  · intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 he
    simp

example : fnum (star 3) = 3 := fnum_star 3

example : fnum ({s(0, 1), s(0, 2), s(0, 3)} : Finset (Sym2 ℕ)) = 3 := by
  have : ({s(0, 1), s(0, 2), s(0, 3)} : Finset (Sym2 ℕ)) = star 3 := by decide
  rw [this, fnum_star]

/-! ### Two disjoint triangles -/

theorem fnum_K3' : fnum ({s(3, 4), s(4, 5), s(5, 3)} : Finset (Sym2 ℕ)) = 1 := by
  have : ({s(3, 4), s(4, 5), s(5, 3)} : Finset (Sym2 ℕ)) = (cycleEdges [3, 4, 5]).toFinset := by
    decide
  rw [this]
  exact fnum_cycleEdges (by decide) (by decide)

/-- f(two vertex-disjoint triangles) = 2 (by [s1:factAdd](c)). -/
example : fnum ({s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3)} : Finset (Sym2 ℕ)) = 2 := by
  have : ({s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3)} : Finset (Sym2 ℕ)) =
      {s(0, 1), s(1, 2), s(2, 0)} ∪ {s(3, 4), s(4, 5), s(5, 3)} := by decide
  rw [this, fnum_union_eq_of_vertexDisjoint, fnum_K3, fnum_K3']
  intro e₁ h₁ e₂ h₂ v hv₁ hv₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    simp only [Sym2.mem_iff] at hv₁ hv₂ <;> omega

/-! ### K₄: cycles are available but cannot be used optimally -/

/-- Two triangles in K₄ always share an edge. -/
theorem two_triangles_K4 (a b c a' b' c' : Fin 4) (h : [a, b, c].Nodup) (h' : [a', b', c'].Nodup) :
    ¬ (cycleEdges [a, b, c] ++ cycleEdges [a', b', c']).Nodup := by
  revert a b c a' b' c'
  decide

/-- A well-formed object on `Fin 4` has 1 edge, is a triangle, or has 4 edges. -/
theorem obj_cases_fin4 (o : Obj (Fin 4)) (ho : o.WF) :
    o.edges.length = 1 ∨ (∃ a b c, o = Obj.cycle [a, b, c] ∧ [a, b, c].Nodup) ∨
      o.edges.length = 4 := by
  cases o with
  | edge e => left; rfl
  | cycle c =>
    obtain ⟨hn, h3⟩ := ho
    have h4 : c.length ≤ 4 := by simpa using hn.length_le_card
    rcases Nat.eq_or_lt_of_le h3 with h | h
    · right; left
      match c, h with
      | [a, b, d], _ => exact ⟨a, b, d, rfl, hn⟩
    · right; right; simp; omega

/-- f(K₄) = 3: the 4-cycle 0123 and the two diagonals; two objects would have to be two
edge-disjoint triangles, which do not exist in K₄. -/
theorem fnum_K4 : fnum (⊤ : SimpleGraph (Fin 4)).edgeFinset = 3 := by
  have hF : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by decide
  refine le_antisymm ?_ ?_
  · rw [fnum_edgeFinset_le_iff]
    refine ⟨[Obj.cycle [0, 1, 2, 3], Obj.edge s(0, 2), Obj.edge s(1, 3)], ?_, by simp⟩
    refine ⟨?_, by decide, fun e => ?_⟩
    · intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · show ¬ _; decide
      · show ¬ _; decide
    · induction e using Sym2.ind with
      | h x y =>
        simp only [SimpleGraph.top_adj, SimpleGraph.mem_edgeSet]
        revert x y; decide
  · rw [le_fnum_iff (loopless_edgeFinset _)]
    intro D hD
    by_contra hlt
    push Not at hlt
    have htot := hD.length_flatMap
    rw [hF] at htot
    match D, hlt with
    | [], _ => simp at htot
    | [o], _ =>
      have h4 : o.edges.length ≤ 4 := by
        rcases obj_cases_fin4 o (hD.wf o (by simp)) with h | ⟨a, b, c, rfl, -⟩ | h
        · omega
        · simp
        · omega
      simp at htot; omega
    | [o₁, o₂], _ =>
      have hnd := hD.nodup
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htot hnd
      rw [List.length_append] at htot
      rcases obj_cases_fin4 o₁ (hD.wf o₁ (by simp)) with h1 | ⟨a, b, c, rfl, hn⟩ | h1 <;>
        rcases obj_cases_fin4 o₂ (hD.wf o₂ (by simp)) with h2 | ⟨a', b', c', rfl, hn'⟩ | h2
      all_goals first
        | omega
        | exact two_triangles_K4 _ _ _ _ _ _ hn hn' hnd
        | (simp at htot; omega)

/-! ### Loops are ignored (convention of `EG/Defs/Fnum.lean`) -/

example : fnum ({s(0, 0)} : Finset (Sym2 ℕ)) = 0 := fnum_eq_zero_iff.2 (by simp)

example : fnum ({s(0, 0), s(0, 1)} : Finset (Sym2 ℕ)) = 1 := by
  rw [← fnum_filter_not_isDiag]
  have : (({s(0, 0), s(0, 1)} : Finset (Sym2 ℕ)).filter fun e => ¬ e.IsDiag) = {s(0, 1)} := by
    decide
  rw [this]
  exact fnum_singleton (by simp)

/-- A set containing a loop has no decomposition at all. -/
example (D : List (Obj ℕ)) : ¬ IsDecomp ({s(0, 0)} : Set (Sym2 ℕ)) D :=
  fun h => h.not_isDiag (Set.mem_singleton _) (by simp)

/-- The caveat for statement authors: for a raw edge set with a loop, `fnum F ≤ k` does not say
that `F` decomposes (here `k = 0`). Statements about raw `F` need `∀ e ∈ F, ¬ e.IsDiag` (then
`fnum_le_iff` applies), or `F = H.edges` for an `FGraph` `H`. -/
example : fnum ({s(0, 0)} : Finset (Sym2 ℕ)) ≤ 0 ∧
    ¬ ∃ D : List (Obj ℕ), IsDecomp (({s(0, 0)} : Finset (Sym2 ℕ)) : Set (Sym2 ℕ)) D :=
  ⟨(fnum_eq_zero_iff.2 (by simp)).le,
    fun ⟨_, h⟩ => h.not_isDiag (Finset.mem_coe.2 (Finset.mem_singleton_self _)) (by simp)⟩

/-! ### f(n) -/

example : fmax 2 = 1 := by
  apply le_antisymm
  · obtain ⟨H, hH⟩ := exists_fnum_eq_fmax 2
    classical
    rw [← hH]
    refine (fnum_le_card _).trans ?_
    have := H.card_edgeFinset_le_card_choose_two
    simpa using this
  · have := fnum_le_fmax (⊤ : SimpleGraph (Fin 2)) (Fintype.card_fin 2)
    have h1 : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
    rw [h1, fnum_singleton (by decide)] at this
    exact this

/-! ### Iterated unions of decompositions (s6:lemHCCglob) -/

/-- The two triangles, as a family indexed by `Fin 2`. -/
def triangles : Fin 2 → Set (Sym2 ℕ)
  | 0 => {e | e ∈ cycleEdges [0, 1, 2]}
  | 1 => {e | e ∈ cycleEdges [3, 4, 5]}

/-- Their decompositions, one cycle each. -/
def triangleDecomps : Fin 2 → List (Obj ℕ)
  | 0 => [Obj.cycle [0, 1, 2]]
  | 1 => [Obj.cycle [3, 4, 5]]

/-- The union of the two triangles decomposes into `1 + 1` objects. -/
example : ∃ D : List (Obj ℕ), IsDecomp (⋃ i ∈ (Finset.univ : Finset (Fin 2)), triangles i) D ∧
    D.length = 2 := by
  refine (exists_isDecomp_biUnion (Ds := triangleDecomps) Finset.univ ?_ ?_).imp
    fun D hD => ⟨hD.1, by rw [hD.2]; rfl⟩
  · intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, Set.disjoint_left]
      simp only [triangles, Set.mem_ofPred_eq]
      intro e h₁ h₂
      simp only [cycleEdges] at h₁ h₂
      revert e; decide
    · rw [Function.onFun, Set.disjoint_left]
      simp only [triangles, Set.mem_ofPred_eq]
      intro e h₁ h₂
      simp only [cycleEdges] at h₁ h₂
      revert e; decide
    · exact absurd rfl hij
  · intro i _
    fin_cases i
    · exact isDecomp_cycle (by decide) (by decide)
    · exact isDecomp_cycle (by decide) (by decide)

/-! ### `FGraph` lemmas -/

/-- The triangle `012` together with an isolated vertex `3`. -/
def triPlus : FGraph ℕ := FGraph.ofEdges {0, 1, 2, 3} {s(0, 1), s(1, 2), s(2, 0)}

theorem triPlus_edges : triPlus.edges = {s(0, 1), s(1, 2), s(2, 0)} := by decide

example : fnum triPlus.edges = 1 := by rw [triPlus_edges]; exact fnum_K3

/-- Deleting the isolated vertex `3` (s7:thmHI step (1)). -/
example : fnum (triPlus.deleteVerts {3}).edges = fnum triPlus.edges ∧
    (triPlus.deleteVerts {3}).card = triPlus.card - 1 :=
  ⟨triPlus.fnum_edges_deleteVerts_singleton_of_deg_eq_zero (by decide),
    triPlus.card_deleteVerts_singleton (by decide)⟩

/-- f(H) ≤ f(|H|) for an `FGraph`: here `1 ≤ f(4)`. -/
example : 1 ≤ fmax 4 := by
  have h := triPlus.fnum_edges_le_fmax
  rw [triPlus_edges, fnum_K3] at h
  have hc : triPlus.card = 4 := by decide
  rwa [hc] at h

/-- The optimal decomposition of `E(triPlus)` has one object. -/
example : ∃ D : List (Obj ℕ), IsDecomp (triPlus.edges : Set (Sym2 ℕ)) D ∧ D.length ≤ 1 := by
  rw [← triPlus.fnum_edges_le_iff, triPlus_edges, fnum_K3]

/-! ### Counting single edges (`Obj.isEdge`) -/

/-- The optimal decomposition of K₄ above (a 4-cycle and two diagonals) has two single edges. -/
example : ([Obj.cycle [0, 1, 2, 3], Obj.edge s(0, 2), Obj.edge s(1, 3)] : List (Obj (Fin 4))).countP
    Obj.isEdge = 2 := rfl

/-- The decomposition of the star into its edges consists of `k` single edges. -/
example (k : ℕ) : ((star k).toList.map Obj.edge).countP Obj.isEdge = k := by
  rw [countP_isEdge_singletons, card_star]

/-- Relabelling keeps the number of single edges. -/
example : (([Obj.cycle [0, 1, 2], Obj.edge s(0, 3)] : List (Obj ℕ)).map
    (Obj.map fun v => v + 10)).countP Obj.isEdge = 1 := by
  rw [countP_isEdge_map]; rfl

/-- The union of the two triangles decomposes into `2` objects, none of them a single edge. -/
example : ∃ D : List (Obj ℕ), IsDecomp (⋃ i ∈ (Finset.univ : Finset (Fin 2)), triangles i) D ∧
    D.length = 2 ∧ D.countP Obj.isEdge = 0 := by
  refine (exists_isDecomp_biUnion_countP (Ds := triangleDecomps) Finset.univ ?_ ?_).imp
    fun D hD => ⟨hD.1, by rw [hD.2.1]; rfl, by rw [hD.2.2]; rfl⟩
  · intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, Set.disjoint_left]
      simp only [triangles, Set.mem_ofPred_eq]
      intro e h₁ h₂
      simp only [cycleEdges] at h₁ h₂
      revert e; decide
    · rw [Function.onFun, Set.disjoint_left]
      simp only [triangles, Set.mem_ofPred_eq]
      intro e h₁ h₂
      simp only [cycleEdges] at h₁ h₂
      revert e; decide
    · exact absurd rfl hij
  · intro i _
    fin_cases i
    · exact isDecomp_cycle (by decide) (by decide)
    · exact isDecomp_cycle (by decide) (by decide)

/-! ### `fmax` and the internal main theorem -/

/-- The trivial bound `f(n) ≤ n²` holds unconditionally; the internal main theorem is the linear
bound (`mainInternal_iff_fmax`). -/
theorem fmax_le_sq (n : ℕ) : fmax n ≤ n * n := by
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax n
  rw [← hH]
  refine (fnum_le_card _).trans (H.card_edgeFinset_le_card_choose_two.trans ?_)
  rw [Fintype.card_fin, Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- Under the internal main theorem, every `FGraph` (in any universe) has `f(H) ≤ c |H|`; applied
to `triPlus` (4 vertices, f = 1). -/
example (h : EG.Spec.MainInternal) : ∃ c : ℕ, 1 ≤ c * 4 := by
  obtain ⟨c, hc⟩ := fnum_edges_le_of_mainInternal.{0} h
  refine ⟨c, ?_⟩
  have := hc ℕ triPlus
  rwa [triPlus_edges, fnum_K3, show triPlus.card = 4 by decide] at this

/-- The two forms of the internal main theorem agree. -/
example : (∃ c : ℕ, ∀ n, fmax n ≤ c * n) ↔
    ∃ c : ℕ, ∀ (V : Type) (H : FGraph V), fnum H.edges ≤ c * H.card :=
  mainInternal_iff_fmax.symm.trans mainInternal_iff_fnum_edges

end EGTest.Fnum
