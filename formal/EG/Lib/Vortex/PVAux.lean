module

public import EG.Lib.Found.PathDecomp

/-!
# Small helpers for the PV run (manuscript s4:lemPV, proof)

Unit P3-s4.
* `EG.PVRun.exists_eight`: eight distinct elements of a set with at least eight elements,
  indexed by `Fin 4 × Fin 2` (step (i): "choose eight distinct edges `e^{c,i}_w ∈ C^j_w`
  (`c ∈ [4]`, `i ∈ [2]`), possible by (G4)").
* `EG.PVRun.exists_step_phase`: step (ii), "give the edge a phase
  `γ ∈ [4] \ {κ(x), ext(x), ext(w)}`; at most three of the four values are excluded".
* `EG.PVRun.isPathDecomp_append`, `EG.PVRun.isPathDecomp_biUnion`: path decompositions of
  pairwise disjoint edge sets concatenate.
-/

public section

namespace EG

namespace PVRun

variable {V : Type*}

/-- Eight distinct elements of a set with at least eight elements, indexed by `Fin 4 × Fin 2`. -/
theorem exists_eight {s : Finset V} (h : 8 ≤ s.card) :
    ∃ f : Fin 4 → Fin 2 → V, (∀ c i, f c i ∈ s) ∧
      ∀ c i c' i', f c i = f c' i' → c = c' ∧ i = i' := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h
  let g : Fin 8 → V := fun k => (t.equivFin.symm (Fin.cast htc.symm k)).1
  have hg : Function.Injective g := by
    intro a b hab
    have := Subtype.ext hab
    have := t.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  refine ⟨fun c i => g (finProdFinEquiv (c, i)), fun c i => hts ?_, fun c i c' i' h' => ?_⟩
  · exact (t.equivFin.symm _).2
  · have := finProdFinEquiv.injective (hg h')
    simp only [Prod.mk.injEq] at this
    exact this

/-- Three excluded values leave a phase. -/
theorem exists_phase_three (x y : Option (Fin 4)) (k : Fin 5) :
    ∃ c : Fin 4, x ≠ some c ∧ y ≠ some c ∧ k ≠ c.succ := by
  revert x y k
  decide

/-- [s4:lemPV] proof, step (ii): an edge meeting `W` has a phase `c` with `ext(y) ≠ c` at both
ends and `κ(y) ≠ c` at every end outside `W` (the phase avoids `κ(x)`, `ext(x)` and `ext(w)` for
the chosen end `w ∈ W` and the other end `x`). -/
theorem exists_step_phase (W : Finset V) (kap : V → Fin 5) (ext : V → Option (Fin 4))
    {e : Sym2 V} (he : ∃ w ∈ W, w ∈ e) :
    ∃ c : Fin 4, ∀ y ∈ e, ext y ≠ some c ∧ (y ∉ W → kap y ≠ c.succ) := by
  obtain ⟨w, hw, hwe⟩ := he
  induction e using Sym2.ind with
  | _ a b =>
    rcases Sym2.mem_iff.1 hwe with rfl | rfl
    · obtain ⟨c, h1, h2, h3⟩ := exists_phase_three (ext w) (ext b) (kap b)
      refine ⟨c, fun y hy => ?_⟩
      rcases Sym2.mem_iff.1 hy with rfl | rfl
      · exact ⟨h1, fun h => absurd hw h⟩
      · exact ⟨h2, fun _ => h3⟩
    · obtain ⟨c, h1, h2, h3⟩ := exists_phase_three (ext w) (ext a) (kap a)
      refine ⟨c, fun y hy => ?_⟩
      rcases Sym2.mem_iff.1 hy with rfl | rfl
      · exact ⟨h2, fun _ => h3⟩
      · exact ⟨h1, fun h => absurd hw h⟩

/-- Path decompositions of disjoint edge sets concatenate. -/
theorem isPathDecomp_append {F₁ F₂ : Set (Sym2 V)} {P₁ P₂ : List (List V)}
    (h₁ : IsPathDecomp F₁ P₁) (h₂ : IsPathDecomp F₂ P₂) (hd : Disjoint F₁ F₂) :
    IsPathDecomp (F₁ ∪ F₂) (P₁ ++ P₂) := by
  refine ⟨fun p hp => ?_, ?_, fun e => ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    exacts [h₁.1 p hp, h₂.1 p hp]
  · rw [List.flatMap_append, List.nodup_append]
    refine ⟨h₁.2.1, h₂.2.1, fun a ha b hb hab => ?_⟩
    subst hab
    exact Set.disjoint_left.1 hd (h₁.mem_iff.1 ha) (h₂.mem_iff.1 hb)
  · rw [List.flatMap_append, List.mem_append, h₁.mem_iff, h₂.mem_iff, Set.mem_union]

/-- Path decompositions of pairwise disjoint edge sets (indexed by a list) concatenate. -/
theorem isPathDecomp_flatMap {ι : Type*} {Fs : ι → Set (Sym2 V)} {Ps : ι → List (List V)} :
    ∀ {l : List ι}, (∀ i ∈ l, IsPathDecomp (Fs i) (Ps i)) →
      l.Pairwise (fun i j => Disjoint (Fs i) (Fs j)) →
      IsPathDecomp (⋃ i ∈ l, Fs i) (l.flatMap Ps)
  | [], _, _ => by simpa using (isPathDecomp_nil : IsPathDecomp (∅ : Set (Sym2 V)) [])
  | i :: l, h, hd => by
    rw [List.pairwise_cons] at hd
    have hl := isPathDecomp_flatMap (l := l) (fun j hj => h j (List.mem_cons_of_mem _ hj)) hd.2
    have hdisj : Disjoint (Fs i) (⋃ j ∈ l, Fs j) :=
      Set.disjoint_iUnion₂_right.2 fun j hj => hd.1 j hj
    rw [List.flatMap_cons]
    have := isPathDecomp_append (h i List.mem_cons_self) hl hdisj
    convert this using 1
    ext e
    simp

/-- Path decompositions of pairwise disjoint finite edge sets `Fs i` (`i ∈ s`) concatenate to a
path decomposition of `s.biUnion Fs`. -/
theorem isPathDecomp_biUnion [DecidableEq V] {ι : Type*} (s : Finset ι)
    {Fs : ι → Finset (Sym2 V)} {Ps : ι → List (List V)}
    (hd : (s : Set ι).PairwiseDisjoint Fs)
    (h : ∀ i ∈ s, IsPathDecomp (Fs i : Set (Sym2 V)) (Ps i)) :
    IsPathDecomp ((s.biUnion Fs : Finset (Sym2 V)) : Set (Sym2 V)) (s.toList.flatMap Ps) := by
  have hl := isPathDecomp_flatMap (l := s.toList) (Fs := fun i => (Fs i : Set (Sym2 V)))
    (Ps := Ps) (fun i hi => h i (Finset.mem_toList.1 hi))
    (s.nodup_toList.pairwise_of_forall_ne fun i hi j hj hij =>
      Finset.disjoint_coe.2 (hd (Finset.mem_coe.2 (Finset.mem_toList.1 hi))
        (Finset.mem_coe.2 (Finset.mem_toList.1 hj)) hij))
  convert hl using 1
  ext e
  simp

end PVRun

end EG
