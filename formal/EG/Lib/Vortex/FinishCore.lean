module

public import EG.Lib.Vortex.Finish

/-!
# The PV finish, deterministic core (manuscript s4:lemPV, proof, "Finish"; CR1-PV)

Unit P4A, stage 3. Given the decomposition `D₁` of `E_1` (Fact EG0(b)), a phase map `ph` avoiding
the external phases of both ends, and Corollary-22 decompositions `Pc c` of the phase classes
`E_{2,c}`, stripping (`EG.strip_exists`) gives the objects and arcs of the finish
(`EG.PVFin.finish_core`).
-/

public section

namespace EG

namespace PVFin

open List

variable {V : Type*} [DecidableEq V]

section Defs

variable (PlJ : Finset V) (HJ : Finset (Sym2 V)) (ph : Sym2 V → Fin 4)

/-- `E_1`: the edges of `H_J` with both ends in `Pl_J`. -/
@[expose] def E1 : Finset (Sym2 V) := HJ.filter (· ∈ PlJ.sym2)

/-- `E_2 = H_J \ E_1`. -/
@[expose] def E2 : Finset (Sym2 V) := HJ.filter (· ∉ PlJ.sym2)

/-- `E_{2,c}`: the edges of `E_2` of phase `c`. -/
@[expose] def E2c (c : Fin 4) : Finset (Sym2 V) := (E2 PlJ HJ).filter (ph · = c)

end Defs

theorem mem_E1 {PlJ : Finset V} {HJ : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ E1 PlJ HJ ↔ e ∈ HJ ∧ ∀ v ∈ e, v ∈ PlJ := by
  simp [E1, Finset.mem_sym2_iff]

theorem mem_E2 {PlJ : Finset V} {HJ : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ E2 PlJ HJ ↔ e ∈ HJ ∧ ¬ ∀ v ∈ e, v ∈ PlJ := by
  simp [E2, Finset.mem_sym2_iff]

theorem mem_E2c {PlJ : Finset V} {HJ : Finset (Sym2 V)} {ph : Sym2 V → Fin 4} {c : Fin 4}
    {e : Sym2 V} : e ∈ E2c PlJ HJ ph c ↔ e ∈ E2 PlJ HJ ∧ ph e = c := by
  simp [E2c]

section Core

variable {Rt PlJ : Finset V} {HJ : Finset (Sym2 V)} {ext : V → Option (Fin 4)}
  {ph : Sym2 V → Fin 4} {Pc : Fin 4 → List (List V)} {D1 : List (Obj V)}

/-- The edges of all phase classes. -/
theorem allE_props (hPc : ∀ c, IsPathDecomp ((E2c PlJ HJ ph c : Finset (Sym2 V)) : Set (Sym2 V))
      (Pc c)) :
    ((List.finRange 4).flatMap (fun c => (Pc c).flatMap walkEdges)).Nodup ∧
      ∀ e, e ∈ (List.finRange 4).flatMap (fun c => (Pc c).flatMap walkEdges) ↔
        e ∈ E2 PlJ HJ := by
  refine ⟨?_, fun e => ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun c _ => (hPc c).2.1, (List.nodup_finRange 4).pairwise_of_forall_ne ?_⟩
    intro c _ c' _ hne e he he'
    have h1 := mem_E2c.1 ((hPc c).mem_iff.1 he)
    have h2 := mem_E2c.1 ((hPc c').mem_iff.1 he')
    exact hne (h1.2.symm.trans h2.2)
  · rw [List.mem_flatMap]
    constructor
    · rintro ⟨c, _, he⟩
      exact (mem_E2c.1 ((hPc c).mem_iff.1 he)).1
    · intro he
      exact ⟨ph e, List.mem_finRange _, (hPc (ph e)).mem_iff.2 (mem_E2c.2 ⟨he, rfl⟩)⟩

theorem flatMap_filter_eq {α β : Type*} (l : List α) (p : α → Bool) (f : α → List β)
    (h : ∀ x ∈ l, p x = false → f x = []) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx : p x = true
    · simp [hx, ih']
    · have : f x = [] := h x (List.mem_cons_self ..) (by simpa using hx)
      simp [hx, ih', this]

omit [DecidableEq V] in
theorem flatMap_map_edge (l : List (Sym2 V)) : (l.map Obj.edge).flatMap Obj.edges = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [Obj.edges, ih]

omit [DecidableEq V] in
theorem walkEdges_eq_nil_of_length_le_one {T : List V} (h : T.length ≤ 1) : walkEdges T = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [length_walkEdges, pathLength]
  omega

/-- [s4:lemPV] (proof, "Finish"; CR1-PV), the deterministic core. -/
theorem finish_core (hdis : Disjoint Rt PlJ) (hloop : ∀ e ∈ HJ, ¬ e.IsDiag)
    (hends : ∀ e ∈ HJ, ∀ v ∈ e, v ∈ Rt ∪ PlJ) (hph : ∀ e, ∀ v ∈ e, ext v ≠ some (ph e))
    (hPc : ∀ c, IsPathDecomp ((E2c PlJ HJ ph c : Finset (Sym2 V)) : Set (Sym2 V)) (Pc c))
    (hPc2 : ∀ c v, pathEndCount (Pc c) v ≤ 2)
    (hD1 : IsDecomp ((E1 PlJ HJ : Finset (Sym2 V)) : Set (Sym2 V)) D1) :
    ∃ (Hobj : Finset (Sym2 V)) (D : List (Obj V)) (arcs : List (List V × Fin 4)),
      Hobj ⊆ HJ ∧ IsDecomp (Hobj : Set (Sym2 V)) D ∧
      D.length ≤ D1.length + 8 * PlJ.card ∧
      IsPathDecomp ((HJ \ Hobj : Finset (Sym2 V)) : Set (Sym2 V)) (arcs.map Prod.fst) ∧
      (∀ a ∈ arcs, (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ Rt) ∧
        ∀ x ∈ a.1, ext x ≠ some a.2) ∧
      arcs.length ≤ 4 * (Rt ∪ PlJ).card ∧
      (PlJ = ∅ → Hobj = ∅) := by
  -- the paths of the phase classes
  have hT : ∀ c, ∀ T ∈ Pc c, T.Nodup ∧ 2 ≤ T.length ∧ (∀ x ∈ T, x ∈ Rt ∪ PlJ) ∧
      (∀ e ∈ walkEdges T, ∃ x ∈ Rt, x ∈ e) ∧ (∀ e ∈ walkEdges T, e ∈ E2c PlJ HJ ph c) := by
    intro c T hTc
    have hE : ∀ e ∈ walkEdges T, e ∈ E2c PlJ HJ ph c := fun e he => (hPc c).edges_mem hTc he
    refine ⟨(hPc c).nodup hTc, (hPc c).two_le_length hTc, ?_, ?_, hE⟩
    · intro x hx
      obtain ⟨e, he, hxe⟩ := exists_mem_walkEdges_of_mem ((hPc c).two_le_length hTc) hx
      exact hends e (mem_E2.1 (mem_E2c.1 (hE e he)).1).1 x hxe
    · intro e he
      obtain ⟨heH, hnot⟩ := mem_E2.1 (mem_E2c.1 (hE e he)).1
      push Not at hnot
      obtain ⟨v, hv, hvP⟩ := hnot
      have := hends e heH v hv
      rw [Finset.mem_union] at this
      exact ⟨v, this.resolve_right hvP, hv⟩
  -- stripping
  have hs : ∀ (c : Fin 4) (T : List V), ∃ (S : List (Sym2 V)) (T' : List V),
      T ∈ Pc c → StripOut Rt PlJ T S T' := by
    intro c T
    by_cases hTc : T ∈ Pc c
    · obtain ⟨h1, h2, h3, h4, _⟩ := hT c T hTc
      obtain ⟨S, T', hST⟩ := strip_exists hdis h1 h2 h3 h4
      exact ⟨S, T', fun _ => hST⟩
    · exact ⟨[], [], fun h => absurd h hTc⟩
  choose St Tp hST using hs
  obtain ⟨hallN, hallM⟩ := allE_props hPc
  -- stripped edges, arc edges
  obtain ⟨SE, hSE⟩ : ∃ SE : List (Sym2 V),
      SE = (List.finRange 4).flatMap fun c => (Pc c).flatMap (St c) := ⟨_, rfl⟩
  obtain ⟨AE, hAE⟩ : ∃ AE : List (Sym2 V),
      AE = (List.finRange 4).flatMap fun c => (Pc c).flatMap fun T => walkEdges (Tp c T) :=
    ⟨_, rfl⟩
  have hperm : List.Perm (SE ++ AE)
      ((List.finRange 4).flatMap (fun c => (Pc c).flatMap walkEdges)) := by
    rw [hSE, hAE]
    apply flatMap2_perm
    intro c _
    apply flatMap2_perm
    intro T hTc
    exact (hST c T hTc).1
  have hnd : (SE ++ AE).Nodup := hperm.nodup_iff.2 hallN
  obtain ⟨hSEnd, hAEnd, hSEAE⟩ := List.nodup_append.1 hnd
  have hmemSA : ∀ e, e ∈ SE ∨ e ∈ AE ↔ e ∈ E2 PlJ HJ := fun e => by
    rw [← List.mem_append, hperm.mem_iff, hallM]
  have hE12 : ∀ e, e ∈ E1 PlJ HJ → e ∉ E2 PlJ HJ := fun e h1 h2 =>
    (mem_E2.1 h2).2 (mem_E1.1 h1).2
  -- arcs
  obtain ⟨arcs, harcs⟩ : ∃ arcs : List (List V × Fin 4), arcs = (List.finRange 4).flatMap
      fun c => ((Pc c).filter fun T => 2 ≤ (Tp c T).length).map fun T => (Tp c T, c) :=
    ⟨_, rfl⟩
  have hmemArc : ∀ a ∈ arcs, ∃ c T, T ∈ Pc c ∧ 2 ≤ (Tp c T).length ∧ a = (Tp c T, c) := by
    intro a ha
    rw [harcs] at ha
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at ha
    obtain ⟨c, _, T, ⟨hTc, hl⟩, rfl⟩ := ha
    exact ⟨c, T, hTc, hl, rfl⟩
  have hAEeq : (arcs.map Prod.fst).flatMap walkEdges = AE := by
    rw [harcs, hAE, List.map_flatMap, List.flatMap_assoc]
    congr 1
    funext c
    rw [List.map_map, List.flatMap_map]
    simp only [Function.comp_def]
    apply flatMap_filter_eq
    intro T _ hl
    apply walkEdges_eq_nil_of_length_le_one
    simpa using hl
  -- the objects
  refine ⟨E1 PlJ HJ ∪ SE.toFinset, D1 ++ SE.map Obj.edge, arcs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact (mem_E1.1 h).1
    · exact (mem_E2.1 ((hmemSA e).1 (Or.inl (List.mem_toFinset.1 h)))).1
  · refine ⟨?_, ?_, ?_⟩
    · intro o ho
      rcases List.mem_append.1 ho with h | h
      · exact hD1.1 o h
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
        exact hloop e (mem_E2.1 ((hmemSA e).1 (Or.inl he))).1
    · rw [List.flatMap_append, flatMap_map_edge, List.nodup_append]
      refine ⟨hD1.2.1, hSEnd, ?_⟩
      rintro a ha b hb rfl
      exact hE12 a ((hD1.2.2 a).1 ha) ((hmemSA a).1 (Or.inl hb))
    · intro e
      rw [List.flatMap_append, flatMap_map_edge, List.mem_append, hD1.2.2 e, Finset.mem_coe,
        Finset.mem_coe, Finset.mem_union, List.mem_toFinset]
  · -- the count
    have hc : ∀ c : Fin 4, ((Pc c).flatMap (St c)).length ≤ 2 * PlJ.card := by
      intro c
      rw [List.length_flatMap]
      calc ((Pc c).map fun T => (St c T).length).sum
          ≤ ((Pc c).map fun T => (PlJ.filter fun p => T.head? = some p ∨
              T.getLast? = some p).card).sum :=
            PVStep.sum_map_le _ _ _ fun T hTc => (hST c T hTc).2.1
        _ = ∑ p ∈ PlJ, pathEndCount (Pc c) p := sum_card_filter_ends _ _
        _ ≤ ∑ _p ∈ PlJ, 2 := Finset.sum_le_sum fun p _ => hPc2 c p
        _ = 2 * PlJ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hSElen : SE.length ≤ 8 * PlJ.card := by
      rw [hSE, List.length_flatMap]
      calc ((List.finRange 4).map fun c => ((Pc c).flatMap (St c)).length).sum
          ≤ ((List.finRange 4).map fun _ => 2 * PlJ.card).sum :=
            PVStep.sum_map_le _ _ _ fun c _ => hc c
        _ = 8 * PlJ.card := by simp; ring
    simp only [List.length_append, List.length_map]
    omega
  · refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
      obtain ⟨c, T, hTc, hl, rfl⟩ := hmemArc a ha
      exact ⟨hl, ((hPc c).nodup hTc).sublist (hST c T hTc).2.2.1.sublist⟩
    · rw [hAEeq]; exact hAEnd
    · intro e
      rw [hAEeq, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset]
      constructor
      · intro he
        have h2 := (hmemSA e).1 (Or.inr he)
        refine ⟨(mem_E2.1 h2).1, ?_⟩
        rintro (h | h)
        · exact hE12 e h h2
        · exact hSEAE e h e he rfl
      · rintro ⟨hH, hn⟩
        have h2 : e ∈ E2 PlJ HJ := mem_E2.2 ⟨hH, fun h => hn (Or.inl (mem_E1.2 ⟨hH, h⟩))⟩
        exact ((hmemSA e).2 h2).resolve_left fun h => hn (Or.inr h)
  · intro a ha
    obtain ⟨c, T, hTc, hl, rfl⟩ := hmemArc a ha
    obtain ⟨_, _, hinf, hout⟩ := hST c T hTc
    refine ⟨?_, ?_⟩
    · rcases hout with h | ⟨_, ⟨x, hx, hxh⟩, y, hy, hyl⟩
      · omega
      · rintro z (hz | hz)
        · rw [hxh] at hz; cases hz; exact hx
        · rw [hyl] at hz; cases hz; exact hy
    · intro x hx
      have hxT : x ∈ T := hinf.subset hx
      obtain ⟨e, he, hxe⟩ := exists_mem_walkEdges_of_mem (hT c T hTc).2.1 hxT
      have hph' := hph e x hxe
      rwa [(mem_E2c.1 ((hT c T hTc).2.2.2.2 e he)).2] at hph'
  · -- the arc count
    have hc : ∀ c : Fin 4, ((Pc c).filter fun T => 2 ≤ (Tp c T).length).length ≤
        (Rt ∪ PlJ).card := by
      intro c
      refine (List.length_filter_le _ _).trans ((hPc c).length_le_card (hPc2 c) ?_)
      intro e he v hv
      exact hends e (mem_E2.1 (mem_E2c.1 he).1).1 v hv
    rw [harcs, List.length_flatMap]
    calc ((List.finRange 4).map fun c =>
          (((Pc c).filter fun T => 2 ≤ (Tp c T).length).map fun T => (Tp c T, c)).length).sum
        ≤ ((List.finRange 4).map fun _ => (Rt ∪ PlJ).card).sum :=
          PVStep.sum_map_le _ _ _ fun c _ => by rw [List.length_map]; exact hc c
      _ = 4 * (Rt ∪ PlJ).card := by simp; ring
  · intro hP
    subst hP
    have h1 : E1 (∅ : Finset V) HJ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | _ a b => simpa using (mem_E1.1 he).2 a (Sym2.mem_mk_left a b)
    have h2 : SE = [] := by
      apply PVStep.eq_nil_of_forall_not_mem
      intro e he
      rw [hSE] at he
      simp only [List.mem_flatMap] at he
      obtain ⟨c, _, T, hTc, he⟩ := he
      have := (hST c T hTc).2.1
      simp only [Finset.filter_empty, Finset.card_empty, nonpos_iff_eq_zero,
        List.length_eq_zero_iff] at this
      rw [this] at he
      simp at he
    rw [h1, h2]
    simp

end Core

end PVFin

end EG
