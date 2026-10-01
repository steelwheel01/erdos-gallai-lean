module

public import EG.Lib.Vortex.PVRunStep
public import EG.Proof.Vortex.PVFinish

/-!
# The PV run for labels in the good event (manuscript s4:lemPV, proof, "The process", "Finish",
"Conclusion" (a)–(d))

Unit P3-s4. `EG.PVRun.core`: for labels in the good event (the deterministic consequences (G2),
(G4), (G5) and the multiplicity bound of the sets `A(w)`, `EG.PVRun.Good`), every admissible
edge set `H_0` has a partition `H_0 = H^obj ⊔ H^arc` and arcs with (a)–(d) of Lemma PV.

* The finish is P4A's `EG.pvFinish` ((s4:lemPV) "Finish": Fact EG0(b) on `E_1`, phases, Corollary
  22 and stripping on `E_2`), applied to `H_J = H_0 \ S` at `j = J`.
* `EG.PVRun.run_from`: the steps `j, j+1, …, J-1` and the finish, by downward induction.
* `EG.PVRun.core`: the conclusion with `S = ∅` before step `0`; the count
  `28·8|Pl| + 64|Pl| + 8|Pl_J| ≤ 296|Pl| ≤ 369|Pl|` (the manuscript's is
  `224|Pl| + 64|Pl| + 16|Pl| = 304|Pl|`), `|𝔄| ≤ 4JN + 4N`, the per-vertex bound of (c) by
  P4A's `EG.pvArcEndsDeg`, and (d).
-/

public section

namespace EG

namespace PVRun

open List

variable {V : Type*} [DecidableEq V]

/-- [s4:lemPV] proof: steps `j, …, J - 1` and the finish, from a state `S` satisfying
(Inv1)–(Inv3) before step `j` (downward induction on `n = J - j`). -/
theorem run_from {D : Vortex.PVData V} {lev : V → ℕ} {kap : V → Fin 5} {ℓ t : ℝ}
    (hg : Good D lev kap ℓ t) {H0 : Finset (Sym2 V)} (hH : Vortex.PVAdm D H0)
    (hG5b : ((D.Pl.filter fun v => Vortex.pvJ D.Z.card ≤ lev v).card : ℝ) ≤
      64 * D.Pl.card / Vortex.L D.Z.card) :
    ∀ n j, j + n = Vortex.pvJ D.Z.card → ∀ S : Finset (Sym2 V), Inv D lev H0 j S →
      ∃ (Hobj Harc : Finset (Sym2 V)) (Dl : List (Obj V)) (arcs : List (List V × Fin 4)),
        Disjoint Hobj Harc ∧ Hobj ∪ Harc = H0 \ S ∧
        IsDecomp (Hobj : Set (Sym2 V)) Dl ∧
        Dl.length ≤ 28 * ∑ i ∈ Finset.Ico j (Vortex.pvJ D.Z.card),
            (D.Pl.filter fun v => i ≤ lev v).card + 64 * D.Pl.card +
          8 * (D.Pl.filter fun v => Vortex.pvJ D.Z.card ≤ lev v).card ∧
        IsPathDecomp (Harc : Set (Sym2 V)) (arcs.map Prod.fst) ∧ (∀ a ∈ arcs, ArcOK D a) ∧
        arcs.length ≤ 4 * (n + 1) * D.Z.card := by
  classical
  have hyp := hg.hyp
  obtain ⟨hsize, _, _, _, _, _, _, _, _, _, _, hRtPl, hZ, _⟩ := hyp
  have hPlZ : D.Pl ⊆ D.Z := hZ ▸ Finset.subset_union_right
  intro n
  induction n with
  | zero =>
    intro j hj S hS
    simp only [Nat.add_zero] at hj
    subst hj
    set J := Vortex.pvJ D.Z.card with hJdef
    set PlJ := D.Pl.filter fun v => J ≤ lev v with hPlJdef
    have hends : ∀ e ∈ H0 \ S, ∀ v ∈ e, v ∈ D.Rt ∪ PlJ := by
      intro e he v hv
      have he' := Finset.mem_sdiff.1 he
      obtain ⟨hvZ, h⟩ := TPVRun.mem_U.1 (hS.1 e he'.1 he'.2 v hv)
      by_cases hvPl : v ∈ D.Pl
      · rcases h with h | h
        · exact absurd hvPl h
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hvPl, h⟩)
      · rw [← hZ] at hvZ
        rcases Finset.mem_union.1 hvZ with h' | h'
        · exact Finset.mem_union_left _ h'
        · exact absurd h' hvPl
    obtain ⟨Hobj, Dl, arcs, h1, h2, h3, h4, h5, h6, _⟩ := EG.pvFinish V D.Z.card D.Rt D.Pl PlJ
      (H0 \ S) D.ext hsize.cond_i (Finset.card_le_card hPlZ) (Finset.filter_subset _ _) hRtPl
      hG5b (fun e he => hH.1 e (Finset.mem_sdiff.1 he).1) hends
    refine ⟨Hobj, (H0 \ S) \ Hobj, Dl, arcs, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h1, h2,
      ?_, h4, h5, ?_⟩
    · simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, zero_add]
      exact_mod_cast h3
    · refine h6.trans ?_
      have : (D.Rt ∪ PlJ).card ≤ D.Z.card := by
        refine Finset.card_le_card (Finset.union_subset ?_ ((Finset.filter_subset _ _).trans hPlZ))
        exact hZ ▸ Finset.subset_union_left
      omega
  | succ n ih =>
    intro j hj S hS
    have hjJ : j < Vortex.pvJ D.Z.card := by omega
    obtain ⟨Tobj, Tarc, D1, arcs1, hd1, hdS, hTH, hD1, hl1, hA1, hok1, hn1, hinv1⟩ :=
      step hg hH hjJ hS
    obtain ⟨Hobj2, Harc2, D2, arcs2, hd2, hu2, hD2, hl2, hA2, hok2, hn2⟩ :=
      ih (j + 1) (by omega) (S ∪ (Tobj ∪ Tarc)) hinv1
    have hmem2 : ∀ e, e ∈ Hobj2 ∨ e ∈ Harc2 → e ∈ H0 ∧ e ∉ S ∧ e ∉ Tobj ∪ Tarc := by
      intro e he
      have : e ∈ Hobj2 ∪ Harc2 := Finset.mem_union.2 he
      rw [hu2, Finset.mem_sdiff, Finset.mem_union, not_or] at this
      exact ⟨this.1, this.2.1, this.2.2⟩
    have hTobj2 : Disjoint Tobj Hobj2 := by
      rw [Finset.disjoint_left]
      intro e h h'
      exact (hmem2 e (Or.inl h')).2.2 (Finset.mem_union_left _ h)
    have hTarc2 : Disjoint Tarc Harc2 := by
      rw [Finset.disjoint_left]
      intro e h h'
      exact (hmem2 e (Or.inr h')).2.2 (Finset.mem_union_right _ h)
    refine ⟨Tobj ∪ Hobj2, Tarc ∪ Harc2, D1 ++ D2, arcs1 ++ arcs2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      refine ⟨⟨hd1, ?_⟩, ?_, hd2⟩
      · rw [Finset.disjoint_left]
        intro e h h'
        exact (hmem2 e (Or.inr h')).2.2 (Finset.mem_union_left _ h)
      · rw [Finset.disjoint_left]
        intro e h h'
        exact (hmem2 e (Or.inl h)).2.2 (Finset.mem_union_right _ h')
    · ext e
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ((h | h) | (h | h))
        · exact ⟨hTH (Finset.mem_union_left _ h),
            fun hs => Finset.disjoint_left.1 hdS (Finset.mem_union_left _ h) hs⟩
        · exact ⟨(hmem2 e (Or.inl h)).1, (hmem2 e (Or.inl h)).2.1⟩
        · exact ⟨hTH (Finset.mem_union_right _ h),
            fun hs => Finset.disjoint_left.1 hdS (Finset.mem_union_right _ h) hs⟩
        · exact ⟨(hmem2 e (Or.inr h)).1, (hmem2 e (Or.inr h)).2.1⟩
      · rintro ⟨he, heS⟩
        by_cases hT : e ∈ Tobj ∪ Tarc
        · rcases Finset.mem_union.1 hT with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        · have : e ∈ Hobj2 ∪ Harc2 := by
            rw [hu2, Finset.mem_sdiff, Finset.mem_union, not_or]
            exact ⟨he, heS, hT⟩
          rcases Finset.mem_union.1 this with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
    · rw [Finset.coe_union]
      exact hD1.append hD2 (Finset.disjoint_coe.2 hTobj2)
    · rw [List.length_append, Finset.sum_eq_sum_Ico_succ_bot hjJ]
      rw [Nat.mul_add]
      omega
    · rw [List.map_append, Finset.coe_union]
      exact isPathDecomp_append hA1 hA2 (Finset.disjoint_coe.2 hTarc2)
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hok1 a ha
      · exact hok2 a ha
    · rw [List.length_append]
      have : 4 * (n + 1 + 1) * D.Z.card = 4 * D.Z.card + 4 * (n + 1) * D.Z.card := by ring
      omega

/-- [s4:lemPV], deterministic core: for labels in the good event, every admissible `H_0` has a
partition `H_0 = H^obj ⊔ H^arc` and arcs with (a)–(d). (G5) is `hG5a`, `hG5b`. -/
theorem core {D : Vortex.PVData V} {lev : V → ℕ} {kap : V → Fin 5} {ℓ t : ℝ}
    (hg : Good D lev kap ℓ t)
    (hG5a : ∑ i ∈ Finset.range (Vortex.pvJ D.Z.card), (D.Pl.filter fun v => i ≤ lev v).card ≤
      8 * D.Pl.card)
    (hG5b : ((D.Pl.filter fun v => Vortex.pvJ D.Z.card ≤ lev v).card : ℝ) ≤
      64 * D.Pl.card / Vortex.L D.Z.card)
    {H0 : Finset (Sym2 V)} (hH : Vortex.PVAdm D H0) :
    ∃ (Hobj : Finset (Sym2 V)) (Dobj : List (Obj V)) (arcs : List (List V × Fin 4)),
      Hobj ⊆ H0 ∧
      IsDecomp (Hobj : Set (Sym2 V)) Dobj ∧ Dobj.length ≤ 369 * D.Pl.card ∧
      IsPathDecomp ((H0 \ Hobj : Finset (Sym2 V)) : Set (Sym2 V)) (arcs.map Prod.fst) ∧
      (∀ a ∈ arcs, (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ D.Rt) ∧
        ∀ x ∈ a.1, D.ext x ≠ some a.2) ∧
      arcs.length ≤ 4 * (Vortex.pvJ D.Z.card + 1) * D.Z.card ∧
      (∀ x : V, pathEndCount (arcs.map Prod.fst) x ≤ degE H0 x) ∧
      (∀ x : V, degE H0 x ≤ D.Z.card - 1) ∧
      (D.Rt = ∅ → arcs = []) ∧ (D.Pl = ∅ → Hobj = ∅) := by
  classical
  obtain ⟨Hobj, Harc, Dl, arcs, hd, hu, hD, hl, hA, hok, hn⟩ :=
    run_from hg hH hG5b (Vortex.pvJ D.Z.card) 0 (by omega) ∅ (inv_zero hH)
  rw [Finset.sdiff_empty] at hu
  have hHobj : Hobj ⊆ H0 := hu ▸ Finset.subset_union_left
  have hsd : H0 \ Hobj = Harc := by
    rw [← hu, Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint hd.symm
  have hPlJ : (D.Pl.filter fun v => Vortex.pvJ D.Z.card ≤ lev v).card ≤ D.Pl.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hlen : Dl.length ≤ 296 * D.Pl.card := by
    rw [← Finset.range_eq_Ico] at hl
    omega
  have hA' : IsPathDecomp ((H0 \ Hobj : Finset (Sym2 V)) : Set (Sym2 V)) (arcs.map Prod.fst) := by
    rw [hsd]; exact hA
  refine ⟨Hobj, Dl, arcs, hHobj, hD, by omega, hA', hok, by simpa using hn, fun x => ?_,
    fun x => ?_, ?_, ?_⟩
  · exact (EG.pvArcEndsDeg V D.Z H0 (H0 \ Hobj) (arcs.map Prod.fst) hH.1 hH.2.1
      Finset.sdiff_subset hA' x).1
  · exact (EG.pvArcEndsDeg V D.Z H0 (H0 \ Hobj) (arcs.map Prod.fst) hH.1 hH.2.1
      Finset.sdiff_subset hA' x).2
  · intro hRt
    rcases harcs : arcs with _ | ⟨a, arcs'⟩
    · rfl
    exfalso
    have ha : a ∈ arcs := by rw [harcs]; exact List.mem_cons_self
    have h2 := hA'.two_le_length (List.mem_map_of_mem (f := Prod.fst) ha)
    obtain ⟨x, hx⟩ : ∃ x, a.1.head? = some x := by
      cases h : a.1 with
      | nil => rw [h] at h2; simp at h2
      | cons x _ => exact ⟨x, rfl⟩
    have := (hok a ha).1 x (Or.inl hx)
    rw [hRt] at this
    exact Finset.notMem_empty x this
  · intro hPl
    have h0 : Dl = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [hPl, Finset.card_empty] at hlen
      omega
    subst h0
    ext e
    simp only [Finset.notMem_empty, iff_false]
    intro he
    have := hD.2.2 e
    simp at this
    exact this he

end PVRun

end EG
