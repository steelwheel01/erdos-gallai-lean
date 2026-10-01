module

public import EG.Lib.Vortex.TPVStepMain
public import EG.Lib.Vortex.Params
public import EG.Proof.Found.EG0

/-!
# The TPV run for labels in the good event (manuscript s4:lemTPV, proof, "The process",
"Finish", "Conclusion")

Unit P3-s4. `EG.TPVRun.core`: for labels in the good event (the deterministic consequences
(G2), (G4), (G5) and the multiplicity bound of the sets `A(w)`, `EG.TPVRun.Good`), every
admissible edge set `E` has a partition `E = E^V ⊔ E^Q` with (T1)–(T4) (`EG.Vortex.TPVConcl`).

* `EG.TPVRun.finish`: "By (Inv1) for `j = J`, every edge of `H_J` has both ends in `P ∩ U_J`,
  and `|P ∩ U_J| ≤ 48|P|/L` by (G5). Apply Fact s1:factEG0(b) with `F := H_J`, `W := P ∩ U_J`,
  `β := 48` and `α := |P| ≤ N` … So `H_J` decomposes into at most `48|P|` objects".
* `EG.TPVRun.run_from`: the steps `j, j+1, …, J-1` and the finish, by downward induction.
* `EG.TPVRun.core`: the conclusion with `S = ∅` before step `0`; the count
  `12·8|P| + 48|P| = 144|P| ≤ 169|P|` (the manuscript's count is `84|P| + 48|P| = 132|P|`; the
  per-step bound used here is the cruder `12|P ∩ U_j|`).
-/

public section

namespace EG

namespace TPVRun

open List

variable {V : Type*} [DecidableEq V]

variable {Z P : Finset V} {lev : V → ℕ} {kap : V → Fin 4}

/-- [s4:lemTPV] proof, "Finish" (Fact s1:factEG0(b) with `β = 48`, `α = |P|`). -/
theorem finish {O : FGraph V} {J : ℕ} (hPZ : P ⊆ Z) {E : Finset (Sym2 V)}
    (hE : Vortex.TPVAdm Z O E) {S : Finset (Sym2 V)}
    (hI1 : ∀ e ∈ H0 P E, e ∉ S → ∀ v ∈ e, J ≤ lev v)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card)
    (hG5b : ((P.filter fun v => J ≤ lev v).card : ℝ) ≤ 48 * P.card / Vortex.L Z.card) :
    ∃ D : List (Obj V), IsDecomp ((H0 P E \ S : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      D.length ≤ 48 * P.card := by
  classical
  have hN : 1 < Z.card := Vortex.one_lt_of_L_pos (by linarith)
  have hNR : (1 : ℝ) < Z.card := by exact_mod_cast hN
  obtain ⟨D, hD, hlen, _⟩ := EG.factEG0b V (Z.card : ℝ) (P.card : ℝ) 48 (H0 P E \ S)
    (P.filter fun v => J ≤ lev v) hNR (by positivity)
    (by exact_mod_cast Finset.card_le_card hPZ) (by norm_num)
    (by rw [← Vortex.L_eq]; linarith)
    (fun e he => hE.1 e (mem_H0.1 (Finset.mem_sdiff.1 he).1).1)
    (fun e he v hv => by
      have he' := Finset.mem_sdiff.1 he
      exact Finset.mem_filter.2 ⟨(mem_H0.1 he'.1).2 v hv, hI1 e he'.1 he'.2 v hv⟩)
    (by rw [← Vortex.L_eq]; exact hG5b)
  refine ⟨D, hD, ?_⟩
  exact_mod_cast hlen

/-- [s4:lemTPV] proof: steps `j, …, J - 1` and the finish, from a state `S` satisfying
(Inv1)–(Inv3) before step `j` (downward induction on `J - j`). -/
theorem run_from {O : FGraph V} {J : ℕ} {R : ℕ → Fin 3 → Finset (Sym2 V)} {M : Finset (Sym2 V)}
    {A : V → Finset V} {ℓ t : ℝ} (hg : Good Z P O J R M lev kap A ℓ t)
    {E : Finset (Sym2 V)} (hE : Vortex.TPVAdm Z O E)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card)
    (hG5b : ((P.filter fun v => J ≤ lev v).card : ℝ) ≤ 48 * P.card / Vortex.L Z.card) :
    ∀ n j, j + n = J → ∀ S : Finset (Sym2 V), Inv Z P J R M lev E j S →
      ∃ (T : Finset (Sym2 V)) (D : List (Obj V)),
        Disjoint T S ∧ T ⊆ E ∧ H0 P E \ S ⊆ T ∧ (∀ e ∈ T, e ∈ H0 P E ∨ e ∈ O.edges) ∧
        IsDecomp (T : Set (Sym2 V)) D ∧
        D.length ≤ 12 * ∑ i ∈ Finset.Ico j J, (P.filter fun v => i ≤ lev v).card +
          48 * P.card := by
  classical
  intro n
  induction n with
  | zero =>
    intro j hj S hS
    simp only [Nat.add_zero] at hj
    subst hj
    obtain ⟨D, hD, hlen⟩ := finish hg.PZ hE hS.1 hL hG5b
    refine ⟨H0 P E \ S, D, Finset.sdiff_disjoint, fun e he =>
      (mem_H0.1 (Finset.mem_sdiff.1 he).1).1, subset_refl _,
      fun e he => Or.inl (Finset.mem_sdiff.1 he).1, hD, ?_⟩
    simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, zero_add]
    exact hlen
  | succ n ih =>
    intro j hj S hS
    have hjJ : j < J := by omega
    obtain ⟨T1, D1, hd1, hE1, hF1, hH1, hD1, hl1, hinv1⟩ := step hg hE hjJ hS
    obtain ⟨T2, D2, hd2, hE2, hH2, hHO2, hD2, hl2⟩ := ih (j + 1) (by omega) (S ∪ T1) hinv1
    have hd12 : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact Finset.disjoint_left.1 hd2 h2 (Finset.mem_union_right _ h1)
    refine ⟨T1 ∪ T2, D1 ++ D2, ?_, Finset.union_subset hE1 hE2, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_union_left]
      refine ⟨hd1, ?_⟩
      rw [Finset.disjoint_left]
      intro e h2 hs
      exact Finset.disjoint_left.1 hd2 h2 (Finset.mem_union_left _ hs)
    · intro e he
      rw [Finset.mem_sdiff] at he
      by_cases h1 : e ∈ T1
      · exact Finset.mem_union_left _ h1
      · refine Finset.mem_union_right _ (hH2 ?_)
        rw [Finset.mem_sdiff, Finset.mem_union]
        exact ⟨he.1, fun h => h.elim he.2 h1⟩
    · intro e he
      rcases Finset.mem_union.1 he with h | h
      · exact hH1 e h
      · exact hHO2 e h
    · rw [Finset.coe_union]
      exact hD1.append hD2 (Finset.disjoint_coe.2 hd12)
    · rw [List.length_append, Finset.sum_eq_sum_Ico_succ_bot hjJ]
      have := hl1
      omega

/-- [s4:lemTPV], deterministic core: for labels in the good event, every admissible `E` has a
partition with (T1)–(T4). (G5) is `hG5a`, `hG5b`; size condition (i) is `hL`. -/
theorem core {O : FGraph V} {J : ℕ} {R : ℕ → Fin 3 → Finset (Sym2 V)} {M : Finset (Sym2 V)}
    {A : V → Finset V} {ℓ t : ℝ} (hg : Good Z P O J R M lev kap A ℓ t)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card)
    (hG5a : ∑ i ∈ Finset.range J, (P.filter fun v => i ≤ lev v).card ≤ 8 * P.card)
    (hG5b : ((P.filter fun v => J ≤ lev v).card : ℝ) ≤ 48 * P.card / Vortex.L Z.card)
    {E : Finset (Sym2 V)} (hE : Vortex.TPVAdm Z O E) : Vortex.TPVConcl Z O P E := by
  classical
  rcases P.eq_empty_or_nonempty with hP | hP
  · subst hP
    refine ⟨∅, E, Finset.disjoint_empty_left _, Finset.empty_union _, ?_, ?_, ?_, fun _ => rfl⟩
    · intro e _ he
      exfalso
      induction e using Sym2.ind with
      | _ a b => exact Finset.notMem_empty a (he a (Sym2.mem_mk_left a b))
    · intro e he; exact absurd he (Finset.notMem_empty e)
    · exact ⟨[], by simpa using (isDecomp_nil : IsDecomp (∅ : Set (Sym2 V)) []), by simp⟩
  · have hinv0 : Inv Z P J R M lev E 0 ∅ :=
      ⟨fun _ _ _ _ _ => Nat.zero_le _, fun _ _ _ _ _ _ _ h => Finset.notMem_empty _ h,
        fun _ _ _ _ _ _ _ _ h => Finset.notMem_empty _ h⟩
    obtain ⟨T, D, _, hTE, hHT, hTO, hD, hlen⟩ := run_from hg hE hL hG5b J 0 (by omega) ∅ hinv0
    refine ⟨T, E \ T, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hTE, ?_, ?_, ?_, ?_⟩
    · intro e he hP'
      exact hHT (Finset.mem_sdiff.2 ⟨mem_H0.2 ⟨he, hP'⟩, Finset.notMem_empty e⟩)
    · intro e he ⟨v, hve, hvQ⟩
      rcases hTO e he with h | h
      · exact absurd ((mem_H0.1 h).2 v hve) (Finset.mem_sdiff.1 hvQ).2
      · exact h
    · refine ⟨D, hD, ?_⟩
      rw [← Finset.range_eq_Ico] at hlen
      omega
    · intro h
      exact absurd h hP.ne_empty

end TPVRun

end EG
