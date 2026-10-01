module

public import EG.Lib.Vortex.VXStepMain
public import EG.Lib.Vortex.TPVRun
public import EG.Lib.Vortex.TPVLaws

/-!
# The VX⁺ run for labels in the good event (manuscript s4:thmVXp, proof, "The process", "Cost")

Unit P3-s4. `EG.VXRun.core`: for labels in the good event ((G2), (G3), (G4) with nine edges, the
multiplicity bound of the sets `A(w)`), every graph `G` with `V(G) = Z` and `E(O) ⊆ E(G)` has a
decomposition of `E(G)` into at most `38.4N + 13N` objects of which at most `N + 13N/L` are single
edges.

* `EG.VXRun.finish`: "By Fact s1:factEG0(b) with `F := H_J`, `W := U_J`, `β := 13` and `α := N`
  …, `H_J` decomposes into at most `13N` objects, at most `|U_J| ≤ 13N/L` of which are single
  edges."
* `EG.VXRun.run_from`: the steps `j, …, J-1` and the finish.
* `EG.VXRun.core`: the count "`Σ_{j<J} 19·1.01·2^{-j}N + 13N ≤ 38.4N + 13N`" (here with the
  per-step bound `13|U_j|` in place of `19|U_j|`) and the single edges ("The only single edges are
  the parity edges, at most `Σ_j |W_j| ≤ N` in total …, and the at most `13N/L` single edges of the
  finish").
-/

public section

namespace EG

namespace VXRun

open TPVRun List

variable {V : Type*} [DecidableEq V]

variable {Z : Finset V} {lev : V → ℕ} {kap : V → Fin 4}

/-- [s4:thmVXp] proof, the finish (Fact s1:factEG0(b) with `β = 13`, `α = N`). -/
theorem finish {O : FGraph V} {J : ℕ} {E : Finset (Sym2 V)}
    (hE : Vortex.TPVAdm Z O E) {S : Finset (Sym2 V)}
    (hI1 : ∀ e ∈ H0 Z E, e ∉ S → ∀ v ∈ e, J ≤ lev v)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card)
    (hUJ : ((Z.filter fun v => J ≤ lev v).card : ℝ) ≤ 13 * Z.card / Vortex.L Z.card) :
    ∃ D : List (Obj V), IsDecomp ((H0 Z E \ S : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      D.length ≤ 13 * Z.card ∧ D.countP Obj.isEdge ≤ (Z.filter fun v => J ≤ lev v).card := by
  classical
  have hN : 1 < Z.card := Vortex.one_lt_of_L_pos (by linarith)
  have hNR : (1 : ℝ) < Z.card := by exact_mod_cast hN
  obtain ⟨D, hD, hlen, hcnt⟩ := EG.factEG0b V (Z.card : ℝ) (Z.card : ℝ) 13 (H0 Z E \ S)
    (Z.filter fun v => J ≤ lev v) hNR (by positivity) le_rfl (by norm_num)
    (by rw [← Vortex.L_eq]; linarith)
    (fun e he => hE.1 e (mem_H0.1 (Finset.mem_sdiff.1 he).1).1)
    (fun e he v hv => by
      have he' := Finset.mem_sdiff.1 he
      exact Finset.mem_filter.2 ⟨(mem_H0.1 he'.1).2 v hv, hI1 e he'.1 he'.2 v hv⟩)
    (by rw [← Vortex.L_eq]; exact hUJ)
  refine ⟨D, hD, ?_, ?_⟩
  · exact_mod_cast hlen
  · refine le_trans (le_of_eq ?_) hcnt
    exact List.countP_congr fun o _ => by cases o <;> simp [Obj.isEdge]

/-- [s4:thmVXp] proof: steps `j, …, J - 1` and the finish (downward induction on `J - j`). -/
theorem run_from {O : FGraph V} {J : ℕ} {R : ℕ → Fin 3 → Finset (Sym2 V)} {M : Finset (Sym2 V)}
    {A : V → Finset V} {ℓ t : ℝ} (hg : Good Z Z O J R M lev kap A ℓ t)
    (hG9 : ∀ j < J, ∀ w ∈ Z,
      9 ≤ ((A w).filter fun u => s(w, u) ∈ M ∧ u ∈ Zr Z Z lev kap j).card)
    {E : Finset (Sym2 V)} (hE : Vortex.TPVAdm Z O E)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card)
    (hUJ : ((Z.filter fun v => J ≤ lev v).card : ℝ) ≤ 13 * Z.card / Vortex.L Z.card) :
    ∀ n j, j + n = J → ∀ S : Finset (Sym2 V), Inv Z Z J R M lev E j S →
      ∃ (T : Finset (Sym2 V)) (D : List (Obj V)),
        Disjoint T S ∧ T ⊆ E ∧ H0 Z E \ S ⊆ T ∧ IsDecomp (T : Set (Sym2 V)) D ∧
        D.length ≤ 13 * ∑ i ∈ Finset.Ico j J, (Z.filter fun v => i ≤ lev v).card + 13 * Z.card ∧
        D.countP Obj.isEdge ≤ ∑ i ∈ Finset.Ico j J, (Wt Z lev i).card +
          (Z.filter fun v => J ≤ lev v).card := by
  classical
  intro n
  induction n with
  | zero =>
    intro j hj S hS
    simp only [Nat.add_zero] at hj
    subst hj
    obtain ⟨D, hD, hlen, hcnt⟩ := finish hE hS.1 hL hUJ
    refine ⟨H0 Z E \ S, D, Finset.sdiff_disjoint, fun e he =>
      (mem_H0.1 (Finset.mem_sdiff.1 he).1).1, subset_refl _, hD, ?_, ?_⟩
    · simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, zero_add]
      exact hlen
    · simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
      exact hcnt
  | succ n ih =>
    intro j hj S hS
    have hjJ : j < J := by omega
    obtain ⟨T1, D1, hd1, hE1, hF1, hD1, hl1, hc1, hinv1⟩ := step hg hG9 hE hjJ hS
    obtain ⟨T2, D2, hd2, hE2, hH2, hD2, hl2, hc2⟩ := ih (j + 1) (by omega) (S ∪ T1) hinv1
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
      · by_cases hW : ∃ w ∈ Wt Z lev j, w ∈ e
        · exact absurd (hF1 e he.1 he.2 hW) h1
        · refine Finset.mem_union_right _ (hH2 ?_)
          rw [Finset.mem_sdiff, Finset.mem_union]
          exact ⟨he.1, fun h => h.elim he.2 h1⟩
    · rw [Finset.coe_union]
      exact hD1.append hD2 (Finset.disjoint_coe.2 hd12)
    · rw [List.length_append, Finset.sum_eq_sum_Ico_succ_bot hjJ]
      omega
    · rw [countP_isEdge_append, Finset.sum_eq_sum_Ico_succ_bot hjJ]
      omega

/-- [s4:thmVXp], deterministic core: for labels in the good event, `E(G)` decomposes into at most
`38.4N + 13N` objects, at most `N + 13N/L` of which are single edges. (G3) is `hG3` (for
`j < J`) and `hUJ` (at `J`, in the form `|U_J| ≤ 13N/L`). -/
theorem core {O : FGraph V} {J : ℕ} {R : ℕ → Fin 3 → Finset (Sym2 V)} {M : Finset (Sym2 V)}
    {A : V → Finset V} {ℓ t : ℝ} (hg : Good Z Z O J R M lev kap A ℓ t)
    (hG9 : ∀ j < J, ∀ w ∈ Z,
      9 ≤ ((A w).filter fun u => s(w, u) ∈ M ∧ u ∈ Zr Z Z lev kap j).card)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card)
    (hG3 : ∀ j < J, ((Z.filter fun v => j ≤ lev v).card : ℝ) ≤ 1.01 * (1 / 2) ^ j * Z.card)
    (hUJ : ((Z.filter fun v => J ≤ lev v).card : ℝ) ≤ 13 * Z.card / Vortex.L Z.card)
    {G : FGraph V} (hGZ : G.verts = Z) (hOG : O.edges ⊆ G.edges) :
    ∃ D : List (Obj V), IsDecomp (G.edges : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ 38.4 * (Z.card : ℝ) + 13 * (Z.card : ℝ) ∧
      (D.countP Obj.isEdge : ℝ) ≤ (Z.card : ℝ) + 13 * (Z.card : ℝ) / Vortex.L Z.card := by
  classical
  have hE : Vortex.TPVAdm Z O G.edges :=
    ⟨G.loopless, fun e he v hv => hGZ ▸ G.edge_verts e he v hv, hOG⟩
  have hinv0 : Inv Z Z J R M lev G.edges 0 ∅ :=
    ⟨fun _ _ _ _ _ => Nat.zero_le _, fun _ _ _ _ _ _ _ h => Finset.notMem_empty _ h,
      fun _ _ _ _ _ _ _ _ h => Finset.notMem_empty _ h⟩
  obtain ⟨T, D, _, hTE, hHT, hD, hlen, hcnt⟩ :=
    run_from hg hG9 hE hL hUJ J 0 (by omega) ∅ hinv0
  have hTeq : T = G.edges := by
    refine Finset.Subset.antisymm hTE fun e he => hHT (Finset.mem_sdiff.2 ⟨mem_H0.2 ⟨he,
      fun v hv => hGZ ▸ G.edge_verts e he v hv⟩, Finset.notMem_empty e⟩)
  rw [hTeq] at hD
  refine ⟨D, hD, ?_, ?_⟩
  · rw [← Finset.range_eq_Ico] at hlen
    have hsum : ((∑ i ∈ Finset.range J, (Z.filter fun v => i ≤ lev v).card : ℕ) : ℝ) ≤
        2.02 * Z.card := by
      push_cast
      calc (∑ i ∈ Finset.range J, ((Z.filter fun v => i ≤ lev v).card : ℝ))
          ≤ ∑ i ∈ Finset.range J, 1.01 * (1 / 2 : ℝ) ^ i * Z.card :=
            Finset.sum_le_sum fun i hi => hG3 i (Finset.mem_range.1 hi)
        _ = 1.01 * Z.card * ∑ i ∈ Finset.range J, (1 / 2 : ℝ) ^ i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ 1.01 * Z.card * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h := VortexLaw.geom_sum_half J
            have : ∑ i ∈ Finset.range J, (1 / 2 : ℝ) ^ i =
                2 * ∑ i ∈ Finset.range J, (1 / 2 : ℝ) ^ (i + 1) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
            rw [this, h]
            have : (0 : ℝ) ≤ (1 / 2) ^ J := by positivity
            linarith
        _ = 2.02 * Z.card := by ring
    have hlen' : (D.length : ℝ) ≤ 13 * ((∑ i ∈ Finset.range J,
        (Z.filter fun v => i ≤ lev v).card : ℕ) : ℝ) + 13 * Z.card := by exact_mod_cast hlen
    have hN : (0 : ℝ) ≤ Z.card := by positivity
    linarith
  · rw [← Finset.range_eq_Ico] at hcnt
    have hW : ∑ i ∈ Finset.range J, (Wt Z lev i).card ≤ Z.card := by
      rw [← Finset.card_biUnion]
      · exact Finset.card_le_card fun v hv => by
          obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hv
          exact (mem_Wt.1 hi).1
      · intro i _ i' _ hii'
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro v hv hv'
        exact Wt_ne hii'.symm hv hv'
    have hcnt' : (D.countP Obj.isEdge : ℝ) ≤ ((∑ i ∈ Finset.range J, (Wt Z lev i).card : ℕ) : ℝ) +
        ((Z.filter fun v => J ≤ lev v).card : ℝ) := by exact_mod_cast hcnt
    have hW' : ((∑ i ∈ Finset.range J, (Wt Z lev i).card : ℕ) : ℝ) ≤ Z.card := by
      exact_mod_cast hW
    linarith

end VXRun

end EG
