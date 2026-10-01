module

public import EG.Proof.Quot.HI
public import EG.Lib.Found.FnumMain

/-!
# From the hypothesis of Theorem HI″ to the internal main theorem (s7:thmHI, s7:thmMainProof)

The proof of the Main Theorem (s7:thmMainProof) establishes the hypothesis of Theorem HI″
(s7:thmHI) with `C := C₀`, `ϑ := ϑ_Q`, and concludes: "Theorem HI″ … therefore gives
`f(G) ≤ c_EG |V(G)|` for every graph `G`. In particular `f(n) ≤ c_EG n` for every `n`, so
`f(n) = O(n)`." This file is that last step, for `EG/Proof/Main.lean`:

* `EG.decomp_le_of_hiHyp`: under `EG.Spec.HIHyp D_* N₀ C ϑ` with `C ≥ D_*/2`, `ϑ ∈ [0,1/2)`, every
  finite simple graph on a vertex type `V : Type` decomposes into at most `⌈c⌉₊ · |V|` objects,
  `c = max(C/(1-2ϑ), N₀/2)` (the real constant `c` rounded up to a natural number, since
  `EG.Spec.MainInternal` asks for `c : ℕ`);
* `EG.mainInternal_of_hiHyp`: the same hypotheses give `EG.Spec.MainInternal`.
-/

public section


namespace EG

variable {Dstar N₀ C ϑ : ℝ}

/-- [s7:thmHI] + [s7:thmMainProof], with the constant rounded up: `f(G) ≤ ⌈c⌉₊ |V(G)|` for every
graph `G : FGraph V`, `c = max(C/(1-2ϑ), N₀/2)`. -/
theorem fnum_edges_le_ceil_of_hiHyp (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) (V : Type) (G : FGraph V) :
    fnum G.edges ≤ ⌈max (C / (1 - 2 * ϑ)) (N₀ / 2)⌉₊ * G.card := by
  have h1 := hi Dstar N₀ C ϑ hC hϑ0 hϑ h V G
  have h2 : max (C / (1 - 2 * ϑ)) (N₀ / 2) * (G.card : ℝ) ≤
      (⌈max (C / (1 - 2 * ϑ)) (N₀ / 2)⌉₊ : ℝ) * G.card :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
  exact_mod_cast h1.trans h2

/-- [s7:thmHI] + [s7:thmMainProof] "Theorem HI″ … therefore gives `f(G) ≤ c_EG |V(G)|` for every
graph `G`", in the form of `EG.Spec.MainInternal` with the explicit constant `⌈c⌉₊`: every simple
graph on a finite vertex type `V : Type` has a decomposition into at most `⌈c⌉₊ · |V|` objects,
where `c = max(C/(1-2ϑ), N₀/2)`. -/
theorem decomp_le_of_hiHyp (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) (V : Type) [Fintype V] (G : SimpleGraph V) :
    ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧
      D.length ≤ ⌈max (C / (1 - 2 * ϑ)) (N₀ / 2)⌉₊ * Fintype.card V := by
  classical
  refine (fnum_edgeFinset_le_iff G).1 ?_
  have := fnum_edges_le_ceil_of_hiHyp hC hϑ0 hϑ h V (FGraph.ofSimpleGraph G)
  simpa using this

/-- [s7:thmHI] + [s7:thmMainProof]: the hypothesis of Theorem HI″, for constants `C ≥ D_*/2` and
`ϑ ∈ [0,1/2)`, implies the internal main theorem `EG.Spec.MainInternal` (with the constant
`⌈max(C/(1-2ϑ), N₀/2)⌉₊`). -/
theorem mainInternal_of_hiHyp (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) : Spec.MainInternal :=
  ⟨⌈max (C / (1 - 2 * ϑ)) (N₀ / 2)⌉₊, fun V _ _ G => decomp_le_of_hiHyp hC hϑ0 hϑ h V G⟩

/-- Consistency check with `EG.Lib.Found.FnumMain`: the same conclusion via
`EG.mainInternal_of_fnum_edges_le` (the `FGraph` form of f(n) = O(n)). -/
theorem mainInternal_of_hiHyp' (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) : Spec.MainInternal :=
  mainInternal_of_fnum_edges_le _ fun n H => fnum_edges_le_ceil_of_hiHyp hC hϑ0 hϑ h (Fin n) H

/-- Fidelity check (not a manuscript statement): the hypothesis of Theorem HI″ is neither
vacuous nor stronger than the internal main theorem. `EG.Spec.MainInternal` holds iff there are
constants `D_*, N₀, C, ϑ` with `C ≥ D_*/2`, `ϑ ∈ [0,1/2)` and `HIHyp D_* N₀ C ϑ` (for `→`, take
`k = 0` quotients and `C = c`). -/
theorem mainInternal_iff_exists_hiHyp :
    Spec.MainInternal ↔ ∃ Dstar N₀ C ϑ : ℝ, Dstar / 2 ≤ C ∧ 0 ≤ ϑ ∧ ϑ < 1 / 2 ∧
      Spec.HIHyp Dstar N₀ C ϑ := by
  refine ⟨fun hM => ?_, fun ⟨Dstar, N₀, C, ϑ, hC, hϑ0, hϑ, h⟩ =>
    mainInternal_of_hiHyp hC hϑ0 hϑ h⟩
  obtain ⟨c, hc⟩ := fnum_edges_le_of_mainInternal.{0} hM
  refine ⟨0, 0, c, 0, by simp, le_rfl, by norm_num, fun V G _ _ _ => ?_⟩
  refine ⟨0, fun _ => PEmpty, fun i => i.elim0, ?_, by simp⟩
  simpa using (show (fnum G.edges : ℝ) ≤ c * G.card by exact_mod_cast hc V G)

end EG
