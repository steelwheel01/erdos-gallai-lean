module

public import EG.Spec.Main
public import EGCheck.BridgeLemmas
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Bridge core: internal main theorem ⇒ upstream statement, FC-184-free

The comparator-compatible half of the bridge (trust audits of 2026-09-26; PLAN_FORMALIZATION.md
§3, design decisions 1, 8). **Does not import `FormalConjectures.ErdosProblems.«184»`**, so that
comparator's `Solution` module (`formal/comparator/Solution.lean`), which restates
`Erdos184.IsCycleOrEdge` and `Erdos184.erdos_184` verbatim, can import it.

`of_mainInternal_unfolded` has the statement of the upstream `Erdos184.erdos_184` with
`IsCycleOrEdge H.coe` replaced by the body of its definition, for **arbitrary** instances
`i₁ : H.coe.LocallyFinite` and `i₂ : Fintype H.coe.edgeSet` (the upstream body uses classical
instances; quantifying over all of them makes the result independent of which ones elaboration
picked). It therefore implies the upstream statement by unfolding `IsCycleOrEdge` and
instantiating `i₁`, `i₂`; the wrapper `EGCheck/Bridge.lean` does this in the kernel against the
imported upstream constant, and `comparator/Solution.lean` against its verbatim restatement.

Proof: given `G` on `V : Type u`, take `e := Fintype.equivFin V`, apply the hypothesis to the copy
`G.comap e.symm` on `Fin n`, map the objects back along `e.symm` (`isDecomp_comap_symm`), and
convert the list of objects into a `Finset G.Subgraph` (`exists_finset_of_isDecomp`), with
`f := fun n ↦ c * n`.
-/

public section

namespace EGCheck.Bridge

open Filter SimpleGraph

universe u

/-- The internal main theorem implies the upstream statement `Erdos184.erdos_184` with
`IsCycleOrEdge` unfolded (for all instances), with `f n = c * n`. -/
theorem of_mainInternal_unfolded (h : EG.Spec.MainInternal) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, ∀ (i₁ : H.coe.LocallyFinite) (i₂ : Fintype H.coe.edgeSet),
          (H.coe.Connected ∧ @IsRegularOfDegree _ H.coe i₁ 2) ∨
            (@edgeFinset _ H.coe i₂).card = 1) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun n : ℕ => (c : ℝ) * (n : ℝ), (Asymptotics.isBigO_refl _ _).const_mul_left _, ?_⟩
  intro V _ _ G
  obtain ⟨D₀, hD₀, hlen⟩ := hc (Fin (Fintype.card V)) (G.comap (Fintype.equivFin V).symm)
  obtain ⟨D, hcyc, hdec, hcard⟩ :=
    exists_finset_of_isDecomp (isDecomp_comap_symm (Fintype.equivFin V) G hD₀)
  refine ⟨D, hcyc, hdec, ?_⟩
  rw [List.length_map] at hcard
  rw [Fintype.card_fin] at hlen
  show (D.card : ℝ) ≤ (c : ℝ) * (Fintype.card V : ℝ)
  exact_mod_cast hcard.trans hlen

end EGCheck.Bridge
