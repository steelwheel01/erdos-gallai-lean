import EG.Spec.Chain.Lost
import EG.Spec.Chain.MixC
import EG.Spec.Chain.JPlusV
import EG.Spec.Chain.CONCL
import EG.Lib.Stage1.Law
import EG.Lib.Chain.JSet
import EG.Lib.Chain.JConsumer
import EG.Lib.Chain.Lending
import EG.Lib.Prob.Basic
import EG.Lib.Found.Fnum

/-! Cheap non-vacuity checks for the new s6b Specs (`EG/Spec/Chain/{Lost,MixC,JPlusV}.lean`;
`formal/work/p2s/s6b.md`).

* `JplusVStatement` (s6:lemJplus (v)) is proved outright from the stage-1 law API (so it is true,
  not merely well typed);
* `MixCConcStatement` follows from the existing Spec `ConcLSumStatement` (s6:thmCONCL (iv)), as the
  manuscript says ("by Theorem s6:thmCONCL(iv)");
* "for every stage-1 outcome" ranges over a nonempty set; J-consumers exist; the per-round bound
  hypothesis of `MixCStatement` is satisfiable (by the consumer's own output lengths); the
  `JPlusProps` part of its conclusion and `IsDecomp` of an empty edge set are satisfiable;
* `Lost_Z = ∅` and `Lost_l = ∅` for `l ≤ 2`, so (K6) is trivial there (consistent with "for every
  round `l`").

Not checked here: satisfiability of `RunHyp` (a valid run with `d_1 ≥ D_*` under Γ1 is far beyond
a concrete example; as in `EGTest/Spec_s5.lean`).
-/

open EG EG.HB EG.Chain EG.Quot EG.Stage1

section

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- [s6:lemJplus] (v) holds: the per-edge colour triples are mutually independent under the
stage-1 law (the blocks `{(1a, Y, e)}` of coordinates are pairwise disjoint). -/
example : EG.Spec.JplusVStatement.{0} := by
  intro V _ G run
  refine iIndepFun_of_dependsOn G run (fun p => {Sum.inl p}) ?_ _ ?_
  · intro p q hpq
    simp only [Set.disjoint_singleton, ne_eq, Sum.inl.injEq]
    exact hpq
  · intro p ω ω' h
    cases ω; cases ω'
    exact h _ (Set.mem_singleton _)

/-- "for every stage-1 outcome" is not vacuous. -/
example : (Stage1.law G run).supp.Nonempty := FinDist.supp_nonempty _

end

/-- [s6:thmMIXC] (c), last sentence, follows from [s6:thmCONCL] (iv) (the existing Spec). -/
example (h : EG.Spec.ConcLSumStatement.{0}) : EG.Spec.MixCConcStatement.{0} := by
  intro V _ G N0 Dstar run δ hR hδ
  have h1 := h V G Dstar run hR.1.1 hR.2.2.2.2.2 δ hδ
  nlinarith

section

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V) (δ : Designation V)
  (ω : Outcome G run)

/-- The J-consumer quantifier of MIX-C is not vacuous. -/
example : Nonempty (JConsumer run G δ (stageOf ω)) := nonempty_jConsumer run G δ (stageOf ω)

/-- The per-round bound hypothesis of `MixCStatement` is satisfiable for every consumer (take the
consumer's own output lengths; this is the literal `Σ_l |Obj_l|`). -/
example (C : JConsumer run G δ (stageOf ω)) :
    ∃ b : ℕ → Finset (Sym2 V) → ℝ, ∀ l J, 3 ≤ l → l ≤ run.R →
      JPlusProps run G δ (stageOf ω) l J → ((C.out l J).1.length : ℝ) ≤ b l J :=
  ⟨fun l J => ((C.out l J).1.length : ℝ), fun _ _ _ _ _ => le_rfl⟩

/-- The `JPlusProps` part of the MIX-C conclusion is satisfiable. -/
example : ∃ Js : ℕ → Finset (Sym2 V),
    ∀ l ∈ Finset.Icc 3 run.R, JPlusProps run G δ (stageOf ω) l (Js l) :=
  ⟨fun _ => ∅, fun l _ => jPlusProps_empty run G δ (stageOf ω) l⟩

/-- `IsDecomp` of the (empty) edge set of an edgeless graph is satisfiable. -/
example : IsDecomp (∅ : Set (Sym2 V)) ([] : List (Obj V)) := isDecomp_nil

/-- For `l ≤ 2` there are no lost ports, so (K6) of s6:lemLost is trivial there. -/
example (l : ℕ) (hl : l ≤ 2) : lostRound run G δ (stageOf ω) l = ∅ :=
  lostRound_of_le_two run G δ (stageOf ω) hl

end
