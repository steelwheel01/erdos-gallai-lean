import EG.Spec.Light.Setting
import EG.Spec.Light.Zones
import EG.Spec.Light.Stages
import EG.Spec.Light.E1
import EG.Spec.Light.Expect
import EG.Spec.Light.Child
import EG.Spec.Light.Parent
import EG.Spec.Light.Demoted
import EG.Spec.Light.KRED
import EG.Lib.Light.Stages
import EG.Lib.Light.Constants
import EG.Lib.Prob.Basic
import EG.Lib.Found.Fnum

/-! Cheap non-vacuity checks for the s5 Specs (`EG/Spec/Light/*.lean`; `formal/work/p2s/s5.md`).

* the two limit statements are the existing API lemmas `tendsto_epsU`, `tendsto_epsChain`;
* "for every stage-1 outcome" is not vacuous: the support of `Stage1.law G run` is nonempty;
* the K-RED hypothesis `LentExtHyp` holds for the empty family;
* the conclusion bodies of lemChild (at `H_0 = ∅`) and lemParent (for empty arc systems) are
  satisfiable, so neither conclusion is contradictory by encoding.

Not checked here: satisfiability of `RunHyp` (it needs `D_*` satisfying Γ1 and a valid run with
`d_1 ≥ D_*`, far beyond a concrete example; `Gamma1core` is satisfiable, `EG.exists_gamma1core`).
-/

open EG EG.HB EG.Stage1 EG.Light

example : EG.Spec.LemExpectLimitStatement := tendsto_epsU

example : EG.Spec.LemParentLimitStatement := tendsto_epsChain

section

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- The quantifier `∀ ω ∈ (Stage1.law G run).supp` ranges over a nonempty set. -/
example : (Stage1.law G run).supp.Nonempty := FinDist.supp_nonempty _

/-- The empty family satisfies the hypothesis of Lemma K-RED. -/
example (ω : Outcome G run) : LentExtHyp ω (fun _ => ∅) := by
  intro Y _
  exact ⟨Finset.empty_subset _, fun _ => rfl⟩

/-- The body of the lemChild conclusion is satisfiable (at `H_0 = ∅`, no objects, no arcs). -/
example (ω : Outcome G run) (Z : PartId) :
    ∃ (Hobj : Finset (Sym2 V)) (Dobj : List (Obj V)) (as : List (Arc V)),
      Disjoint Hobj (arcEdges as) ∧ Hobj ∪ arcEdges as = ∅ ∧
      IsDecomp (Hobj : Set (Sym2 V)) Dobj ∧ Dobj.length ≤ 369 * (Pl ω Z).card ∧
      ArcSys ω Z ∅ as :=
  ⟨∅, [], [], by simp, by simp [arcEdges], by simpa using isDecomp_nil, by simp,
    ArcSys.nil ω Z ∅⟩

/-- The body of the lemParent conclusion is satisfiable for empty arc systems (no objects, no
lent edges, `cap_l = 0`). -/
example (ω : Outcome G run) (l : ℕ) :
    ∃ (LentU : Fin 4 → Finset (Sym2 V)) (D : Fin 4 → List (Obj V)) (cap : ℕ),
      (∀ c, Disjoint (LentU c) (bundleEdges ω l (fun _ => []) c)) ∧
      (∀ c, IsDecomp ((bundleEdges ω l (fun _ => []) c ∪ LentU c : Finset (Sym2 V)) :
        Set (Sym2 V)) (D c)) ∧
      (∀ c, LentU c ⊆ lentUAvail ω l c) ∧
      (∀ c, ∀ Y ∈ goodParents ω l, ∀ σ < Tslot G run Y, ∀ e ∈ LentU c,
        e ∈ (LU G run Y (ω.colAt Y) l c σ).edges →
          ∃ p : List V, IsConnector ω l c Y σ p ∧ e ∈ walkEdges p) ∧
      (cap : ℝ) ≤ 14 * ((Jbar G run l : ℝ) + 1) * (G.card : ℝ) /
        (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 ∧
      ((∑ c, (D c).length : ℕ) : ℝ) ≤
        4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
          (run.nuAnc G l : ℝ) + cap ∧
      (∀ c c', c ≠ c' → Disjoint (LentU c) (LentU c')) := by
  have hB : ∀ c, bundleEdges ω l (fun _ => ([] : List (Arc V))) c = ∅ := by
    intro c
    ext e
    simp [mem_bundleEdges]
  refine ⟨fun _ => ∅, fun _ => [], 0, fun c => by simp, fun c => ?_, fun c => by simp,
    fun c Y _ σ _ e he => by simp at he, by simp; positivity, by simp; positivity,
    fun c c' _ => by simp⟩
  rw [hB c]
  simpa using isDecomp_nil

end
