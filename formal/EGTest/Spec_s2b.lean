import EG.Spec.HB.Structure
import EG.Spec.HB.OVRun
import EG.Spec.HB.DegRec
import EG.Spec.HB.Exists
import EG.Spec.HB.Lacunary
import EG.Spec.HB.Tower
import EG.Spec.HB.Parentless
import EG.Lib.Found.Gamma
import EGTest.HB

/-! Cheap non-vacuity checks for the new s2b Specs (`EG/Spec/HB/{Structure, OVRun, DegRec,
Exists, Lacunary, Tower, Parentless}.lean`; `formal/work/p2s/s2b.md`).

* `Gamma1core` (hypothesis of the Γ1-statements) and `Gamma2a` are satisfiable.
* `Run.Valid` is satisfiable with `R = 1` (`EGTest.HB.run1_valid`, a run on `K₃` with
  `D_* = 1`), so the round quantifiers of the run-level statements are not empty; the run has
  light parts, so the quantifiers of `ParentlessCountStatement` are not empty either.
* `RunTerminatesStatement`: its hypothesis on the choice list is satisfiable by a list of length
  `1` (the same run).
* `LacunarySeqStatement`, `LacunaryIIStatement`, `LacunaryRunStatement`: the hypotheses on `F` and
  on the sequence are satisfiable (`F = 0`, a constant sequence `λ_r = 2` with `R = 2`).
* `LacunaryExamplesStatement`: the disjunction on `η` is satisfiable.

Not checked here (as in `Spec_s2a.lean`): the joint satisfiability of `Γ1`/`Γ2(a)` with a valid
run or round with `d ≥ D_*` (it needs a graph of average degree at least `2^{117}` or
`2^{2^{256}}` with a valid round on it, which is s2:propExists itself; no concrete example is
feasible). The statements carrying these hypotheses (`OVRoundStatement`, `DegRec*`,
`RoundTauTermStatement`, `RoundExistsStatement`, `Tower*`, `Lacunary{II,Run}Statement`,
`AdmissibleParentStatement`, `StructureExp/PartitionStatement`) are non-vacuous exactly when
`ExistsRunStatement` / `RoundExistsStatement` hold.
-/

open EG EG.HB

namespace EGTest.Spec_s2b

/-- `Γ1` (a)–(e) is satisfiable. -/
example : ∃ D : ℝ, Gamma1core D := exists_gamma1core

/-- `Γ2(a)` is satisfiable. -/
example : Gamma2a ((2 : ℝ) ^ 117) := le_rfl

/-- `Run.Valid` is satisfiable with one round. -/
example : ∃ (G : FGraph (Fin 3)) (run : Run (Fin 3)) (Dstar : ℝ), run.Valid G Dstar ∧ run.R = 1 :=
  ⟨_, _, _, EGTest.HB.run1_valid, rfl⟩

/-- The run of `EGTest.HB` has a light part (so `lightParts` in `ParentlessCountStatement` and
`AdmissibleParentStatement` can be non-empty). -/
example : (1, [false]) ∈ EGTest.HB.run1.lightParts EGTest.HB.K3 := by
  rw [Run.mem_lightParts]
  refine ⟨?_, ?_⟩
  · rw [Run.prePartAddrs_of_isRound EGTest.HB.run1 EGTest.HB.K3 ⟨le_rfl, le_rfl⟩, Run.graph_one]
    change [false] ∈ Round.prePartAddrs EGTest.HB.K3 EGTest.HB.c1
    rw [EGTest.HB.prePartAddrs_eq, EGTest.HB.tree0_leafAddrs]
    decide
  · change Round.isLight (EGTest.HB.run1.graph EGTest.HB.K3 1) EGTest.HB.c1 [false]
    rw [Run.graph_one]
    exact EGTest.HB.isLight_c1 _

/-- The hypothesis of `RunTerminatesStatement` on the choice list is satisfiable by a list of
length `1`. -/
example : ∃ (G : FGraph (Fin 3)) (cs : List (RoundChoice (Fin 3))) (Dstar : ℝ),
    cs.length = 1 ∧ ∀ l ∈ Finset.Icc 1 cs.length, Dstar ≤ (Run.mk cs).d G l ∧
      Round.Valid ((Run.mk cs).graph G l) ((Run.mk cs).choice l) :=
  ⟨EGTest.HB.K3, [EGTest.HB.c1], 1, rfl, EGTest.HB.run1_valid.1⟩

/-- The hypotheses of `LacunarySeqStatement` are satisfiable (`x_0 = 0`, `F = 0`, `λ_r = 2`,
`R = 2`). -/
example : ∃ (x0 : ℝ) (F : ℝ → ℝ) (lam : ℕ → ℝ) (R : ℕ), 1 ≤ R ∧
    (∀ x : ℝ, x0 ≤ x → 0 ≤ F x) ∧ HypH x0 F ∧ (∀ r ∈ Finset.Icc 1 R, x0 ≤ lam r) ∧
    (∀ r ∈ Finset.Ico 1 R, (2 : ℝ) ^ (lam (r + 1) / (Aexp : ℝ)) ≤ lam r) := by
  refine ⟨0, fun _ => 0, fun _ => 2, 2, by norm_num, fun _ _ => le_rfl, ?_, ?_, ?_⟩
  · intro x y _ _ _; simp
  · intro r _; norm_num
  · intro r _
    calc (2 : ℝ) ^ ((2 : ℝ) / (Aexp : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [div_le_one (by simp [Aexp])]
          norm_num [Aexp]
      _ = 2 := Real.rpow_one 2

/-- The hypotheses on `F` of `LacunaryIIStatement` (and of `LacunaryRunStatement`) are satisfiable
(`F = 0`), for every `D_*`. -/
example (Dstar : ℝ) : ∃ F : ℝ → ℝ, (∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ F x) ∧
    AntitoneOn F (Set.Ici (Real.logb 2 Dstar)) ∧
    (∀ x : ℝ, Real.logb 2 Dstar ≤ x → F ((2 : ℝ) ^ (x / (Aexp : ℝ))) ≤ F x / 2) ∧
    HypH (Real.logb 2 Dstar) F :=
  ⟨fun _ => 0, fun _ _ => le_rfl, fun _ _ _ _ _ => le_rfl, fun _ _ => by simp,
    fun _ _ _ _ _ => by simp⟩

/-- The disjunction on `η` in `LacunaryExamplesStatement` is satisfiable. -/
example : ∃ η : ℝ → ℝ,
    η = (fun x => x) ∨ η = (fun x => x ^ (1 / 2 : ℝ)) ∨ η = (fun x => Real.logb 2 x) :=
  ⟨_, Or.inl rfl⟩

/-- The statements elaborate as propositions (the conjunctions of the whole lemmas). -/
example : Prop := EG.Spec.TowerStatement.{0}
example : Prop := EG.Spec.LacunaryStatement.{0}

end EGTest.Spec_s2b
