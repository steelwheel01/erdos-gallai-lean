import EGTest.Chain
import EGTest.HB
import EG.Spec.Chain.JSLC
import EG.Spec.Chain.JSLCSteps
import EG.Spec.Chain.JSLCRouting
import EG.Spec.Chain.JPlus
import EG.Spec.HB.CapPrePart
import EG.Spec.HB.StructureHY
import EG.Spec.HB.TowerBLate
import EG.Proof.Chain.JPlus
import EG.Proof.Chain.JSLCTypes
import EG.Proof.Chain.JSLCStep7
import EG.Lib.Chain.JSet
import EG.Lib.Chain.StageInst
import EG.Lib.Found.Fnum
import EG.Lib.Found.Gamma

/-! Non-vacuity and sanity checks for the statements of probe unit P2J (probe P-2, part 2; design
note `formal/work/p2b/P2J.md`).

What is checked here:
* the input hypotheses of `JSLCStatement` / `JslcStep2Statement` that do not involve the round
  structure are satisfiable for every run (a designation, coherent stage data, `B_Z = ∅`), and the
  conclusions are consistent (they hold for `B_Z = ∅` with `J = LentJS = ∅`, `D = []`);
* the refutation target of probe P-2 (two `J^hub` edges of one class at one hub in one round) is
  exactly what the aggregated (J1) conjunct excludes;
* the pre-routing systems of `EG/Defs/Probe/P2J/PreSystem.lean` on the HCC-P test systems `S1`
  (`k = 1`) and `S2` (`k = 2`) of `EGTest.Chain`: `PreValid`, junction occurrences, the hypotheses
  of `JslcPairsBalanceStatement`, `JslcPairsDistinctStatement`, `JslcJointMultStatement` and
  their conclusions on the instances; and that the cherry-count hypothesis of
  `JslcJointMultStatement` is needed (three cherry systems through one port exceed `2M − 2`);
* the hypotheses of the declared input `CapPrePartStatement`, of `StructureHYStatement` (proved in
  fix round 1) and of
  `JplusFactsStatement` are satisfiable (the run without rounds).
Not checked (documented in the design note): hypotheses that need a valid run with `R ≥ 3` rounds
under `Γ1` and `n ≥ N_0` (`RunHyp`, `3 ≤ l ≤ R`, `TowerBLateStatement`): such runs need
`d_1 ≥ D_* ≥ 2^{2^{256}}` and are not buildable at toy size (s2:propExists). -/

namespace EGTest.ProbeP2J

open EG EG.HB EG.Chain EGTest.Chain

/-! ## Helpers: `M_l ≥ 1`, `jBound ≥ 0` -/

theorem one_le_M {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (l : ℕ) :
    1 ≤ run.M G l := by
  unfold Run.M MOf
  refine Nat.one_le_iff_ne_zero.2 fun h => ?_
  rw [Nat.ceil_eq_zero] at h
  have h40 : (0 : ℝ) < 2 ^ 40 := by positivity
  linarith [le_max_left (2 ^ 40 : ℝ)
    (2 ^ 16 * TOf (run.d G l) * Real.logb 2 (TOf (run.d G l)) ^ 4)]

theorem jBound_nonneg {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V)
    (δ : Designation V) (S : StageData V) (l : ℕ) : 0 ≤ jBound run G δ S l := by
  have hM : (0 : ℝ) ≤ (run.M G l : ℝ) - 1 :=
    sub_nonneg.2 (by exact_mod_cast one_le_M run G l)
  unfold jBound
  refine add_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    (Finset.sum_nonneg fun a _ => add_nonneg (add_nonneg
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (mul_nonneg hM (Nat.cast_nonneg _)))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)))

/-! ## `JSLCStatement`: inputs and a consistency check -/

section JSLC

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V) (δ : Designation V)
  (S : StageData V) (l : ℕ)

/-- A designation and coherent stage data exist for every run (the hypotheses
`IsDesignation run G δ`, `S.Coherent run G` of `JSLCStatement` are jointly satisfiable). -/
example : (∃ δ : Designation V, IsDesignation run G δ) ∧ ∃ S : StageData V, S.Coherent run G :=
  ⟨exists_isDesignation run G, exists_coherent run G⟩

/-- The input condition of `JSLCStatement` holds for `B_Z = ∅`. -/
example : ∀ a ∈ run.Std G l, (∅ : Finset (Sym2 V)) ⊆ run.E G l a ∧
    ∀ e ∈ (∅ : Finset (Sym2 V)), ∃ u ∈ qs run G δ S l a, u ∈ e :=
  fun _ _ => ⟨Finset.empty_subset _, fun _ he => absurd he (Finset.notMem_empty _)⟩

open Classical in
/-- Consistency of the conclusion of `JSLCStatement`: for `B_Z = ∅` it holds with
`J = LentJS = ∅`, `D = []` (for every run, designation, stage data and round). -/
example : ∃ (J LentJS : Finset (Sym2 V)) (D : List (Obj V)),
      J ⊆ (run.Std G l).biUnion (fun _ => (∅ : Finset (Sym2 V))) ∧
      LentJS ⊆ (lendGoodAnc run G S l).biUnion
        (fun Y => (Finset.range (Stage1.KJS G run l)).biUnion (S.ljs Y l)) ∧
      IsDecomp ((((run.Std G l).biUnion (fun _ => (∅ : Finset (Sym2 V))) ∪ LentJS) \ J :
        Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      (∀ o ∈ D, ∃ c : List V, o = Obj.cycle c) ∧
      (D.length : ℝ) ≤ 126 * (G.card : ℝ) / (run.M G l : ℝ) +
        1.5 * ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l),
          (mY run G δ Y l : ℝ) ∧
      (∀ o ∈ D, ∃ Y ∈ run.ancestors G, ∀ e ∈ o.edges,
        e ∈ (run.Std G l).biUnion (fun _ => (∅ : Finset (Sym2 V))) ∨
          ∃ j < Stage1.KJS G run l, e ∈ S.ljs Y l j) ∧
      (J.card : ℝ) ≤ jBound run G δ S l ∧
      JPlusProps run G δ S l J := by
  refine ⟨∅, ∅, [], Finset.empty_subset _, Finset.empty_subset _, ?_, by simp, ?_, by simp,
    by simpa using jBound_nonneg run G δ S l, jPlusProps_empty run G δ S l⟩
  · simpa using (isDecomp_nil : IsDecomp (∅ : Set (Sym2 V)) [])
  · simp only [List.length_nil, Nat.cast_zero]
    have h1 : (0 : ℝ) ≤ 126 * (G.card : ℝ) / (run.M G l : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l),
        (mY run G δ Y l : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    linarith

open Classical in
/-- Consistency of the conclusion of `JslcStep2Statement`: for `B_Z = ∅` it holds with
`J = ∅`, `R_Y = ∅`. -/
example : ∃ (J : Finset (Sym2 V)) (R : PartId → Finset (Sym2 V)),
      J ⊆ (run.Std G l).biUnion (fun _ => (∅ : Finset (Sym2 V))) ∧
      (∀ Y, R Y ⊆ (run.Std G l).biUnion (fun _ => (∅ : Finset (Sym2 V)))) ∧
      (∀ e ∈ (run.Std G l).biUnion (fun _ => (∅ : Finset (Sym2 V))), e ∈ J ∨ ∃ Y, e ∈ R Y) ∧
      (∀ Y, Disjoint J (R Y)) ∧
      (∀ Y Y', Y ≠ Y' → Disjoint (R Y) (R Y')) ∧
      (∀ Y, ∀ e ∈ R Y, ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
        ∃ h u, e = s(h, u) ∧ u ∈ qs run G δ S l a ∧ δ l u = Y ∧ h ∉ run.ancVerts G Y) ∧
      (∀ Y, ∀ h ∉ run.ancVerts G Y, Even (degE (R Y) h)) ∧
      (∀ Y, R Y ⊆ Bead run G δ Y l) ∧
      (∀ h ∈ run.D G l, ∀ Y : PartId, (J.filter (IsJhubEdge run G δ S l h Y)).card ≤ 1) ∧
      (J.card : ℝ) ≤ jBound run G δ S l ∧
      JPlusProps run G δ S l J := by
  refine ⟨∅, fun _ => ∅, Finset.empty_subset _, fun _ => Finset.empty_subset _, ?_,
    fun _ => Finset.disjoint_empty_left _, fun _ _ _ => Finset.disjoint_empty_left _,
    fun _ e he => absurd he (Finset.notMem_empty e), fun _ h _ => ?_,
    fun _ => Finset.empty_subset _, fun _ _ _ => by simp, by simpa using jBound_nonneg run G δ S l,
    jPlusProps_empty run G δ S l⟩
  · intro e he; simp at he
  · simp [degE, edgesAt]

/-! ### The refutation target of probe P-2: (J1) aggregated -/

open Classical in
/-- Two distinct `J^hub`-edges of one class `Y` at one hub `h ∈ D_l` in `J` (from the same or
from different parts of round `l`) violate the explicit (J1) conjunct of `JslcStep2Statement`
(the refutation target "two `J^hub` edges of one class at one hub in one round"). -/
theorem two_jhub_violates_J1 (J : Finset (Sym2 V)) (h : V) (Y : PartId) (e₁ e₂ : Sym2 V)
    (hne : e₁ ≠ e₂) (h1 : e₁ ∈ J) (h2 : e₂ ∈ J) (hh1 : IsJhubEdge run G δ S l h Y e₁)
    (hh2 : IsJhubEdge run G δ S l h Y e₂) :
    ¬ (J.filter (IsJhubEdge run G δ S l h Y)).card ≤ 1 := by
  intro hc
  have hsub : ({e₁, e₂} : Finset (Sym2 V)) ⊆ J.filter (IsJhubEdge run G δ S l h Y) := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Finset.mem_filter.2 ⟨h1, hh1⟩
    · rw [Finset.mem_singleton.1 he]; exact Finset.mem_filter.2 ⟨h2, hh2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  omega

/-- The same target excludes `JPlusProps` (its field `J1hub`). -/
example (J : Finset (Sym2 V)) (h : V) (hD : h ∈ run.D G l) (Y : PartId) (e₁ e₂ : Sym2 V)
    (hne : e₁ ≠ e₂) (h1 : e₁ ∈ J) (h2 : e₂ ∈ J) (hh1 : IsJhubEdge run G δ S l h Y e₁)
    (hh2 : IsJhubEdge run G δ S l h Y e₂) : ¬ JPlusProps run G δ S l J := fun hJ =>
  two_jhub_violates_J1 G run δ S l J h Y e₁ e₂ hne h1 h2 hh1 hh2 (by
    convert hJ.J1hub h hD Y)

end JSLC

/-! ## Pre-routing systems (`EG/Defs/Probe/P2J/PreSystem.lean`) on `S1`, `S2` -/

theorem S1_preValid : S1.PreValid G3 :=
  ⟨S1_valid.k_pos, S1_valid.adm, S1_valid.beads_G, S1_valid.T_disj, S1_valid.pad_k1,
    S1_valid.D_KK, S1_valid.D_KT, S1_valid.parityClean⟩

theorem S2_preValid : S2.PreValid G4 :=
  ⟨S2_valid.k_pos, S2_valid.adm, S2_valid.beads_G, S2_valid.T_disj, S2_valid.pad_k1,
    S2_valid.D_KK, S2_valid.D_KT, S2_valid.parityClean⟩

/-- Junction occurrences of `S2` (`k = 2`; layer 0: ports `0 → 1`, layer 1: ports `2 → 3`):
junction 0 pairs `1` (out-unit of layer 0) with `2` (in-unit of layer 1); junction 1 pairs `3`
with `0`; there is no junction 2. -/
example : S2.junctionOcc 0 0 = 0 ∧ S2.junctionOcc 0 1 = 1 ∧ S2.junctionOcc 0 2 = 1 ∧
    S2.junctionOcc 0 3 = 0 ∧ S2.junctionOcc 1 0 = 1 ∧ S2.junctionOcc 1 1 = 0 ∧
    S2.junctionOcc 1 2 = 0 ∧ S2.junctionOcc 1 3 = 1 ∧ S2.junctionOcc 2 1 = 0 := by
  decide

/-- Junction occurrences of `S1` (`k = 1`, one bead `0 → 1`): `X^out = {1}`, `X^in = {0}`, one
pair `(1, 0)` at junction 0. -/
example : S1.junctionOcc 0 0 = 1 ∧ S1.junctionOcc 0 1 = 1 ∧ S1.junctionOcc 0 2 = 0 ∧
    S1.junctionOcc 1 0 = 0 := by
  decide

/-- The hypotheses of `JslcPairsBalanceStatement` on `S2` (equal padded loads) and its conclusion
at both junctions. -/
example : S2.Phi S2j0 = S2.Phi S2j1 ∧
    ∑ u ∈ S2.layP S2j0, S2.demMinus u = ∑ v ∈ S2.layP (S2.succ S2j0), S2.demPlus v ∧
    ∑ u ∈ S2.layP S2j1, S2.demMinus u = ∑ v ∈ S2.layP (S2.succ S2j1), S2.demPlus v := by
  decide

/-- The hypotheses of `JslcPairsDistinctStatement` are met by an out-unit and an in-unit of `S2`
at junction 0 (`1` and `2`). -/
example : 1 ∈ S2.layP S2j0 ∧ 2 ∈ S2.layP (S2.succ S2j0) ∧ 0 < S2.demMinus 1 ∧
    0 < S2.demPlus 2 := by
  decide

/-- The hypotheses of `JslcJointMultStatement` with `M = 2` and the single cherry system `S2`
(`|exc| ≤ 1`, `pad ≤ 1` at every vertex), and its conclusion at both junctions. -/
example : (∀ u : Fin 4, (S2.pexc u).natAbs ≤ 1 ∧ S2.pad u ≤ 1) ∧
    ∀ v : Fin 4, S2.junctionOcc 0 v ≤ 2 * 2 - 2 ∧ S2.junctionOcc 1 v ≤ 2 * 2 - 2 := by
  decide

/-- The hypotheses of `JslcJointMultStatement` with `M = 2` and `S1` as the system `𝒮_0`
(`|exc| ≤ M − 1 = 1`, `pad = 0 ≤ ⌈M/2⌉ = 1`), and its conclusion. -/
example : (∀ u : Fin 3, (S1.pexc u).natAbs ≤ 2 - 1 ∧ S1.pad u ≤ ⌈((2 : ℕ) : ℝ) / 2⌉₊) ∧
    ∀ v : Fin 3, S1.junctionOcc 0 v ≤ 2 * 2 - 2 := by
  refine ⟨fun u => ⟨by revert u; decide, ?_⟩, by decide⟩
  show 0 ≤ _
  exact Nat.zero_le _

/-- The cherry-count hypothesis of `JslcJointMultStatement` ("a port lies in at most `M_l − 1`
cherry systems") is needed: three copies of the cherry system `S2` through the port `1` give
`3 > 2M − 2 = 2` junction-0 pairs at `1` for `M = 2`. -/
example : (∑ _s : Fin 3, S2.junctionOcc 0 1) = 3 ∧ ¬ (3 ≤ 2 * 2 - 2) := by
  decide

/-! ## Declared inputs and `JplusFactsStatement`: hypotheses satisfiable -/

/-- `Γ2(a)` and a valid run (the hypotheses of `CapPrePartStatement`), and a valid run (the
hypothesis of `StructureHYStatement`, `JslcTypesStatement`, `JslcStep7DisjStatement`,
`JplusFactsStatement`): the run without rounds on `E2` with `D_* = 2^{117}`. -/
example : Gamma2a (2 ^ 117) ∧ (⟨[]⟩ : Run (Fin 2)).Valid EGTest.HB.E2 (2 ^ 117) := by
  refine ⟨le_rfl, (Run.valid_nil_iff EGTest.HB.E2 _).2 ?_⟩
  have hE : EGTest.HB.E2.edges = ∅ := by decide
  simp only [Round.d, hE, Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
  positivity

/-- `JplusFactsStatement` is proved (from `EG.structureHY`, proved in fix round 1); its hypotheses
(a valid run and a designation) are satisfiable. -/
example : EG.Spec.JplusFactsStatement := EG.jplusFacts

example : ∃ δ : Designation (Fin 2), IsDesignation (⟨[]⟩ : Run (Fin 2)) EGTest.HB.E2 δ :=
  exists_isDesignation _ _

/-- `JslcTypesStatement` and `JslcStep7DisjStatement` are proved (from Lemma EL,
`EG.edgeLaminarity`, proved by unit P3A, and `EG.structureHY`, proved in fix round 1). -/
example : EG.Spec.JslcTypesStatement ∧ EG.Spec.JslcStep7DisjStatement :=
  ⟨EG.jslcTypes, EG.jslcStep7Disj⟩

end EGTest.ProbeP2J
