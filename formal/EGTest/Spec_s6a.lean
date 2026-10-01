import EGTest.Gate
import EGTest.Chain
import EGTest.HB
import EG.Spec.Chain.Gate
import EG.Spec.Chain.MED
import EG.Spec.Chain.EqLpt
import EG.Spec.Chain.PAR
import EG.Spec.Chain.HCCP
import EG.Spec.Chain.CONC
import EG.Spec.Chain.ConcTower
import EG.Lib.Found.Components
import EG.Lib.Found.Fnum
import EG.Lib.Found.Gamma
import EG.Lib.Chain.Design

/-! Cheap non-vacuity checks for the Specs of chunk s6a (`formal/work/p2s/s6a.md`). Every node of
the chunk already had a Spec (probe units P1b, P2E, P3B); no Spec is new. The checks below show
that the hypotheses of each `…Statement` are jointly satisfiable, mostly on the small instances of
`EGTest.Gate` (triangle), `EGTest.Chain` (clusters `K5`, `C01`; loads `Φ3`; HCC-P systems `S1`,
`S2`) and `EGTest.HB` (runs on `E2`, `K3`), plus two new degenerate HCC-P systems (`k = 3`, and a
union of two systems).

Not checked (as in `EGTest/ProbeP3B.lean`): a valid run with a standalone pre-part (`a ∈ Std_r`)
does not exist at toy size, so the hypotheses of `ConcIStatement` / `ConcIIStatement` are checked
only up to `run.Valid` and `IsDesignation`; the Γ-statements are checked on the run without rounds. -/

namespace EGTest.Spec_s6a

open EG EG.Chain

/-! ## [s6:lemGATE]: `GateStatement`, `GatePreciseStatement` -/

/-- The hypotheses of GATE hold for the cyclically oriented triangle with `𝒲` one arc. -/
example : EGTest.F3 ⊆ EGTest.K3.edges ∧ IsOrientation EGTest.F3 EGTest.A3 ∧
    IsBalanced EGTest.A3 ∧ EGTest.W3 ⊆ EGTest.A3 ∧ IsAcyclic (EGTest.A3 \ EGTest.W3) :=
  ⟨EGTest.F3_sub, EGTest.A3_orientation, EGTest.A3_balanced, EGTest.W3_sub,
    EGTest.A3_sdiff_W3_acyclic⟩

/-! ## [s6:lemMED]: `MedStatement`, `MedExcStatement` -/

open EGTest.Chain in
/-- The hypotheses of MED (a) (`K5` parity-clean, rank injective on the ports) and of MED (b)
(`O5` admissible) hold. -/
example : K5.ParityClean ∧ Set.InjOn (fun v : Fin 5 => v.val) (K5.ports : Set (Fin 5)) ∧
    K5.IsAdmissible O5 :=
  ⟨by decide, fun _ _ _ _ h => Fin.ext h, O5_admissible⟩

/-! ## [s6:lemEQLPT]: `EqLptExistsStatement`, `EqLptStatement` -/

open EGTest.Chain in
theorem Φ3_antitone : Antitone Φ3 := by
  intro a b hab
  have h : ∀ a b : Fin 3, a ≤ b → Φ3n b ≤ Φ3n a := by decide
  exact Nat.cast_le.2 (h a b hab)

open EGTest.Chain in
/-- The hypotheses of EQ-LPT (`m = 3`, `k = 2`, loads `3, 2, 1`) and a greedy placement `σ3`. -/
example : 1 ≤ 2 ∧ 2 ≤ 3 ∧ Antitone Φ3 ∧ (∀ i, 0 ≤ Φ3 i) ∧ IsGreedyLPT Φ3 σ3 :=
  ⟨by norm_num, by norm_num, Φ3_antitone, fun _ => Nat.cast_nonneg _, σ3_greedy⟩

/-! ## [s6:lemPAR]: `ParExistsStatement`, `ParStatement` -/

/-- A single edge `01`, sides `{0}` and `{1}`. -/
def E01 : Finset (Sym2 (Fin 2)) := {s(0, 1)}

theorem E01_mk (a b : Fin 2) :
    (edgeGraph E01).connectedComponentMk a = (edgeGraph E01).connectedComponentMk b := by
  have hadj : (edgeGraph E01).Adj 0 1 := edgeGraph_adj.2 ⟨by decide, by decide⟩
  rw [SimpleGraph.ConnectedComponent.eq]
  fin_cases a <;> fin_cases b
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

/-- The hypotheses of PAR hold for `E01` with sides `{0}`, `{1}`, and `J' = E01` (the pendant
edge of the one odd component) is an admissible choice. -/
example : Disjoint ({0} : Finset (Fin 2)) {1} ∧
    (∀ e ∈ E01, ∃ a ∈ ({0} : Finset (Fin 2)), ∃ b ∈ ({1} : Finset (Fin 2)), e = s(a, b)) ∧
    IsParChoice E01 E01 := by
  refine ⟨by decide, by decide, Finset.Subset.refl _, fun C hC => ?_, fun e he => Or.inr ?_⟩
  · obtain ⟨v, -, rfl⟩ := mem_edgeComps.1 hC
    have hc : compEdges E01 ((edgeGraph E01).connectedComponentMk v) = E01 := by
      ext e
      rw [mem_compEdges]
      exact ⟨fun h => h.1, fun h => ⟨h, fun w _ => E01_mk w v⟩⟩
    rw [hc, Finset.inter_self]
    decide
  · have he' : e = s(0, 1) := Finset.mem_singleton.1 he
    subst he'
    exact ⟨by decide, 0, Sym2.mem_mk_left _ _, by decide⟩

/-! ## [s6:lemHCCP]: `HccpStatement` -/

/-- The hypotheses of HCC-P hold for the systems `S1` (`k = 1`, a triangle) and `S2` (`k = 2`, a
4-cycle) of `EGTest.Chain`. -/
example : EGTest.Chain.S1.Valid EGTest.Chain.G3 ∧ EGTest.Chain.S2.Valid EGTest.Chain.G4 :=
  ⟨EGTest.Chain.S1_valid, EGTest.Chain.S2_valid⟩

/-- The empty system with `k` layers (no clusters, empty junction sets and path families). -/
def emptySys (V : Type) (k : ℕ) : HccpData V where
  k := k
  N := 0
  K := Fin.elim0
  O := Fin.elim0
  lay := Fin.elim0
  T := fun _ => ∅
  pad := fun _ => 0
  P := fun _ => []

theorem emptySys_layP {V : Type} [DecidableEq V] (k : ℕ) (j : Fin k) :
    (emptySys V k).layP j = ∅ := by
  ext u
  simp only [HccpData.layP, Finset.mem_biUnion, Finset.notMem_empty, iff_false]
  rintro ⟨i, -, -⟩
  exact i.elim0

theorem emptySys_pexc {V : Type} [DecidableEq V] (k : ℕ) (u : V) : (emptySys V k).pexc u = 0 :=
  Finset.sum_eq_zero fun i _ => i.elim0

/-- The empty system is valid for every `k ≥ 1` (degenerate; with `k = 3` it shows that the case
`max(3,k) = k` of the length bound has satisfiable hypotheses). -/
theorem emptySys_valid {V : Type} [DecidableEq V] (G : FGraph V) (k : ℕ) (hk : 1 ≤ k) :
    (emptySys V k).Valid G where
  k_pos := hk
  adm i := i.elim0
  beads_G i := i.elim0
  T_disj _ _ _ := Finset.disjoint_empty_left _
  pad_k1 _ _ _ _ := rfl
  D_KK i := i.elim0
  D_KT i := i.elim0
  parityClean i := i.elim0
  path_G _ _ hp := absurd hp List.not_mem_nil
  path_ends _ _ hp := absurd hp List.not_mem_nil
  path_T _ _ hp := absurd hp List.not_mem_nil
  starts _ _ _ := by rw [HccpData.demMinus, emptySys_pexc]; simp [emptySys]
  ends _ _ _ := by rw [HccpData.demPlus, emptySys_pexc]; simp [emptySys]
  path_edisj _ := List.Pairwise.nil
  pp_disj _ _ _ := by simp [HccpData.pathEdges, emptySys]
  pb_disj _ i := i.elim0
  bb_disj i := i.elim0

example : (emptySys (Fin 3) 3).Valid EGTest.Chain.G3 ∧ max 3 (emptySys (Fin 3) 3).k = 3 :=
  ⟨emptySys_valid _ 3 (by norm_num), rfl⟩

/-! ## [s6:lemHCCglob]: `HccUnionStatement`, `HccGlobStatement` -/

/-- The hypotheses of the first paragraph (one set, the triangle's empty sub-case: `E_0 = ∅`,
decomposed by the empty list). -/
example : (∀ i : Fin 1, (fun _ => (∅ : Finset (Sym2 (Fin 3)))) i ⊆ EGTest.Chain.G3.edges) ∧
    (∀ i i' : Fin 1, i ≠ i' → Disjoint ((fun _ => (∅ : Finset (Sym2 (Fin 3)))) i)
      ((fun _ => (∅ : Finset (Sym2 (Fin 3)))) i')) ∧
    ∀ i : Fin 1, IsDecomp (((fun _ => (∅ : Finset (Sym2 (Fin 3)))) i : Finset (Sym2 (Fin 3))) :
      Set (Sym2 (Fin 3))) ([] : List (Obj (Fin 3))) := by
  refine ⟨fun _ => Finset.empty_subset _, fun _ _ _ => Finset.disjoint_empty_left _, fun _ => ?_⟩
  simpa using (isDecomp_nil : IsDecomp (∅ : Set (Sym2 (Fin 3))) [])

/-- Two systems: `S1` (the triangle, `k = 1`) and the empty system with `k = 3`. Both are valid
and their beads and path edges are disjoint (the input-level hypothesis). -/
def Sys2 : Fin 2 → HccpData (Fin 3) := ![EGTest.Chain.S1, emptySys (Fin 3) 3]

example : (∀ s, (Sys2 s).Valid EGTest.Chain.G3) ∧
    ∀ s s', s ≠ s' → Disjoint ((Sys2 s).beads ∪ (Sys2 s).allPathEdges)
      ((Sys2 s').beads ∪ (Sys2 s').allPathEdges) := by
  have h1 : (emptySys (Fin 3) 3).beads ∪ (emptySys (Fin 3) 3).allPathEdges = ∅ := by
    ext e
    simp [HccpData.beads, HccpData.allPathEdges, HccpData.pathEdges, emptySys]
  refine ⟨fun s => ?_, fun s s' hss' => ?_⟩
  · fin_cases s
    · exact EGTest.Chain.S1_valid
    · exact emptySys_valid _ 3 (by norm_num)
  · fin_cases s <;> fin_cases s'
    · exact absurd rfl hss'
    · show Disjoint _ ((emptySys (Fin 3) 3).beads ∪ (emptySys (Fin 3) 3).allPathEdges)
      rw [h1]; exact Finset.disjoint_empty_right _
    · show Disjoint ((emptySys (Fin 3) 3).beads ∪ (emptySys (Fin 3) 3).allPathEdges) _
      rw [h1]; exact Finset.disjoint_empty_left _
    · exact absurd rfl hss'

/-! ## [s6:thmCONC], (s6:eqTowerHalf), (s6:eqTowerEnd) -/

open EG.HB in
/-- `ConcIStatement`, `ConcIIStatement` (hypotheses up to `a ∈ Std_r`): the one-round run `run1`
on `K3` is valid, and a designation exists. -/
example : EGTest.HB.run1.Valid EGTest.HB.K3 1 ∧
    ∃ δ : Designation (Fin 3), IsDesignation EGTest.HB.run1 EGTest.HB.K3 δ :=
  ⟨EGTest.HB.run1_valid, exists_isDesignation _ _⟩

open EG.HB in
/-- `ConcIIIStatement`, `ConcTauSumStatement`, `ConcDStarSumStatement`, `TowerHalfStatement`
(hypotheses): `Gamma1core D`, the run without rounds on `E2` (valid for every such `D`), and a
designation. -/
example : ∃ D : ℝ, Gamma1core D ∧ (⟨[]⟩ : Run (Fin 2)).Valid EGTest.HB.E2 D ∧
    ∃ δ : Designation (Fin 2), IsDesignation (⟨[]⟩ : Run (Fin 2)) EGTest.HB.E2 δ := by
  obtain ⟨D, hD⟩ := exists_gamma1core
  refine ⟨D, hD, (Run.valid_nil_iff EGTest.HB.E2 D).2 ?_, exists_isDesignation _ _⟩
  have hE : EGTest.HB.E2.edges = ∅ := by decide
  have h2 : (2 : ℝ) < D := hD.1
  simp only [Round.d, hE, Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
  linarith

/-- `TowerEndStatement`, `KStarStatement` (hypotheses): `Gamma1core D` and `D ≤ d`. -/
example : ∃ D d : ℝ, Gamma1core D ∧ D ≤ d := by
  obtain ⟨D, hD⟩ := exists_gamma1core
  exact ⟨D, D, hD, le_rfl⟩

end EGTest.Spec_s6a
