import EGTest.Chain
import EG.Spec.Chain.MED
import EG.Spec.Chain.EqLpt
import EG.Spec.Chain.PAR
import EG.Spec.Chain.HCCP
import EG.Spec.Chain.EngineMult
import EG.Spec.Found.EulerTreeTJoin
import EG.Proof.Chain.EngineMult
import EG.Proof.Chain.HCCUnion
import EG.Lib.Found.Components

/-! Non-vacuity checks for the statements of probe unit P2E (probe P-2, part 1; design note
`formal/work/p2b/P2E.md`): the hypotheses of `MedStatement`, `MedExcStatement`,
`EqLptStatement`, `EqLptExistsStatement`, `ParStatement`, `ParExistsStatement`,
`HccpStatement`, `HccGlobStatement`, `HccpEndMultStatement` and `EulerTreeTJoinStatement` are
satisfiable on small instances, and the conclusions hold on them where this is cheap to check.
Reuses the instances of `EGTest.Chain` (`K5`, `O5`, `Φ3`, `σ3`, the HCC-P systems `S1`, `S2`). -/

namespace EGTest.ProbeP2E

open EG EG.Chain EGTest.Chain

/-! ## MED ([s6:lemMED]) on the cluster `K5` (hub `0`, ports `1..4`) -/

/-- The hypotheses of `MedStatement` hold for `K5` and the rank `v ↦ v`. -/
example : K5.ParityClean ∧ Set.InjOn (fun v : Fin 5 => v.val) (K5.ports : Set (Fin 5)) :=
  ⟨by decide, fun _ _ _ _ h => Fin.ext h⟩

/-- Conclusion (a) on the instance: `MED(≺)` is the admissible orientation `O5`. -/
example : K5.IsAdmissible (K5.medOrient (fun v => v.val)) := by
  have h : K5.medOrient (fun v => v.val) = O5 := by decide
  rw [h]; exact O5_admissible

/-- Conclusion (b) on the instance `O5`: the port bounds, the zero sum and `Φ ≤ b`. -/
example : (∀ u ∈ K5.ports, |exc O5 u| ≤ (degE K5.beads u : ℤ) ∧
      Even (exc O5 u - (degE K5.beads u : ℤ))) ∧ ∑ u ∈ K5.ports, exc O5 u = 0 := by
  decide

example : ((K5.load O5 : ℕ) : ℝ) ≤ K5.beadCount := by
  have h1 : K5.load O5 = 2 := by decide
  rw [h1, K5.beadCount_eq_natCast (by decide)]
  have h2 : (∑ h ∈ K5.hubs, degE K5.beads h / 2 + K5.portBeads.card : ℕ) = 3 := by decide
  rw [h2]; norm_num

/-! ## A cherry (JS-LC Step 5): `u → h → u'` with `exc(u) = +1`, `exc(u') = −1`, load `1` -/

/-- The cherry `1 – 0 – 2`: hub `0`, ports `1, 2`, beads `01`, `02`. -/
def Cherry : Cluster (Fin 3) where
  hubs := {0}
  ports := {1, 2}
  beads := {s(0, 1), s(0, 2)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

/-- Its orientation `1 → 0 → 2`. -/
def OCherry : Finset (Fin 3 × Fin 3) := {(1, 0), (0, 2)}

theorem OCherry_adm : Cherry.IsAdmissible OCherry :=
  ⟨isOrientation_of (by decide) (by decide) (by decide),
    isAcyclic_of_potential (fun v : Fin 3 => (![1, 0, 2] v : ℕ)) (by decide), by decide⟩

example : Cherry.ParityClean ∧ exc OCherry 1 = 1 ∧ exc OCherry 2 = -1 ∧ Cherry.load OCherry = 1 :=
  by decide

/-! ## EQ-LPT ([s6:lemEQLPT]): loads `3, 2, 1` into `2` layers -/

theorem Φ3_antitone : Antitone Φ3 := by
  intro a b hab
  have h : ∀ a b : Fin 3, a ≤ b → Φ3n b ≤ Φ3n a := by decide
  exact Nat.cast_le.2 (h a b hab)

/-- The hypotheses of `EqLptStatement` / `EqLptExistsStatement` hold (`m = 3`, `k = 2`), and a
greedy placement exists (`σ3`). -/
example : 1 ≤ 2 ∧ 2 ≤ 3 ∧ Antitone Φ3 ∧ (∀ i, 0 ≤ Φ3 i) ∧ ∃ σ : Fin 3 → Fin 2, IsGreedyLPT Φ3 σ :=
  ⟨by norm_num, by norm_num, Φ3_antitone, fun _ => Nat.cast_nonneg _, σ3, σ3_greedy⟩

/-- The conclusion on `σ3`: both layers are used. -/
example : Function.Surjective σ3 := by decide

/-! ## PAR ([s6:lemPAR]) -/

/-- The path `0 1 2 3` is bipartite with disjoint sides `{0, 2}`, `{1, 3}` (the hypotheses of
`ParStatement` with a non-empty edge set). -/
example : Disjoint ({0, 2} : Finset (Fin 4)) {1, 3} ∧
    ∀ e ∈ ({s(0, 1), s(1, 2), s(2, 3)} : Finset (Sym2 (Fin 4))),
      ∃ a ∈ ({0, 2} : Finset (Fin 4)), ∃ b ∈ ({1, 3} : Finset (Fin 4)), e = s(a, b) := by
  decide

/-- The empty choice for the empty edge set is a PAR choice. -/
example : IsParChoice (∅ : Finset (Sym2 (Fin 2))) ∅ := by
  refine ⟨Finset.empty_subset _, fun C hC => ?_, fun e he => absurd he (Finset.notMem_empty e)⟩
  exfalso
  have h : edgeComps (∅ : Finset (Sym2 (Fin 2))) = ∅ := by
    unfold edgeComps edgeVerts
    simp
  rw [h] at hC
  exact Finset.notMem_empty C hC

/-- A single edge `01`: one odd component; choosing that (pendant) edge is a PAR choice. -/
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

example : IsParChoice E01 E01 := by
  refine ⟨Finset.Subset.refl _, fun C hC => ?_, fun e he => Or.inr ?_⟩
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

/-! ## HCC-P ([s6:lemHCCP]): the systems `S1` (`k = 1`) and `S2` (`k = 2`) of `EGTest.Chain`
are valid (the hypotheses of `HccpStatement` and `HccpEndMultStatement` are satisfiable); the
conclusion (i) holds on them. -/

example : S1.Valid G3 ∧ S2.Valid G4 := ⟨S1_valid, S2_valid⟩

example : ∃ Φ : ℕ, ∀ j, S1.Phi j = Φ ∧ (S1.P j).length = Φ :=
  ⟨1, fun j => by fin_cases j; decide⟩

/-- `HccpEndMultStatement` on `S1`, junction `0`, port `1` (first vertex of the only path):
`1 ≤ max(dem⁻, dem⁺) = |exc| + pad = 1 ≤ deg_B = 1`. -/
example : (S1.P (0 : Fin 1)).countP (fun p => p.head? = some 1 ∨ p.getLast? = some 1) ≤
      max (S1.demMinus 1) (S1.demPlus 1) ∧
    max (S1.demMinus 1) (S1.demPlus 1) = (S1.pexc 1).natAbs + S1.pad 1 ∧
    (S1.pexc 1).natAbs ≤ degE (S1.K (0 : Fin 1)).beads 1 := by
  decide

/-! ## HCCglob ([s6:lemHCCglob]): two systems sharing a vertex (a bowtie)

Vertices `0..4`, triangles `0 1 2` and `0 3 4`. System `SA`: port–port bead `0 → 1`, junction
set `{2}`, path `1 2 0`. System `SB`: bead `0 → 3`, junction set `{4}`, path `3 4 0`. The vertex
`0` is a port of both systems (no cross-system vertex-disjointness, GLOB-NO-VERTEX-DISJ); their
beads and path edges are disjoint (the input-level hypothesis of `HccGlobStatement`). -/

def G5 : FGraph (Fin 5) :=
  FGraph.ofEdges Finset.univ {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 0)}

def CA : Cluster (Fin 5) where
  hubs := ∅
  ports := {0, 1}
  beads := {s(0, 1)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

def CB : Cluster (Fin 5) where
  hubs := ∅
  ports := {0, 3}
  beads := {s(0, 3)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

def SA : HccpData (Fin 5) where
  k := 1
  N := 1
  K := fun _ => CA
  O := fun _ => {(0, 1)}
  lay := fun _ => 0
  T := fun _ => {2}
  pad := fun _ => 0
  P := fun _ => [[1, 2, 0]]

def SB : HccpData (Fin 5) where
  k := 1
  N := 1
  K := fun _ => CB
  O := fun _ => {(0, 3)}
  lay := fun _ => 0
  T := fun _ => {4}
  pad := fun _ => 0
  P := fun _ => [[3, 4, 0]]

theorem CA_adm : CA.IsAdmissible {(0, 1)} :=
  ⟨isOrientation_of (by decide) (by decide) (by decide),
    isAcyclic_of_potential (fun v : Fin 5 => v.val) (by decide), by decide⟩

theorem CB_adm : CB.IsAdmissible {(0, 3)} :=
  ⟨isOrientation_of (by decide) (by decide) (by decide),
    isAcyclic_of_potential (fun v : Fin 5 => v.val) (by decide), by decide⟩

theorem SA_valid : SA.Valid G5 where
  k_pos := by decide
  adm _ := CA_adm
  beads_G := by decide
  T_disj := by decide
  pad_k1 _ _ _ _ := rfl
  D_KK := by decide
  D_KT := by decide
  parityClean := by decide
  path_G := by decide
  path_ends := by decide
  path_T := by decide
  starts := by decide
  ends := by decide
  path_edisj _ := List.pairwise_singleton _ _
  pp_disj := by decide
  pb_disj := by decide
  bb_disj := by decide

theorem SB_valid : SB.Valid G5 where
  k_pos := by decide
  adm _ := CB_adm
  beads_G := by decide
  T_disj := by decide
  pad_k1 _ _ _ _ := rfl
  D_KK := by decide
  D_KT := by decide
  parityClean := by decide
  path_G := by decide
  path_ends := by decide
  path_T := by decide
  starts := by decide
  ends := by decide
  path_edisj _ := List.pairwise_singleton _ _
  pp_disj := by decide
  pb_disj := by decide
  bb_disj := by decide

/-- The family of the two systems. -/
def Sys : Fin 2 → HccpData (Fin 5) := ![SA, SB]

/-- The hypotheses of `HccGlobStatement` hold for `Sys` on `G5`. -/
example : (∀ s, (Sys s).Valid G5) ∧
    ∀ s s', s ≠ s' →
      Disjoint ((Sys s).beads ∪ (Sys s).allPathEdges) ((Sys s').beads ∪ (Sys s').allPathEdges) := by
  refine ⟨fun s => ?_, fun s s' hss' => ?_⟩
  · fin_cases s
    · exact SA_valid
    · exact SB_valid
  · fin_cases s <;> fin_cases s' <;> first | exact absurd rfl hss' | decide

/-- The vertex `0` is a port of both systems. -/
example : (0 : Fin 5) ∈ (SA.K (0 : Fin 1)).ports ∧ (0 : Fin 5) ∈ (SB.K (0 : Fin 1)).ports := by
  decide

/-! ## The union lemma, first paragraph (proved: `EG.hccUnion`) and the numeric part of the
multiplicity target (proved: `EG.jsMultNum`) -/

example : EG.Spec.HccUnionStatement := EG.hccUnion

/-- At `M = 2^40` (the lower bound of (R2)) the joint multiplicity bound is `2M − 2 < 2M + 2`. -/
example : max (2 * 2 ^ 40 - 2) ((2 ^ 40 - 1) + ⌈((2 ^ 40 : ℕ) : ℝ) / 2⌉₊) = 2 * 2 ^ 40 - 2 :=
  (EG.jsMultNum (2 ^ 40) (by norm_num)).2.2.2.1

/-! ## Declared input s1:citEuler (a): hypotheses satisfiable

The single edge `01` on `Fin 2`: connected, `T = {0, 1}` even, the spanning tree `S = {01}`. -/

def G2 : FGraph (Fin 2) := FGraph.ofEdges Finset.univ {s(0, 1)}

example : (∀ x ∈ G2.verts, ∀ y ∈ G2.verts, G2.toSimpleGraph.Reachable x y) ∧
    ({0, 1} : Finset (Fin 2)) ⊆ G2.verts ∧ Even ({0, 1} : Finset (Fin 2)).card ∧
    ({s(0, 1)} : Finset (Sym2 (Fin 2))) ⊆ G2.edges := by
  have hadj : G2.toSimpleGraph.Adj 0 1 := by
    show s(0, 1) ∈ G2.edges
    decide
  refine ⟨fun x _ y _ => ?_, by decide, by decide, by decide⟩
  fin_cases x <;> fin_cases y
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

end EGTest.ProbeP2E
