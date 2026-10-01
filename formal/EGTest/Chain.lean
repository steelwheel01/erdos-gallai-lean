import EG.Lib.Chain.Cluster
import EG.Lib.Chain.EqLpt
import EG.Lib.Chain.HCCP

/-! Unit tests for `EG.Defs.Chain.Cluster` ([s6:defCluster]), `EG.Defs.Chain.EqLpt`
([s6:lemEQLPT]) and `EG.Defs.Chain.HCCP` ([s6:lemHCCP]): a small cluster with its median
orientation, excesses, load and bead count; a greedy placement and a non-greedy one; two valid
HCC-P systems (`k = 1` and `k = 2`), which shows that `HccpData.Valid` is satisfiable, and
negative tests. -/

namespace EGTest.Chain

open EG EG.Chain

/-- Orientation from three decidable conditions (helper for the tests). -/
theorem isOrientation_of {V : Type*} [DecidableEq V] {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (h1 : ∀ a ∈ A, a.1 ≠ a.2) (h2 : A.image (fun a => s(a.1, a.2)) = F)
    (h3 : ∀ a ∈ A, ∀ b ∈ A, s(a.1, a.2) = s(b.1, b.2) → a = b) : IsOrientation F A :=
  isOrientation_iff.2 ⟨h1, h2, fun a ha b hb hab => h3 a ha b hb hab⟩

/-! ## A cluster on `Fin 5`

Hub `0`, ports `1, 2, 3, 4`, beads `01, 02, 34, 13`. The hub has the two neighbours `1 ≺ 2`
(`d = 1`), so `MED(id)` orients `1 → 0 → 2`; the port–port beads go up: `3 → 4`, `1 → 3`. -/

def K5 : Cluster (Fin 5) where
  hubs := {0}
  ports := {1, 2, 3, 4}
  beads := {s(0, 1), s(0, 2), s(3, 4), s(1, 3)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

def O5 : Finset (Fin 5 × Fin 5) := {(1, 0), (0, 2), (3, 4), (1, 3)}

example : K5.medOrient (fun v => v.val) = O5 := by decide

example : K5.verts = Finset.univ := by decide
example : K5.beadNbrs 0 = {1, 2} := by decide
example : K5.portBeads = {s(3, 4), s(1, 3)} := by decide
example : K5.ParityClean := by decide

/-- The excesses: `exc(1) = 2`, `exc(2) = −1`, `exc(3) = 0`, `exc(4) = −1`; they sum to `0`. -/
example : exc O5 1 = 2 ∧ exc O5 2 = -1 ∧ exc O5 3 = 0 ∧ exc O5 4 = -1 := by decide
example : ∑ u ∈ K5.ports, exc O5 u = 0 := by decide
example : excPos O5 1 = 2 ∧ excNeg O5 1 = 0 ∧ excPos O5 2 = 0 ∧ excNeg O5 2 = 1 := by decide

/-- The load `Φ(K5) = 2`. -/
example : K5.load O5 = 2 := by decide

/-- The bead count `b(K5) = deg(0)/2 + e(B[U]) = 1 + 2 = 3`. -/
example : K5.beadCount = 3 := by
  rw [K5.beadCount_eq_natCast (by decide)]
  have : (∑ h ∈ K5.hubs, degE K5.beads h / 2 + K5.portBeads.card : ℕ) = 3 := by decide
  rw [this]; norm_num

theorem O5_orient : IsOrientation K5.beads O5 :=
  isOrientation_of (by decide) (by decide) (by decide)

/-- A potential for `O5` (rank order `1 < 0 < 2`, `3 < 4`). -/
def pot5 : Fin 5 → ℕ := ![1, 0, 2, 1, 2]

theorem O5_admissible : K5.IsAdmissible O5 where
  orient := O5_orient
  acyclic := isAcyclic_of_potential pot5 (by decide)
  hub_bal := by decide

/-- Admissibility is balance at hubs only: the ports `1, 2, 4` are unbalanced. -/
example : ¬ IsBalanced O5 := fun h => absurd (h 1) (by decide)

/-- A cluster that is not parity-clean: hub `0` with the three port neighbours `1, 2, 3`. It has
no admissible orientation (`IsAdmissible.parityClean`), and its bead count `3/2` is not an
integer. -/
def Kodd : Cluster (Fin 4) where
  hubs := {0}
  ports := {1, 2, 3}
  beads := {s(0, 1), s(0, 2), s(0, 3)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

example : ¬ Kodd.ParityClean := by decide
example (O : Finset (Fin 4 × Fin 4)) : ¬ Kodd.IsAdmissible O := fun h =>
  absurd h.parityClean (by decide)
example : Kodd.beadCount = 3 / 2 := by
  unfold Cluster.beadCount
  have h1 : degE Kodd.beads 0 = 3 := by decide
  have h2 : Kodd.portBeads.card = 0 := by decide
  simp only [show Kodd.hubs = {0} from rfl, Finset.sum_singleton, h1, h2]
  norm_num

/-- A bead joining two hubs is not allowed. -/
example : ¬ ∃ K : Cluster (Fin 2), K.hubs = {0, 1} ∧ s(0, 1) ∈ K.beads := by
  rintro ⟨K, hh, hb⟩
  exact K.no_hub_hub _ hb (by intro v hv; rw [hh]; revert v; decide)

/-! ## EQ-LPT: loads `3, 2, 1` into `2` layers -/

/-- The loads `3, 2, 1` (natural numbers, cast to `ℝ`). -/
def Φ3n : Fin 3 → ℕ := ![3, 2, 1]

def Φ3 : Fin 3 → ℝ := fun i => (Φ3n i : ℝ)

/-- The greedy placement: item `0` → layer `0`, item `1` → the empty layer `1`, item `2` → the
lighter layer `1`. -/
def σ3 : Fin 3 → Fin 2 := ![0, 1, 1]

/-- A non-greedy placement: item `1` goes to the non-empty layer `0` although layer `1` is empty. -/
def σ3bad : Fin 3 → Fin 2 := ![0, 0, 1]

theorem σ3_greedy : IsGreedyLPT Φ3 σ3 := by
  intro i
  refine ⟨?_, ?_⟩
  · intro j
    unfold loadBefore Φ3
    rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le]
    revert i j; decide
  · unfold EmptyBefore; revert i; decide

example : ¬ IsGreedyLPT Φ3 σ3bad := by
  intro h
  have h2 := (h 1).2 ⟨1, by unfold EmptyBefore; decide⟩
  exact h2 0 (by decide) rfl

example : layerLoad Φ3 σ3 0 = 3 ∧ layerLoad Φ3 σ3 1 = 3 := by
  unfold layerLoad Φ3
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  have h0 : (∑ i ∈ Finset.univ.filter (fun i => σ3 i = 0), Φ3n i) = 3 := by decide
  have h1 : (∑ i ∈ Finset.univ.filter (fun i => σ3 i = 1), Φ3n i) = 3 := by decide
  rw [h0, h1]; norm_num

/-! ## HCC-P, `k = 1`: a triangle

Vertices `0, 1, 2`. One cluster without hubs: ports `0, 1`, the bead `01` oriented `0 → 1`, so
`exc(0) = 1`, `exc(1) = −1`, `X^out = {1}`, `X^in = {0}`. Junction set `T_0 = {2}` and the single
path `1 2 0`. Then `Φ = 1`, and the bead with the path is the triangle. -/

def G3 : FGraph (Fin 3) := FGraph.ofEdges Finset.univ {s(0, 1), s(1, 2), s(2, 0)}

def C01 : Cluster (Fin 3) where
  hubs := ∅
  ports := {0, 1}
  beads := {s(0, 1)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

def S1 : HccpData (Fin 3) where
  k := 1
  N := 1
  K := fun _ => C01
  O := fun _ => {(0, 1)}
  lay := fun _ => 0
  T := fun _ => {2}
  pad := fun _ => 0
  P := fun _ => [[1, 2, 0]]

theorem C01_adm : C01.IsAdmissible {(0, 1)} :=
  ⟨isOrientation_of (by decide) (by decide) (by decide),
    isAcyclic_of_potential (fun v : Fin 3 => v.val) (by decide), by decide⟩

theorem S1_valid : S1.Valid G3 where
  k_pos := by decide
  adm _ := C01_adm
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

example : S1.Phi (0 : Fin 1) = 1 ∧ (S1.P (0 : Fin 1)).length = 1 := by decide
example : S1.xOut (0 : Fin 1) = {1} ∧ S1.xIn (0 : Fin 1) = {0} := by decide
example : S1.JcpOne (0 : Fin 1) :=
  (S1.jcp_iff_jcpOne rfl (0 : Fin 1) fun _ _ => rfl).1 (S1_valid.jcpUniform (0 : Fin 1))

/-- With the path reversed (`0 2 1`, from `X^in` to `X^out`) the system is not valid. -/
example : ¬ ({ S1 with P := fun _ => [[0, 2, 1]] } : HccpData (Fin 3)).Valid G3 := fun h =>
  absurd (h.starts (0 : Fin 1) 0 (by decide)) (by decide)

/-! ## HCC-P, `k = 2`: a 4-cycle

Vertices `0, 1, 2, 3`. Layer `0`: ports `0, 1`, bead `0 → 1`; layer `1`: ports `2, 3`, bead
`2 → 3`. `𝒫_0 = [1 2]` (from `LayP_0` to `LayP_1`), `𝒫_1 = [3 0]` (from `LayP_1` to
`LayP_0`), empty junction sets. Then `Φ_0 = Φ_1 = 1` and the four edges form the cycle
`0 1 2 3`. -/

def G4 : FGraph (Fin 4) := FGraph.ofEdges Finset.univ {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}

def Ca : Cluster (Fin 4) where
  hubs := ∅
  ports := {0, 1}
  beads := {s(0, 1)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

def Cb : Cluster (Fin 4) where
  hubs := ∅
  ports := {2, 3}
  beads := {s(2, 3)}
  disjoint := by decide
  loopless := by decide
  ends_mem := by decide
  no_hub_hub := by decide

theorem Ca_adm : Ca.IsAdmissible {(0, 1)} :=
  ⟨isOrientation_of (by decide) (by decide) (by decide),
    isAcyclic_of_potential (fun v : Fin 4 => v.val) (by decide), by decide⟩

theorem Cb_adm : Cb.IsAdmissible {(2, 3)} :=
  ⟨isOrientation_of (by decide) (by decide) (by decide),
    isAcyclic_of_potential (fun v : Fin 4 => v.val) (by decide), by decide⟩

def S2 : HccpData (Fin 4) where
  k := 2
  N := 2
  K := ![Ca, Cb]
  O := ![{(0, 1)}, {(2, 3)}]
  lay := ![0, 1]
  T := fun _ => ∅
  pad := fun _ => 0
  P := ![[[1, 2]], [[3, 0]]]

theorem S2_valid : S2.Valid G4 where
  k_pos := by decide
  adm i := by
    fin_cases i
    · exact Ca_adm
    · exact Cb_adm
  beads_G := by decide
  T_disj := by decide
  pad_k1 h := absurd h (by decide)
  D_KK := by decide
  D_KT := by decide
  parityClean := by decide
  path_G := by decide
  path_ends := by decide
  path_T := by decide
  starts := by decide
  ends := by decide
  path_edisj j := by fin_cases j <;> exact List.pairwise_singleton _ _
  pp_disj := by decide
  pb_disj := by decide
  bb_disj := by decide

example : S2.Phi (0 : Fin 2) = 1 ∧ S2.Phi (1 : Fin 2) = 1 := by decide
example : (S2.succ (1 : Fin 2)).val = 0 := rfl
example : S2.layP (0 : Fin 2) = {0, 1} ∧ S2.layP (1 : Fin 2) = {2, 3} := by decide

/-! Padded load vs cluster loads (`Phi_eq_sum_load_add_pad`, `sum_demMinus_eq`): layer `0` of `S2`
is the cluster `Ca` with load `1` and no padding. (Indices are given at type `Fin S2.k`: at type
`Fin 2` the `DecidablePred` instance of the filter is not found.) -/

def S2j0 : Fin S2.k := ⟨0, by decide⟩
def S2j1 : Fin S2.k := ⟨1, by decide⟩

example : S2.Phi S2j0 =
    ∑ i ∈ Finset.univ.filter (fun i => S2.lay i = S2j0), (S2.K i).load (S2.O i) +
      ∑ u ∈ S2.layP S2j0, S2.pad u :=
  S2_valid.Phi_eq_sum_load_add_pad _
example : ∑ i ∈ Finset.univ.filter (fun i => S2.lay i = S2j0), (S2.K i).load (S2.O i) = 1 ∧
    ∑ u ∈ S2.layP S2j0, S2.pad u = 0 := by decide
example : ∑ u ∈ S2.layP S2j1, S2.demMinus u =
    ∑ i ∈ Finset.univ.filter (fun i => S2.lay i = S2j1),
      ∑ u ∈ (S2.K i).ports, excNeg (S2.O i) u + ∑ u ∈ S2.layP S2j1, S2.pad u :=
  S2_valid.sum_demMinus_eq _

/-- The common padded load in the `∃`-form (no accessor), and its uniqueness. -/
example : ∃ Φ, ∀ j, S2.Phi j = Φ := ⟨1, fun j => by fin_cases j <;> decide⟩
example (a : ℕ) (ha : ∀ j, S2.Phi j = a) : a = 1 :=
  S2.eq_of_forall_Phi_eq S2_valid.k_pos ha (fun j => by fin_cases j <;> decide)

/-- Padding the ports by `1` breaks the demands of the given paths. -/
example : ¬ ({ S2 with pad := fun _ => 1 } : HccpData (Fin 4)).Valid G4 := fun h =>
  absurd (h.starts (0 : Fin 2) 1 (by decide)) (by decide)

end EGTest.Chain
