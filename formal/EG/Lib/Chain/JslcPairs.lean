module

public import EG.Defs.Probe.P2J.PreSystem
public import EG.Lib.Chain.HccpAux
public import EG.Lib.Chain.HccpEnds

/-!
# Junction pairs of HCC-P systems before routing (manuscript s6:lemJSLC, proof, Step 6)

Probe unit P2J (probe P-2, part 2), proof round 1. Lemmas about systems with the HCC-P hypotheses
other than (JC-P) (`EG.Chain.HccpData.PreValid`, new Defs file `EG.Defs.Probe.P2J.PreSystem`):
* `PreValid.sum_demMinus_eq_Phi`: `∑_{LayP_j} dem⁻ = Φ_j` (Lemma MED (b), `∑_{U_𝒦} exc = 0`);
* `PreValid.junctionOcc_le`: a vertex occurs in at most `|exc(u)| + pad(u)` junction-`j` pairs of
  one system, and in none if it is not a port of the system ("at a fixed junction a port occurs
  in at most `max(dem⁻, dem⁺)` pairs of each system containing it. Centres occur in no pair").
-/

public section

namespace EG.Chain

namespace HccpData

variable {V : Type*} [DecidableEq V] {S : HccpData V} {G : FGraph V}

/-- The `D_KK` field gives the (D) hypothesis in the form of the HCC-P Lib lemmas. -/
theorem PreValid.layP_disjoint (hS : S.PreValid G) {j j' : Fin S.k} (hjj : j ≠ j') :
    Disjoint (S.layP j) (S.layP j') :=
  S.layP_disjoint hS.D_KK hjj

/-- [s6:lemJSLC] (proof, claim (a)) "the number of out-units of layer `j` equals its padded load":
`∑_{u ∈ LayP_j} dem⁻(u) = Φ_j` (Lemma MED (b): `∑_{u∈U_𝒦} exc(u)^- = Φ(𝒦)`). -/
theorem PreValid.sum_demMinus_eq_Phi (hS : S.PreValid G) (j : Fin S.k) :
    ∑ u ∈ S.layP j, S.demMinus u = S.Phi j := by
  rw [S.sum_demMinus_eq hS.D_KK, S.Phi_eq_sum_load_add_pad hS.D_KK]
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_excNeg_eq_load (hS.adm i)

theorem isPort_of_mem_layP {j : Fin S.k} {u : V} (hu : u ∈ S.layP j) : S.IsPort u := by
  obtain ⟨i, -, hi⟩ := (S.mem_layP).1 hu
  exact ⟨i, hi⟩

/-- A vertex that is not a port of the system occurs in no junction pair ("Centres occur in no
pair"). -/
theorem junctionOcc_eq_zero_of_not_isPort {u : V} (hu : ¬ S.IsPort u) (j : ℕ) :
    S.junctionOcc j u = 0 := by
  unfold junctionOcc
  split_ifs with h h1 h2 h2
  · exact absurd (isPort_of_mem_layP h1) hu
  · exact absurd (isPort_of_mem_layP h1) hu
  · exact absurd (isPort_of_mem_layP h2) hu
  · rfl
  · rfl

/-- [s6:lemJSLC] (proof, claim (c)) "at a fixed junction a port occurs in at most
`max(dem⁻, dem⁺)` pairs of each system containing it": the number of junction-`j` pairs of `S`
containing `u` is at most `|exc(u)| + pad(u)` (`= max(dem⁻(u), dem⁺(u))`). For `k ≥ 2` the layers
`j` and `j+1` are disjoint; for `k = 1`, `pad = 0` and `exc⁻ + exc⁺ = |exc|`. -/
theorem PreValid.junctionOcc_le (hS : S.PreValid G) (j : ℕ) (u : V) :
    S.junctionOcc j u ≤ (S.pexc u).natAbs + S.pad u := by
  unfold junctionOcc
  split_ifs with hj h1 h2 h2
  · -- both layers contain `u`: only possible for `k = 1`
    by_cases hk : S.k = 1
    · have hp := hS.pad_k1 hk _ u h1
      unfold demMinus demPlus
      rw [hp]
      omega
    · have hne : S.succ ⟨j, hj⟩ ≠ ⟨j, hj⟩ := S.succ_ne_self (by have := hS.k_pos; omega) _
      exact absurd h2 (Finset.disjoint_left.1 (hS.layP_disjoint hne.symm) h1)
  · unfold demMinus; omega
  · unfold demPlus; omega
  · omega
  · omega

end HccpData

end EG.Chain
