module

public import EG.Lib.HB.Params
public import EG.Lib.HB.Run

/-!
# Run-level access to the (R2) parameter algebra (manuscript s2:lemTower)

Helper lemmas for the P3 stubs of s2:lemTower (unit P3-s2):
* `Run.paramHyp`: every round `r ≤ R` of a valid run has `d_r ≥ D_*`, so `ParamHyp (d_r)` under
  Γ1 ("Every round `r ≤ R` has `d_r ≥ D_*`, so … the items of Γ1 hold at `μ = log λ_r`");
* `Run.P_le_card_Z0`: a round-`r` pre-part has `|Z^0| ≥ P_r` (definition of pre-parts);
* `Run.d_anti`: `d_l ≤ d_j` for `j ≤ l` (edges of `G_l` shrink; s2:propStructure (iii)).
-/

public section

namespace EG.HB

open Real

universe u

variable {V : Type u} [DecidableEq V]

namespace Run

theorem paramHyp {G : FGraph V} {Dstar : ℝ} {run : Run V} (hD : Gamma1core Dstar)
    (hv : run.Valid G Dstar) {r : ℕ} (hr : r ∈ Finset.Icc 1 run.R) : ParamHyp (run.d G r) :=
  ParamHyp.of_gamma hD (hv.1 r hr).1

theorem P_le_card_Z0 {G : FGraph V} {run : Run V} {r : ℕ} {a : Addr}
    (ha : a ∈ run.prePartAddrs G r) : run.P G r ≤ (run.Z0 G r a).card := by
  have hr := isRound_of_mem_prePartAddrs ha
  rw [prePartAddrs_of_isRound run G hr] at ha
  exact (Finset.mem_filter.1 ha).2

theorem d_anti (run : Run V) (G : FGraph V) {j l : ℕ} (hjl : j ≤ l) : run.d G l ≤ run.d G j := by
  rw [d_eq, d_eq]
  have h := Finset.card_le_card (run.graph_edges_subset_of_le G hjl)
  have h' : ((run.graph G l).edges.card : ℝ) ≤ (run.graph G j).edges.card := by exact_mod_cast h
  have hn : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  gcongr

end Run

end EG.HB
