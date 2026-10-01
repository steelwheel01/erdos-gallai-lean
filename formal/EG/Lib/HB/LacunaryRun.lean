module

public import EG.Lib.HB.Lacunary
public import EG.Spec.HB.DegRec

/-!
# Tower-lacunary sums: run facts (manuscript s2:lemLacunary (ii), (iii))

Helper lemmas for the run forms of s2:lemLacunary (unit P3-s2). The degree recursion
(s2:propDegRec, `EG.Spec.DegRecStatement`) is taken as a hypothesis `hDR`, so that this file
imports only statements; the stubs pass `EG.Todo.DegRec`.
* `Run.logb_le_lam`: `λ_r ≥ x_0 = log D_*` for `r ≤ R` (from `d_r ≥ D_*`, `Run.Valid`);
* `Run.lam_step`: proof of (iii), "Proposition s2:propDegRec at round `r` gives
  `d_{r+1} ≤ λ_r^A`, i.e. `λ_{r+1} ≤ A log λ_r`, i.e. `λ_r ≥ 2^{λ_{r+1}/A}`" for `r < R`.
-/

public section

namespace EG.HB

open Real

universe u

variable {V : Type u} [DecidableEq V]

/-- `λ_r ≥ log D_*` for every round `r ≤ R` of a valid run with `D_* > 0`. -/
theorem Run.logb_le_lam {G : FGraph V} {Dstar : ℝ} {run : Run V} (hDpos : 0 < Dstar)
    (hv : run.Valid G Dstar) {r : ℕ} (hr : r ∈ Finset.Icc 1 run.R) :
    logb 2 Dstar ≤ run.lam G r :=
  Real.logb_le_logb_of_le (by norm_num) hDpos (hv.1 r hr).1

/-- Proof of [s2:lemLacunary] (iii): `λ_r ≥ 2^{λ_{r+1}/A}` for `r < R` (under Γ1, from
s2:propDegRec at round `r`). -/
theorem Run.lam_step (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ}
    (hr : r ∈ Finset.Ico 1 run.R) :
    (2 : ℝ) ^ (run.lam G (r + 1) / (Aexp : ℝ)) ≤ run.lam G r := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
  have hr' : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨h1, h2.le⟩
  have hr1 : r + 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hD2 := hD.two_lt
  have hd1 : 0 < run.d G (r + 1) := by linarith [(hv.1 (r + 1) hr1).1]
  have hdr : 2 < run.d G r := by linarith [(hv.1 r hr').1]
  have hlam : 0 < run.lam G r := Real.logb_pos (by norm_num) (by linarith)
  obtain ⟨-, -, -, hA1, hA2, hA3, hA4, -⟩ := hDR V G Dstar run hD hv r hr'
  exact lam_step_of_d_le hd1 hlam (by linarith)

end EG.HB
