module

public import EG.Lib.HB.TowerRun
public import EG.Spec.HB.DegRec
public import EG.Lib.HB.Lacunary

/-!
# Consequences of the degree recursion used by s2:lemTower (manuscript s2:lemTower (a), (b))

Helper lemmas for the P3 stubs of s2:lemTower (unit P3-s2). The degree recursion
(s2:propDegRec, `EG.Spec.DegRecStatement`) is a hypothesis `hDR` (the stubs pass
`EG.Todo.DegRec`), so this file imports only statements.
* `Run.d_nonneg`: `d_l ≥ 0`;
* `Run.d_succ_le_lamA`: "Proposition s2:propDegRec at round `r` gives `d_{r+1} ≤ λ_r^A`";
* `Run.lam_succ_le`: "`λ_{r+1} = log d_{r+1} ≤ A log λ_r`" (`r < R`);
* `Run.d_add_two_le`: "`d_{r+2} ≤ (A log λ_r)^A ≤ λ_r`" (`r ≤ R - 1`), with Γ1 (c) at `log λ_r`.
-/

public section

namespace EG.HB

open Real

universe u

variable {V : Type u} [DecidableEq V]

namespace Run

theorem d_nonneg (run : Run V) (G : FGraph V) (l : ℕ) : 0 ≤ run.d G l := by
  rw [d_eq]; positivity

theorem d_succ_le_lamA (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ}
    (hr : r ∈ Finset.Icc 1 run.R) : run.d G (r + 1) ≤ run.lam G r ^ Aexp := by
  obtain ⟨-, -, -, hA1, hA2, hA3, hA4, -⟩ := hDR V G Dstar run hD hv r hr
  linarith

theorem lam_succ_le (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r + 1 ≤ run.R) : run.lam G (r + 1) ≤ (Aexp : ℝ) * logb 2 (run.lam G r) := by
  have hrR : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hr1, by omega⟩
  have hr1R : r + 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hr⟩
  have h1 := d_succ_le_lamA hDR hD hv hrR
  have hpos : 0 < run.d G (r + 1) := (paramHyp hD hv hr1R).d_pos
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos h1
  rw [Real.logb_pow] at this
  exact this

theorem d_add_two_le (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r + 1 ≤ run.R) : run.d G (r + 2) ≤ run.lam G r := by
  have hrR : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hr1, by omega⟩
  have hr1R : r + 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hr⟩
  have h1 := d_succ_le_lamA hDR hD hv hr1R
  have h2 := lam_succ_le hDR hD hv hr1 hr
  have h0 : 0 ≤ run.lam G (r + 1) := (paramHyp hD hv hr1R).lam_pos.le
  have h3 : run.lam G (r + 1) ^ Aexp ≤ ((Aexp : ℝ) * logb 2 (run.lam G r)) ^ Aexp :=
    pow_le_pow_left₀ h0 h2 _
  exact h1.trans (h3.trans (paramHyp hD hv hrR).Amu_pow_A_le_lam)


/-- [s2:lemTower] (b) "For `2 ≤ l ≤ R`: `M_{l-1} ≥ 2M_l`". -/
theorem two_M_le (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {l : ℕ} (hl2 : 2 ≤ l)
    (hl : l ≤ run.R) : 2 * run.M G l ≤ run.M G (l - 1) := by
  have hl1 : l - 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hlR : l ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hl⟩
  have h1 := d_succ_le_lamA hDR hD hv hl1
  rw [Nat.sub_add_cancel (by omega : 1 ≤ l)] at h1
  have hp1 := paramHyp hD hv hl1
  have hp := paramHyp hD hv hlR
  have hM : (run.M G l : ℝ) ≤ run.d G l ^ 2 := hp.M_le_sq
  have hd0 : 0 ≤ run.d G l := d_nonneg run G l
  have h2 : run.d G l ^ 2 ≤ (run.lam G (l - 1) ^ Aexp) ^ 2 := pow_le_pow_left₀ hd0 h1 2
  have e : (run.lam G (l - 1) ^ Aexp) ^ 2 = run.lam G (l - 1) ^ (2 * Aexp) := by ring
  have h3 : 2 * run.lam G (l - 1) ^ (2 * Aexp) ≤ run.d G (l - 1) := hp1.two_lam_pow_le_d
  have h4 : run.d G (l - 1) ≤ (run.M G (l - 1) : ℝ) := hp1.d_le_M
  have : ((2 * run.M G l : ℕ) : ℝ) ≤ run.M G (l - 1) := by push_cast; linarith
  exact_mod_cast this

/-- [s2:lemTower] (b) "For `r < R`: `P_r ≥ 2P_{r+1}`". -/
theorem two_P_le (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r + 1 ≤ run.R) : 2 * run.P G (r + 1) ≤ run.P G r := by
  have hrR : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hr1, by omega⟩
  have hr1R : r + 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hr⟩
  have hp := paramHyp hD hv hrR
  have hp1 := paramHyp hD hv hr1R
  have h1 := lam_succ_le hDR hD hv hr1 hr
  have hx1 : 1 ≤ (Aexp : ℝ) * logb 2 (run.lam G r) := hp.one_le_Amu
  have h2 : run.lam G (r + 1) ^ 103 ≤ ((Aexp : ℝ) * logb 2 (run.lam G r)) ^ 103 :=
    pow_le_pow_left₀ hp1.lam_pos.le h1 _
  have h3 : ((Aexp : ℝ) * logb 2 (run.lam G r)) ^ 103 ≤
      ((Aexp : ℝ) * logb 2 (run.lam G r)) ^ Aexp :=
    pow_le_pow_right₀ hx1 (by norm_num [Aexp])
  have h4 := hp.Amu_pow_A_le_lam
  have h5 := hp1.P_le_add_one
  rw [Cp_eq] at h5
  have h6 := hp.lam_add_one_le
  have h7 := ParamHyp.P_ge (d := run.d G r)
  rw [Cp_eq] at h7
  have : ((2 * run.P G (r + 1) : ℕ) : ℝ) ≤ run.P G r := by
    push_cast
    change 2 * (POf (run.d G (r + 1)) : ℝ) ≤ POf (run.d G r)
    change run.lam G r + 1 ≤ run.lam G r ^ 103 / 2 at h6
    change ((Aexp : ℝ) * logb 2 (run.lam G r)) ^ Aexp ≤ run.lam G r at h4
    change (POf (run.d G (r + 1)) : ℝ) ≤ run.lam G (r + 1) ^ 103 + 1 at h5
    change run.lam G r ^ 103 ≤ (POf (run.d G r) : ℝ) at h7
    linarith
  exact_mod_cast this

/-- [s2:lemTower] (b) "For `3 ≤ l ≤ R`: `M_l ≤ (A log λ_{l-2})^{2A}`" ("By Proposition
s2:propDegRec at rounds `l-1` and `l-2`, `d_l ≤ λ_{l-1}^A` and `λ_{l-1} ≤ A log λ_{l-2}`; with
`M_l ≤ d_l^2` …"). -/
theorem M_le_Amu (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {l : ℕ} (hl3 : 3 ≤ l)
    (hl : l ≤ run.R) :
    (run.M G l : ℝ) ≤ ((Aexp : ℝ) * logb 2 (run.lam G (l - 2))) ^ (2 * Aexp) := by
  have hl1 : l - 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hlR : l ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hl⟩
  have h1 := d_succ_le_lamA hDR hD hv hl1
  rw [Nat.sub_add_cancel (by omega : 1 ≤ l)] at h1
  have h2 := lam_succ_le hDR hD hv (r := l - 2) (by omega) (by omega)
  rw [show l - 2 + 1 = l - 1 by omega] at h2
  have hp1 := paramHyp hD hv hl1
  have hp := paramHyp hD hv hlR
  have hM : (run.M G l : ℝ) ≤ run.d G l ^ 2 := hp.M_le_sq
  have hd0 : 0 ≤ run.d G l := d_nonneg run G l
  have h3 : run.d G l ^ 2 ≤ (run.lam G (l - 1) ^ Aexp) ^ 2 := pow_le_pow_left₀ hd0 h1 2
  have h4 : run.lam G (l - 1) ^ Aexp ≤ ((Aexp : ℝ) * logb 2 (run.lam G (l - 2))) ^ Aexp :=
    pow_le_pow_left₀ hp1.lam_pos.le h2 _
  have h5 : (run.lam G (l - 1) ^ Aexp) ^ 2 ≤
      (((Aexp : ℝ) * logb 2 (run.lam G (l - 2))) ^ Aexp) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg hp1.lam_pos.le _) h4 2
  have e : (((Aexp : ℝ) * logb 2 (run.lam G (l - 2))) ^ Aexp) ^ 2 =
      ((Aexp : ℝ) * logb 2 (run.lam G (l - 2))) ^ (2 * Aexp) := by ring
  linarith


/-- "`Σ_{r ≤ k} 1/P_r ≤ 2/P_k`" for `1 ≤ k ≤ R` (by `P_r ≥ 2P_{r+1}` and s2:lemLacunary (i)). -/
theorem sum_inv_P_le (hDR : EG.Spec.DegRecStatement.{u}) {G : FGraph V} {Dstar : ℝ}
    {run : Run V} (hD : Gamma1core Dstar) (hv : run.Valid G Dstar) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ run.R) :
    ∑ r ∈ Finset.Icc 1 k, (1 : ℝ) / (run.P G r : ℝ) ≤ 2 * ((1 : ℝ) / (run.P G k : ℝ)) := by
  have hPpos : ∀ r ∈ Finset.Icc 1 k, (0 : ℝ) < run.P G r := by
    intro r hr
    have hr' : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hr).1,
      (Finset.mem_Icc.1 hr).2.trans hk⟩
    have hp := paramHyp hD hv hr'
    have h7 := ParamHyp.P_ge (d := run.d G r)
    exact lt_of_lt_of_le (pow_pos hp.lam_pos _) h7
  have hgeom := lacGeom (fun r => (1 : ℝ) / (run.P G r : ℝ)) k hk1
    (fun r hr => (one_div_pos.2 (hPpos r hr)).le) (by
      intro r hr
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
      have h := two_P_le hDR hD hv (r := r) h1 (by omega)
      have h' : 2 * (run.P G (r + 1) : ℝ) ≤ run.P G r := by exact_mod_cast h
      have hp := hPpos (r + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [div_div, div_le_div_iff₀ (hPpos r (Finset.mem_Icc.2 ⟨h1, h2.le⟩)) (by linarith)]
      linarith)
  exact hgeom.1

end Run

end EG.HB
