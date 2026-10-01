module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core
public import EG.Defs.Log
public import EG.Spec.HB.TowerA
public import EG.Spec.HB.TowerB
public import EG.Spec.HB.TowerBM
public import EG.Spec.HB.TowerBLate
public import EG.Spec.HB.TowerC

/-!
# Statements of Lemma "tower facts": the clauses of (b) not stated yet, (d), (e), and the whole
lemma (manuscript s2:lemTower)

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:lemTower. Definitions: `EG/Defs/HB/Round.lean`, `Run.lean` (`EG.HB.psiPool`,
`EG.HB.epsA`), `EG/Defs/Log.lean`, `EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemTower]:
"For every valid `HB*^{τ+}` run with `d_1 ≥ D_*` (so `R ≥ 1`):
(a) `λ_r ≥ d_{r+1}^{1/A}` for `r ≤ R`; `d_{r+2} ≤ λ_r` for `r ≤ R-1`; `R - r ≤ 2 log* d_r - 1`, in
particular `R - r ≤ 2 log* d_r + 2` (`r ≤ R`); and `λ_r ≥ λ_{l-2}` whenever `r ≤ l-2 ≤ R`.
(b) For `r ≤ R`: `M_r ≤ d_r^2`; `λ_r ≤ Λ_r ≤ 2λ_r`; `λ_r^{100} ≤ s_r ≤ 2Λ_r^σ`; `s_r ≤ P_r`; and
`L_Y ≤ log M_r ≤ 2λ_r` for every ancestor `Y` of round `r`. For `3 ≤ l ≤ R`:
`M_l ≤ (A log λ_{l-2})^{2A} ≤ λ_{l-2}^{1.6}`; `P_{l-2} ≥ M_l^{13}`; and
`P_{l-2}/2 ≥ M_l log^4 M_l`. For `2 ≤ l ≤ R`: `M_{l-1} ≥ 2M_l`. For `r < R`: `P_r ≥ 2P_{r+1}`.
Moreover `Σ_{l≤R} 1/M_l ≤ 2/D_*` and `Σ_{l≤R} ψ(M_l) ≤ 2.1 ψ(D_*)` with
`ψ(x) := (6 log x + 12)/x`. Finally, completing (K1) of Proposition s2:propOV, the number `ν_l` of
ancestors of rounds at most `l-2` satisfies `ν_l ≤ 2.74 n/P_{l-2}` for `3 ≤ l ≤ R`.
(c) For `r ≤ R`: `τ_r ≤ 257 Λ_r^{σ+2} ≤ 2^{σ+11} λ_r^{σ+2}` and `τ_r/P_r ≤ 2^{σ+11}/λ_r`; and
`θ^GC_r(Z^0) ≥ P_r λ_r^{-1/2} > τ_r` for every round-`r` pre-part `Z`.
(d) For `r ≤ l ≤ R`: `λ_r ≥ 2^{2 log* d_r + 2} ≥ 2^{R-r} ≥ 2^{l-r}`.
(e) Put `ε_A := 31 ε/(C' log log D_*)`, a function of `D_*` alone (it depends neither on the run
nor on `n`). Then `Σ_{l≤R} 15.2 ε/log P_l ≤ ε_A`. Consequently `Σ_{l≤R} |D_l| ≤ ε_A n` and
`Σ_{l≤R} Σ_{Z∈Std_l} |A_Z| ≤ ε_A n`."

Where each part is stated (the earlier probe Specs are reused, not restated).
* (a): `EG.Spec.TowerAStatement` (`TowerA.lean`, unit P3B).
* (b), first sentence: `EG.Spec.TowerBRoundStatement` (`TowerB.lean`, unit P4A); the `M_l`
  clauses `M_l ≤ (A log λ_{l-2})^{2A} ≤ λ_{l-2}^{1.6}` and `Σ 1/M_l ≤ 2/D_*`:
  `EG.Spec.TowerBMStatement` (`TowerBM.lean`, unit P4B); `P_{l-2} ≥ M_l^{13}` and
  `ν_l ≤ 2.74 n/P_{l-2}`: `EG.Spec.TowerBLateStatement` (`TowerBLate.lean`, unit P2J); the rest
  (`P_{l-2}/2 ≥ M_l log⁴ M_l`, `M_{l-1} ≥ 2M_l`, `P_r ≥ 2P_{r+1}`, the `ψ`-sum):
  `TowerBRestStatement` (this file).
* (c): `EG.Spec.TowerCStatement` (`TowerC.lean`, unit P3A).
* (d): `TowerDStatement`; (e): `TowerEStatement` (this file).
* `TowerStatement`: the conjunction of all of them (the whole lemma).

Formal reading (same conventions as the probe Specs `TowerAStatement` … `TowerCStatement`).
* Condition on `D_*`: the standing assumption; the proof uses Γ1 (a)–(d) (blueprint
  TOW-GAMMA-ITEMS), and Γ2(a) through Lemma s2:lemCap(ii) and Proposition s2:propOV (implied by
  Γ1, `EG.Gamma1core.gamma2a`). Every statement carries `Gamma1core Dstar`. "valid run with
  `d_1 ≥ D_*`": `run.Valid G Dstar` and `Dstar ≤ run.d G 1`.
* Rounds are 1-indexed; "`3 ≤ l ≤ R`" is `3 ≤ l ∧ l ≤ run.R` with `l - 2` the natural subtraction
  (exact); "`2 ≤ l ≤ R`" likewise with `l - 1`; "`r < R`" is `1 ≤ r ∧ r + 1 ≤ run.R`.
* `M_l = run.M G l`, `P_r = run.P G r` are natural numbers: `M_{l-1} ≥ 2M_l` and
  `P_r ≥ 2P_{r+1}` are stated in `ℕ`; `P_{l-2}/2 ≥ M_l log⁴ M_l` in `ℝ` (`log = Real.logb 2`).
* `ψ = EG.HB.psiPool` (Defs, exactly `(6 log x + 12)/x`), `ε_A = EG.HB.epsA D_*` (Defs, exactly
  `31 ε/(C' log log D_*)`, `ε = EG.epsC`, `C' = EG.Cp`).
* (d): the powers `2^{2 log* d_r + 2}`, `2^{R-r}`, `2^{l-r}` have natural-number exponents
  (`log* = EG.logStar`, `R - r` and `l - r` exact as `r ≤ l ≤ R`); `λ_r = run.lam G r` is real.
* (e): the sums run over `l ∈ Finset.Icc 1 run.R`; `|D_l| = (run.D G l).card`,
  `A_Z = run.hubs G l a` for `a ∈ Std_l` (`Z^0 ∩ D_l`, [s2:defAncestors]); `n = G.card`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemTower] (b), the clauses not stated in `TowerBRoundStatement`, `TowerBMStatement`,
`TowerBLateStatement`: "For `3 ≤ l ≤ R`: … `P_{l-2}/2 ≥ M_l log^4 M_l`. For `2 ≤ l ≤ R`:
`M_{l-1} ≥ 2M_l`. For `r < R`: `P_r ≥ 2P_{r+1}`. Moreover … `Σ_{l≤R} ψ(M_l) ≤ 2.1 ψ(D_*)` with
`ψ(x) := (6 log x + 12)/x`." (For every valid run with `d_1 ≥ D_*`, under Γ1 (a)–(e).) -/
def TowerBRestStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    (∀ l : ℕ, 3 ≤ l → l ≤ run.R →
      (run.M G l : ℝ) * Real.logb 2 (run.M G l : ℝ) ^ 4 ≤ (run.P G (l - 2) : ℝ) / 2) ∧
    (∀ l : ℕ, 2 ≤ l → l ≤ run.R → 2 * run.M G l ≤ run.M G (l - 1)) ∧
    (∀ r : ℕ, 1 ≤ r → r + 1 ≤ run.R → 2 * run.P G (r + 1) ≤ run.P G r) ∧
    ∑ l ∈ Finset.Icc 1 run.R, psiPool (run.M G l : ℝ) ≤ 2.1 * psiPool Dstar

/-- [s2:lemTower] (d) "For `r ≤ l ≤ R`: `λ_r ≥ 2^{2 log* d_r + 2} ≥ 2^{R-r} ≥ 2^{l-r}`." (For every
valid run with `d_1 ≥ D_*`, under Γ1 (a)–(e).) -/
def TowerDStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ r l : ℕ, 1 ≤ r → r ≤ l → l ≤ run.R →
      (2 : ℝ) ^ (2 * logStar (run.d G r) + 2) ≤ run.lam G r ∧
      (2 : ℝ) ^ (run.R - r) ≤ (2 : ℝ) ^ (2 * logStar (run.d G r) + 2) ∧
      (2 : ℝ) ^ (l - r) ≤ (2 : ℝ) ^ (run.R - r)

/-- [s2:lemTower] (e) "Put `ε_A := 31 ε/(C' log log D_*)` … Then `Σ_{l≤R} 15.2 ε/log P_l ≤ ε_A`.
Consequently `Σ_{l≤R} |D_l| ≤ ε_A n` and `Σ_{l≤R} Σ_{Z∈Std_l} |A_Z| ≤ ε_A n`." (For every valid
run with `d_1 ≥ D_*`, under Γ1 (a)–(e).) -/
def TowerEStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∑ l ∈ Finset.Icc 1 run.R, 15.2 * epsC / Real.logb 2 (run.P G l : ℝ) ≤ epsA Dstar ∧
    ((∑ l ∈ Finset.Icc 1 run.R, (run.D G l).card : ℕ) : ℝ) ≤ epsA Dstar * (G.card : ℝ) ∧
    ((∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.hubs G l a).card : ℕ) : ℝ) ≤
      epsA Dstar * (G.card : ℝ)

/-- [s2:lemTower], all parts (a)–(e) (module docstring: which statement holds which clause). -/
def TowerStatement : Prop :=
  TowerAStatement.{u} ∧ TowerBRoundStatement.{u} ∧ TowerBMStatement.{u} ∧
    TowerBLateStatement.{u} ∧ TowerBRestStatement.{u} ∧ TowerCStatement.{u} ∧
    TowerDStatement.{u} ∧ TowerEStatement.{u}

end EG.Spec
