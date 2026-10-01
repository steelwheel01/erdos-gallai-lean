module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma "tower facts", part (c) (manuscript s2:lemTower (c)) — declared input of
unit P3A

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). This statement is a DECLARED INPUT
of the probe: [s2:lemGC] (iv) is [s2:lemTower] (c), and the probe does not prove it; the stub is
`EG.towerC` in `EG/Proof/HB/TowerC.lean`. Justification: design note `formal/work/p2b/P3A.md`,
"Declared inputs". The full Spec of [s2:lemTower] (parts (a)–(e), blueprint s2b
`TowerAStatement` … `TowerEStatement`) is not written yet; its part (c) must be this statement
(import this file, do not restate it).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemTower]:
"For every valid `HB*^{τ+}` run with `d_1 ≥ D_*` (so `R ≥ 1`): … (c) For `r ≤ R`:
`τ_r ≤ 257 Λ_r^{σ+2} ≤ 2^{σ+11} λ_r^{σ+2}` and `τ_r/P_r ≤ 2^{σ+11}/λ_r`; and
`θ^GC_r(Z^0) ≥ P_r λ_r^{-1/2} > τ_r` for every round-`r` pre-part `Z`."

Formal reading.
* Standing assumption of s2: `D_*` satisfies Γ1–Γ4; the proof of [s2:lemTower] uses Γ1 (a)–(d)
  (blueprint TOW-GAMMA-ITEMS), so the statement carries `Gamma1core Dstar` (items (a)–(e) of
  Γ1; CONVENTIONS "Constants and Γ").
* "valid run with `d_1 ≥ D_*`": `run.Valid G Dstar` and `Dstar ≤ run.d G 1`; rounds
  `r ∈ Finset.Icc 1 run.R`.
* `σ = EG.sigmaC` (natural-number exponents `σ + 2`, `σ + 11`), `Λ_r = run.Lam G r`,
  `λ_r = run.lam G r`, `P_r = run.P G r`, `τ_r = run.tau G r` (casts to `ℝ`),
  `θ^GC_r(Z^0) = run.thetaGC G r a` for the pre-part at address `a`; `λ_r^{-1/2}` is `Real.rpow`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemTower] (c) "For `r ≤ R`: `τ_r ≤ 257 Λ_r^{σ+2} ≤ 2^{σ+11} λ_r^{σ+2}` and
`τ_r/P_r ≤ 2^{σ+11}/λ_r`; and `θ^GC_r(Z^0) ≥ P_r λ_r^{-1/2} > τ_r` for every round-`r` pre-part
`Z`." (For every valid run with `d_1 ≥ D_*`, under Γ1 (a)–(e); module docstring.) -/
def TowerCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ r ∈ Finset.Icc 1 run.R,
      (run.tau G r : ℝ) ≤ 257 * run.Lam G r ^ (sigmaC + 2) ∧
      257 * run.Lam G r ^ (sigmaC + 2) ≤ 2 ^ (sigmaC + 11) * run.lam G r ^ (sigmaC + 2) ∧
      (run.tau G r : ℝ) / run.P G r ≤ 2 ^ (sigmaC + 11) / run.lam G r ∧
      ∀ a ∈ run.prePartAddrs G r,
        (run.P G r : ℝ) * run.lam G r ^ (-(1 / 2 : ℝ)) ≤ run.thetaGC G r a ∧
        (run.tau G r : ℝ) < run.P G r * run.lam G r ^ (-(1 / 2 : ℝ))

end EG.Spec
