module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core
public import EG.Defs.Log

/-!
# Statement of Lemma "tower facts", part (a) (manuscript s2:lemTower (a)) — declared input of
unit P3B

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). This statement is a DECLARED INPUT of
the probe: Theorems [s6:thmCONC] (iii) and [s6:thmCONCL] (iv) and the tower fact (s6:eqTowerHalf)
use it, and the probe does not prove it; the stub is `EG.towerA` in `EG/Proof/HB/TowerA.lean`.
Justification: design note `formal/work/p2b/P3B.md`, "Declared inputs". The full Spec of
[s2:lemTower] (blueprint s2b `TowerAStatement` … `TowerEStatement`) is not written yet; its part
(a) must be this statement (import this file, do not restate it), as part (c) is
`EG/Spec/HB/TowerC.lean`.

Manuscript v6.1, `s2.tex`, Lemma [s2:lemTower]:
"For every valid `HB*^{τ+}` run with `d_1 ≥ D_*` (so `R ≥ 1`):
(a) `λ_r ≥ d_{r+1}^{1/A}` for `r ≤ R`; `d_{r+2} ≤ λ_r` for `r ≤ R-1`; `R - r ≤ 2 log* d_r - 1`, in
particular `R - r ≤ 2 log* d_r + 2` (`r ≤ R`); and `λ_r ≥ λ_{l-2}` whenever `r ≤ l-2 ≤ R`."

Formal reading.
* Standing assumption of s2: `D_*` satisfies Γ1–Γ4; the proof of (a) uses Γ1 (c) (through
  [s2:propDegRec] and directly), so the statement carries `Gamma1core Dstar` (as
  `TowerCStatement`). "valid run with `d_1 ≥ D_*`": `run.Valid G Dstar` and
  `Dstar ≤ run.d G 1`.
* Rounds are 1-indexed: "`r ≤ R`" is `r ∈ Finset.Icc 1 run.R`; "`r ≤ R-1`" is `1 ≤ r` and
  `r + 1 ≤ run.R` (no `ℕ`-subtraction); "`r ≤ l-2 ≤ R`" is `1 ≤ r`, `r + 2 ≤ l`, `l ≤ run.R + 2`,
  and `λ_{l-2}` is `run.lam G (l - 2)` (exact, as `l ≥ 3`).
* `d_{r+1}` for `r = R` is the density of the stopping graph `G_{R+1}` (`run.d G (R + 1)`).
  `d_{r+1}^{1/A}` is `Real.rpow` with exponent `1/A`, `A = EG.Aexp = 105`.
* `R - r ≤ 2 log* d_r - 1` and `R - r ≤ 2 log* d_r + 2` are stated in `ℤ` (no truncated
  subtraction; blueprint TOW-NAT-SUB); `log* = EG.logStar`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemTower] (a) "`λ_r ≥ d_{r+1}^{1/A}` for `r ≤ R`; `d_{r+2} ≤ λ_r` for `r ≤ R-1`;
`R - r ≤ 2 log* d_r - 1`, in particular `R - r ≤ 2 log* d_r + 2` (`r ≤ R`); and
`λ_r ≥ λ_{l-2}` whenever `r ≤ l-2 ≤ R`." (For every valid run with `d_1 ≥ D_*`, under Γ1 (a)–(e);
module docstring.) -/
def TowerAStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    (∀ r ∈ Finset.Icc 1 run.R, run.d G (r + 1) ^ ((1 : ℝ) / (Aexp : ℝ)) ≤ run.lam G r) ∧
    (∀ r : ℕ, 1 ≤ r → r + 1 ≤ run.R → run.d G (r + 2) ≤ run.lam G r) ∧
    (∀ r ∈ Finset.Icc 1 run.R, (run.R : ℤ) - r ≤ 2 * (logStar (run.d G r) : ℤ) - 1) ∧
    (∀ r ∈ Finset.Icc 1 run.R, (run.R : ℤ) - r ≤ 2 * (logStar (run.d G r) : ℤ) + 2) ∧
    (∀ r l : ℕ, 1 ≤ r → r + 2 ≤ l → l ≤ run.R + 2 → run.lam G (l - 2) ≤ run.lam G r)

end EG.Spec
