module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core
public import EG.Defs.Probe.P3B.TowerFns

/-!
# Statements of the `log*` facts and the tower facts (s6:eqTowerHalf), (s6:eqTowerEnd)
(manuscript s6, text between s6:defDesign and s6:thmCONC)

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). Design note
`formal/work/p2b/P3B.md`. Definitions: `EG/Defs/Log.lean`, `EG/Defs/HB/Run.lean`,
`EG/Defs/Gamma/Core.lean` (locked) and the new probe Defs `EG/Defs/Probe/P3B/TowerFns.lean`
(`EG.Chain.towA`, `towB`, `towC`).

Manuscript v6.1, `s6.tex` ("All logarithms are to base `2`"):
"The following elementary facts about `log*` are used in the proofs of the next two theorems. Put
`𝖳_0 := 1` and `𝖳_{i+1} := 2^{𝖳_i}`. For `x ≥ 1` and an integer `k ≥ 0`, `log* x ≤ k` iff
`x ≤ 𝖳_k`. For `x > 1`, `log* x = 1 + log*(log x)`. And `log* x ≤ 1 + log x` for all `x ≥ 1`: …
Put `k_* := log* D_*`. By Γ1(a) at `μ = log log D_*`, `log log D_* ≥ 2^8 > 16`, so
`D_* > 2^{65536} = 𝖳_5` and `k_* ≥ 6`.
For `d ≥ D_*` put `𝖺(d) := (2 log* d + 2)/log d`, `𝖻(d) := (2 log* d + 1)/log log d`,
`𝖼(d) := (2 log* d + 1)/(log d)^{1/2}`. We use two facts. First, for every valid run and every
`r < R`,
(s6:eqTowerHalf) `𝖺(d_r) ≤ ½𝖺(d_{r+1})`, `𝖻(d_r) ≤ ½𝖻(d_{r+1})`, `𝖼(d_r) ≤ ½𝖼(d_{r+1})`.
Second, for every `d ≥ D_*`,
(s6:eqTowerEnd) `𝖺(d) ≤ (2k_*+4)/log D_*`, `𝖻(d) ≤ (2k_*+3)/log log D_*`,
`𝖼(d) ≤ (2k_*+3)/(log D_*)^{1/2}`."

Formal reading.
* `log = Real.logb 2`, `log* = EG.logStar` (cast to `ℝ` in real expressions), `𝖳_i = EG.tower i`,
  `(·)^{1/2}` is `Real.rpow`. `𝖺, 𝖻, 𝖼` are `EG.Chain.towA`, `towB`, `towC`.
* The standing assumption of the manuscript on `D_*` (Γ1–Γ4) enters as `Gamma1core Dstar` (items
  (a), (b) of Γ1 are used, and (a) gives `k_* ≥ 6`); a "valid run" is `run.Valid G Dstar`
  (rounds are 1-indexed, "`r < R`" is `r ∈ Finset.Ico 1 run.R`; then `R ≥ 2`, so `d_1 ≥ D_*` holds
  and is not a separate hypothesis). No `n ≥ N_0`.
* The three `log*` facts are `LogStarFactsStatement` (no hypothesis beyond `x ≥ 1`, resp.
  `x > 1`); the chain "`log log D_* ≥ 2^8 > 16`, so `D_* > 𝖳_5` and `k_* ≥ 6`" is
  `KStarStatement` (`𝖳_5 = 2^{65536}` is `EG.tower 5`; the numeral identity is not restated).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem: the `log*` facts)
"For `x ≥ 1` and an integer `k ≥ 0`, `log* x ≤ k`
iff `x ≤ 𝖳_k`. For `x > 1`, `log* x = 1 + log*(log x)`. And `log* x ≤ 1 + log x` for all
`x ≥ 1`." (`𝖳_0 := 1`, `𝖳_{i+1} := 2^{𝖳_i}` is `EG.tower`.) -/
def LogStarFactsStatement : Prop :=
  (∀ (x : ℝ) (k : ℕ), 1 ≤ x → (logStar x ≤ k ↔ x ≤ tower k)) ∧
    (∀ x : ℝ, 1 < x → logStar x = 1 + logStar (Real.logb 2 x)) ∧
    (∀ x : ℝ, 1 ≤ x → (logStar x : ℝ) ≤ 1 + Real.logb 2 x)

/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem) "Put `k_* := log* D_*`.
By Γ1(a) at `μ = log log D_*`,
`log log D_* ≥ 2^8 > 16`, so `D_* > 2^{65536} = 𝖳_5` and `k_* ≥ 6`." -/
def KStarStatement : Prop :=
  ∀ Dstar : ℝ, Gamma1core Dstar →
    (2 : ℝ) ^ 8 ≤ Real.logb 2 (Real.logb 2 Dstar) ∧ (16 : ℝ) < Real.logb 2 (Real.logb 2 Dstar) ∧
      tower 5 < Dstar ∧ 6 ≤ logStar Dstar

/-- [s6:eqTowerHalf] "for every valid run and every `r < R`,
`𝖺(d_r) ≤ ½𝖺(d_{r+1})`, `𝖻(d_r) ≤ ½𝖻(d_{r+1})`, `𝖼(d_r) ≤ ½𝖼(d_{r+1})`." (Under the standing
assumption Γ1 on `D_*`; module docstring.) -/
def TowerHalfStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Ico 1 run.R,
      towA (run.d G r) ≤ towA (run.d G (r + 1)) / 2 ∧
      towB (run.d G r) ≤ towB (run.d G (r + 1)) / 2 ∧
      towC (run.d G r) ≤ towC (run.d G (r + 1)) / 2

/-- [s6:eqTowerEnd] "for every `d ≥ D_*`, `𝖺(d) ≤ (2k_*+4)/log D_*`,
`𝖻(d) ≤ (2k_*+3)/log log D_*`, `𝖼(d) ≤ (2k_*+3)/(log D_*)^{1/2}`" (`k_* = log* D_*`; under the
standing assumption Γ1 on `D_*`). -/
def TowerEndStatement : Prop :=
  ∀ Dstar : ℝ, Gamma1core Dstar → ∀ d : ℝ, Dstar ≤ d →
    towA d ≤ (2 * (logStar Dstar : ℝ) + 4) / Real.logb 2 Dstar ∧
    towB d ≤ (2 * (logStar Dstar : ℝ) + 3) / Real.logb 2 (Real.logb 2 Dstar) ∧
    towC d ≤ (2 * (logStar Dstar : ℝ) + 3) / Real.logb 2 Dstar ^ ((1 : ℝ) / 2)

end EG.Spec
