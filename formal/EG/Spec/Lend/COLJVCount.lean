module

public import EG.Defs.Stage1.COL
public import EG.Defs.Gamma.Full
public import EG.Defs.Log

/-!
# Statement of Lemma COL-JV (i), the counting part (manuscript s3:lemCOLJV (i)) — declared input
of unit P4A

Statement file (`EG/Spec/**`), unit P4A (probe P-4, part 1). This statement is a DECLARED INPUT
of the probe: the derivations of rows 4 and 7 of the COL-JV table (probe nodes,
`EG/Spec/Lend/COLJVRows.lean`) use "`|I^U(Y)| ≤ 12L_Y^3`" and "`k_lend(Y) ≤ k̄`" from part (i),
and the probe does not prove part (i) (its proof needs [s2:lemTower] (a), (b), (d) and the
geometric sum over `M_l`); the stub is `EG.colJVCount` in `EG/Proof/Lend/COLJVCount.lean`.
Justification: design note `formal/work/p2b/P4A.md`, "Declared inputs". The full Spec of
[s3:lemCOLJV] (blueprint s3b `COLJVStatement`) must import this file for part (i).

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOLJV]:
"Assume condition Γ1. Let `Y` be an ancestor of round `r ≤ R`, and write `λ := λ_r` and
`μ := log λ`; if `r ≤ R-2`, write also `M := M_{r+2}`. Then:
(i) If `r ≥ R-1`, then `k_lend(Y) = 0`. If `r ≤ R-2`, then `|I^U(Y)| ≤ 12L_Y^3`,
`|I^JS(Y)| ≤ (4/3)M^2` and `|I^JV(Y)| = R-r-1 ≤ 2 log* d_r + 1`. Hence
`k_lend(Y) ≤ 12L_Y^3 + (4/3)M^2 + 2 log* d_r + 2 ≤ 24L_Y^3 + (4/3)M^2 ≤ k̄ ≤ λ^{3.3}`,
and consequently `p_Y ≥ λ^{-4}`. The JV family has `R-r-1 ≤ 2 log* d_r + 1` members. Its size is
not bounded by an absolute constant, since `d_1` may be of order `n`; the count "`+16`" must not
be used."

Formal reading (TRIAGE §2.6: s3 COL/COLJV Specs take `Gamma1 D ∧ run.Valid G D`).
* `Y ∈ run.ancestors G`, `r = Y.1`; "`r ≥ R-1`" is `run.R ≤ Y.1 + 1`, "`r ≤ R-2`" is
  `Y.1 + 2 ≤ run.R` (no natural subtraction in the guards); `R - r - 1` is natural subtraction,
  exact under the guard.
* `I^U`, `I^JS`, `I^JV`, `k_lend`, `p_Y` are `EG.Stage1.IU/IJS/IJV/klend/pY`; `L_Y = run.LY G Y`,
  `M = run.M G (Y.1 + 2)`, `d_r = run.d G Y.1`, `λ = run.lam G Y.1`, `μ = log₂ λ`,
  `k̄ = EG.COLTable.kbar μ`, `log* = EG.logStar`; `λ^{3.3}` and `λ^{-4}` are `Real.rpow` with the
  exact exponents `33/10` and `-4`.
* The last two sentences of (i) are remarks (the first repeats `|I^JV(Y)| ≤ 2 log* d_r + 1`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s3:lemCOLJV] (i) "If `r ≥ R-1`, then `k_lend(Y) = 0`. If `r ≤ R-2`, then `|I^U(Y)| ≤ 12L_Y^3`,
`|I^JS(Y)| ≤ (4/3)M^2` and `|I^JV(Y)| = R-r-1 ≤ 2 log* d_r + 1`. Hence
`k_lend(Y) ≤ 12L_Y^3 + (4/3)M^2 + 2 log* d_r + 2 ≤ 24L_Y^3 + (4/3)M^2 ≤ k̄ ≤ λ^{3.3}`, and
consequently `p_Y ≥ λ^{-4}`." (Under Γ1, for every ancestor `Y` of a valid run; module
docstring.) -/
def COLJVCountStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G,
      (run.R ≤ Y.1 + 1 → Stage1.klend G run Y = 0) ∧
      (Y.1 + 2 ≤ run.R →
        ((Stage1.IU G run Y).card : ℝ) ≤ 12 * run.LY G Y ^ 3 ∧
        ((Stage1.IJS G run Y).card : ℝ) ≤ 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 ∧
        (Stage1.IJV run Y).card = run.R - Y.1 - 1 ∧
        run.R - Y.1 - 1 ≤ 2 * logStar (run.d G Y.1) + 1 ∧
        (Stage1.klend G run Y : ℝ) ≤ 12 * run.LY G Y ^ 3 + 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 +
          2 * (logStar (run.d G Y.1) : ℝ) + 2 ∧
        12 * run.LY G Y ^ 3 + 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 +
          2 * (logStar (run.d G Y.1) : ℝ) + 2 ≤
          24 * run.LY G Y ^ 3 + 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 ∧
        24 * run.LY G Y ^ 3 + 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 ≤
          COLTable.kbar (Real.logb 2 (run.lam G Y.1)) ∧
        COLTable.kbar (Real.logb 2 (run.lam G Y.1)) ≤ run.lam G Y.1 ^ (33 / 10 : ℝ) ∧
        run.lam G Y.1 ^ (-4 : ℝ) ≤ Stage1.pY G run Y)

end EG.Spec
