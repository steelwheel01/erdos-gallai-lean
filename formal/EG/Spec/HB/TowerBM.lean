module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma "tower facts", part (b), the `M_l` clauses used by s5:lemParent
(manuscript s2:lemTower (b)) — declared input of probe P-4, part 2

Statement file (`EG/Spec/**`), unit P4B (probe P-4, part 2). This statement is a DECLARED INPUT of
the probe: Lemma [s5:lemParent] uses it in Step 5 ("By Lemma s2:lemTower(b) (row 12 of Table
s3:tabCOLJV) and Lemma s2:lemTower(a), `M_l ≤ λ_{l-2}^{1.6} ≤ λ_r^{1.6} ≤ ⌈λ_r^{1.6}⌉ = t_Y`") and
in Step 9 ("`M_l ≤ (A log λ_{l-2})^{2A}` (Lemma s2:lemTower(b))", "`Σ_l 1/M_l ≤ 2/D_*`
(Lemma s2:lemTower(b))"). Its proof (the (R2) algebra and Γ1 (c) at `μ = log λ_{l-2}`) is the s2
tower unit's job. The other clauses of (b) are `EG.Spec.TowerBRoundStatement` (first sentence,
P4A) and `EG.Spec.TowerBLateStatement` (`P_{l-2} ≥ M_l^{13}`, `ν_l ≤ 2.74n/P_{l-2}`, P2J); the
clauses `P_{l-2}/2 ≥ M_l log^4 M_l` (only in the unused fact (F-b)), `M_{l-1} ≥ 2M_l`,
`P_r ≥ 2P_{r+1}` and the `ψ`-sum are not used by P4B and not stated here. Design note
`formal/work/p2b/P4B.md`.

Manuscript v6.1, `s2.tex`, Lemma [s2:lemTower] (b): "… For `3 ≤ l ≤ R`:
`M_l ≤ (A log λ_{l-2})^{2A} ≤ λ_{l-2}^{1.6}`; `P_{l-2} ≥ M_l^{13}`; and
`P_{l-2}/2 ≥ M_l log^4 M_l`. … Moreover `Σ_{l≤R} 1/M_l ≤ 2/D_*` and …"

Formal reading (same conventions as `TowerBRoundStatement`, `TowerBLateStatement`): Γ1 (a)–(e)
(`Gamma1core`), a valid run with `d_1 ≥ D_*`; rounds `3 ≤ l ≤ R`, `l - 2` natural subtraction
(exact there); `log = log₂`; `A = Aexp = 105`, the exponent `2A` a natural power; the sum over
`l ≤ R` is over the rounds `1 ≤ l ≤ R`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemTower] (b), the `M_l` clauses: "For `3 ≤ l ≤ R`: `M_l ≤ (A log λ_{l-2})^{2A} ≤
λ_{l-2}^{1.6}` … Moreover `Σ_{l≤R} 1/M_l ≤ 2/D_*`" (for every valid run with `d_1 ≥ D_*`, under
Γ1 (a)–(e)). -/
def TowerBMStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    (∀ l : ℕ, 3 ≤ l → l ≤ run.R →
      (run.M G l : ℝ) ≤ ((Aexp : ℝ) * Real.logb 2 (run.lam G (l - 2))) ^ (2 * Aexp) ∧
      ((Aexp : ℝ) * Real.logb 2 (run.lam G (l - 2))) ^ (2 * Aexp) ≤
        run.lam G (l - 2) ^ (1.6 : ℝ)) ∧
    ∑ l ∈ Finset.Icc 1 run.R, (1 : ℝ) / (run.M G l : ℝ) ≤ 2 / Dstar

end EG.Spec
