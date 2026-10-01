module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma "tower facts", part (b), first sentence (manuscript s2:lemTower (b)) —
declared input of unit P4A

Statement file (`EG/Spec/**`), unit P4A (probe P-4, part 1). This statement is a DECLARED INPUT
of the probe: rows 4, 7 and 8 of the COL-JV table ([s3:lemCOLJV] (ii)) use the standing bounds
(B1) "`L_Y ≤ log M_r ≤ 2λ`" and (B3) "`s_r ≥ λ^{100}`", both quoted from [s2:lemTower] (b), and
the probe does not prove them; the stub is `EG.towerBRound` in `EG/Proof/HB/TowerB.lean`.
Justification: design note `formal/work/p2b/P4A.md`, "Declared inputs". The full Spec of
[s2:lemTower] (b) (blueprint s2b) is not written yet; its first sentence must be this statement
(import this file, do not restate it). Same conventions as `EG/Spec/HB/TowerC.lean` (unit P3A).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemTower]:
"For every valid `HB*^{τ+}` run with `d_1 ≥ D_*` (so `R ≥ 1`): … (b) For `r ≤ R`: `M_r ≤ d_r^2`;
`λ_r ≤ Λ_r ≤ 2λ_r`; `λ_r^{100} ≤ s_r ≤ 2Λ_r^σ`; `s_r ≤ P_r`; and `L_Y ≤ log M_r ≤ 2λ_r` for every
ancestor `Y` of round `r`. …"

Formal reading.
* Standing assumption of s2: `D_*` satisfies Γ1–Γ4; as for part (c) (`TowerCStatement`), the
  statement carries `Gamma1core Dstar` (items (a)–(e) of Γ1). This is stronger than the literal
  TeX hypotheses (review P4A.review1, m3), and expected to be provable: lemTower's `\deps` list
  Γ1 and Γ2 only (not Γ3, Γ4); Γ2(a) `D_* ≥ 2^{117}` (used by lemCap for `L_Y ≤ log M_r` and
  inside propDegRec) follows from `Gamma1core` (`EG.Gamma1core.gamma2a`); Γ2(b), (c) follow from
  Γ1 and, by [s1:condG2], none of their proofs uses them (Γ2(b) is itself proved in lemTower
  (b)); the hypothesis `n ≥ N_0` of propStructure is dropped (TRIAGE STR-N0). The s2 tower unit
  must confirm this form when it proves lemTower (b).
* "valid run with `d_1 ≥ D_*`": `run.Valid G Dstar` and `Dstar ≤ run.d G 1`; rounds
  `r ∈ Finset.Icc 1 run.R`.
* `M_r = run.M G r` (a natural number), `d_r = run.d G r`, `λ_r = run.lam G r`,
  `Λ_r = log M_r = run.Lam G r`, `s_r = run.s G r`, `P_r = run.P G r`, `σ = EG.sigmaC`
  (natural-number power), `λ_r^{100}` a natural-number power; `L_Y = run.LY G Y`; "ancestor `Y`
  of round `r`": `Y ∈ run.ancestors G` with `Y.1 = r`.
* The per-ancestor conjunct `Λ_r ≤ 2λ_r` repeats the round conjunct: it transcribes the TeX chain
  "`L_Y ≤ log M_r ≤ 2λ_r`" literally (review P4A.review1 re-dispatch, c2). It is logically
  redundant and harmless; the full lemTower (b) Spec of the s2 unit may drop it.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemTower] (b), first sentence: "For `r ≤ R`: `M_r ≤ d_r^2`; `λ_r ≤ Λ_r ≤ 2λ_r`;
`λ_r^{100} ≤ s_r ≤ 2Λ_r^σ`; `s_r ≤ P_r`; and `L_Y ≤ log M_r ≤ 2λ_r` for every ancestor `Y` of round
`r`." (For every valid run with `d_1 ≥ D_*`, under Γ1 (a)–(e); module docstring.) -/
def TowerBRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ r ∈ Finset.Icc 1 run.R,
      (run.M G r : ℝ) ≤ run.d G r ^ 2 ∧
      run.lam G r ≤ run.Lam G r ∧ run.Lam G r ≤ 2 * run.lam G r ∧
      run.lam G r ^ 100 ≤ (run.s G r : ℝ) ∧ (run.s G r : ℝ) ≤ 2 * run.Lam G r ^ sigmaC ∧
      run.s G r ≤ run.P G r ∧
      ∀ Y ∈ run.ancestors G, Y.1 = r →
        run.LY G Y ≤ run.Lam G r ∧ run.Lam G r ≤ 2 * run.lam G r

end EG.Spec
