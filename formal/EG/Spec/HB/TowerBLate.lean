module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma "tower facts", part (b), the late-round clauses used by JS-LC (manuscript
s2:lemTower (b)) — declared input of unit P2J

Statement file (`EG/Spec/**`), unit P2J (probe P-2, part 2). This statement is a DECLARED INPUT
of the probe: Step 8 of the proof of Lemma JS-LC [s6:lemJSLC] ("The number of ancestors `Y` of
rounds `≤ l − 2` is `ν_l ≤ 2.74n/P_{l−2}` (Lemma s2:lemTower(b), which completes (K1) of
Proposition s2:propOV). Moreover `γ_l ≤ P_{l−2}/M_l` and `P_{l−2} ≥ M_l^{13}` (Lemma
s2:lemTower(b))") cites it, and the probe does not prove it; the stub is `EG.towerBLate` in
`EG/Proof/HB/TowerBLate.lean`. Justification: design note `formal/work/p2b/P2J.md`, "Declared
inputs". The first sentence of (b) is `EG.Spec.TowerBRoundStatement` (`EG/Spec/HB/TowerB.lean`,
unit P4A); the full Spec of [s2:lemTower] (b) (blueprint s2b, not written yet) must imply both.

Manuscript v6.1, `s2.tex`, Lemma [s2:lemTower]:
"For every valid `HB*^{τ+}` run with `d_1 ≥ D_*` (so `R ≥ 1`): … (b) … For `3 ≤ l ≤ R`:
`M_l ≤ (A log λ_{l−2})^{2A} ≤ λ_{l−2}^{1.6}`; `P_{l−2} ≥ M_l^{13}`; and
`P_{l−2}/2 ≥ M_l log⁴ M_l`. … Finally, completing (K1) of Proposition s2:propOV, the number `ν_l`
of ancestors of rounds at most `l − 2` satisfies `ν_l ≤ 2.74 n/P_{l−2}` for `3 ≤ l ≤ R`."

Formal reading (same conventions as `TowerBRoundStatement` and `TowerCStatement`).
* Standing assumption of s2: `D_*` satisfies Γ1–Γ4; the statement carries `Gamma1core Dstar`
  (items (a)–(e) of Γ1), as `TowerBRoundStatement` does; "valid run with `d_1 ≥ D_*`" is
  `run.Valid G Dstar` and `Dstar ≤ run.d G 1`.
* `M_l = run.M G l`, `P_{l−2} = run.P G (l - 2)` (natural numbers; `l ≥ 3`, so `l − 2` is the real
  difference); `M_l^{13} ≤ P_{l−2}` in `ℕ`.
* `ν_l = run.nuAnc G l` (the number of ancestors `Y` with `r(Y) + 2 ≤ l`), `n = G.card`;
  `ν_l ≤ 2.74 n/P_{l−2}` in `ℝ`.
* Only the two clauses used by JS-LC are stated; the others (`M_l ≤ λ_{l−2}^{1.6}`,
  `P_{l−2}/2 ≥ M_l log⁴ M_l`, …) are not used by the probe.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemTower] (b), late-round clauses: "For `3 ≤ l ≤ R`: … `P_{l−2} ≥ M_l^{13}` … Finally,
completing (K1) of Proposition s2:propOV, the number `ν_l` of ancestors of rounds at most `l − 2`
satisfies `ν_l ≤ 2.74 n/P_{l−2}` for `3 ≤ l ≤ R`." (For every valid run with `d_1 ≥ D_*`, under
Γ1 (a)–(e); module docstring.) -/
def TowerBLateStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
      run.M G l ^ 13 ≤ run.P G (l - 2) ∧
      (run.nuAnc G l : ℝ) ≤ 2.74 * (G.card : ℝ) / (run.P G (l - 2) : ℝ)

end EG.Spec
