module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma "the stage-1 weight `X_V`" (manuscript s7:lemVstar)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:lemVstar`.

Manuscript v6.1, `s7.tex`, Lemma [s7:lemVstar] (The stage-1 weight `X_V`):
"For `3 ≤ l ≤ R` put
`X_{V,l} := 3M_l(t^CC_l + 1)|Pool_l| + 4M_l Σ_{w ∈ Pool_l} mult_{r(w)}(w)`,
`X_V := Σ_{l=3}^{R} X_{V,l}`.
Each `X_{V,l}` is a deterministic function of the run and the pool labels, and
`E X_{V,l} ≤ (6 log₂M_l + 12) n / M_l`, `E X_V ≤ 2.1 (6 log₂D_* + 12) n / D_*`."

Formal reading.
* Setting: the standing hypotheses of s7, `EG.RunHyp N0 Dstar G run` (TRIAGE §2.6: Γ1, Γ3,
  `N0Cond`, `n ≥ N_0`, `d_1 ≥ D_*`, a valid run); `n = G.card`, `M_l = run.M G l` (a natural
  number, v6.1 (R2)), `log₂ = Real.logb 2`.
* `X_{V,l}` and `X_V` are the Defs `EG.Quot.XVl run G π l` and `EG.Quot.XV run G π`
  (`EG/Defs/Quot/Xprime.lean`), with `t^CC_l = EG.Quot.tCC M_l` (the one constant shared with
  s7:lemCC (iii)) and the pool labels `π`. For a stage-1 outcome `ω` the pool labels are `ω.pool`
  (component (1d)); `XVOf run G ω = XV run G ω.pool`.
* "Each `X_{V,l}` is a deterministic function of the run and the pool labels" is not a separate
  conjunct: it holds by the type of `XVl`, whose only random argument is the pool-label map `π`
  (T0, recorded in work/p2s/s7b.md).
* `E` is the expectation under the joint stage-1 law `EG.Stage1.law G run` (TRIAGE §2.7; only the
  pool-label marginal matters).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Quot

universe u

/-- [s7:lemVstar] "For `3 ≤ l ≤ R` put `X_{V,l} := 3M_l(t^CC_l+1)|Pool_l| + 4M_l Σ_{w∈Pool_l}
mult_{r(w)}(w)`, `X_V := Σ_{l=3}^{R} X_{V,l}`. Each `X_{V,l}` is a deterministic function of the
run and the pool labels, and `E X_{V,l} ≤ (6 log₂M_l + 12) n/M_l`,
`E X_V ≤ 2.1 (6 log₂D_* + 12) n/D_*`." (Setting `RunHyp`; `E` over the stage-1 law.) -/
def VstarStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    (∀ l : ℕ, 3 ≤ l → l ≤ run.R →
      (Stage1.law G run).expect (fun ω => (XVl run G ω.pool l : ℝ)) ≤
        (6 * Real.logb 2 (run.M G l : ℝ) + 12) * (G.card : ℝ) / (run.M G l : ℝ)) ∧
    (Stage1.law G run).expect (fun ω => (XVOf run G ω : ℝ)) ≤
      2.1 * ((6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar)

end EG.Spec
