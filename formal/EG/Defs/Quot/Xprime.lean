module

public import EG.Defs.Quot.Cand

/-!
# The stage-1 weights `X_V`, `X_pool` and the functional `X'` (manuscript s7:lemVstar,
s7:lemPay (a2), s7:defXprime)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`: the definitions inside Lemma [s7:lemVstar] (`X_{V,l}`, `X_V`), Lemma
[s7:lemCC] (iii) (`t^CC_l`), Lemma [s7:lemPay] (a2) (`ω_l(v)`) and Definition [s7:defXprime]
(`X_pool`, `X'`), quoted below. Design note: `formal/work/p2d/quot.md`. Namespace `EG.Quot`;
TRIAGE §2.10, §3 item 32.

Encoding:
* the stage-1 outcome enters, as in `EG.Chain` (work/p2d/design.md D-DES-1), through the stage data
  `S : EG.Chain.StageData V` (for `X_U` and JV-badness) and the pool labels
  `π : ↥G.verts → Option (ℕ × ℕ)` (for `Pool_l`, `r(w)` and JV-badness); for an outcome `ω` these
  are `StageData.ofOutcome ω …` and `ω.pool`;
* every quantity is a natural number (`M_l ≥ 2^{40} ≥ 1`, so `M_l − 1` in `ℕ` is the manuscript's
  value; `X_U` is a natural number, D-DES-6 of work/p2d/design.md);
* `t^CC` is one constant, `tCC M` (TRIAGE §2.10: "`tCC` is one Defs constant, used by lemCC(iii)
  and `X_{V,l}`"); the weight `ω_l(v)` is `poolWeight` (name clash with the outcome `ω`);
* the sums over rounds are over `l ∈ [3, R]` as written.
-/

@[expose] public section

namespace EG.Quot

open EG.HB EG.Chain

/-- [s7:lemCC] (iii) "`t := t^CC_l := ⌈2 log₂ M_l⌉`" (as a function of `M = M_l`). -/
noncomputable def tCC (M : ℕ) : ℕ := ⌈2 * Real.logb 2 (M : ℝ)⌉₊

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-- [s7:lemVstar] "For `3 ≤ l ≤ R` put
`X_{V,l} := 3M_l(t^CC_l + 1)|Pool_l| + 4M_l Σ_{w ∈ Pool_l} mult_{r(w)}(w)`" (`Pool_l`, `r(w)` from
the pool labels `π`; `mult_r(w) = run.mult G r w`). -/
noncomputable def XVl (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) : ℕ :=
  3 * run.M G l * (tCC (run.M G l) + 1) * (Stage1.poolL G π l).card +
    4 * run.M G l * ∑ w ∈ Stage1.poolL G π l, run.mult G (Stage1.poolRound π w) w

/-- [s7:lemVstar] "`X_V := Σ_{l=3}^{R} X_{V,l}`". -/
noncomputable def XV (π : ↥G.verts → Option (ℕ × ℕ)) : ℕ :=
  ∑ l ∈ Finset.Icc 3 run.R, XVl run G π l

open Classical in
/-- [s7:lemPay] (a2) "`ω_l(v) := c^agg_{v,l}` if `v ∈ D_l` and `ω_l(v) := M_l` otherwise"
(`c^agg` of [s6:defDesign], `EG.Chain.cAgg`). -/
noncomputable def poolWeight (l : ℕ) (v : V) : ℕ :=
  if v ∈ run.D G l then cAgg run G δ v l else run.M G l

open Classical in
/-- [s7:defXprime] "the JV-bad classed ports of round `l`" ([s7:defCand]). -/
noncomputable def jvBadPorts (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) : Finset V :=
  (classedPorts run G l).filter (JVBad run G δ S π l)

/-- [s7:defXprime] "`X_pool := Σ_{l=3}^{R} [Σ_{v ∈ Pool_l} ω_l(v) + (M_l − 1)·#{JV-bad classed
ports of round l}]`". -/
noncomputable def Xpool (π : ↥G.verts → Option (ℕ × ℕ)) : ℕ :=
  ∑ l ∈ Finset.Icc 3 run.R,
    ((∑ v ∈ Stage1.poolL G π l, poolWeight run G δ l v) +
      (run.M G l - 1) * (jvBadPorts run G δ S π l).card)

/-- [s7:defXprime] "Then `X' := X_U + X_pool + X_V`" (`X_U` of [s6:defLending], `EG.Chain.XU`).
"Each of the three terms is non-negative and is a deterministic function of the run, `δ` and the
stage-1 outcome." -/
noncomputable def Xprime (π : ↥G.verts → Option (ℕ × ℕ)) : ℕ :=
  XU run G δ S + Xpool run G δ S π + XV run G π

end EG.Quot
