module

public import EG.Defs.Gamma.Core
public import EG.Defs.Lend.COLTable
public import EG.Defs.Vortex
public import EG.Defs.HB.Run

/-!
# Γ1 with item (f), the size threshold `N_0`, Γ3, and the run hypothesis bundle
(manuscript s1:defConstants (ii), s1:condGamma Γ1 (f) and Γ3; settings of s5 and s7)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s1.tex`, Definition [s1:defConstants] (ii):
"`N_0` is an absolute constant, i.e. it depends only on `σ`, `C'` and `A`, with `N_0 ≥ 2^{40}`
(redundant: size condition (i), `L ≥ 2^{10}`, already forces `N_0 ≥ 2^{1024}`) and `N_0` at least
each of the absolute size thresholds required in the proofs of Lemma s4:lemTPV, Lemma s4:lemPV and
Theorem s4:thmVXp. Every requirement on `N_0` in this item is an *eventuality*: it holds for every
sufficiently large value of `N_0`. Indeed `N_0 ≥ 2^{40}` is a lower bound, and every other
requirement asks that an explicit inequality in `N`, which holds for all sufficiently large `N`,
hold for every `N ≥ N_0`. So such an `N_0` exists (finitely many eventualities have a common
threshold), and only its existence is used; no numerical value of `N_0` enters any proof."

`s4.tex` (after the observations): "The absolute constant `N_0` (Definition s1:defConstants) is
chosen so large that the finitely many explicit inequalities listed as *size conditions* in the
three proofs of this section hold for every `N ≥ N_0`".

[s1:condG1] (f): "for every row of the COL-JV table (Table s3:tabCOLJV), every inequality in
column 3 of that row holds at `λ`, where `M̄ := (Aμ)^{2A}` and `k̄ := 192λ^3 + (4/3)M̄^2` as in
the caption of that table." (inside "`D_* > 2`, …; and for every real `μ ≥ log₂log₂D_*`, with
`λ := 2^μ`, the following hold: …").

[s1:condG3]: "`(log₂ D_*)^{C'} ≥ 2 N_0`."

Setting of s5: "Throughout, `G` is a graph on `n ≥ N_0` vertices with `d_1 ≥ D_*`; `D_*`
satisfies Γ1–Γ4 (Condition s1:condGamma); a valid `HB^tp` run on `G` is fixed
(Definition s2:defHBtp)". Setting of s7: "Throughout, `D_*` satisfies Γ1–Γ4, `G` is a graph with
`n ≥ N_0` vertices and `d_1 ≥ D_*`, a valid `HB^tp` run on `G` is fixed, a designation `δ` is
fixed (Definition s6:defDesign), and there are no VX-parts (`𝒱 = ∅`)". The s5 setting continues
"and the stage-1 lending data of Definition s3:defCOL are drawn". These last hypotheses are not
predicates of `(N_0, D_*, G, run)` and are NOT part of `RunHyp` (see its docstring).

Formal counterparts (TRIAGE §2.4, §2.6 and §3 item 14; design note `formal/work/p2b/GAMMA.md`):
* `EG.Gamma1f D`: item (f) on the ray `μ ≥ log₂log₂D` (`EG.COLTable.col3 μ`, the one table
  predicate, rows `1 … 13`);
* `EG.Gamma1 D := Gamma1core D ∧ Gamma1f D` (the whole of Γ1; `Gamma1core` contains `2 < D`);
* `EG.N0Cond N0`: `2^{40} ≤ N_0` and the size conditions of the three vortex proofs at every
  vertex count `N ≥ N_0` (`N : ℕ`, the size predicates of `EG.Vortex` take the vertex count;
  decision D-VX-1 of `formal/work/p2d/params.md`);
* `EG.Gamma3 N0 D`: `2 N_0 ≤ (log₂ D)^{C'}` (`C' = EG.Cp = 103`, a natural-number power);
* `EG.RunHyp N0 D G run`: the standing hypotheses of s5–s7 that are about `D_*`, `N_0`, `G` and
  the run, except Γ4 (TRIAGE §2.6: "`RunHyp N0 D G run := Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧
  N0 ≤ G.card ∧ D ≤ run.d G 1 ∧ run.Valid G D`"). Γ2(a) is derived from Γ1
  (`Gamma1core.gamma2a`); Γ4 is added by the few statements that use it (`EG.Gamma4`,
  `EG/Defs/Main/Gamma.lean`), since Γ4 lives after the s7 Defs.

`GammaCond` (all four conditions) is in `EG/Defs/Main/GammaCond.lean`, because Γ4 mentions the s7
functions `ε_1`, `ε_2`.
-/

@[expose] public section

namespace EG

open Real

/-- [s1:condG1] (f) "for every row of the COL-JV table (Table s3:tabCOLJV), every inequality in
column 3 of that row holds at `λ`", for every real `μ ≥ log₂log₂D_*` with `λ := 2^μ`
(`EG.COLTable.col3 μ`: the 18 column-3 inequalities of rows `1 … 13`). -/
def Gamma1f (D : ℝ) : Prop :=
  ∀ μ : ℝ, logb 2 (logb 2 D) ≤ μ → COLTable.col3 μ

/-- [s1:condG1] Γ1 (the tower condition), items (a)–(f): "`D_* > 2`, so that `log₂log₂D_*` is
defined and positive; and for every real `μ ≥ log₂log₂D_*`, with `λ := 2^μ`, the following hold:
(a) … (f)". -/
def Gamma1 (D : ℝ) : Prop := Gamma1core D ∧ Gamma1f D

/-- [s1:defConstants] (ii) "`N_0 ≥ 2^{40}` … and `N_0` at least each of the absolute size
thresholds required in the proofs of Lemma s4:lemTPV, Lemma s4:lemPV and Theorem s4:thmVXp", i.e.
(s4) "the finitely many explicit inequalities listed as *size conditions* in the three proofs of
this section hold for every `N ≥ N_0`" (`N` a vertex count; `TPVSize`, `PVSize`, `VXSize` are the
size conditions (i), (ii), (iv) of the three proofs, (iii) being a consequence of (i)). -/
def N0Cond (N0 : ℝ) : Prop :=
  (2 : ℝ) ^ 40 ≤ N0 ∧
    ∀ N : ℕ, N0 ≤ (N : ℝ) → Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N

/-- [s1:condG3] "`(log₂ D_*)^{C'} ≥ 2 N_0`" (`C' = 103`).

Junk range: `Real.logb 2 D = logb 2 |D|`, so `Gamma3 N0 D` can hold at negative `D`
(e.g. `Gamma3 (2^40) (-(2^300))`). Every use here (`GammaCond`, `RunHyp`) is conjoined with
`Gamma1 D`, which gives `2 < D`; a Spec that takes `Gamma3` alone must add `2 < D` or `Gamma1 D`. -/
def Gamma3 (N0 D : ℝ) : Prop := 2 * N0 ≤ logb 2 D ^ Cp

/-- The standing hypotheses of s5 and s7 (without Γ4): [s5] "Throughout, `G` is a graph on
`n ≥ N_0` vertices with `d_1 ≥ D_*`; `D_*` satisfies Γ1–Γ4 …; a valid `HB^tp` run on `G` is
fixed", with `N_0` as in [s1:defConstants] (ii). TRIAGE §2.6: Γ2(a) is derived from Γ1, Γ4 is
added separately by the statements that use it (thmJVps, `C0_le`, thmMainProof,
s7:lemUHsplit (iv), s5:remConstants (b)).

`RunHyp` is NOT the whole s5/s7 setting. Not included, and to be carried by the Specs themselves:
Γ4 (above); in s5, "the stage-1 lending data of Definition s3:defCOL are drawn" (an outcome of
the stage-1 law); in s7, "a designation `δ` is fixed (s6:defDesign)" (an argument with its
validity hypothesis) and "there are no VX-parts (`𝒱 = ∅`)" (an explicit hypothesis on the run). -/
def RunHyp {V : Type*} [DecidableEq V] (N0 D : ℝ) (G : FGraph V) (run : HB.Run V) : Prop :=
  Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧ N0 ≤ (G.card : ℝ) ∧ D ≤ run.d G 1 ∧ run.Valid G D

end EG
