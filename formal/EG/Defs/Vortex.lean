module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Vortex runs: size conditions, failure functions `η` and run parameters (manuscript s4)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s4:convVortex]): "Inside one run of Lemma TPV, Lemma PV or Theorem VX⁺ below
(a *vortex run*), `Z` denotes the vertex set of the run, `N := |Z|` and `L := log₂|Z|`. All
run-local objects are written in sans-serif: the number of steps `J`; … the parameters `m`, `b`
(of Lemma HB) and `t` … None of these symbols has a meaning outside the run in which it is
defined."

Manuscript text (s4, after the observations): "The absolute constant `N_0`
(Definition s1:defConstants) is chosen so large that the finitely many explicit inequalities
listed as *size conditions* in the three proofs of this section hold for every `N ≥ N_0`".

Formal counterparts (TRIAGE §2.4 and §3 item 12; blueprint s4 node `s4:convVortex`), namespace
`EG.Vortex`:
* `L N = log₂ N`;
* the failure functions `etaTPV`, `etaPV`, `etaVX` (`η_TPV`, `η_PV`, `η_VX` of (s4:eqTPVprob),
  (s4:eqPVprob), (s4:eqVXprob));
* the size predicates `TPVSize`, `PVSize`, `VXSize`: the size conditions (i), (ii), (iv) of the
  three proofs;
* the numbers of steps `tpvJ`, `pvJ`, `vxJ`, and the Lemma-HB parameters `pvM`, `pvB` of
  Lemma PV (the only run parameters that occur in a statement: `pvJ` indexes the own classes,
  `pvM` and `pvB` constrain the given sets `A(w)`).

Names (blueprint note CONV-SYMBOL-CLASH). The same sans-serif letter has different values in the
three runs (`J = ⌊log₂(L/6)⌋` in TPV and VX⁺, `⌊log₂(L/8)⌋` in PV; `b = ⌈2^8L^2m⌉`, `⌈2^7L^2m⌉`,
`⌈2mL^2/ε_O⌉`), so every name carries its run: `tpvJ`, `pvJ`, `vxJ`, `pvM`, `pvB`. The formulas of
`tpvJ` and `vxJ` coincide, but they are different symbols of different runs.

Decisions.
* `N` is a natural number (`N = |Z|`); `L N` and the `η`'s are real. A statement about a run on
  `Z` takes `TPVSize Z.card` (etc.). `N^{-5}` and `N^{-3}` are integer powers (`zpow`);
  `e^{x}` is `Real.exp x`.
* Size condition (iii) ("`4·48 ≤ L`", "`4·64 ≤ L`", "`4·13 ≤ L`") is omitted from the
  predicates: the manuscript itself calls it "a consequence of (i)", and the Lib lemmas
  `TPVSize.cond_iii`, `PVSize.cond_iii`, `VXSize.cond_iii` derive it. So each predicate is
  equivalent to the full list (i)–(iv).
* `J := ⌊log₂(L/6)⌋` is `Nat.floor (Real.logb 2 (L/6))`. For `L ≥ 6` (so under size condition (i))
  the real `log₂(L/6)` is `≥ 0` and this is the manuscript's floor; the two-sided bound
  `6·2^J ≤ L < 12·2^J` used in the proofs is the Lib lemma `tpvJ_bounds` (and `pvJ_bounds`,
  `vxJ_bounds`). For `L < 6` the value is `0` (junk, never used).
* `m := ⌈L^6⌉` and `b := ⌈2^7L^2m⌉` are natural numbers (`Nat.ceil`).
* `η_VX` contains `log₂ L = log₂ log₂ N` (`Real.logb 2 (L N)`); it is positive under (i).
-/

@[expose] public section


namespace EG.Vortex

open Real

/-- [s4:convVortex] "`N := |Z|` and `L := log₂|Z|`": `L` as a function of `N`. -/
noncomputable def L (N : ℕ) : ℝ := logb 2 (N : ℝ)

/-- [s4:lemTPV] (s4:eqTPVprob) "`η_TPV(N) := 2LN^{-5} + 2^{96}L^{31}N^{-3} + NL e^{-3L^4/8}`". -/
noncomputable def etaTPV (N : ℕ) : ℝ :=
  2 * L N * (N : ℝ) ^ (-5 : ℤ) + (2 : ℝ) ^ 96 * L N ^ 31 * (N : ℝ) ^ (-3 : ℤ)
    + (N : ℝ) * L N * exp (-(3 * L N ^ 4 / 8))

/-- [s4:lemPV] (s4:eqPVprob) "`η_PV(N) := 2^{95}L^{31}N^{-3} + NL e^{-L^4/16}`". -/
noncomputable def etaPV (N : ℕ) : ℝ :=
  (2 : ℝ) ^ 95 * L N ^ 31 * (N : ℝ) ^ (-3 : ℤ) + (N : ℝ) * L N * exp (-(L N ^ 4 / 16))

/-- [s4:thmVXp] (s4:eqVXprob) "`η_VX(N) := 2LN^{-5} + 2^{95}L^{28}N^{-3}
+ NL e^{-3L^2/(32 log₂L)} + L e^{-N/(5000L)}`". -/
noncomputable def etaVX (N : ℕ) : ℝ :=
  2 * L N * (N : ℝ) ^ (-5 : ℤ) + (2 : ℝ) ^ 95 * L N ^ 28 * (N : ℝ) ^ (-3 : ℤ)
    + (N : ℝ) * L N * exp (-(3 * L N ^ 2 / (32 * logb 2 (L N))))
    + L N * exp (-((N : ℝ) / (5000 * L N)))

/-- [s4:lemTPV] (proof, "Size conditions") "We use: (i) `L ≥ 2^{10}`; (ii) `N ≥ L^3`;
(iii) `4·48 ≤ L` (a consequence of (i)); (iv) `η_TPV(N) ≤ 1/100`." Condition (iii) is derived
(`TPVSize.cond_iii`). -/
def TPVSize (N : ℕ) : Prop :=
  (2 : ℝ) ^ 10 ≤ L N ∧ L N ^ 3 ≤ (N : ℝ) ∧ etaTPV N ≤ 1 / 100

/-- [s4:lemPV] (proof, "Size conditions") "We use: (i) `L ≥ 2^{10}`; (ii) `N ≥ L^3`;
(iii) `4·64 ≤ L` (a consequence of (i)); (iv) `η_PV(N) ≤ 1/100`." Condition (iii) is derived
(`PVSize.cond_iii`). -/
def PVSize (N : ℕ) : Prop :=
  (2 : ℝ) ^ 10 ≤ L N ∧ L N ^ 3 ≤ (N : ℝ) ∧ etaPV N ≤ 1 / 100

/-- [s4:thmVXp] (proof, "Size conditions") "We use: (i) `L ≥ 2^{10}`; (ii) `N ≥ L^3`;
(iii) `4·13 ≤ L` (a consequence of (i)); (iv) `η_VX(N) ≤ 1/100`." Condition (iii) is derived
(`VXSize.cond_iii`). -/
def VXSize (N : ℕ) : Prop :=
  (2 : ℝ) ^ 10 ≤ L N ∧ L N ^ 3 ≤ (N : ℝ) ∧ etaVX N ≤ 1 / 100

/-- [s4:lemTPV] "`J := ⌊log₂(L/6)⌋`" (the number of steps of a TPV run). -/
noncomputable def tpvJ (N : ℕ) : ℕ := ⌊logb 2 (L N / 6)⌋₊

/-- [s4:lemPV] "`J := ⌊log₂(L/8)⌋`" (the number of steps of a PV run; the own classes are
`R_{j,c}`, `0 ≤ j < J`, `c ∈ [4]`). The same `J` is `J_Y := ⌊log(L_Y/8)⌋` of [s3:defCOL] (iii),
with `L_Y = log₂|V(Y)|`. -/
noncomputable def pvJ (N : ℕ) : ℕ := ⌊logb 2 (L N / 8)⌋₊

/-- [s4:thmVXp] "`J := ⌊log₂(L/6)⌋`" (the number of steps of a VX⁺ run; same formula as
`tpvJ`, a different run). -/
noncomputable def vxJ (N : ℕ) : ℕ := ⌊logb 2 (L N / 6)⌋₊

/-- [s4:lemPV] "`m := ⌈L^6⌉`". -/
noncomputable def pvM (N : ℕ) : ℕ := ⌈L N ^ 6⌉₊

/-- [s4:lemPV] "`b := ⌈2^7L^2m⌉`". -/
noncomputable def pvB (N : ℕ) : ℕ := ⌈(2 : ℝ) ^ 7 * L N ^ 2 * (pvM N : ℝ)⌉₊

end EG.Vortex
