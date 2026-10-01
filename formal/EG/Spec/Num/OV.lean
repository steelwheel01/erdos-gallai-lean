module

public import EG.Defs.Constants
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The numeric facts of Lemma OV, Lemma 14^τ(b) and Proposition OV (manuscript s2)

Statement file (`EG/Spec/**`), unit NUM (cheap numeric probes, TRIAGE §4). Proofs:
`EG/Proof/Num/OV.lean`. Design note: `formal/work/p2b/NUM.md`.

Manuscript v6.1, `s2.tex`: Lemma [s2:lemOVgeneric] ("generic overlap bound, Lemma OV"), the proof
of Lemma [s2:lem14tau] (b), and the proof of Proposition [s2:propOV] ("overlap constants on
HB^{tp}"). Throughout `ε = 2^{-5}` (`EG.epsC`), `log = log₂` and `c_OV := log₂(4/3)`
(`Real.logb 2 (4/3)`).

The thin constant (TRIAGE §1b OV-CONST-546): `1.6(1 + 1/c_OV) ≤ 5.46` needs
`c_OV ≥ 0.414508…` (true value `0.415037…`; slack 0.13% in `c_OV`, 0.08% in `5.46`). The rational
bound `12/29 ≤ c_OV` (enough for `3.42`) does not suffice (it gives `5.4667 > 5.46`); `17/41 ≤ c_OV`
(i.e. `2^{65} ≥ 3^{41}`) does. `NumOVLogFourThirdsStatement` records the bound `17/41`, and the
negative fact about `12/29` is checked in `EGTest/ProbeNUM.lean`.

The "OV potential" of the task list is the charge estimate of OV(a),
`∑_{j≥0} 1/(log M + j c_OV)^2 ≤ 1/log^2 M + 1/(c_OV log M)` (`NumOVChargeSumStatement`, for
every finite partial sum, which is equivalent to the bound on the series of non-negative terms
and is the form the proof uses: the charges come from finitely many ancestors).
-/

@[expose] public section


namespace EG.Spec

open Finset

/-- [s2:lemOVgeneric] (a), proof: "The charge received by `(Leaf,u)` is therefore at most
`cε ∑_{j≥0} 1/(log M + j c_OV)^2 ≤ cε(1/log^2M + ∫_0^∞ dx/(log M + x c_OV)^2)
= cε(1/log^2M + 1/(c_OV log M))`, because the summand is decreasing in `j`." The real-analysis
content, for `x = log M > 0` and any `c = c_OV > 0`, for every finite partial sum. -/
def NumOVChargeSumStatement : Prop :=
  ∀ x c : ℝ, 0 < x → 0 < c → ∀ k : ℕ,
    ∑ j ∈ range k, 1 / (x + j * c) ^ 2 ≤ 1 / x ^ 2 + 1 / (c * x)

/-- [s2:lemOVgeneric] (helper; TRIAGE OV-CONST-546): `c_OV = log₂(4/3) ≥ 17/41`, equivalently
`2^{65} ≥ 3^{41}`. Not a manuscript sentence: it is the rational lower bound through which the
constants `3.42` and `5.46` below are proved. -/
def NumOVLogFourThirdsStatement : Prop :=
  (17 : ℝ) / 41 ≤ Real.logb 2 (4 / 3) ∧ (3 : ℕ) ^ 41 ≤ 2 ^ 65

/-- [s2:lemOVgeneric] (a) and (c), and the instance `c = 1`: "(a)
`Δ_{≥M} ≤ cε(1/log^2M + 1/(c_OV log M))S ≤ 3.42cεS/log M`"; proof: "For `M ≥ 2` we have
`log M ≥ 1`, so `1/log^2M ≤ 1/log M`, and `1+1/c_OV = 3.4095… ≤ 3.42`"; "(c) `S ≤ n_0/(1−3.42cε)`"
(for `c > 0` with `3.42cε < 1`); instance `c = 1`: "its total leaf size is at most
`n_0/(1−3.42ε) ≤ 1.12n_0`", "Finally `1/(1−3.42/32) = 1.1196… ≤ 1.12`".
Conjuncts: `1 + 1/c_OV ≤ 3.42`; the second inequality of (a) for every `c > 0` and real `M ≥ 2`;
`3.42ε < 1` (the hypothesis of the lemma at `c = 1`); `1/(1 − 3.42ε) ≤ 1.12`.
(The manuscript's decimal `3.4095…` is a misprint for `3.4094…`; see NUM.md, finding NUM-F1.) -/
def NumOVConstStatement : Prop :=
  1 + 1 / Real.logb 2 (4 / 3) ≤ 3.42 ∧
    (∀ c M : ℝ, 0 < c → 2 ≤ M →
      c * epsC * (1 / Real.logb 2 M ^ 2 + 1 / (Real.logb 2 (4 / 3) * Real.logb 2 M)) ≤
        3.42 * c * epsC / Real.logb 2 M) ∧
    3.42 * epsC < 1 ∧ 1 / (1 - 3.42 * epsC) ≤ 1.12

/-- [s2:lemOVgeneric] (c), proof: "`S = n_0 + ∑_ν|N''_ν| = n_0 + Δ_{≥2} ≤ n_0 + 3.42cεS` by (a)
with `M = 2`. Rearranging gives (c)", where (c) is "`S ≤ n_0/(1−3.42cε)`" under the lemma's
hypothesis "`c > 0` with `3.42cε < 1`". The rearrangement, for reals `S`, `n_0`. (Added in fix
round 1, review I-4.) -/
def NumOVRearrangeStatement : Prop :=
  ∀ c S n₀ : ℝ, 0 < c → 3.42 * c * epsC < 1 → S ≤ n₀ + 3.42 * c * epsC * S →
    S ≤ n₀ / (1 - 3.42 * c * epsC)

/-- [s2:lemOVgeneric], instance `c = 1`, proof: "`|ν_1| = |U_ν| + |N_ν| < (1+ε)(2/3)m < (3/4)m`,
using `log m ≥ 1`". The constant: `(1+ε)(2/3) < 3/4` (`0.6875`; `ε = 2^{-5}`). (Added in fix
round 1, review I-4.) -/
def NumOVInstanceStatement : Prop :=
  (1 + epsC) * (2 / 3) < 3 / 4

/-- [s2:lem14tau] (b), proof: "By (a), `|N''| < 1.5ε|U|/log^2m ≤ 1.5·(128/127)ε|U'|/log^2m
< 1.52ε|U'|/log^2m`. (The first bound of (a) even gives
`|N''| < 1.25·(128/127)ε|U'|/log^2m < 1.26ε|U'|/log^2m`; the looser constant `1.6` suffices.)
[…] As `3.42·1.6ε = 0.171 < 1`, Lemma OV applies with `c=1.6`: by its part (c),
`S ≤ n_0/(1−5.472ε) ≤ n_0/(1−5.5ε) = 1.2075…n_0 ≤ 1.21n_0`; by its part (a),
`Δ_{≥M} ≤ 1.6ε(1+1/c_OV)S/log M ≤ 5.46εS/log M`, since `1.6(1+1/c_OV) = 5.455…`."
The last conjunct is the thin one (slack 0.08%). -/
def NumLem14tauConstStatement : Prop :=
  1.5 * (128 / 127 : ℝ) < 1.52 ∧ 1.25 * (128 / 127 : ℝ) < 1.26 ∧ (1.52 : ℝ) ≤ 1.6 ∧
    3.42 * 1.6 * epsC = 0.171 ∧ (0.171 : ℝ) < 1 ∧ (3.42 : ℝ) * 1.6 = 5.472 ∧
    1 / (1 - 5.472 * epsC) ≤ 1 / (1 - 5.5 * epsC) ∧ 1 / (1 - 5.5 * epsC) ≤ 1.21 ∧
    1.6 * (1 + 1 / Real.logb 2 (4 / 3)) ≤ 5.46

/-- [s2:propOV], proof: "`S_r ≤ n/(1−5.472ε) ≤ 1.21n`, and for `M ≥ 2`,
`Δ_{≥M} ≤ 5.46εS_r/log M ≤ 6.61εn/log M` (s2:eqDupComposite)"; "(K1) […]
`∑|Z^0| ≤ S_r ≤ 1.21n ≤ 1.37n`"; "(K2) […] `≤ 6.61εn/log P_r ≤ 7.6εn/log P_r`" and
"`≤ 2dup_r ≤ 15.2εn/log P_r`"; "(K3) […] at most `4dup_r ≤ 30.4εn/log P_r`" and
"`≤ 2Δ_{≥P_r} ≤ 13.3εn/log P_r ≤ 16εn/log P_r`". The constants: `5.46·1.21 ≤ 6.61`
(`6.6066`; slack 0.05%), `6.61 ≤ 7.6`, `1.21 ≤ 1.37`, `2·7.6 = 15.2`, `4·7.6 = 30.4`,
`2·6.61 ≤ 13.3`, `13.3 ≤ 16`. -/
def NumPropOVConstStatement : Prop :=
  (5.46 : ℝ) * 1.21 ≤ 6.61 ∧ (6.61 : ℝ) ≤ 7.6 ∧ (1.21 : ℝ) ≤ 1.37 ∧ 2 * (7.6 : ℝ) = 15.2 ∧
    4 * (7.6 : ℝ) = 30.4 ∧ 2 * (6.61 : ℝ) ≤ 13.3 ∧ (13.3 : ℝ) ≤ 16

end EG.Spec
