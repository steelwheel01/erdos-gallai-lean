module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core
public import EG.Defs.Log
public import EG.Spec.HB.LacunaryGeom

/-!
# Statements of Lemma "tower-lacunary sums", parts (ii)–(iv) (manuscript s2:lemLacunary)

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:lemLacunary. Definitions: `EG/Defs/HB/Run.lean` (`EG.HB.HypH`), `EG/Defs/Log.lean`
(`EG.logStar`), `EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemLacunary]:
"Let `x_0 := log D_*`.
(i) If `X_1, …, X_R ≥ 0` and `X_r ≤ X_{r+1}/2` for all `r < R`, then `Σ_{r≤R} X_r ≤ 2X_R` and
`Σ_{r≤R} (R-r+1) X_r ≤ 4X_R`.
(ii) For a valid run with `R ≥ 1`, the degree recursion gives `λ_r ≥ 2^{λ_{r+1}/A}` for all
`r < R`. Hence, if `F : [x_0,∞) → [0,∞)` is non-increasing and `F(2^{x/A}) ≤ F(x)/2` for all
`x ≥ x_0`, then `Σ_{r≤R} F(λ_r) ≤ 2F(λ_R) ≤ 2F(x_0)` and `Σ_{r≤R} (R-r+1) F(λ_r) ≤ 4F(x_0)`; for
the shifted sums (when `R ≥ 3`), `Σ_{l=3}^R F(λ_{l-2}) ≤ 2F(λ_{R-2}) ≤ 2F(x_0)` and
`Σ_{l=3}^R (R-l+1) F(λ_{l-2}) ≤ 4F(λ_{R-2}) ≤ 4F(x_0)`.
(iii) More generally, if `F : [x_0,∞) → [0,∞)` satisfies
(H) `F(y) ≤ F(x)/2` whenever `x ≥ x_0` and `y ≥ 2^{x/A}`,
then `Σ_{r≤R} F(λ_r) ≤ 2F(λ_R)` and `Σ_{r≤R} (R-r+1) F(λ_r) ≤ 4F(λ_R)` (and likewise for
`F(λ_{l-2})`).
(iv) Under Γ1, condition (H) holds for `F(x) = x^{-a}` (every `a ≥ 1/100`), for `F(x) = 1/log x`
and for `F(x) = (95 log x + 8) x^{-b}` (every `b ≥ 1`; not used in this manuscript), all three
non-increasing on `[x_0,∞)`; and for the three functions `F(x) = (2 log*(2^x) + 2)/η(x)` with
`η(x) ∈ {x, x^{1/2}, log x}` (note `2 log*(2^x) + 2 = 2 log* x + 4` for `x > 1`; not used in this
manuscript). Each of these three satisfies `F(x) ≤ 2F(x_0)` for all `x ≥ x_0` (not used in this
manuscript)."
and, from the proof of (ii): "Hence `2^{x/A} ≥ x ≥ x_0` for `x ≥ x_0`. If `F` is non-increasing
and `F(2^{x/A}) ≤ F(x)/2`, then for `y ≥ 2^{x/A}` we get `F(y) ≤ F(2^{x/A}) ≤ F(x)/2`, which is
(H)." The closing paragraph of the lemma (how round-`l` quantities are summed; an example not used
in the manuscript) is commentary and is not formalized (blueprint LAC-COMMENTARY).

Where each part is stated.
* (i): `EG.Spec.LacunaryGeomStatement` (`EG/Spec/HB/LacunaryGeom.lean`, unit P3B; not restated).
* (ii): `LacunaryMonoStatement` (the function-level step "monotone and halving ⇒ (H)", with
  `2^{x/A} ≥ x` from the proof) and `LacunaryIIStatement` (the run form with all displayed
  bounds, including `λ_r ≥ 2^{λ_{r+1}/A}`).
* (iii): `LacunarySeqStatement` (for an abstract real sequence `λ_1, …, λ_R` with `λ_r ≥ x_0` and
  `λ_r ≥ 2^{λ_{r+1}/A}`: the form in which the proof uses it, blueprint LAC-SEQ-FORM; `x_0`
  arbitrary, no condition on `D_*`) and `LacunaryRunStatement` (the run form, with the shifted
  sums of "likewise for `F(λ_{l-2})`" written out as in (ii)).
* (iv): `LacunaryExamplesStatement`.
* `LacunaryStatement`: the conjunction of all parts.

Formal reading.
* `log = Real.logb 2`, `x_0 = logb 2 D_*`, `A = EG.Aexp = 105`; `2^{x/A}`, `x^{-a}`, `x^{-b}`,
  `x^{1/2}` are `Real.rpow`; `log* = EG.logStar` (a natural number, cast to `ℝ`).
* "`F : [x_0,∞) → [0,∞)`": a total `F : ℝ → ℝ` with the hypotheses `0 ≤ F x` for `x ≥ x_0`
  (nonnegativity, needed for (i)); "non-increasing" is `AntitoneOn F (Set.Ici x_0)`; (H) is
  `EG.HB.HypH x_0 F` (Defs; it quantifies over `x, y ≥ x_0`, the domain of `F`). In (ii) the
  hypothesis "`F(2^{x/A}) ≤ F(x)/2` for all `x ≥ x_0`" evaluates `F` at `2^{x/A}`, which lies in
  the domain (`2^{x/A} ≥ x` under Γ1, a conjunct of `LacunaryMonoStatement`).
* Condition on `D_*`: the run forms use Proposition s2:propDegRec (Γ1 (a), (b)) and (ii), (iv)
  use Γ1 (a), (b) directly (blueprint LAC-GAMMA); they carry `Gamma1core Dstar`. The sequence form
  (iii) needs no condition.
* Rounds are 1-indexed: "`r ≤ R`" is `r ∈ Finset.Icc 1 R`, "`r < R`" is `r ∈ Finset.Ico 1 R`.
  `R ≥ 1` is a hypothesis of every run form: for `R = 0` the bound `0 ≤ 2F(λ_0)` would read `F` at
  the junk value `λ_0 = log d(G) < x_0` (outside the domain); (ii) states it, and in (iii) it is
  implicit in "`F(λ_R)`". The shifted sums range over `l ∈ Finset.Icc 3 R` with `λ_{l-2}` the
  natural subtraction (exact for `l ≥ 3`), and `λ_{R-2}` with `R ≥ 3` (blueprint LAC-SHIFT-NAT).
  The weights `R - r + 1`, `R - l + 1` are natural numbers (exact, as `r, l ≤ R`) cast to `ℝ`.
* (iv), the three `log*` functions: `η` ranges over the three functions `x ↦ x`, `x ↦ x^{1/2}`,
  `x ↦ log x`; for each, (H), nonnegativity on `[x_0,∞)` and `F(x) ≤ 2F(x_0)` for `x ≥ x_0`. The
  first three functions also get nonnegativity (implicit in "`F : [x_0,∞) → [0,∞)`" of (iii),
  which (iv) feeds). The three `log*` functions are not claimed non-increasing (they are not;
  blueprint LAC-NONMONO-LOGSTAR).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemLacunary] (ii), the function-level step of the proof: under Γ1, "`2^{x/A} ≥ x ≥ x_0`
for `x ≥ x_0`. If `F` is non-increasing and `F(2^{x/A}) ≤ F(x)/2`, then for `y ≥ 2^{x/A}` we get
`F(y) ≤ F(2^{x/A}) ≤ F(x)/2`, which is (H)" (`x_0 = log D_*`). -/
def LacunaryMonoStatement : Prop :=
  ∀ Dstar : ℝ, Gamma1core Dstar →
    (∀ x : ℝ, Real.logb 2 Dstar ≤ x → x ≤ (2 : ℝ) ^ (x / (Aexp : ℝ))) ∧
    ∀ F : ℝ → ℝ, AntitoneOn F (Set.Ici (Real.logb 2 Dstar)) →
      (∀ x : ℝ, Real.logb 2 Dstar ≤ x → F ((2 : ℝ) ^ (x / (Aexp : ℝ))) ≤ F x / 2) →
      HypH (Real.logb 2 Dstar) F

/-- [s2:lemLacunary] (ii) "For a valid run with `R ≥ 1`, the degree recursion gives
`λ_r ≥ 2^{λ_{r+1}/A}` for all `r < R`. Hence, if `F : [x_0,∞) → [0,∞)` is non-increasing and
`F(2^{x/A}) ≤ F(x)/2` for all `x ≥ x_0`, then `Σ_{r≤R} F(λ_r) ≤ 2F(λ_R) ≤ 2F(x_0)` and
`Σ_{r≤R} (R-r+1) F(λ_r) ≤ 4F(x_0)`; for the shifted sums (when `R ≥ 3`),
`Σ_{l=3}^R F(λ_{l-2}) ≤ 2F(λ_{R-2}) ≤ 2F(x_0)` and
`Σ_{l=3}^R (R-l+1) F(λ_{l-2}) ≤ 4F(λ_{R-2}) ≤ 4F(x_0)`" (`x_0 = log D_*`; under Γ1 (a)–(e)). -/
def LacunaryIIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → 1 ≤ run.R →
    (∀ r ∈ Finset.Ico 1 run.R, (2 : ℝ) ^ (run.lam G (r + 1) / (Aexp : ℝ)) ≤ run.lam G r) ∧
    ∀ F : ℝ → ℝ, (∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ F x) →
      AntitoneOn F (Set.Ici (Real.logb 2 Dstar)) →
      (∀ x : ℝ, Real.logb 2 Dstar ≤ x → F ((2 : ℝ) ^ (x / (Aexp : ℝ))) ≤ F x / 2) →
      ∑ r ∈ Finset.Icc 1 run.R, F (run.lam G r) ≤ 2 * F (run.lam G run.R) ∧
      2 * F (run.lam G run.R) ≤ 2 * F (Real.logb 2 Dstar) ∧
      ∑ r ∈ Finset.Icc 1 run.R, ((run.R - r + 1 : ℕ) : ℝ) * F (run.lam G r) ≤
        4 * F (Real.logb 2 Dstar) ∧
      (3 ≤ run.R →
        ∑ l ∈ Finset.Icc 3 run.R, F (run.lam G (l - 2)) ≤ 2 * F (run.lam G (run.R - 2)) ∧
        2 * F (run.lam G (run.R - 2)) ≤ 2 * F (Real.logb 2 Dstar) ∧
        ∑ l ∈ Finset.Icc 3 run.R, ((run.R - l + 1 : ℕ) : ℝ) * F (run.lam G (l - 2)) ≤
          4 * F (run.lam G (run.R - 2)) ∧
        4 * F (run.lam G (run.R - 2)) ≤ 4 * F (Real.logb 2 Dstar))

/-- [s2:lemLacunary] (iii), sequence form (the form the proof uses: "By (H) with `x = λ_{r+1}` and
`y = λ_r`, `F(λ_r) ≤ F(λ_{r+1})/2`, and (i) applies to `X_r := F(λ_r)`"): if
`F : [x_0,∞) → [0,∞)` satisfies (H), and `λ_1, …, λ_R ≥ x_0` with `λ_r ≥ 2^{λ_{r+1}/A}` for all
`r < R`, then `Σ_{r≤R} F(λ_r) ≤ 2F(λ_R)` and `Σ_{r≤R} (R-r+1) F(λ_r) ≤ 4F(λ_R)` (any real `x_0`;
no condition on `D_*`). -/
def LacunarySeqStatement : Prop :=
  ∀ (x0 : ℝ) (F : ℝ → ℝ) (lam : ℕ → ℝ) (R : ℕ), 1 ≤ R →
    (∀ x : ℝ, x0 ≤ x → 0 ≤ F x) → HypH x0 F →
    (∀ r ∈ Finset.Icc 1 R, x0 ≤ lam r) →
    (∀ r ∈ Finset.Ico 1 R, (2 : ℝ) ^ (lam (r + 1) / (Aexp : ℝ)) ≤ lam r) →
    ∑ r ∈ Finset.Icc 1 R, F (lam r) ≤ 2 * F (lam R) ∧
    ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * F (lam r) ≤ 4 * F (lam R)

/-- [s2:lemLacunary] (iii) "if `F : [x_0,∞) → [0,∞)` satisfies (H) `F(y) ≤ F(x)/2` whenever
`x ≥ x_0` and `y ≥ 2^{x/A}`, then `Σ_{r≤R} F(λ_r) ≤ 2F(λ_R)` and
`Σ_{r≤R} (R-r+1) F(λ_r) ≤ 4F(λ_R)` (and likewise for `F(λ_{l-2})`)", for a valid run with
`R ≥ 1` (`x_0 = log D_*`; under Γ1 (a)–(e); the shifted sums as in (ii), for `R ≥ 3`). -/
def LacunaryRunStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V) (F : ℝ → ℝ),
    Gamma1core Dstar → run.Valid G Dstar → 1 ≤ run.R →
    (∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ F x) → HypH (Real.logb 2 Dstar) F →
    ∑ r ∈ Finset.Icc 1 run.R, F (run.lam G r) ≤ 2 * F (run.lam G run.R) ∧
    ∑ r ∈ Finset.Icc 1 run.R, ((run.R - r + 1 : ℕ) : ℝ) * F (run.lam G r) ≤
      4 * F (run.lam G run.R) ∧
    (3 ≤ run.R →
      ∑ l ∈ Finset.Icc 3 run.R, F (run.lam G (l - 2)) ≤ 2 * F (run.lam G (run.R - 2)) ∧
      ∑ l ∈ Finset.Icc 3 run.R, ((run.R - l + 1 : ℕ) : ℝ) * F (run.lam G (l - 2)) ≤
        4 * F (run.lam G (run.R - 2)))

/-- [s2:lemLacunary] (iv) "Under Γ1, condition (H) holds for `F(x) = x^{-a}` (every
`a ≥ 1/100`), for `F(x) = 1/log x` and for `F(x) = (95 log x + 8) x^{-b}` (every `b ≥ 1`), all
three non-increasing on `[x_0,∞)`; and for the three functions `F(x) = (2 log*(2^x) + 2)/η(x)` with
`η(x) ∈ {x, x^{1/2}, log x}` (note `2 log*(2^x) + 2 = 2 log* x + 4` for `x > 1`). Each of these
three satisfies `F(x) ≤ 2F(x_0)` for all `x ≥ x_0`" (`x_0 = log D_*`; nonnegativity on
`[x_0,∞)` added, module docstring). -/
def LacunaryExamplesStatement : Prop :=
  ∀ Dstar : ℝ, Gamma1core Dstar →
    (∀ a : ℝ, 1 / 100 ≤ a →
      HypH (Real.logb 2 Dstar) (fun x => x ^ (-a)) ∧
      AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Ici (Real.logb 2 Dstar)) ∧
      ∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ x ^ (-a)) ∧
    (HypH (Real.logb 2 Dstar) (fun x => 1 / Real.logb 2 x) ∧
      AntitoneOn (fun x : ℝ => 1 / Real.logb 2 x) (Set.Ici (Real.logb 2 Dstar)) ∧
      ∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ 1 / Real.logb 2 x) ∧
    (∀ b : ℝ, 1 ≤ b →
      HypH (Real.logb 2 Dstar) (fun x => (95 * Real.logb 2 x + 8) * x ^ (-b)) ∧
      AntitoneOn (fun x : ℝ => (95 * Real.logb 2 x + 8) * x ^ (-b))
        (Set.Ici (Real.logb 2 Dstar)) ∧
      ∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ (95 * Real.logb 2 x + 8) * x ^ (-b)) ∧
    (∀ x : ℝ, 1 < x →
      2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2 = 2 * (logStar x : ℝ) + 4) ∧
    ∀ η : ℝ → ℝ,
      (η = (fun x => x) ∨ η = (fun x => x ^ (1 / 2 : ℝ)) ∨ η = (fun x => Real.logb 2 x)) →
      HypH (Real.logb 2 Dstar) (fun x => (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / η x) ∧
      (∀ x : ℝ, Real.logb 2 Dstar ≤ x → 0 ≤ (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / η x) ∧
      ∀ x : ℝ, Real.logb 2 Dstar ≤ x →
        (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / η x ≤
          2 * ((2 * (logStar ((2 : ℝ) ^ Real.logb 2 Dstar) : ℝ) + 2) / η (Real.logb 2 Dstar))

/-- [s2:lemLacunary], all parts: (i) `LacunaryGeomStatement`, (ii) `LacunaryMonoStatement` and
`LacunaryIIStatement`, (iii) `LacunarySeqStatement` and `LacunaryRunStatement`, (iv)
`LacunaryExamplesStatement`. -/
def LacunaryStatement : Prop :=
  LacunaryGeomStatement ∧ LacunaryMonoStatement ∧ LacunaryIIStatement.{u} ∧
    LacunarySeqStatement ∧ LacunaryRunStatement.{u} ∧ LacunaryExamplesStatement

end EG.Spec
