module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The local parameters (eqStar) of Theorem 16* (manuscript s3:eqStar)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text (s3.tex, paragraph "Local parameters", equation `s3:eqStar`):
"Let `n ≥ 2` be the number of vertices of the graph at hand, `L := log n`, `ε' ∈ [2^{-7},1]` its
expansion parameter, `ρ ∈ (0,1]` a density and `t ≥ 1` a multiplicity. The following quantities
are local to this subsection. … Throughout, `ℓ_*`, `d_*`, `λ_*`, `Δ_*`, `M_*` and `K_*` are
integers.
  `ℓ_* := ⌊2^{10}L^3⌋`, `g_* := ε'/(8L^2)`, `q_* := 0.9ρ`,
  `p_* ∈ (0,1]` given by `(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)`,
  `d_* := ⌈1/p_*⌉`, `λ_* := ⌈6/p_*⌉`, `Δ_* := λ_* + ⌈d_*λ_*/3⌉`, `σ_* := 24L^2/ε'`,
  `θ_* := 2^{19}ℓ_*^2L^3/(ε'ρ^2)`, `μ_* := ε'/(6θ_*L^2)`, `s̄_* := 2^{28}tL^8/ρ`,
  `M_* := ⌈2.1/ρ⌉`, `K_* := ⌈6 s̄_* θ_* L^2/ε'⌉`."
(`log = log₂` throughout, [s1:convGraphs] (b).)

Formal counterparts (TRIAGE §2.11, blueprint s3a node `s3:eqStar`), namespace `EG.Star`:
`L`, `ell`, `g`, `q`, `p`, `d`, `lam`, `Delta`, `sigma`, `theta`, `mu`, `sbar`, `M`, `K`.
Each takes exactly the inputs among `(n : ℕ) (ε' ρ t : ℝ)` on which its formula depends, in this
order (so `EG.Star.theta n ε' ρ`, `EG.Star.K n ε' ρ t`, `EG.Star.M ρ`). The well-expanding
predicate of Lemma 17* is `EG.FGraph.IsWellExpanding` (`EG/Defs/Graph.lean`).

Types. The six quantities that the manuscript calls integers (`ℓ_*, d_*, λ_*, Δ_*, M_*, K_*`) are
natural numbers (`Nat.floor` / `Nat.ceil` of a real; under the domain hypotheses the arguments of
the ceilings are positive, so `⌈·⌉₊` is the integer ceiling). The others are real numbers.
Decimals are exact rationals: `0.9 = 9/10`, `2.1 = 21/10`.

`p_*` (decision STAR-PSTAR-IMPLICIT). The manuscript defines `p_*` implicitly, and (S2) proves
that it exists and is unique. We use the explicit solution
  `p_* = 1 - b^{1/(ℓ_*-1)}` with `b := (1-ρ)/(1-(9/10)ρ)` (`Real.rpow`).
For `n ≥ 2` and `0 < ρ ≤ 1` we have `ℓ_* ≥ 2^{10}` and `b ∈ [0,1)`, and the Lib lemmas
`EG.Star.p_pos`, `EG.Star.p_le_one`, `EG.Star.one_sub_p_pow` and `EG.Star.p_unique`
(`EG/Lib/Link/Star.lean`) show that this `p_*` lies in `(0,1]`, satisfies
`(1-p_*)^{ℓ_*-1} = b` (natural-number power) and is the only such number: it is the `p_*` of the
manuscript.

Totality. All definitions are total. Outside the domain `n ≥ 2`, `ε' ∈ [2^{-7},1]`,
`ρ ∈ (0,1]`, `t ≥ 1` they are junk values (for example `n ≤ 1` gives `L = 0` and `ℓ_* = 0`, and
then the exponent `1/(ℓ_*-1) = -1` of `p_*` is meaningless); every statement that uses them must
carry the domain hypotheses (blueprint note STAR-DOMAIN).
-/

@[expose] public section


namespace EG.Star

open Real

/-- [s3:eqStar] "`L := log n`" (`log = log₂`), for the number `n` of vertices of the graph at
hand. -/
noncomputable def L (n : ℕ) : ℝ := logb 2 (n : ℝ)

/-- [s3:eqStar] "`ℓ_* := ⌊2^{10}L^3⌋`" (an integer; a natural number here). -/
noncomputable def ell (n : ℕ) : ℕ := ⌊(2 : ℝ) ^ 10 * L n ^ 3⌋₊

/-- [s3:eqStar] "`g_* := ε'/(8L^2)`". -/
noncomputable def g (n : ℕ) (ε' : ℝ) : ℝ := ε' / (8 * L n ^ 2)

/-- [s3:eqStar] "`q_* := 0.9ρ`". -/
noncomputable def q (ρ : ℝ) : ℝ := 9 / 10 * ρ

/-- [s3:eqStar] "`p_* ∈ (0,1]` given by `(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)`", as the explicit
solution `1 - ((1-ρ)/(1-0.9ρ))^{1/(ℓ_*-1)}` (`Real.rpow`). That it is the unique solution in
`(0,1]` (for `n ≥ 2`, `0 < ρ ≤ 1`) is `EG.Star.p_spec` / `EG.Star.p_unique`. -/
noncomputable def p (n : ℕ) (ρ : ℝ) : ℝ :=
  1 - ((1 - ρ) / (1 - 9 / 10 * ρ)) ^ ((1 : ℝ) / ((ell n : ℝ) - 1))

/-- [s3:eqStar] "`d_* := ⌈1/p_*⌉`" (an integer; a natural number here). -/
noncomputable def d (n : ℕ) (ρ : ℝ) : ℕ := ⌈1 / p n ρ⌉₊

/-- [s3:eqStar] "`λ_* := ⌈6/p_*⌉`" (an integer; a natural number here). -/
noncomputable def lam (n : ℕ) (ρ : ℝ) : ℕ := ⌈6 / p n ρ⌉₊

/-- [s3:eqStar] "`Δ_* := λ_* + ⌈d_*λ_*/3⌉`" (an integer; a natural number here). -/
noncomputable def Delta (n : ℕ) (ρ : ℝ) : ℕ :=
  lam n ρ + ⌈((d n ρ : ℝ) * (lam n ρ : ℝ)) / 3⌉₊

/-- [s3:eqStar] "`σ_* := 24L^2/ε'`". -/
noncomputable def sigma (n : ℕ) (ε' : ℝ) : ℝ := 24 * L n ^ 2 / ε'

/-- [s3:eqStar] "`θ_* := 2^{19}ℓ_*^2L^3/(ε'ρ^2)`". -/
noncomputable def theta (n : ℕ) (ε' ρ : ℝ) : ℝ :=
  (2 : ℝ) ^ 19 * (ell n : ℝ) ^ 2 * L n ^ 3 / (ε' * ρ ^ 2)

/-- [s3:eqStar] "`μ_* := ε'/(6θ_*L^2)`". -/
noncomputable def mu (n : ℕ) (ε' ρ : ℝ) : ℝ := ε' / (6 * theta n ε' ρ * L n ^ 2)

/-- [s3:eqStar] "`s̄_* := 2^{28}tL^8/ρ`". -/
noncomputable def sbar (n : ℕ) (ρ t : ℝ) : ℝ := (2 : ℝ) ^ 28 * t * L n ^ 8 / ρ

/-- [s3:eqStar] "`M_* := ⌈2.1/ρ⌉`" (an integer; a natural number here). -/
noncomputable def M (ρ : ℝ) : ℕ := ⌈(21 / 10 : ℝ) / ρ⌉₊

/-- [s3:eqStar] "`K_* := ⌈6 s̄_* θ_* L^2/ε'⌉`" (an integer; a natural number here). -/
noncomputable def K (n : ℕ) (ε' ρ t : ℝ) : ℕ :=
  ⌈6 * sbar n ρ t * theta n ε' ρ * L n ^ 2 / ε'⌉₊

end EG.Star
