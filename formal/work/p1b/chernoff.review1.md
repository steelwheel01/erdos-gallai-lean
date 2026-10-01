# Clean-room review, round 1: task [chernoff]

Reviewer: clean-room agent (round 1). I did not edit any Lean file. My scratch checks are in
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/ChernoffVac.lean`,
which imports `EG.Lib.Prob.Chernoff`. It compiles with no errors.

**Verdict: APPROVE.** I found no fidelity, vacuity or hygiene defect. Every statement is the
manuscript statement or a stronger one: non-strict tails, `δ ≥ 0` for the lower tail, and `j : ℕ`
including `0`. Each strengthening is documented and proved. The items below are minor or cosmetic.

Files reviewed (as listed in `work/p1b/chernoff.md`):
- `EG/Lib/Prob/Chernoff.lean` (923 lines)
- `EGTest/Chernoff.lean`

Foundations used by the statements, which I also read: `EG/Defs/Prob/FinDist.lean` (`FinDist`,
`prob`, `expect`, `pi`, `map`, `bernoulli`, `rsubset`, `randColouring`, `iIndepFun`,
`IsRSubset`).

Manuscript passages checked:
- s1.tex l.419–429 (`s1:citChernoff`)
- s1.tex l.784–816 (`s1:citChernoffGen` and its derivation)
- Uses:
  - s3.tex l.145–157 (lemL15p Step 3)
  - s3.tex l.475–487 (lemL17s Case (a))
  - s3.tex l.575–582 (Step 5, `δ = 0.09`, strict upper tail `|V| > 1.09ρn`)
  - s3.tex l.843–846 (Step 3)
  - s4.tex l.72–80 ((B)) and l.622–625 ((G3))
  - s5.tex l.122 (lemE1(a))
  - s7.tex l.138–142 (lemCand(iii)), l.764–770 (lemCC(ii)) and l.835–840 (lemUltra(ii))

## 1. Fidelity: back-translation

In the Lean statements `μ` is the distribution and `m` is the manuscript's mean parameter `μ`.
I printed the elaborated types with `#check` (scratch file).

### `chernoffGen_upper` / `chernoffGen_lower` / `chernoffGen_lower_half` vs s1:citChernoffGen (a)

Manuscript: "Let `X=∑_{i=1}^m I_i` be a sum of independent indicator variables with
`P(I_i=1)=p_i` (a Poisson-binomial variable), and let `0≤δ≤1`. (a) If `μ≥EX` then
`P(X≥(1+δ)μ)≤e^{-δ²μ/3}`; if `0≤μ≤EX` then `P(X≤(1-δ)μ)≤e^{-δ²μ/2}`."

Back-translation: let `Ω`, `ι` be any types, `μ` a finitely supported distribution on `Ω`, and
`I : ι → Ω → ℝ` a family with `I i ω ∈ {0,1}` for all `i, ω`. Assume the family is mutually
independent (`μ.iIndepFun I`: for every finite `s'` and all events `A u ⊆ ℝ`,
`P(∀u∈s', I u ∈ A u) = ∏ P(I u ∈ A u)`). Then for every finite `s ⊆ ι`, with `X = ∑_{i∈s} I i`:
- upper tail: for every real `m, δ` with `E X ≤ m` and `0 ≤ δ ≤ 1`,
  `P((1+δ)m ≤ X) ≤ exp(-(δ²m/3))`;
- lower tail: for every real `m, δ` with `0 ≤ m ≤ E X` and `0 ≤ δ`,
  `P(X ≤ (1-δ)m) ≤ exp(-(δ²m/2))`;
- `lower_half` is the lower tail at `δ = 1/2`, with a strict event: `P(X < m/2) ≤ exp(-m/8)`.

| Item | Lean | Manuscript | OK? |
|---|---|---|---|
| variables | `I i ω = 0 ∨ I i ω = 1`, `iIndepFun I` | independent indicators | yes: `ι := Fin m`, `s := univ` is literally the manuscript. Hypotheses on all of `ι` are harmless (index by `↥s`); see issue 1 |
| mean hyp. (upper) | `μ.expect (∑ i∈s, I i) ≤ m` | `μ ≥ EX` | yes |
| mean hyp. (lower) | `0 ≤ m`, `m ≤ E X` | `0 ≤ μ ≤ EX` | yes |
| δ (upper) | `0 ≤ δ`, `δ ≤ 1` | `0 ≤ δ ≤ 1` | yes |
| δ (lower) | `0 ≤ δ` only | `0 ≤ δ ≤ 1` | stronger; the proof is valid for all `δ ≥ 0` |
| upper event | `(1+δ)*m ≤ X` | `X ≥ (1+δ)μ` | yes (non-strict) |
| lower event | `X ≤ (1-δ)*m` | `X ≤ (1-δ)μ` | yes (non-strict) |
| bounds | `exp(-(δ^2*m/3))`, `exp(-(δ^2*m/2))` | `e^{-δ²μ/3}`, `e^{-δ²μ/2}` | yes; natural `exp` |

The manuscript does not state `m ≥ 0` for the upper tail. The Lean statement does not need it:
`E X ≥ 0` implies it.

### `chernoffGen_tail` / `chernoffGen_tail_exp` vs s1:citChernoffGen (b)

Manuscript: "If `EX≤μ` then for every integer `j≥1`, `P(X≥j)≤μ^j/j!≤(eμ/j)^j`."

Lean (same setting as above): if `E X ≤ m`, then for every `j : ℕ`:
- `P((j:ℝ) ≤ X) ≤ m^j/j!`, and
- `m^j/j! ≤ (Real.exp 1 * m / j)^j` (conjunction).

The case `j = 0` is included and trivially true: `1 ≤ 1`, and `(e m/0)^0 = 1` in Lean. The parse
`Real.exp 1 * m / ↑j` is `(e·m)/j`. Faithful, and stronger in `j`.

### `chernoff_binomial` (+ `_upper`, `_lower`, `expect_of_map_eq_binomial`) vs s1:citChernoff

Manuscript: "Let `n` be an integer, `0≤δ,p≤1`, `X∼Bin(n,p)` and `μ≔EX=np`. Then
`P(X>(1+δ)μ)≤e^{-δ²μ/3}` and `P(X<(1-δ)μ)≤e^{-δ²μ/2}`."

Lean: `n : ℕ`, `p : ℝ` with `h0 : 0 ≤ p`, `h1 : p ≤ 1`, `X : Ω → ℕ` with
`μ.map X = binomial n p h0 h1`, and `0 ≤ δ ≤ 1`. The conclusion is the conjunction
- `E X = n p`,
- `P((1+δ)(np) < X) ≤ exp(-(δ²(np)/3))`, and
- `P(X < (1-δ)(np)) ≤ exp(-(δ²(np)/2))`.

These are the strict inequalities of the manuscript, with `μ = np`, and the claim `E X = np` is
also proved. Faithful.

`binomial n p h0 h1 := (pi fun _ : Fin n => bernoulli p h0 h1).map (fun f => #{i | f i = true})`.
This is exactly the law of the number of successes in `n` independent Bernoulli(`p`) trials:
`bernoulli` puts weight `p` on `true`. The definition is not degenerate:
- `expect_binomial` proves the mean is `np`;
- my scratch check evaluates `E` of `binomial 4 (1/2)` to `2`;
- the test instantiates the hypothesis `μ.map X = binomial …` with `X = id`.

### Task-specific forms

- **Bernoulli product, count over `s`**: `chernoff_pi_bernoulli_upper/lower/tail`.
  - Upper: `∑_{i∈s} p i ≤ m`, `0≤δ≤1` ⟹ `P((1+δ)m ≤ #{i∈s | f i}) ≤ e^{-δ²m/3}`.
  - Lower: `0 ≤ m ≤ ∑ p i` and `δ ≥ 0`.
  - Tail: `P(j ≤ #…) ≤ m^j/j!`.

  These are faithful to the task ("μ := Σ pᵢ, or any μ ≥ EX") and are non-strict, hence stronger
  than the task's strict forms.
- **Arbitrary finite product, indicators of distinct coordinates**:
  `chernoff_pi_dependsOn_upper/lower/tail`. The events `E u` (`u ∈ s`) depend only on the blocks
  `B u`: `∀ f g, (∀ i ∈ B u, f i = g i) → f ∈ E u → g ∈ E u`. The blocks are pairwise disjoint
  on `s`. This generalizes "functions of distinct coordinates" (`B u = {σ u}`, `σ` injective).
  The mean hypothesis is `∑_u P(E u)` on the correct side of `m`. Correct.
- **Core** (`IndepEvents.*`). The hypothesis `IndepEvents μ s A` is
  `∀ T ⊆ s, P(⋂_{i∈T} A i) = ∏_{i∈T} P(A i)`, the textbook mutual independence of events. The
  mean is `∑_{i∈s} P(A i)`, which equals `E X`. The versions `chernoff_*` take a real `X` that
  equals the count on outcomes of positive weight. That is sound, since `prob` sums over the
  support only.
- **Uses in the manuscript** (read above). Every form I found is available.

  | Use | Available form |
  |---|---|
  | s3:lemL15p Step 3 (`Z ≤ su/(2k)`, colour class, δ = 1/2) | `chernoff_randColouring_lower` (non-strict event) or `_lower_half` |
  | s3:lemL17s Case (a) | `IsRSubset.chernoff_card_inter_lower_half` |
  | s3:lemL17s Step 3 | `IsRSubset.chernoff_card_lower_half` |
  | Step 5 (δ = 0.09; strict `>` follows from `≥`) | `_card_inter_lower`, `_card_upper` |
  | s4 (G3) (δ = 1/100) | `chernoff_binomial_upper` / `IsRSubset.chernoff_card_upper` |
  | s4 (B) | `chernoffGen_lower_half` with `m = m'p ≤ E X`; the coupling is not needed |
  | s5:lemE1(a), s7:lemCand(iii) | `chernoffGen_lower_half` |
  | s7:lemCC(ii), s7:lemUltra(ii) (`(eμ/j)^j`, `E X ≤ μ`) | `chernoffGen_tail_exp` |

  The conditional distributions are ordinary `FinDist`s (`cond`), so the theorems apply to them.

### Elementary inequalities

The task requires the inequalities to be proved, and they are:
- `sq_div_two_add_le`: `(1+δ)log(1+δ) - δ ≥ δ²/(2+δ)`, hence `≥ δ²/3` on `[0,1]`. It uses
  `log(1+x) ≥ 2x/(2+x)`, which comes from Mathlib's series `hasSum_log_sub_log_of_abs_lt_one`.
- `exp_neg_le_quadratic`: `e^{-x} ≤ 1-x+x²/2`.
- `sum_powersetCard_prod_le`: `e_j(p) ≤ (∑p)^j/j!`, by induction.
- `pow_div_factorial_le`: `m^j/j! ≤ (em/j)^j`.

I checked the arithmetic of both optimizations by hand:
- Upper tail, `t = log(1+δ)`. The exponent is `-t(1+δ)m + δ∑p ≤ -m((1+δ)log(1+δ) - δ)`. This
  uses `δ ≥ 0` and `∑p ≤ m`.
- Lower tail, `t = -δ`. The exponent is `δ(1-δ)m + (e^{-δ}-1)∑p ≤ m(δ - δ² + e^{-δ} - 1) ≤ -mδ²/2`.
  This uses `e^{-δ} - 1 ≤ 0` and `m ≤ ∑p`, and holds for all `δ ≥ 0`.

## 2. Vacuity

- All hypotheses are jointly satisfiable with non-trivial data. `EGTest/Chernoff.lean`
  instantiates every main form on concrete product spaces: `iIndepFun` from `iIndepFun_eval_pi`,
  `E X = 10` computed, a binomial with `X = id`, disjoint blocks, a ρ-random subset and a
  colouring. The resulting bounds are `< 1`.
- `IndepEvents` is not trivially true. The scratch file proves that on one fair coin the family
  `A 0 = A 1 = {f | f 0 = true}` is not `IndepEvents` (`1/2 ≠ 1/4`).
- The conclusions are not trivial. The right-hand sides `exp(-δ²m/3)`, `exp(-δ²m/2)` and `m^j/j!`
  are `< 1` for `δ, m > 0` (resp. small `m`). The scratch file shows the tail (b) is tight for one
  fair coin (`P(X ≥ 1) = 1/2 = m^1/1!`).
- There is no contradictory hypothesis: all hypotheses are inequalities on real parameters,
  `iIndepFun`/`IndepEvents`, `0/1`-valuedness, and a law equality. The tests realize each of them.

## 3. Hygiene

- `python3 scripts/lint.py`: `lint (development): 0 findings`.
- `lake env lean --run scripts/Axioms.lean --prefix EG --no-sorry EG.Lib.Prob.Chernoff`:
  `inspected 484 constants under [EG]; 0 use sorryAx; 0 violations`.
- `LEAN_NUM_THREADS=2 scripts/check.sh EG/Lib/Prob/Chernoff.lean 900`: `rc=0 errors=0
  sorry-warnings=0`. I also checked that the olean is newer than the source.
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/Chernoff.lean 900`: `rc=0 errors=0
  sorry-warnings=0`.
- Module conventions:
  - `module`, then `public import`, then the docstring, then `public section` (Lib).
  - Both new definitions carry `@[expose]`.
  - The test file is a plain (non-module) file.
- No `set_option maxHeartbeats`. No forbidden token. No Defs or Spec file touched: `git status`
  shows only the two task files modified under `formal/EG*`.
- Docstring tags: `[s1:citChernoffGen](a)`/`(b)` on the `chernoffGen_*` and on the `IndepEvents`
  core forms; `[s1:citChernoff]` on the binomial forms.

## 4. The proofs prove the stated results

- The public statements that carry a manuscript tag use only:
  - Defs vocabulary: `iIndepFun`, `expect`, `prob`, `map`;
  - `binomial` (checked above);
  - `IndepEvents`, a hypothesis-side Lib predicate equal to the textbook definition.

  No auxiliary definition appears in a conclusion, so nothing is weakened through a definition.
- `private` lemmas (`card_eq_sum_indicator_*`, `sum_prob_*`, `IsRSubset.card_inter_eq_sum`, …)
  are proof internals only.
- The cited forms are thin wrappers around the core:
  - `expect_sum_of_zero_or_one` turns the literal `E X` into `∑ P(I i = 1)`;
  - `sum_eq_sum_indicator_of_zero_or_one` identifies `∑ I i` with the indicator count
    pointwise, for every `ω`.
  - Nothing is lost.

## Issues

1. (minor, usability) The `chernoffGen_*` forms ask for `I i ω ∈ {0,1}` and `μ.iIndepFun I` on
   the whole index type `ι`, although `X` sums only over `s`.
   - This is faithful: `ι := Fin m`, `s := univ` is exactly the manuscript's statement.
   - Downstream families that are indicators and independent only for `i ∈ s` (e.g. `χ_u`,
     `u ∈ Aw_Y(w)` in s5:lemE1(a)) must be re-indexed by `↥s`. Alternatively they can use the
     `IndepEvents` core, which is already relative to `s`.

   Suggested fix (optional): add a variant with hypotheses restricted to `s`, i.e.
   `∀ i ∈ s, ∀ ω, …` and `μ.iIndepFun (fun i : ↥s => I i)`. Alternatively, add a lemma
   converting `μ.iIndepFun (fun i : ↥s => I i)` to `μ.IndepEvents s (fun i => {I i = 1})`.
2. (cosmetic) `chernoff_pi_bernoulli_tail` gives only `m^j/j!`, not `(em/j)^j`, unlike
   `chernoff_pi_dependsOn_tail`. It is available through `IndepEvents.chernoff_tail_exp`.
   Suggested fix (optional): add the second form for uniformity.
3. (cosmetic) The roots `EG.lean` and `EGTest.lean` do not yet import `EG.Lib.Prob.Chernoff` /
   `EGTest.Chernoff`. The author was told not to edit roots. The integrator should add the two
   imports.
4. (cosmetic) The JLR `t`-forms used in the manuscript's derivation of (a) are not formalized.
   They are not part of the cited statement and have no downstream use. No action needed unless a
   later node cites them.
