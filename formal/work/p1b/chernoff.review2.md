# Clean-room review, round 2: task [chernoff]

Reviewer: clean-room agent (round 2). I did not edit any Lean file. Scratch checks are in
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/ChernoffR2.lean`
and `.../ChernoffR2b.lean`. Both import `EG.Lib.Prob.Chernoff` and compile with no errors.

**Verdict: APPROVE.** I found no fidelity, vacuity, hygiene or proof-soundness defect. Every
statement tagged with a manuscript label is the manuscript statement or a stronger one, and each
strengthening is documented. The round-1 items are resolved. Two cosmetic notes are at the end;
neither needs action.

Files reviewed (listed in `work/p1b/chernoff.md`):
- `EG/Lib/Prob/Chernoff.lean`: 1041 lines, identical to `HEAD`.
- `EGTest/Chernoff.lean`: 239 lines. The note says 238.

Foundations read:
- `EG/Defs/Prob/FinDist.lean`: `FinDist`, `prob`, `expect`, `pi`, `map`, `bernoulli`,
  `randColouring`, `rsubset`, `iIndepFun`, `IsRSubset`.
- The lemmas of `EG/Lib/Prob/{Basic,Indep,Named}.lean` that the proofs use:
  - `prob_pi_forall_mem`, `prob_pi_forall_of_dependsOn`, `prob_congr`;
  - `prob_le_expect_div`, `prob_biUnion_le`, `expect_sum_indicator`;
  - `IsRSubset.prob_superset`, `IsRSubset.subset_ae`, `prob_randColouring_apply`.

Manuscript passages checked:
- s1.tex l.419–429 (`s1:citChernoff`).
- s1.tex l.784–816 (`s1:citChernoffGen` and its derivation).
- Uses:
  - s3.tex l.145–157 (lemL15p Step 3), l.475–487 (lemL17s Case (a)), l.575–582 (Step 5),
    l.843–846 (Step 3);
  - s4.tex l.72–80 ((B)) and l.622–631 ((G3), (G4));
  - s5.tex l.122 (lemE1(a));
  - s7.tex l.138–142 (lemCand(iii)), l.764–770 (lemCC(ii)) and l.835–840 (lemUltra(ii)).

## 1. Fidelity: back-translation

I printed the elaborated statements with `#check` (scratch file). In Lean, `μ` is the
distribution and `m` is the manuscript's mean parameter `μ`.

### [s1:citChernoffGen] (a): `chernoffGen_upper`, `chernoffGen_lower`, `chernoffGen_lower_half`

Manuscript: "Let `X=∑_{i=1}^m I_i` be a sum of independent indicator variables with
`P(I_i=1)=p_i` (a Poisson-binomial variable), and let `0≤δ≤1`. (a) If `μ≥EX` then
`P(X≥(1+δ)μ)≤e^{-δ²μ/3}`; if `0≤μ≤EX` then `P(X≤(1-δ)μ)≤e^{-δ²μ/2}`."

Back-translation of the elaborated types:

> Let `Ω`, `ι` be any types, `μ` a finitely supported probability distribution on `Ω`, and
> `I : ι → Ω → ℝ` with `I i ω ∈ {0,1}` for all `i, ω`. Assume the family is mutually independent:
> for every finite `s'` and all events `A u ⊆ ℝ`, `P(∀u∈s', I u ∈ A u) = ∏ P(I u ∈ A u)`. Let
> `s` be any finite set of indices and `X := ∑_{i∈s} I i`. Then:
> - **upper tail**: for all real `m, δ` with `E X ≤ m` and `0 ≤ δ ≤ 1`,
>   `P((1+δ)·m ≤ X) ≤ exp(-(δ²m/3))`;
> - **lower tail**: for all real `m, δ` with `0 ≤ m`, `m ≤ E X` and `0 ≤ δ`,
>   `P(X ≤ (1-δ)·m) ≤ exp(-(δ²m/2))`;
> - **`δ = 1/2`**: if `0 ≤ m ≤ E X`, then `P(X < m/2) ≤ exp(-(m/8))`.

Comparison with the manuscript:
- Quantifiers match. With `ι := Fin m` and `s := univ` the statement is literally the
  manuscript's.
- The events are non-strict (`≥`, `≤`), as in the manuscript.
- `exp` is the natural exponential. The constants are 3 and 2.
- The mean hypotheses are `E X ≤ m` (upper) and `0 ≤ m ≤ E X` (lower), exactly as in the
  manuscript.
- Only deviation: the lower tail drops `δ ≤ 1`, which makes it stronger. The proof with
  `t = -δ` is valid for every `δ ≥ 0`, because `e^{-δ} ≤ 1-δ+δ²/2` holds for `δ ≥ 0`.
- The manuscript does not state `m ≥ 0` for the upper tail, and Lean does not need it:
  `E X ≥ 0`.

The `_on` variants (fix round 1) replace the two hypotheses by
`∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1` and `μ.iIndepFun (fun i : ↥s => I i)`, with the same
conclusions. Their hypotheses are implied by the unrestricted ones. They are faithful and more
usable, e.g. for the `χ_u`, `u ∈ Aw_Y(w)`, of s5:lemE1(a).

The manuscript remarks: "In particular the two bounds of Cited result s1:citChernoff hold
verbatim with `μ = E X`". These are the strict forms, and they follow by monotonicity. My scratch
file derives both from `chernoffGen_upper`/`chernoffGen_lower` in 8 lines, with `m := E X`.

### [s1:citChernoffGen] (b): `chernoffGen_tail`, `chernoffGen_tail_exp` (+ `_on`)

Manuscript: "If `EX≤μ` then for every integer `j≥1`, `P(X≥j)≤μ^j/j!≤(eμ/j)^j`."

Lean (same setting): if `E X ≤ m`, then for every `j : ℕ`:
- `P((j:ℝ) ≤ X) ≤ m^j/j!`, and
- `m^j/j! ≤ (e·m/j)^j`.

The parse is `Real.exp 1 * m / ↑j = (e·m)/j`. The case `j = 0` is included, which is stronger:
both sides are 1, and `(e m/0)^0 = 1` in Lean. Faithful.

### [s1:citChernoff]: `chernoff_binomial`

Manuscript: "Let `n` be an integer, `0≤δ,p≤1`, `X∼Bin(n,p)` and `μ≔EX=np`. Then
`P(X>(1+δ)μ)≤e^{-δ²μ/3}` and `P(X<(1-δ)μ)≤e^{-δ²μ/2}`."

Lean: `n : ℕ`, `0 ≤ p ≤ 1` (arguments `h0`, `h1`), `X : Ω → ℕ` with
`μ.map X = binomial n p h0 h1`, and `0 ≤ δ ≤ 1`. The conclusion is the conjunction
- `E X = n·p`,
- `P((1+δ)(np) < X) ≤ exp(-(δ²(np)/3))`, and
- `P(X < (1-δ)(np)) ≤ exp(-(δ²(np)/2))`.

The inequalities are strict as in the manuscript, `μ = np` is substituted, and the identity
`μ = E X = np` is proved as the first conjunct. Faithful.

`binomial n p h0 h1 := (pi fun _ : Fin n => bernoulli p h0 h1).map (fun f => #{i | f i = true})`.
This is the law of the number of successes in `n` independent Bernoulli(`p`) trials. It is the
textbook definition, and the scratch file confirms it is not degenerate:
- `(binomial n p _ _).prob {n} = p^n` for all `n`, `p`;
- `(binomial n p _ _).prob {0} = (1-p)^n`;
- `expect_binomial` (the mean is `np`).

The filter uses the standard `Bool` decidability instance: a scratch example with
`s.filter (fun i => f i = true)` unifies with the statement. So downstream users are not stuck
on a classical instance.

### Task-specific forms

Task: "for independent Bernoulli(pᵢ) coordinates … μ := Σ pᵢ, or any μ ≥ EX".

**Bernoulli products** (`chernoff_pi_bernoulli_upper/lower/tail`):
- Upper: `∑_{i∈s} p i ≤ m` and `0 ≤ δ ≤ 1` ⟹ `P((1+δ)m ≤ #{i∈s | f i}) ≤ e^{-δ²m/3}`.
- Lower: `0 ≤ m ≤ ∑ p i` and `δ ≥ 0` ⟹ the lower bound.
- Tail: `∑ p i ≤ m` ⟹ both bounds of (b).

The events are non-strict, which implies the task's strict forms.

"The binomial case as a corollary": `chernoff_binomial` and `binomial_prob_ge_le/le_le`.

"P(X ≥ j) ≤ μ^j/j! … union bound over j-subsets": the proof of `IndepEvents.prob_ge_nat_le` is
exactly that. It uses `prob_biUnion_le` over `s.powersetCard j`, then
`Chernoff.sum_powersetCard_prod_le` (`e_j(p) ≤ (∑p)^j/j!`).

"An arbitrary finite product space in which the indicators are functions of distinct
coordinates": `chernoff_pi_dependsOn_upper/lower/tail`.
- Hypothesis `hE`: each event `E u` (`u ∈ s`) depends only on the coordinates in the block `B u`.
- Hypothesis `hB`: the blocks are pairwise disjoint on `s`.
- Single distinct coordinates are the case `B u = {σ u}`.
- The mean hypothesis is `∑_u P(E u)`, on the appropriate side of `m`.

This generalizes the task and is correct.

**Core** (`IndepEvents.*`): `IndepEvents μ s A :≡ ∀ T ⊆ s, P(⋂_{i∈T} A i) = ∏_{i∈T} P(A i)`.
This is the textbook mutual independence of events. It is equivalent to independence of the
indicators, and it appears only in hypotheses. The `chernoff_*` forms take `X` equal to the count
on outcomes of positive weight. This is sound, because `prob` sums over the support only
(`prob_congr`).

**Downstream uses.** All manuscript uses are covered:

| Use | Form available |
|---|---|
| s3:lemL15p Step 3 (δ=1/2, colour class) | `chernoff_randColouring_lower_half` (used by `EG/Proof/Link/L15.lean`) |
| s3:lemL17s Case (a) and Step 3 | `IsRSubset.chernoff_card_inter_lower_half`, `IsRSubset.chernoff_card_lower_half` |
| Step 5 (δ = 0.09; strict `>` from `≥`) | `IsRSubset.chernoff_card_inter_lower`, `IsRSubset.chernoff_card_upper` |
| s4 (G3) (δ = 1/100) | `chernoff_binomial_upper`, `IsRSubset.chernoff_card_upper` |
| s4 (B)/(G4) | `chernoffGen_lower_half(_on)` with `m = m'p ≤ E X` |
| s5:lemE1(a), s7:lemCand(iii) | `chernoffGen_lower_half(_on)` |
| s7:lemCC(ii), s7:lemUltra(ii) (`(eμ/j)^j`, `EX ≤ μ`) | `chernoffGen_tail_exp(_on)` |

### Elementary inequalities (required by the task to be proved; they are)

- `exp_neg_le_quadratic`: `e^{-x} ≤ 1-x+x²/2` (`x ≥ 0`).
- `two_mul_div_two_add_le_log_one_add`: `log(1+x) ≥ 2x/(2+x)`, from the series
  `hasSum_log_sub_log_of_abs_lt_one`.
- `sq_div_two_add_le`: `(1+δ)log(1+δ) − δ ≥ δ²/(2+δ)`, which is `≥ δ²/3` on `[0,1]`.
- `pow_add_mul_le_pow`, `sum_powersetCard_prod_le`: `e_j ≤ (∑p)^j/j!`.
- `pow_div_factorial_le`: `m^j/j! ≤ (em/j)^j`.

I re-derived both optimizations by hand.
- Upper tail, `t = log(1+δ) ≥ 0`. The exponent is `−t(1+δ)m + δ∑p ≤ −m((1+δ)log(1+δ)−δ)`. This
  uses `δ ≥ 0` and `∑p ≤ m`.
- Lower tail, `t = −δ`. The exponent is `δ(1−δ)m + (e^{−δ}−1)∑p ≤ m(δ−δ²+e^{−δ}−1) ≤ −mδ²/2`.
  This uses `e^{−δ}−1 ≤ 0`, `m ≤ ∑p` and `m ≥ 0`.

Both match the Lean calc chains.

## 2. Vacuity

- **Satisfiable hypotheses.** `EGTest/Chernoff.lean` instantiates every main form on concrete
  distributions:
  - 100 and 20 fair coins, 10 rare coins;
  - `iIndepFun` from `iIndepFun_eval_pi`;
  - an `_on` family that is not {0,1}-valued off `s`;
  - `binomial 10 (1/2)` with `X = id`;
  - disjoint blocks of coordinates;
  - a (1/3)-random subset;
  - a 3-colouring.

  The resulting bounds are `< 1`.
- **`IndepEvents` is not trivially true.** The scratch file refutes it for two copies of one
  fair-coin event (`1/2 ≠ 1/4`).
- **`binomial` is not degenerate.** See the point masses at `0` and `n` above.
- **The conclusions are not trivial.** The (b) bound is attained with equality for one fair coin
  (`P(X ≥ 1) = 1/2 = m^1/1!`, scratch file). The exponential bounds are `< 1` for `δ, m > 0`.
- **No contradictory hypotheses.** Every hypothesis is one of: a real inequality, `iIndepFun` /
  `IndepEvents`, 0/1-valuedness, block disjointness and dependence, `IsRSubset`, or a law
  equality. The tests realize all of them together.

## 3. Hygiene

- `python3 scripts/lint.py`: `lint (development): 0 findings`.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.Prob.Chernoff`: `inspected 495
  constants under [EG]; 0 use sorryAx; 0 violations`. The same holds with `--no-sorry`. The
  allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
- `LEAN_NUM_THREADS=2 scripts/check.sh EG/Lib/Prob/Chernoff.lean 900`:
  `rc=0 errors=0 sorry-warnings=0`. The olean is newer than the source.
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/Chernoff.lean 900`:
  `rc=0 errors=0 sorry-warnings=0`.
- `scripts/lock.py check`: `0 violations`.
- `git diff 461e308 -- EG/Defs EG/Spec` is empty: no Defs or Spec file changed.
- The Chernoff files equal `HEAD`.
- Module conventions:
  - `module`, then `public import`, then the docstring, then `public section`.
  - Both new definitions (`IndepEvents`, `binomial`) are `@[expose]`.
  - The test file is a plain file.
  - There is no `set_option maxHeartbeats` and no `sorry`.
- Docstring tags: `[s1:citChernoffGen](a)/(b)` and `[s1:citChernoff]` are on the formalizing
  declarations.

## 4. The proofs prove the stated results

- **Dependency chain.** Each cited form is a thin wrapper:

  `chernoffGen_*`
  → `iIndepFun.indepEvents_eq_one(_of_subtype)` + `expect_sum_of_zero_or_one(_on)`
  → `IndepEvents.chernoff_*`
  → `IndepEvents.prob_ge_le` / `prob_le_le` / `prob_ge_nat_le(_exp)`
  → `expect_exp_mul_sum_le` / union bound
  → `prob_mul_le_mul_le` (Markov on `e^{tX}`).
- **Wrapper steps are pointwise identities.** `sum_eq_sum_indicator_of_zero_or_one(_on)` holds for
  every `ω`, and `prob_congr` is used only on positive-weight outcomes.
- **No auxiliary definition in a conclusion.** Conclusions use only `prob`, `expect` and
  `Real.exp`. The Lib definitions `IndepEvents` and `binomial` occur only in hypotheses. I checked
  above that both are the textbook notions and that both are satisfiable.
- **Private lemmas** (`card_eq_sum_indicator_*`, `sum_prob_*`, `IsRSubset.card_inter_eq_sum`, …)
  are proof internals.
- **The MGF identity** `E e^{tX} = ∏ ((e^t−1)p_i + 1)` expands `∏(1 + (e^t−1)1_{A_i})` with
  `prod_add`, then uses independence on each `T ⊆ s`. Its bound
  `≤ exp((e^t−1)∑p_i)` uses `1+x ≤ e^x` factorwise, with nonnegative factors.

## Round-1 items

1. (minor) Hypotheses on all of `ι`: **resolved**. The five `_on` variants and the two
   subtype-to-`IndepEvents` lemmas are proved and tested on a family that is not {0,1}-valued
   off `s`.
2. (cosmetic) `(em/j)^j` form for Bernoulli products: **resolved**. `chernoff_pi_bernoulli_tail`
   and `IsRSubset.chernoff_card_inter_tail` now return both bounds.
3. (cosmetic) Root imports: **still pending, integrator action.**
   - `EG.lean` / `EGTest.lean` do not yet import `EG.Lib.Prob.Chernoff` / `EGTest.Chernoff`.
   - `EG/Proof/Link/L15.lean` already imports `EG.Lib.Prob.Chernoff`.
4. (cosmetic) JLR `t`-forms: no action needed. They appear only in the manuscript's derivation.

## Issues (round 2)

1. (cosmetic) There is no named corollary for the manuscript sentence "In particular the two
   bounds of Cited result s1:citChernoff hold verbatim with `μ = E X`": the strict forms for a
   Poisson-binomial `X` with `m := E X`. It follows by `prob_mono` from `chernoffGen_upper` and
   `chernoffGen_lower` in a few lines (proved in my scratch file). Optional: add
   `chernoffGen_strict` if a downstream node quotes that sentence.
2. (cosmetic) The design note says `EGTest/Chernoff.lean` has 238 lines; it has 239. No action.
