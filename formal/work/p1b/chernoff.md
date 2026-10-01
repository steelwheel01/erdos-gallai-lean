# P1b task [chernoff]: Chernoff bounds for sums of independent indicators (design note)

Manuscript: [s1:citChernoff] (B–M Theorem 4, binomial) and [s1:citChernoffGen] (JLR Theorems
2.1 and 2.8, Poisson-binomial, with the tail (b)). Uses read: s3:lemL15p Step 3, s3:lemL17s
Case (a) and Step 3, s4 (B) and (G3)/(G4), s5:lemE1(a), s7:lemCand(iii), s7:lemCC(ii),
s7:lemUltra(ii).

## Files and modules (all new)
- `EG/Lib/Prob/Chernoff.lean` (module `EG.Lib.Prob.Chernoff`, `public section`, 1041 lines).
  Imports `EG.Lib.Prob.Indep` and `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.
- `EGTest/Chernoff.lean` (module `EGTest.Chernoff`, non-module file, 238 lines).

Both compile with 0 errors, 0 warnings and 0 `sorry` (`scripts/check.sh`, `LEAN_NUM_THREADS=2`).
`lake build EG.Lib.Prob.Chernoff` succeeds. `python3 scripts/lint.py`: 0 findings. The axiom scan
of `EG.Lib.Prob.Chernoff` (prefix EG) inspected 495 constants: 0 use sorryAx, 0 violations
(after fix round 1).

## Definitions (both in `EG/Lib/Prob/Chernoff.lean`, `@[expose]`)
- `FinDist.IndepEvents μ s A : Prop := ∀ T ⊆ s, μ.prob {ω | ∀ i ∈ T, ω ∈ A i} = ∏ i ∈ T, μ.prob (A i)`.
  This is the textbook mutual independence of the events `A i`, `i ∈ s` (equivalently, of their
  indicators). It is the one hypothesis of the core lemmas. It is the minimal hypothesis the
  exponential-moment and union-bound proofs use, and every source of independence in the
  project implies it (see "Sources" below).
- `FinDist.binomial n p h0 h1 : FinDist ℕ := (pi fun _ : Fin n => bernoulli p h0 h1).map
  (fun f => #{i | f i = true})`, the law of the number of successes in `n` Bernoulli(p) trials.
  "`X ∼ Bin(n, p)` under `μ`" is written `μ.map X = binomial n p h0 h1`.

No Defs file was changed.

## Main statements

The random variable of the core is `X ω = ∑_{i ∈ s} (A i).indicator 1 ω` (a real sum of
indicators: it needs no decidability instances). `m` is the manuscript's `μ` (the mean
parameter), because `μ` is the distribution here.

Core (hypothesis `h : μ.IndepEvents s A`, `p_i = P(A i)`):
- `IndepEvents.expect_exp_mul_sum`: `E e^{tX} = ∏_{i∈s} ((e^t - 1) p_i + 1)` (expand the product
  with `Finset.prod_add`, then use independence on each subset).
- `IndepEvents.expect_exp_mul_sum_le`: `E e^{tX} ≤ exp((e^t - 1) ∑ p_i)`.
- `prob_mul_le_mul_le`: Markov on `e^{tX}`, `P(t a ≤ t X) ≤ e^{-ta} E e^{tX}` for any real `t`.
- `IndepEvents.prob_ge_le_exp_div`: `∑ p_i ≤ m`, `δ ≥ 0` ⟹ `P(X ≥ (1+δ)m) ≤ exp(-δ²m/(2+δ))`.
  Proof: `t = log(1+δ)` and `(1+δ)log(1+δ) - δ ≥ δ²/(2+δ)`.
- `IndepEvents.prob_ge_le` ([s1:citChernoffGen](a), upper): adds `δ ≤ 1` ⟹ `≤ exp(-δ²m/3)`.
- `IndepEvents.prob_le_le` ([s1:citChernoffGen](a), lower): `0 ≤ m ≤ ∑ p_i`, `δ ≥ 0` ⟹
  `P(X ≤ (1-δ)m) ≤ exp(-δ²m/2)`. Proof: `t = -δ` and `e^{-δ} ≤ 1 - δ + δ²/2`, which gives
  `δ(1-δ) + (e^{-δ} - 1) ≤ -δ²/2` exactly.
- `IndepEvents.prob_ge_nat_le` ([s1:citChernoffGen](b)): `∑ p_i ≤ m` ⟹ `P(X ≥ j) ≤ m^j/j!` for
  every `j : ℕ`. Proof: the union bound over `j`-subsets, as in the manuscript's derivation, and
  `e_j(p) ≤ (∑ p_i)^j/j!`.
- `IndepEvents.prob_ge_nat_le_exp`: `≤ (e m/j)^j`.
- The same four bounds for any real `X` that equals the count on the outcomes of positive
  weight (hypothesis `hX : ∀ ω, 0 < μ.w ω → X ω = ∑_{i∈s} (A i).indicator 1 ω`):
  `IndepEvents.chernoff_upper/lower/tail/tail_exp`. There is also `IndepEvents.chernoff_lower_half`
  (`δ = 1/2`: `P(X < m/2) ≤ exp(-m/8)` for `0 ≤ m ≤ E X`), the instance used in s3:lemL15p,
  s3:lemL17s, s4 (B), s5:lemE1(a) and s7:lemCand(iii).

Manuscript forms:
- [s1:citChernoffGen], quoted in the docstrings: real indicator variables `I : ι → Ω → ℝ` with
  `hI : ∀ i ω, I i ω = 0 ∨ I i ω = 1`, `hind : μ.iIndepFun I` (the shared vocabulary), and
  `X = ∑_{i∈s} I i`. The theorems are:
  - `chernoffGen_upper`: `E X ≤ m`, `0 ≤ δ ≤ 1` ⟹ `P(X ≥ (1+δ)m) ≤ exp(-δ²m/3)`.
  - `chernoffGen_lower`: `0 ≤ m ≤ E X`, `δ ≥ 0` ⟹ `P(X ≤ (1-δ)m) ≤ exp(-δ²m/2)`.
  - `chernoffGen_tail`: `E X ≤ m` ⟹ `P(X ≥ j) ≤ m^j/j!`.
  - `chernoffGen_tail_exp`: the chain `P(X ≥ j) ≤ m^j/j! ∧ m^j/j! ≤ (e m/j)^j`.
  - `chernoffGen_lower_half`: the `δ = 1/2` instance.
  - The same five with hypotheses on the summation range only (fix round 1):
    `chernoffGen_upper_on`, `chernoffGen_lower_on`, `chernoffGen_lower_half_on`,
    `chernoffGen_tail_on`, `chernoffGen_tail_exp_on`. They take `(s : Finset ι)`,
    `hI : ∀ i ∈ s, ∀ ω, I i ω = 0 ∨ I i ω = 1` and `hind : μ.iIndepFun fun i : ↥s => I i`;
    the conclusions are literally those of the unrestricted forms.
- [s1:citChernoff], quoted: `chernoff_binomial (hX : μ.map X = binomial n p h0 h1)
  (0 ≤ δ ≤ 1)` returns `E X = n p ∧ P(X > (1+δ)np) ≤ e^{-δ²np/3} ∧ P(X < (1-δ)np) ≤ e^{-δ²np/2}`.
  The pieces are `expect_of_map_eq_binomial`, `chernoff_binomial_upper` and
  `chernoff_binomial_lower`. On `binomial` itself there are `prob_binomial`, `expect_binomial`,
  `binomial_prob_ge_le` and `binomial_prob_le_le` (the non-strict tails).

Sources of `IndepEvents` (one line each):
- `iIndepFun.indepEvents`: from `μ.iIndepFun fun i ω => ω ∈ A i` (Prop-valued indicators).
  `iIndepFun.indepEvents_eq_one` does the same for real `I` and the events `{I i = 1}`.
- `iIndepFun.indepEvents_of_subtype` / `iIndepFun.indepEvents_eq_one_of_subtype`: the same from
  independence of the subfamily indexed by the subtype `↥s` only (fix round 1).
- `indepEvents_pi_coord`: events `{f | f i ∈ C i}` about distinct coordinates of `pi μ`.
- `indepEvents_pi_of_dependsOn`: events depending on pairwise disjoint blocks `B u` of
  coordinates of `pi μ`, with disjointness only required inside `s`. This is the task's "arbitrary
  finite product space in which the indicators are functions of distinct coordinates"; single
  coordinates are `B u = {σ u}`.
- `IsRSubset.indepEvents`: the events `a ∈ V` (`a ∈ S`) of a ρ-random subset.
- `indepEvents_randColouring`: the events `c e = j` of a uniform colouring.
- `IndepEvents.mono`: restriction to a subfamily.

Corollaries in the forms used downstream:
- Bernoulli products `pi fun i => bernoulli (p i) _ _` and `#{i ∈ s | f i = true}` (mean
  `∑_{i∈s} p i`, any `s`): `chernoff_pi_bernoulli_upper`, `chernoff_pi_bernoulli_lower`,
  `chernoff_pi_bernoulli_tail` (both (b) bounds, `m^j/j!` and `(e m/j)^j`, since fix round 1).
  The helpers are `prob_pi_bernoulli_apply`,
  `sum_prob_pi_bernoulli` and `card_eq_sum_indicator_pi_bernoulli`.
- Disjoint blocks of an arbitrary product: `chernoff_pi_dependsOn_upper`,
  `chernoff_pi_dependsOn_lower`, and `chernoff_pi_dependsOn_tail` (both (b) bounds).
- ρ-random subsets. For `|V ∩ E|` (mean `ρ|S ∩ E|`, e.g. `|Cen ∩ V_i|` in s3:lemL17s Case (a)):
  `IsRSubset.chernoff_card_inter_upper`, `_lower`, `_lower_half` and `_tail` (both (b) bounds
  since fix round 1). For `|V|` (mean
  `ρ|S|`, s3:lemL17s Step 3): `IsRSubset.chernoff_card_upper`, `_lower` and `_lower_half`. The
  equality with the count holds almost surely (`V ⊆ S` a.s.), which is why the core takes an
  a.s. `hX`.
- Colour classes of `randColouring ι k`: `#{e ∈ E | c e = j}`, mean `|E|/k` (s3:lemL15p Step 3):
  `chernoff_randColouring_upper`, `_lower` and `_lower_half`.
- Conversion: `sum_indicator_one_eq_card` (`∑_{i∈s} 1_{A i}(ω) = #{i ∈ s | P i}` when
  `ω ∈ A i ↔ P i` on `s`; any decidability instance).

Elementary inequalities (namespace `EG.Chernoff`, all proved here):
- `exp_neg_le_quadratic`: `e^{-x} ≤ 1 - x + x²/2` for `x ≥ 0`. It follows from Mathlib's
  `quadratic_le_exp_of_nonneg` and `(1-x+x²/2)(1+x+x²/2) = 1 + x⁴/4`.
- `two_mul_div_two_add_le_log_one_add`: `log(1+x) ≥ 2x/(2+x)` for `x ≥ 0`. This is the first term
  of Mathlib's series `hasSum_log_sub_log_of_abs_lt_one` at `y = x/(2+x)`.
- `sq_div_two_add_le`: `(1+δ)log(1+δ) - δ ≥ δ²/(2+δ)`, which is `≥ δ²/3` on `[0, 1]`.
- `pow_add_mul_le_pow`: `m^{n+1} + (n+1)p m^n ≤ (m+p)^{n+1}`.
- `sum_powersetCard_prod_le`: `∑_{|T|=j} ∏_{i∈T} p_i ≤ (∑ p_i)^j/j!`, proved by induction on `s`
  with `powersetCard_succ_insert`.
- `pow_div_factorial_le`: `m^j/j! ≤ (e m/j)^j`, from Mathlib's `pow_div_factorial_le_exp` at
  `x = j`.

## Deviations and design decisions
1. **Stronger statements where the proof allows it**, never weaker:
   - The lower tails need only `δ ≥ 0`; the manuscript has `0 ≤ δ ≤ 1`.
   - (b) holds for every `j : ℕ`, including `j = 0`.
   - The upper tail is also available for all `δ ≥ 0`, with the exponent `δ²m/(2+δ)`.
   - The Bernoulli, colouring and ρ-random-subset forms allow any `m` on the correct side of the
     mean, as s1:citChernoffGen(a) does.
2. **Proof route.** The manuscript cites JLR 2.1/2.8 (`P(X ≥ λ+t) ≤ exp(-t²/(2(λ+t/3)))`, …) and
   reduces to the stated forms. Here the stated forms are proved directly by the exponential
   moment method with `t = log(1+δ)` (upper) and `t = -δ` (lower), which needs only two
   elementary inequalities. The JLR forms themselves are not formalized (no downstream use).
   (b) follows the manuscript's derivation: union bound over `j`-sets and `e_j ≤ (∑p)^j/j!`.
3. **Independence hypothesis.**
   - The core lemmas use `IndepEvents`, a new Lib predicate: mutual independence of events.
   - The cited forms use the vocabulary `μ.iIndepFun I` for real 0/1 indicators, as the
     `iIndepFun` docstring in `FinDist.lean` already anticipates for [s1:citChernoffGen].
   - The family is indexed by any type `ι`, and `X` sums over a `Finset ι`. Variables that are
     indicators and independent only within `s` use the `_on` forms (hypotheses
     `∀ i ∈ s, …` and `μ.iIndepFun fun i : ↥s => I i`).
4. **Mean hypothesis.**
   - The core states `∑_{i∈s} P(A i) ≤ m` (resp. `≥`). This equals `E X` by `expect_sum_indicator`.
   - The cited forms state `μ.expect (fun ω => ∑ i ∈ s, I i ω) ≤ m` literally.
   - `expect_sum_of_zero_or_one` converts between the two.
5. **Binomial.** "`X ∼ Bin(n,p)`" is `μ.map X = binomial n p h0 h1`, with `X : Ω → ℕ` and the
   events stated with the cast `(X ω : ℝ)`. Mathlib has no finite binomial law in the `FinDist`
   setting, hence the new definition. No law-level lemma "`|V ∩ E| ∼ Bin(|S ∩ E|, ρ)`" is proved.
   The ρ-random-subset Chernoff bounds are proved directly (via `IsRSubset.indepEvents`), which
   is all the manuscript uses that fact for.

## Tests (`EGTest/Chernoff.lean`)
- 100 fair coins:
  - `P(#heads ≥ 75) ≤ e^{-25/6}` (`chernoff_pi_bernoulli_upper`);
  - `P(#heads ≤ 25) ≤ e^{-25/4}` (`chernoff_pi_bernoulli_lower`), and this bound is `< 1`.
- 10 coins with `p = 1/100`: `P(#heads ≥ 2) ≤ 1/200` (`chernoff_pi_bernoulli_tail`).
- [s1:citChernoffGen] with real indicators `ind i f = [f i = true]` of 20 fair coins. These tests
  prove `iIndepFun` from `iIndepFun_eval_pi`, `E X = 10`, and instantiate `chernoffGen_upper`,
  `chernoffGen_lower_half` and `chernoffGen_tail_exp`.
- [s1:citChernoff] for `X = fun k => k` on `binomial 10 (1/2)`: the full `chernoff_binomial`
  conjunction, including `E X = 5`.
- A (1/3)-random subset of `range 30`: `P(|T| < 5) ≤ e^{-10/8}`
  (`IsRSubset.chernoff_card_lower_half`).
- A uniform 3-colouring of `Fin 30`: `P(|class 0| < 5) ≤ e^{-10/8}`
  (`chernoff_randColouring_lower_half`).
- Hypotheses on the summation range only (fix round 1): `ind' i = ind i` for `i < 10` and `5`
  otherwise (the test proves this family is not `{0,1}`-valued on all of `Fin 20`), with
  independence of `(ind' i)_{i ∈ s10}` from `iIndepFun_pi_of_dependsOn` (singleton blocks) and
  `E X = 5`; instantiates `chernoffGen_lower_half_on`, `chernoffGen_upper_on` and
  `chernoffGen_tail_exp_on`.
- 10 rare coins, second (b) form: `P(#heads ≥ 2) ≤ e²/400` (`(chernoff_pi_bernoulli_tail …).2`).
- Disjoint blocks: 20 coins in 10 pairs, with `E u` = "both coins of pair `u` are heads". The
  test proves `P(E u) = 1/4` and the block disjointness, then applies
  `chernoff_pi_dependsOn_upper`.

## Open questions / notes for the integrator
- The roots `EG.lean` and `EGTest.lean` need the imports `EG.Lib.Prob.Chernoff` and
  `EGTest.Chernoff`. I did not edit the roots, as the task instructed.
- `IndepEvents` and `binomial` are Lib definitions. If a Spec statement needs "independent events"
  or "`X ∼ Bin(n,p)`", they should move to `EG/Defs/Prob/FinDist.lean` through the approval
  procedure. Their bodies are the textbook definitions quoted above.
- Possible later additions, none needed by the current uses:
  - a lemma restricting `iIndepFun` on `ι` to the subtype subfamily `↥s` (not needed: the
    unrestricted forms remain and prove the same conclusions);
  - the law-level lemma `(μ.map fun ω => #(V ω ∩ E)) = binomial #(S ∩ E) ρ` for an `IsRSubset V`,
    which belongs in a future `RandomSets.lean`;
  - the JLR `t`-forms.
- s4 (B) "binomial domination" needs no coupling in Lean. With `m = m'p ≤ E X`,
  `IndepEvents.chernoff_lower_half` (or `chernoffGen_lower_half`) gives
  `P(X < a) ≤ P(X < m/2) ≤ exp(-m/8)` directly.

## Fix round 1

Review: `work/p1b/chernoff.review1.md` (verdict APPROVE, four minor/cosmetic items). No statement
was weakened; the two changed statements only gained a conjunct.

1. (minor) Hypotheses on all of `ι` in the `chernoffGen_*` forms: **fixed**. Valid usability
   point: e.g. the `χ_u`, `u ∈ Aw_Y(w)`, of s5:lemE1(a) are indicators and independent only on
   `Aw_Y(w)`. Added, keeping the original forms unchanged:
   - `iIndepFun.indepEvents_of_subtype`: `μ.iIndepFun (fun (i : ↥s) ω => ω ∈ A i)` implies
     `μ.IndepEvents s A` (the lemma the reviewer suggested as alternative);
   - `iIndepFun.indepEvents_eq_one_of_subtype`: `μ.iIndepFun (fun i : ↥s => I i)` implies
     `μ.IndepEvents s (fun i => {ω | I i ω = 1})`;
   - `sum_eq_sum_indicator_of_zero_or_one_on`, `expect_sum_of_zero_or_one_on` (0/1 only on `s`);
     the unrestricted helpers are now one-line corollaries of these;
   - `chernoffGen_upper_on`, `chernoffGen_lower_on`, `chernoffGen_lower_half_on`,
     `chernoffGen_tail_on`, `chernoffGen_tail_exp_on`, tagged [s1:citChernoffGen] with the same
     quotes and conclusions as the unrestricted forms. With `ι := Fin m`, `s := univ` they are the
     manuscript statement; their hypotheses are implied by the unrestricted ones.
   Tested in `EGTest/Chernoff.lean` on a family that is not 0/1-valued outside `s`.
2. (cosmetic) `chernoff_pi_bernoulli_tail` lacked `(e m/j)^j`: **fixed**. Its conclusion is now
   `P(j ≤ #…) ≤ m^j/j! ∧ P(j ≤ #…) ≤ (e m/j)^j`, the shape of `chernoff_pi_dependsOn_tail`. For
   uniformity `IsRSubset.chernoff_card_inter_tail` got the same second conjunct. The only user
   (the test) now uses `.1`; a new test uses `.2`.
3. (cosmetic) Root imports: **not an issue for this task** (integrator action). The task forbids
   editing `EG.lean` / `EGTest.lean`; the integrator should add `import EG.Lib.Prob.Chernoff` and
   `import EGTest.Chernoff`.
4. (cosmetic) JLR `t`-forms: **not an issue**. They appear only inside the manuscript's
   derivation of s1:citChernoffGen(a) (s1.tex l.800–812), not in the cited statement; a grep of
   s2–s7 finds no other use (every citation of s1:citChernoffGen uses (a) or (b) in the stated
   form). The stated forms are proved directly.

Checks after the fix: `scripts/check.sh EG/Lib/Prob/Chernoff.lean 900` and
`scripts/check.sh EGTest/Chernoff.lean 900` (`LEAN_NUM_THREADS=2`): rc=0, 0 errors, 0 sorry;
`lake build EG.Lib.Prob.Chernoff` succeeds; `python3 scripts/lint.py`: 0 findings; axiom scan
(`--prefix EG --no-sorry EG.Lib.Prob.Chernoff`): 495 constants, 0 sorryAx, 0 violations.
