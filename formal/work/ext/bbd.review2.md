# Clean-room review, round 2: Lemma BBD (s1:lemBBD), task [bbd]

Reviewer: clean-room agent (round 2), 2026-09-26. Files reviewed, not edited:
`EG/Spec/Found/BBD.lean` (87 lines), `EG/Proof/Found/BBD.lean` (435 lines), author notes
`work/ext/bbd.md` (incl. the fix-round-1 section), round-1 review `work/ext/bbd.review1.md`.
Manuscript: `proofs/manuscript/s1.tex` l. 1161-1276 (statement and proof); the only consumer
s3.tex l. 505-521 (s3:lemL17s case (b)). Blueprint rows BBD-TRANSPORT, BBD-UNREVIEWED, BBD-COORDS,
BBD-CALC (`work/p2/blueprint_s1.md`). Definitions checked at source: `EG/Defs/Prob/FinDist.lean`
(`FinDist`, `prob`, `expect`, `pi`, `map`, `bernoulli`, `iIndepFun`).

**Verdict: APPROVE.** The Spec is a faithful transcription of the manuscript statement (same
hypotheses, same constants, same non-strict inequalities in the events, no added hypothesis beyond
the manuscript's, no dropped one). The hypotheses are jointly satisfiable on non-trivial instances
(fresh tests, independent of round 1), and on an instance where both sides are computed exactly the
inequality is true and strictly non-trivial. The Proof file proves the two Spec `def`s themselves
with standard axioms only. Hygiene is clean. The round-1 notes were handled correctly (the rejected
`[DecidableEq ι]` removal is indeed impossible, see §4). The notes in §5 are cosmetic bookkeeping.

## 1. Fidelity of the Spec to the manuscript

Manuscript (s1.tex l. 1162-1174), checked clause by clause against `BBDStatement` and
`BBDRVStatement`:

| Manuscript clause | Spec | Verdict |
|---|---|---|
| "Let m ≥ 0 be an integer" | coordinates indexed by any `ι : Type v` with `[Fintype ι]`; `Fin m` is the manuscript case, `m = 0` is `ι` empty | faithful (generalises the index only) |
| "p_1,…,p_m ∈ [0,1]" | `hp0 : ∀ k, 0 ≤ p k`, `hp1 : ∀ k, p k ≤ 1` (RV: `∀ k, 0 ≤ p k ∧ p k ≤ 1`) | faithful |
| "I_1,…,I_m independent, P(I_k=1)=p_k, P(I_k=0)=1−p_k" | canonical: `μ := pi (fun k => bernoulli (p k) _ _)`, `I = id`. By the definitions read at source, `(pi μ).w x = ∏ k, (μ k).w (x k)` and `(bernoulli p).w = cond · p (1−p)`, so this is exactly the product Bernoulli law with `true ↦ 1`. RV: `μ.iIndepFun (fun k ω => I ω k)` (the project's shared independence vocabulary, = the product-law characterisation `iIndepFun_iff_map_eq_pi`) and `μ.prob {ω \| I ω k = true} = p k`; `P(I_k = 0) = 1 − p_k` follows since `I ω k : Bool` | faithful |
| "Ψ : {0,1}^m → ℝ" | `Ψ : (ι → Bool) → ℝ` | faithful |
| "b ≥ 0 and c_1,…,c_m ∈ [0,b]" | `0 ≤ b`, `∀ k, 0 ≤ c k ∧ c k ≤ b` | faithful |
| "\|Ψ(x)−Ψ(x')\| ≤ c_k whenever x,x' differ only in the k-th coordinate" | `∀ k x x', (∀ j, j ≠ k → x j = x' j) → \|Ψ x − Ψ x'\| ≤ c k` | faithful: "agree off k" also admits `x = x'`, where the demand is `0 ≤ c k`, already a hypothesis; so the two readings are equivalent |
| "β > 0 with β ≥ ∑_k p_k(1−p_k)c_k²" | `0 < β`, `∑ k, p k * (1 - p k) * c k ^ 2 ≤ β` | faithful |
| "for every a ≥ 0" | `0 ≤ a`, universally quantified before the conjunction | faithful |
| "P(Ψ(I) ≥ EΨ(I)+a)" | `μ.prob {x \| μ.expect Ψ + a ≤ Ψ x}` (RV: `Ψ (I ω)` and `μ.expect (fun ω => Ψ (I ω))`) — non-strict, as in the manuscript | faithful |
| "P(Ψ(I) ≤ EΨ(I)−a)" | `μ.prob {x \| Ψ x ≤ μ.expect Ψ - a}` — non-strict | faithful |
| "exp(−a²/(2(β+ba/3)))" | `Real.exp (-(a ^ 2 / (2 * (β + b * a / 3))))`; `b * a / 3 = (b·a)/3` | constants exact |

* Constants: the `2`, the `/3`, the product `ba` and the sign are all exact. Nothing is weakened
  (no extra `ε`, no `≤` turned into `<`, no `a > 0`).
* Edge cases: `m = 0` (empty `ι`) is allowed, as is `a = 0` (bound `exp 0 = 1`) and `p_k ∈ {0,1}`.
  `β > 0` is kept as in the manuscript (it is what makes the denominator positive when `a = 0`).
* No hypothesis is added beyond the manuscript. The RV form's `0 ≤ p k ∧ p k ≤ 1` is redundant
  given the marginal hypothesis (a probability lies in `[0,1]`), but the manuscript states
  `p_k ∈ [0,1]` too, so it is a faithful transcription, not a strengthening of the hypotheses.
  Likewise `0 ≤ c k` is a manuscript hypothesis the proof happens not to need.
* The Spec carries no `[DecidableEq ι]` (the sums in the statement range over `ι`, not over
  `ι → Bool`), so no spurious decidability assumption is imposed on the consumer.
* Universe polymorphism (`Ω : Type u`, `ι : Type v`) is harmless. Docstrings quote the manuscript
  verbatim and carry `[s1:lemBBD]`; header is `module` / `@[expose] public section`.
* Consumer fit (s3.tex l. 514-516): "Apply the second bound of Lemma BBD with m := |W|,
  I_k := ξ_{w_k}, p_k := p_*, c_k := deg_H(w_k), with Δ_* in the role of b". `BBDRVStatement` has
  exactly this shape with `ι = ↥W`, `c k = (deg_H w_k : ℝ)`, `b = Δ_*`, and only the second
  conjunct used. The restriction/Fubini step (BBD-TRANSPORT (ii)) is correctly left to the s3 task.

## 2. Non-vacuity (fresh scratch tests, round 2)

File: `<scratchpad>/bbd_review2/T.lean`, compiled with `lake env lean` against the built
`EG.Proof.Found.BBD`: 0 errors, 0 `sorry` (one style-linter warning inside my own test). The
parameters differ from round 1's on purpose.

* **T1** (canonical form, non-uniform `p`): `ι = Fin 3`, `p = (1/3, 1/2, 1/4)`,
  `Ψ x = #{k : x k = true}` (bounded differences `≤ 1` proved for a general `Fintype`),
  `c ≡ 1`, `b = 1`, `β = 1` (the true variance sum is `17/36 + 3/16 < 1`), `a = 1/2`.
  All hypotheses discharged; `EG.bbd` yields both tails.
* **T2** (RV form with a **non-identity** `I`): `Ω = Fin 2 → Bool`, `μ = pi bernoulli (1/3, 3/4)`,
  `I ω k = !(ω k)` (negated coordinates), `p k = 1 − q k`. Independence via
  `(iIndepFun_eval_pi _).comp`, marginals via `prob_pi_eval` and a two-term sum. `EG.bbdRV` applies.
  This exercises the `map`/`iIndepFun` transport path with a genuinely transformed `I`.
* **T3** (exact-probability consistency): `ι = Fin 2`, `p ≡ 1/2`, `Ψ = count`, `a = 1`, `β = 1/2`,
  `b = 1`. Proved `μ.expect count = 1` (via `expect_sum`, `expect_pi_eval`) and
  `μ.prob {Ψ ≥ EΨ + 1} = 1/4` exactly (event = `{x 0 = x 1 = true}`, `prob_pi_forall_mem`).
  The Spec's bound there is `exp(−3/5)`; proved `1/4 ≤ exp(−3/5) < 1`. So on a fully computed
  instance the asserted inequality is true and the bound is strictly below `1` — the conclusion is
  not trivially satisfied, and the event encoding (`≤`, not `<`) matches the manuscript's `≥`.
* **T4**: `#print axioms EG.bbd` and `EG.bbdRV`: `[propext, Classical.choice, Quot.sound]`.

## 3. The proof proves exactly the Spec

* `theorem EG.bbd : EG.Spec.BBDStatement.{v}` and `theorem EG.bbdRV : EG.Spec.BBDRVStatement.{u,v}`:
  the stated types are the Spec `def`s themselves, so there is no restated copy that could drift.
* Read through, step by step against s1.tex:
  - Step 2: `hasDerivAt_chi'`, `hasDerivAt_chi`, `chi'_mono` (χ'' = (1−(1−u)e^u)/3 ≥ 0 from
    `1 − u ≤ e^{−u}`), `one_sub_div_three_mul_exp_le` (χ antitone on `Iic 0`, monotone on `Ici 0`,
    χ(0) = 0), `exp_le_quad` (division by `1 − u/3 ≥ 1 − ζ/3 > 0`). Matches (s1:eqBBDphi),
    (s1:eqBBDexp).
  - Step 3: `one_coord` is (s1:eqBBDstep) verbatim, including the cancellation of cross terms and
    `p(1−p)² + (1−p)p² = p(1−p)` (done by `ring`), then `Ξ² ≤ c²` and `1 + v ≤ e^v`.
  - Steps 1 and 4: `wt` is the manuscript's `wt_m`; `pi_bernoulli_w` is `rfl`, so the product law
    is literally the manuscript weight. `mgf_fin` inducts on `n` revealing coordinate `0`:
    `hMsplit` is (s1:eqBBDavg), `hΞ` is `|Ξ| ≤ c_0` (using `∑ wt = 1`), the IH is applied to
    `Ψ(x₀, ·)` with `Fin.tail c`, then `one_coord`. This is the manuscript's Doob-type induction
    ordered from the first coordinate rather than the last; the bound is identical. `mgf`
    transports along `Fintype.equivFin` (`Function.update_comp_equiv` handles the hypothesis).
  - Step 5: `upper_tail`: Markov on `e^{η(Ψ−M−a)}` (indicator ≤ exponential pointwise, weights
    ≥ 0), `η = a/(β+ba/3)`, `ηb < 3` proved by `nlinarith`, `1 − ηb/3 = β/T`, and the exponent
    identity by `field_simp; ring`. This is the manuscript computation exactly.
  - Step 6: `tails` applies `upper_tail` to `−Ψ` and `expect_neg`, exactly as the manuscript.
  - `bbd`: converts the Spec's "agree off k" to the `Function.update` form by
    `Function.update_of_ne` (the equivalence claimed by the Spec docstring is thus used in the
    one direction needed). `bbdRV`: `iIndepFun_iff_map_eq_pi` + `map_eq_bernoulli` give
    `μ.map I = pi bernoulli`, then `prob_map`/`expect_map` transport both tails.
* Usage of hypotheses: `0 ≤ c k` unused; `c k ≤ b` and `0 ≤ b` used (positivity of `β + ba/3`);
  `0 < β` used for `ηb < 3` and `1 − ηb/3 = β/T`. Consistent with BBD-CALC and the author's notes.
* No gap found. No `sorry`, no `set_option` anywhere in either file.

## 4. Hygiene

* `lake build EG.Proof.Found.BBD`: "Build completed successfully (2141 jobs)".
* `python3 scripts/lint.py`: `lint (development): 0 findings`.
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Spec.Found.BBD EG.Proof.Found.BBD`:
  `inspected 420 constants under [EG]; 0 use sorryAx; 0 meta-scan hits; 0 violations`.
* `grep sorry|set_option|axiom|admit|native_decide` on both files: no hits.
* Imports: `EG.*` and Mathlib only. Module headers correct (`@[expose] public section` in Spec,
  `public section` in Proof; `wt` is `@[expose]`, which downstream `rfl`/`unfold` uses).
* Root files `EG.lean` / `EGTest.lean` untouched; the two modules are not yet listed there nor in
  `LOCK.json` (orchestrator's job, as the author notes say).
* Round-1 follow-up checked: the author's refusal of note 2 (drop `[DecidableEq ι]`) is correct.
  `Fintype (ι → Bool)` is `Pi.instFintype`, which requires `DecidableEq ι`, so every lemma summing
  over `ι → Bool` (`sum_wt`, `mgf`, `expect_pi_bernoulli`, `upper_tail`, `tails`) needs it; `bbd`
  supplies it by `classical`, and the **Spec** correctly carries none. Note 3 was addressed as a
  docstring sentence only; the statement text is unchanged from what round 1 approved.

## 5. Notes (all cosmetic / bookkeeping, non-blocking)

1. Blueprint `work/p2/blueprint_s1.md` l. 1073 still names the paths `EG/Spec/Prob/BBD.lean` /
   `EG/Proof/Prob/BBD.lean` and l. 1094 sketches the statement with `ι : Type` and
   `[DecidableEq ι]`. The delivered files live in `EG/Spec/Found/` / `EG/Proof/Found/`, are
   universe-polymorphic, and carry no `DecidableEq` (strictly more general). The blueprint row
   should be updated to the delivered names when the modules are added to the roots/LOCK.
2. The redundant `∀ k, 0 ≤ p k ∧ p k ≤ 1` in `BBDRVStatement` (implied by the marginal hypothesis)
   and the unused `0 ≤ c k` are both manuscript hypotheses; keeping them is the faithful choice.
   Nothing to change.
3. BBD-TRANSPORT (ii) (indicators of a ρ-random subset restricted to `W ⊆ S` are `iIndepFun` with
   marginals ρ, plus Fubini over layers) remains for the s3:lemL17s task, as both the author and
   round 1 recorded. `BBDRVStatement` already has the shape that task needs.
