# Clean-room review, round 1: Lemma BBD (s1:lemBBD), task [bbd]

Reviewer: clean-room agent, 2026-09-26. Files reviewed (not edited):
`EG/Spec/Found/BBD.lean` (87 lines, statements), `EG/Proof/Found/BBD.lean` (435 lines, proofs),
author notes `work/ext/bbd.md`. Manuscript: `proofs/manuscript/s1.tex` l. 1161-1276 (statement and
proof), the only use s3.tex l. 505-521 (s3:lemL17s case (b)); blueprint_s1.md rows BBD-TRANSPORT,
BBD-UNREVIEWED, BBD-COORDS, BBD-CALC.

**Verdict: APPROVE.** The Spec is faithful, the hypotheses can be satisfied, the proof proves exactly
the Spec with standard axioms only, and hygiene is clean. The notes in §5 are cosmetic or
bookkeeping and do not block approval.

## 1. Fidelity of the Spec

Manuscript (s1.tex l. 1162-1175):
> Let m ≥ 0 be an integer, let p_1,…,p_m ∈ [0,1], and let I_1,…,I_m be independent random variables
> with P(I_k=1)=p_k and P(I_k=0)=1−p_k; write I := (I_1,…,I_m). Let Ψ: {0,1}^m → ℝ, and let b ≥ 0
> and c_1,…,c_m ∈ [0,b] be such that |Ψ(x)−Ψ(x')| ≤ c_k whenever x,x' ∈ {0,1}^m differ only in the
> k-th coordinate. Let β > 0 with β ≥ ∑_k p_k(1−p_k)c_k². Then for every a ≥ 0,
> P(Ψ(I) ≥ EΨ(I)+a) ≤ exp(−a²/(2(β+ba/3))) and P(Ψ(I) ≤ EΨ(I)−a) ≤ exp(−a²/(2(β+ba/3))).

| Manuscript | Spec (`BBDStatement` / `BBDRVStatement`) | OK |
|---|---|---|
| m ≥ 0 coordinates 1..m | arbitrary `ι : Type v` with `[Fintype ι]` (m = 0 means `ι` is empty; `Fin m` is a special case) | yes |
| p_k ∈ [0,1] | `0 ≤ p k`, `p k ≤ 1` (RV form: `0 ≤ p k ∧ p k ≤ 1`) | yes |
| I_k independent, P(I_k=1)=p_k, P(I_k=0)=1−p_k | canonical: `μ := pi (fun k => bernoulli (p k) _ _)`, I = id. RV: `μ.iIndepFun (fun k ω => I ω k)` and `μ.prob {ω \| I ω k = true} = p k`. The case `I_k = 0` follows because the values are `Bool` | yes |
| Ψ : {0,1}^m → ℝ | `Ψ : (ι → Bool) → ℝ`, with `true` for 1 | yes |
| b ≥ 0, c_k ∈ [0,b] | `0 ≤ b`, `∀ k, 0 ≤ c k ∧ c k ≤ b` | yes |
| x, x' differ only in coordinate k ⇒ \|Ψx−Ψx'\| ≤ c_k, for all x, x' ∈ {0,1}^m | `∀ k x x', (∀ j, j ≠ k → x j = x' j) → \|Ψ x − Ψ x'\| ≤ c k`, for all x, x' (including those of probability 0, as in the manuscript) | yes (see below) |
| β > 0, β ≥ ∑ p_k(1−p_k)c_k² | `0 < β`, `∑ k, p k * (1 - p k) * c k ^ 2 ≤ β` | yes |
| a ≥ 0 | `0 ≤ a` | yes |
| P(Ψ(I) ≥ EΨ(I)+a) | `μ.prob {x \| μ.expect Ψ + a ≤ Ψ x}` (RV: `μ.expect (fun ω => Ψ (I ω)) + a ≤ Ψ (I ω)`) | yes |
| P(Ψ(I) ≤ EΨ(I)−a) | `μ.prob {x \| Ψ x ≤ μ.expect Ψ - a}` | yes |
| exp(−a²/(2(β+ba/3))) | `Real.exp (-(a ^ 2 / (2 * (β + b * a / 3))))` (`b * a / 3` parses as `(b*a)/3`) | yes |

* "Differ only in the k-th coordinate" is encoded as "agree off k", which also allows `x = x'`.
  In that case the hypothesis says `0 ≤ c k`, which the Spec already assumes, so the encoding is
  equivalent to the literal reading (and to the `Function.update` form used in the proof, BBD-COORDS).
* No hypothesis is added beyond the manuscript. The redundant `0 ≤ p k ∧ p k ≤ 1` in the RV form
  follows from the marginal hypothesis, and the manuscript states it too, so it does no harm. The
  unused hypothesis `0 ≤ c k` also appears in the manuscript. The proof does not need it (the
  author notes say this too), so keeping it follows the manuscript and weakens nothing.
* Constants: the factor 2, the `/3` and `ba` match exactly. The quantifier order ("for every a ≥ 0",
  both tails in one conjunction) matches.
* The RV form is the one the consumer needs. s3.tex l. 514: "Apply the second bound of Lemma BBD
  with m := |W|, I_k := ξ_{w_k}, p_k := p_*, c_k := deg_H(w_k), with Δ_* in the role of b". In that
  application `ι = ↥W`, the `I` are the indicators of a random subset on a general finite space,
  `c_k ≤ Δ_*` holds, and only the lower tail is used. `BBDRVStatement` covers this once the
  consumer proves `iIndepFun` for the restricted indicators (BBD-TRANSPORT (ii), see §5).
* Universe polymorphism (`Ω : Type u`, `ι : Type v`) is more general than needed and harmless.
* The Spec docstrings quote the manuscript verbatim and carry the tag `[s1:lemBBD]`. The header says
  PROTECTED FILE and uses `@[expose] public section`, as AGENTS.md requires.

## 2. Non-vacuity (scratch tests, `/tmp/bbd_review/T.lean`, compiled with `lake env lean`)

All tests compile with no errors, no warnings and no `sorry`:
* T1: all hypotheses of `BBDStatement` hold for a non-constant Ψ: `ι = Fin 2`, p ≡ 1/2,
  Ψ(x) = #{k : x_k = 1}, b = 1, c ≡ 1, β = 1/2, a = 1 (bounded differences proved by `fin_cases`).
  `EG.bbd` is then applied to get both tails.
* T2: all hypotheses of `BBDRVStatement` hold on `μ = pi bernoulli`, `I = id`, `ι = Fin 3`, for
  arbitrary p ∈ [0,1]^3. `iIndepFun` comes from `FinDist.iIndepFun_eval_pi`, and the marginals from
  `prob_pi_eval` and `prob_bernoulli_eq_true`. Ψ = 1[x_0 = 1], c = (1,0,0), β = 1, a = 1/2.
  `EG.bbdRV` is then applied.
* T3: for `a > 0`, `β > 0`, `b ≥ 0` the bound is `< 1`, so the conclusion is not trivial.
* T4: sanity check that `P(x_0 = 1) = 1/2` under `pi (bernoulli (1/2))` on `Fin 1`. With Ψ = 1[x_0 = 1],
  a = 1/2, β = 1/4 and b = 1, the upper tail event has probability 1/2 and the bound is e^{−0.3} ≈ 0.74.
  The statement is consistent there and not trivially true.

## 3. The proof proves exactly the Spec

* `theorem EG.bbd : EG.Spec.BBDStatement.{v}` and `theorem EG.bbdRV : EG.Spec.BBDRVStatement.{u, v}`.
  The types are the Spec definitions themselves, so no restated copy could drift from them.
* `#print axioms`: both use only `[propext, Classical.choice, Quot.sound]`.
* Structure (checked by reading): Step 2 (`one_sub_div_three_mul_exp_le` via χ' monotone, χ
  antitone/monotone on Iic/Ici 0, then `exp_le_quad`). Step 3 (`one_coord`, equal to s1:eqBBDstep).
  Steps 1 and 4 (`mgf_fin`, induction on `Fin n` that reveals coordinate 0: `hMsplit` is
  (s1:eqBBDavg), `hΞ` is |Ξ| ≤ c_0, and the IH is applied to Ψ(x₀,·) with `Fin.tail`). `mgf` transports
  the result along `Fintype.equivFin`. Step 5 (`upper_tail`: Markov with η = a/(β+ba/3),
  `1 − ηb/3 = β/T`). Step 6 (`tails`, via `−Ψ` and `expect_neg`). `bbd` converts the "agree off k"
  hypothesis to the `Function.update` form (`update_of_ne`). `bbdRV` reduces to `bbd` via
  `iIndepFun_iff_map_eq_pi`, `map_eq_bernoulli`, `prob_map` and `expect_map`. No gap. The first-coordinate
  induction differs from the manuscript's last-coordinate prefix induction only in bookkeeping.
  The bound it gives is identical.
* The proof does not use `0 ≤ c k` (only `c k ≤ b`), and it uses `0 ≤ b` for `0 < β + ba/3`.
  This agrees with the author's note and blueprint BBD-CALC.

## 4. Hygiene

* `lake build EG.Proof.Found.BBD`: "Build completed successfully".
* `python3 scripts/lint.py`: `lint (development): 0 findings`.
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Spec.Found.BBD EG.Proof.Found.BBD`:
  `inspected 420 constants under [EG]; 0 use sorryAx; 0 meta-scan hits; 0 violations`.
* No `sorry` and no `set_option` in either file. Imports are Mathlib and `EG` only. The module
  header conventions are followed (`public section` in Proof, `@[expose] public section` in Spec).
  `wt` is `@[expose]`. The root files `EG.lean` / `EGTest.lean` were not edited, and the new modules
  are not yet listed there or in `LOCK.json` (the orchestrator's job).

## 5. Notes (non-blocking)

1. (bookkeeping) BBD-TRANSPORT (ii) is not done here: the lemma that the indicators of a ρ-random
   subset restricted to `W ⊆ S` are `iIndepFun` with marginals ρ, plus the Fubini step over layers.
   The author points to `FinDist.IsRSubset.iIndepFun_mem` in `EG.Lib.Prob.Indep`. This belongs in the
   s3:lemL17s budget. The BBD Spec already has the right shape for it.
2. (cosmetic) `sum_wt`, `mgf`, `upper_tail`, `tails` and `expect_pi_bernoulli` take a `[DecidableEq ι]`
   that only some of them need. It is harmless, since `bbd` supplies it via `classical`.
3. (cosmetic) The Spec docstring justifies the `x = x'` case of "differ only in coordinate k". It
   could also state that "agree off k" is equivalent to the `Function.update` form (BBD-COORDS).
   This is only a documentation note.
