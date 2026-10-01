# [bbd] Lemma BBD, Bernstein inequality for bounded differences (s1:lemBBD, new in v6)

Status: both files compile with 0 errors, 0 warnings and no `sorry`. `lake build EG.Proof.Found.BBD` succeeds.
`python3 scripts/lint.py` reports 0 findings. The axiom scan (`--prefix EG EG.Proof.Found.BBD`) finds 0 `sorryAx` and
0 violations. `EG.bbd` and `EG.bbdRV` use only `propext`, `Classical.choice` and `Quot.sound`.

## Files
| File | Contents |
|---|---|
| `EG/Spec/Found/BBD.lean` (87 lines) | `EG.Spec.BBDStatement` (canonical product space) and `EG.Spec.BBDRVStatement` (random-variable form) |
| `EG/Proof/Found/BBD.lean` (435 lines) | `EG.bbd : BBDStatement.{v}`, `EG.bbdRV : BBDRVStatement.{u,v}`, and the internal development in `EG.BBD.*` |

The root files are not edited. The orchestrator must add `EG.Spec.Found.BBD` and `EG.Proof.Found.BBD` to the roots.

## Statements (universe-polymorphic)
- Coordinates: an arbitrary finite index type `ι` (`[Fintype ι]`), so `ι = Fin m` is the manuscript case. `{0,1}^m` is
  `ι → Bool`, with `true` meaning `1`.
- `BBDStatement`: `μ := pi (fun k => bernoulli (p k) _ _)`, and `I` is the identity. The hypotheses are `0 ≤ b`,
  `0 ≤ c k ≤ b`, "differ only in coordinate `k`" written literally as `(∀ j, j ≠ k → x j = x' j) → |Ψ x − Ψ x'| ≤ c k`,
  `0 < β`, `∑ k, p k (1 − p k) c k² ≤ β` and `0 ≤ a`. The conclusions are
  `μ.prob {x | μ.expect Ψ + a ≤ Ψ x} ≤ exp(−(a²/(2(β + ba/3))))` and
  `μ.prob {x | Ψ x ≤ μ.expect Ψ − a} ≤ exp(−(a²/(2(β + ba/3))))`.
- `BBDRVStatement`: `μ : FinDist Ω` and `I : Ω → ι → Bool`. The coordinates are independent
  (`μ.iIndepFun (fun k ω => I ω k)`, the shared vocabulary) and `μ.prob {ω | I ω k = true} = p k`. The hypothesis
  `P(I_k = 0) = 1 − p_k` is implied for Bool-valued variables, so it is omitted. This is the transport corollary asked
  for by BBD-TRANSPORT (i), and it is what s3:lemL17s case (b) applies. Restriction item (ii), that the indicators of
  a ρ-random subset on `W ⊆ S` are iIndepFun, is not done here. `FinDist.IsRSubset.iIndepFun_mem` in
  `EG.Lib.Prob.Indep` already appears to cover most of it.

## Proof (follows s1.tex; no gap found)
- Step 2: `one_sub_div_three_mul_exp_le` proves `(1 − u/3)e^u ≤ 1 + 2u/3 + u²/6` for all real `u`. It uses
  `χ'' = (1 − (1 − u)e^u)/3 ≥ 0`, so `χ'` is monotone (`monotone_of_deriv_nonneg`). Then `χ` is antitone on `Iic 0`
  and monotone on `Ici 0`. `exp_le_quad` proves `e^u ≤ 1 + u + u²/(2(1 − ζ/3))` for `u ≤ ζ < 3`.
- Step 3: `one_coord` is (s1:eqBBDstep) exactly.
- Steps 1 and 4: `mgf_fin` proves the bound for `Fin n` by induction on `n`. It reveals the first coordinate via
  `Fin.consEquiv`, then applies the IH to `Ψ(x₀, ·)` with `c ∘ succ`. The partial averages satisfy
  `EΨ = pΨ₁(1) + (1 − p)Ψ₁(0)` and `|Ψ₁(1) − Ψ₁(0)| ≤ c₀`. This is the manuscript's Doob-type induction
  organised from the first coordinate instead of the last. The bound is the same,
  `E e^{η(Ψ−EΨ)} ≤ exp(η²∑p_k(1−p_k)c_k²/(2(1−ηb/3)))`. `mgf` transports it to a general `ι` along
  `Fintype.equivFin` (`Function.update_comp_equiv`).
- Step 5: `upper_tail` applies Markov to `e^{η(Ψ−EΨ−a)}` with `η = a/(β + ba/3)`. Here `1 − ηb/3 = β/(β + ba/3)`, and
  the exponent simplifies by `field_simp; ring`.
- Step 6: `tails` gets the lower tail by applying the upper tail to `−Ψ` (`expect_neg`).
- Manuscript check: the hypothesis `c_k ≥ 0` is not used by the proof. The bound `c_k ≤ b` and `b ≥ 0` are used
  (`b ≥ 0` for positivity of `β + ba/3`). The statement is true as written. The edge cases `m = 0` and `a = 0`
  are covered.

## Fix round 1 (review `work/ext/bbd.review1.md`, verdict APPROVE, 3 non-blocking notes)
1. (minor, BBD-TRANSPORT (ii)) Valid as bookkeeping. No change here: the restriction lemma (the indicators of a
   ρ-random subset restricted to `W ⊆ S` are `iIndepFun` with marginals ρ) and the Fubini step over layers belong to
   the s3:lemL17s task. They should build on `FinDist.IsRSubset.iIndepFun_mem` (`EG.Lib.Prob.Indep`) and feed
   `EG.bbdRV` with `ι = ↥W`, `c_k = deg_H(w_k) ≤ Δ_*` (lower tail only). The Spec needs no change.
2. (cosmetic, "unnecessary `[DecidableEq ι]`") Checked and found invalid. Dropping the instance from `sum_wt` and
   `expect_pi_bernoulli` was tried, and the build failed with `failed to synthesize Fintype (ι → Bool)`. The instance
   `Pi.instFintype` needs `DecidableEq ι`, so every lemma that sums over `ι → Bool` uses it. `mgf`, `upper_tail`
   and `tails` also need it for `Function.update` in their hypotheses. The change was reverted, so the Proof file
   is unchanged.
3. (cosmetic, Spec docstring) Done as documentation only. No statement changed, and the file is not yet in
   `LOCK.json`. A sentence in the module docstring now says that "agree off `k`" is equivalent to the
   `Function.update` form `|Ψ(update x k v) − Ψ(x)| ≤ c_k` that the proof uses (BBD-COORDS).

Re-check: `lake build EG.Proof.Found.BBD` succeeds. `python3 scripts/lint.py` reports 0 findings. The axiom scan
(`--prefix EG EG.Spec.Found.BBD EG.Proof.Found.BBD`) inspected 420 constants and found 0 `sorryAx` and 0 violations.

## Fix round 2 (review `work/ext/bbd.review2.md`, 2 cosmetic notes and 1 minor note)
1. (cosmetic, the blueprint row s1:lemBBD still names `EG/Spec/Prob/BBD.lean` and `ι : Type` with `[DecidableEq ι]`)
   Valid. Fixed in `work/p2/blueprint_s1.md`. The **Formalization** line now names the delivered files and
   modules, `EG/Spec/Found/BBD.lean` (`EG.Spec.BBDStatement`, `EG.Spec.BBDRVStatement`) and
   `EG/Proof/Found/BBD.lean` (`EG.bbd`, `EG.bbdRV`). It also says that the statements are universe-polymorphic, carry
   no `[DecidableEq ι]`, and state "differ only in coordinate k" literally. The lean_shape sketch now uses
   `ι : Type v` and has no `[DecidableEq ι]`. No Lean file changed. Adding the modules to the roots and to
   `LOCK.json` is still the orchestrator's job.
2. (cosmetic, the redundant hypotheses `0 ≤ p k ∧ p k ≤ 1` in `BBDRVStatement` and `0 ≤ c k` in both statements)
   Checked, and I agree with the reviewer: these are the literal manuscript hypotheses "`p_k ∈ [0,1]`" and
   "`c_k ∈ [0,b]`". Keeping them is the faithful reading and weakens nothing, so there is no change.
3. (minor, the s3:lemL17s case (b) restriction and Fubini steps) Out of scope for [bbd], as recorded in Fix round 1,
   item 1. There is no change. `BBDRVStatement` already has the shape that consumer needs.

Re-check: `lake build EG.Proof.Found.BBD` succeeds (2141 jobs), and `python3 scripts/lint.py` reports 0 findings. No Lean file changed this round.
