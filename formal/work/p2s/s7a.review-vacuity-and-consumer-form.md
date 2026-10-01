# Clean-room review of the s7a Specs (lens: vacuity-and-consumer-form, model B)

Reviewer: clean-room statement reviewer (no Lean file of the repository edited). Date 2026-09-30.
Scope: `work/p2s/s7a.md` and the six Spec files it lists as new: `EG/Spec/Stage1/Pool.lean`,
`EG/Spec/Quot/{CandDef,Cand,RoundStep,CC,Ultra}.lean` (14 `…Statement` defs), with the test file
`EGTest/Spec_s7a.lean`. Read for comparison: the earlier review `s7a.review-fidelity-first.md`
(model A) and the P1/NUM/s7b Specs the new ones interlock with (`WellDef.lean`, `MULT.lean`,
`OneOutcome.lean`, `Lend/COLJV.lean`, `HB/TowerBM.lean`). Locked Defs read: `EG/Defs/Stage1/{Pool,Law,COL}.lean`,
`EG/Defs/Quot/{Cand,Schedule,Round,Xprime}.lean`, `EG/Defs/Chain/{Design,Lending,StageInst}.lean`,
`EG/Defs/HB/Run.lean`, `EG/Defs/Gamma/{Core,Full}.lean`, `EG/Defs/Prob/FinDist.lean`. Lib read for
the consumer checks: `EG/Lib/Quot/{Round,Cand}.lean`, `EG/Lib/Chain/Design.lean`, `EG/Lib/HB/Run.lean`,
`EG/Lib/Prob/Basic.lean`. TeX: `proofs/manuscript/s7.tex` lines 1–925 (setting, defPool, defCand,
lemCand with proof, defSchedule, consRound, lemWellDef, the preamble of "Quotient size and
payments", lemCC and lemUltra with proofs).

## Verdict: APPROVE (no statement change required; cosmetic and minor notes only)

* No new Spec has contradictory hypotheses. Every conclusion carries the TeX's content except the
  conjuncts the TeX itself presents as trivial (listed in §3); none of those hides a weakening.
* Every Spec is in the form its consumer reads: `RoundInput.ofPast_valid` (fields `cls_anc`,
  `cls_round`, `cls_mem`, `ljv_in`, `good_cand`, `Hcd_ge`) closes on `CandSubsetStatement` and
  `CandCountStatement` (iv) by `rfl`/`ofPast_cand` (checks V12, V13); the s7b consumers
  (`UHsplit`, `OneOutcome`) read `CCCopiesStatement`, `UltraSumStatement` and
  `RoundMarkovStatement` at the abstract round input, which is how they are stated.
* Reuse is correct and there is one genuine duplicate of content, sanctioned by the TeX itself:
  the second conjunct of `CandCountStatement` (iv), `2^{10}M_l^{10} ≤ Hcd_l`, is
  `EG.Spec.COLJVRow11Statement` at `l` (proved equivalent in check V5). The TeX says so ("The
  second is the line … of the table of Lemma s3:lemCOLJV"), so the proof of (iv) should cite
  `COLJVRow11Statement` rather than get a second stub (note N1).
* No hypothesis mentions Γ2(b), Γ2(c), Γ2 at all, or Γ4: `grep -n "Gamma2\|Gamma4"` over the six
  files is empty; `RunHyp = Gamma1 ∧ Gamma3 ∧ N0Cond ∧ n ≥ N_0 ∧ D_* ≤ d_1 ∧ run.Valid`. The
  round-level Specs carry only `I.Valid`, `R.Valid`, whose fields are the manuscript's derived
  facts (`M_l ≥ 2^{40}`, `Hcd_l ≥ 2^{10}M_l^{10}`, J1–J3, typing, LJV facts).
* Hygiene: `python3 -I scripts/lint.py` → `lint (development): 0 findings`.

## 1. Scratch checks (compiled with `lake env lean`, rc 0; file `s7a_vacuity.lean` in the session scratchpad, outside the repository)

| # | Check | Result | Meaning for the review |
|---|---|---|---|
| V1 | `Set.InjOn Prod.snd (ultraItems R L h κ)` for every `R`, `L`, `h`, `κ`, no hypotheses | proved in 3 lines | the first conjunct of `UltraIndepStatement` ("these items lie at `N` distinct ports") is a tautology of the encoding: items of `h` are pairs `(h, u)`, so distinct items have distinct `u`. The TeX's reason ("distinct edges `hu` and `G` is simple") is built into `hubItems ⊆ D_l ×ˢ ports`. Harmless (T0, recorded below). |
| V2 | `IsDesignation run G δ → 3 ≤ l → u ∈ classedPorts run G l → δ l u ∈ ancestors ∧ 1 ≤ r ∧ r + 2 ≤ l ∧ u ∈ V(Y)` | proved from `IsDesignation`, `Run.anc`, `isRound_of_mem_parts`; no `RunHyp`, no `hS` | the four deterministic conjuncts of `CandSubsetStatement` are unfolding-level consequences of the designation; they restate the section setting in the field shapes of `RoundInput.Valid`. Only the `∀ ω, Cand ⊆ N_{H_Y}(u) ⊆ V(Y)` conjunct carries content (Lib: `cand_subset_nbrs` under `S.Coherent`). Not a defect: this is the consumer's form. |
| V3 | `EG.Spec.RoundMarkovStatement` | **proved outright** from `one_sub_inv_le_prob_le_mul_expect`, `prob_compl`, `half_le_prob_le_four_mul_expect_and` (`EG.Lib.Prob.Basic`), 15 lines | the Spec is true, not vacuous, and needs neither `I.Valid` nor `R.Valid` (hazard H8 confirmed). It could be discharged now (note N2). |
| V4 | `run.R < l → classedPorts run G l = ∅` | `classedPorts_eq_empty_of_not_isRound` | hazard H9 is sound: `CandCountStatement`/`CandSubsetStatement` need no `l ≤ R`, and the Bernoulli probability `q_l π_{l,r} p_Y` (which needs `(l, r) ∈ poolIdx`, hence `l ≤ R`) is never claimed for an `l > R`. |
| V5 | `COLJVRow11Statement.{0} → (RunHyp → 3 ≤ l → u ∈ classedPorts → 2^{10} M_l^{10} ≤ Hcd run G l)` | proved (`Hcd_def` is `rfl`, `l ≤ R` from V4) | the second conjunct of `CandCountStatement` (iv) is the COLJV row-11 Spec. Duplicate of content (N1). |
| V6 | `RunHyp → 2 / D_* < 1` | one line (`Gamma1core.1 : 2 < D_*`) | the last link of the chain in `PoolLawStatement` conjunct 2 is a Γ1 triviality, as in the TeX. |
| V7 | `b o false ≠ b o true → b o (ccPartner b o) = false` | `cases`/`simp` | `ccPartner` selects the unmarked end on `S_w` (H2). |
| V8a | `|Cand(u) \ Used(u)| < |E'(u)| → ¬ ∃ f, MapsTo ∧ InjOn` | `card_le_card_of_injOn` | the uniform-injection conjunct of `RoundInjectionStatement` is vacuous exactly when (e2) is ill-defined; well-definedness lives in `WellDefE2Statement`, which consumers must combine with it (minor note N3). |
| V8b | `E'(u) = ∅ → P(univ) = ((c)_0)⁻¹ = 1` | `prob_univ` | at ports without live items the conjunct is the trivial identity `1 = 1` (H7). |
| V9 | `iIndepFun` over an empty index type holds for every law | `Finset.eq_empty_of_isEmpty` | the independence conjuncts of CC (i), Ultra (i) and the lists clause are trivially true on inputs without PAR objects / ultra hubs / hubs; this is the only instance the test file exercises for CC (i) (R5 of the fidelity review stands). |
| V10 | `1 − 2^{−(l−2)} < 1` for every `l : ℕ` | `zpow_pos` | the "`< 1`" half of `PoolLawStatement` conjunct 1 is trivial, as in the TeX. |
| V11 | the geometric identity `Σ_{r=1}^{l−2} π_{l,r} = 1 − 2^{−(l−2)}` at `l = 3` (`{1}`, value `1/2`) and `l = 4` (`{1,2}`, value `3/4`) | `decide` on the filtered `Icc`, `norm_num` | the sum range `(Icc 1 l).filter (r + 2 ≤ l)` is `{1, …, l−2}` and the exponent `−(l−1−r)` is right at the first two rounds; the general identity is content. |
| V12 | `(ofPast …).jvBad u = JVBad …` (rfl), `(ofPast …).Hcd = Hcd run G l` (rfl), `(ofPast …).cand u = cand G δ S π l u` (`ofPast_cand`, under `1 ≤ r`, `r + 2 ≤ l`) ⇒ `good_cand` is (iv) verbatim | proved | consumer form of `CandCountStatement` (iv) closes; the two round facts it needs are the second and third conjuncts of `CandSubsetStatement`. |
| V13 | `qsRound run G δ S l ⊆ classedPorts run G l` | `qs = classed \ lost` | the consumer's `u ∈ I.ports` (`ports := qsRound`) yields the Specs' `u ∈ classedPorts`. |

## 2. Per-Spec: hypotheses satisfiable? conclusion trivial? consumer form

| Spec | Hypotheses satisfiable? | Conclusion trivial? | Consumer (form matches?) |
|---|---|---|---|
| `PoolLawStatement` | `RunHyp` (needs s2:propExists; not exhibitable, as in every s5–s7 run-level Spec; H10) | conjunct 1's "`< 1`" (V10) and conjunct 2's "`2/D_* < 1`" (V6) are trivial, as in the TeX; the identity, the marginal, the point probabilities, `P(v ∈ Pool_l)`, disjointness, `r(w)` and `IndepFun` are content | lemCand (i) (point probability `q_l π_{l,r}`), lemVstar/lemEXprime (`P(v ∈ Pool_l) ≤ q_l`, read at `Stage1.poolL G ω.pool l`, the same term), the Defs guard `poolMass ≤ 1` (from conjunct 3) |
| `CandSubsetStatement` | `RunHyp`, `IsDesignation`, `hS` (satisfiable: `EGTest/Spec_s7a`), a classed port of a round `l ≥ 3` (needs `R ≥ 3`; H10) | four conjuncts are setting restatements (V2); the inclusions are content | `ofPast_valid`: `cls_anc`, `cls_round`, `cls_mem`, `ljv_in` (V(Y) half), and `ofPast_cand`'s two side conditions (V12) |
| `CandCountStatement` | as above | no; the second conjunct of (iv) is a duplicate (V5, N1) | (iii), (iv) → lemEXprime at `jvBadPorts` (same predicate `JVBad run G δ S π l`); (iv) → `good_cand`, `Hcd_ge` (V12) |
| `RoundRulesExistStatement` | `I.Valid` (holds on `Live.I`) | proved in `EGTest/Spec_s7a` (`Rules.exists_valid`) | `RoundInput.chosenRules_valid` |
| `RoundListsLawStatement` | `I.Valid`; a non-ultra hub with `c ≥ 1` (`Live.I`, hub `0`) | no: the card-3/disjointness clause needs `3k_h ≤ 4M_l` (`WellDefListsStatement`), the probability is the uniform count `6^k/(4M)_{3k}`; the independence clause is content for `≥ 2` hubs (trivial on `Live.I`, V9) | `CuckooSDRStatement`'s proof (lists at a port independent and uniform) |
| `RoundInjectionStatement` | `I.Valid`, `R.Valid`, any `L` | trivial at `E'(u) = ∅` (V8b), vacuous when `|E'(u)| > |C(u)|` (V8a); content otherwise; independence content for `≥ 2` ports with ends | CC (i), Ultra (i), lemPay (c) |
| `RoundMarkovStatement` | `I.Valid`, `R.Valid` (unused) | true and easy (V3), as the TeX ("By Markov's inequality") | `xiChosen_spec` needs `∃ ξ, 0 < w ξ ∧ MarkovEvent ξ`, which follows by `exists_of_prob_pos` from the third conjunct; s7b's `OneOutcomeRoundStatement` restates that existence at `pastOf` (N2) |
| `CCPartnerStatement` | `I.Valid`, `R.Valid`, `κ < 3M`, `w ∈ Pool`, an atom of positive probability (satisfiable: on `Live.I` the atom of every `b` is `univ`) | on `Live.I` all three conjuncts are trivial (no PAR objects, V9); content needs a live `J^par` item | CC (ii) |
| `CCMaxStatement` | as above, `t ≥ 1` | no (LHS `= 0` only when `S_w = ∅`, and then the RHS is `0` too: consistent) | CC (iii) |
| `CCCopiesStatement` | `I.Valid`, `R.Valid`, any `L` | no | lemUHsplit (ii), averaged over the lists (UH-AVERAGE-LISTS) |
| `UltraIndepStatement` | an ultra hub under `I.Valid`: consistent (no field of `Valid` bounds `c^live_h` for a hub: `J2` is for non-hubs, `J1` only per class; `n ≥ λ^{95}/(56M^2) ≈ 2^{407}` suffices) but not exhibitable (H10) | first conjunct tautological (V1); the rest content | Ultra (ii) |
| `UltraMaxStatement` | as above, `N ≥ 1` | no | Ultra (iii) |
| `UltraCopiesStatement` | as above | no | Ultra (iv) |
| `UltraSumStatement` | `I.Valid`, `R.Valid`, any `L` (on `Live.I` the sum is empty: `0 ≤ RHS`, with `λ = 64 > 0`) | no | lemUHsplit (ii) |

## 3. Fidelity from this lens (back-translation against the quoted TeX)

Each statement back-translates to the quoted TeX or to a form the TeX proof supports and the
consumer needs. Points checked specifically:

* **Quantifier order.** Run level: `RunHyp → δ → Sω, hS → l, u → …` (the TeX's "a designation δ
  is fixed … Let `u` be a classed port of round `l ≥ 3`"). Round level: `I, I.Valid → R, R.Valid →
  L → (κ, w) → (b, hb) → t`, i.e. "the past and the lists fixed … condition on `(I_x)_x` … for every
  integer `t ≥ 1`". The `E[· | Past_l, lists]` of CC (iii)/Ultra is `(ordersLaw I.G).expect` at the
  fixed `L`, and `E[· | Past_l]` of (f) is `(roundLaw I.G I.M).expect`.
* **Strict vs non-strict.** `Σ π < 1`, `2/D_* < 1`, `poolMass < 1` strict as in the TeX; `≤` in all
  bounds; `t ≥ 1` (`1 ≤ t`), `N ≥ 1`, `c^live_h ≥ 1` non-strict as in the TeX; ultra is the strict
  `θ^ult < c^live_h`.
* **Constants and functions.** `44.7`, `29.8`, `6e`, `4e`, `2e`, `8`, `320`, `95`, `96`, `2^{10}M^{10}`,
  `3/Hcd`, `Hcd/2`, `μ* = 2N/Hcd`; `e = Real.exp 1`; `log₂ = Real.logb 2`; `2^{−t}`, `2^{−(l−r)}`,
  `2^{−(l−2)}` as integer powers (no ℕ-subtraction); `t^CC = ⌈2log₂M⌉` is the shared Defs `tCC`.
* **Integer vs real.** `M_l : ℕ` cast; counts (`card`, `mPar`, `mHub`, `copies`) cast to ℝ inside
  expectations; `Hcd`, `λ` real.
* **Edge cases.** `l > R` excluded by `classedPorts = ∅` (V4); `E'(u) = ∅` trivial (V8b); `C' = ∅` in CC (i)
  is excluded by `hb` under `WellDefE2` (the atom would then have probability `0`); `S_w = ∅` gives
  `0 ≤ 0` in CC (ii); `Real.logb 2 0 = 0` is never reached (ultra hubs have `c ≥ θ + 1 ≥ 2^8 + 1`).
* **Extra or missing hypotheses.** None missing. `RoundMarkovStatement` carries two unused ones
  (H8; harmless, strengthening would be allowed). `CandCountStatement` (iv) is stated for every `S`,
  `π` (H4): stronger than the TeX's sentence, true by the definition of JV-bad and (ii), and exactly
  `good_cand`.
* **Consumer's form.** V12, V13 (run level); `mHub`/`mPar` with `Finset.sup` over `I.pool` /
  `I.pool.erase w` match `MultSublayerStatement` / `ParMultSublayerStatement`, which is how CC (iii)
  and Ultra (iii) are proved from (ii); `parCopies`/`hubCopies` filter the `QTag` kinds/sides of the
  locked `QVert`.

## 4. Mathematics re-derived (no error found)

Independently of the fidelity review I re-derived: lemCand (ii) (`M^{−2} 2^{−(l−1−r)} λ^{−4} λ^{100}/2
= λ^{96}2^{−(l−r)}/M^2`; `λ_r^{96} ≥ 2^{l−r−2} λ_{l−2}^{95}` from Tower (a), (d)); (iii) (Chernoff at
`δ = 1/2`, `μ/8 ≥ Hcd/4`); (iv) (`2^{13}M^{12} ≤ λ^{95}` from `M ≤ λ^{1.6}`, `λ ≥ 2^{25}`); the
uniform-sequence count `6^k (4M−3k)!/(4M)!`; CC (i) (`|C \ {w}| ≥ Hcd/2 − 1 ≥ Hcd/3` for `Hcd ≥ 6`);
CC (ii) (`E[m 1_{m ≥ T}] ≤ eμ 2^{2−T}`, `T − 1 ≤ max(t − 1, 6e|S|/Hcd)`); CC (iii) (`Σ|S_w| ≤ 2|J| ≤
2.74 nM`, `6e·2.74 = 44.69`, `4e·2.74 = 29.79`, `2^{−t} ≤ M^{−2}`); Ultra (ii) (`T − 1 + 2e/T ≤
log₂N + 2eμ* + 1 + 2e < … + 8`); Ultra (iii) (`Σ_κ N_κ ≤ c`, at most `4M` colours); Ultra (iv)
(`g` decreasing, `θ ≥ λ^{95}/(57M)` since `λ^{95}/M ≥ 2^{453}`, `312.36 + 7.5 < 320`,
`log₂θ + 8 ≥ 16`). No math findings beyond the T0 note below.

## 5. Notes (no statement change required)

* **N1 (minor, consistency; `EG/Spec/Quot/Cand.lean` (iv), second conjunct).** `2^{10}M_l^{10} ≤ Hcd run G l`
  is `COLJVRow11Statement` at `l` (V5; `Hcd_def` is `rfl`). The TeX itself makes this
  cross-reference. Suggested action for the proof/stub owner: prove this conjunct from
  `COLJVRow11Statement` (+ V4 for `l ≤ R`) and do not create a second declared-input stub for it.
  No change to the Spec text.
* **N2 (cosmetic, obligation bookkeeping; `EG/Spec/Quot/RoundStep.lean`).** `RoundMarkovStatement`
  is provable today from `EG.Lib.Prob.Basic` (V3, 15 lines). Recommend the proof unit discharges it
  immediately (no stub), and that `s7a.md` H8 records that the two hypotheses are inert. Its
  existence form at `pastOf` is the first conjunct of s7b's `OneOutcomeRoundStatement`; the two are
  not duplicates (probability vs existence, abstract `I` vs `pastOf`), and after V3 no duplicated
  obligation remains.
* **N3 (minor, consumer guidance; `RoundStep.lean` (e2) and `CC.lean` (i)).** The uniform clauses are
  vacuous where `|E'(u)| > |Cand(u) \ Used(u)|` (V8a) and degenerate when `C' = ∅`; existence of
  the junctions is `WellDefE2Statement`. `s7a.md` H7 should say so (the fidelity review's R3), so
  that the proofs of CC (i) and Ultra (i) know to import `WellDefE2Statement`.
* **N4 (cosmetic, T0 record; `EG/Spec/Quot/Ultra.lean` (i)).** The first conjunct is a tautology of
  the encoding (V1). Record in `s7a.md` that "these items lie at `N` distinct ports, because … `G` is
  simple" has no Lean content: `hubItems` is a set of pairs `(h, u)`. Nothing is lost, since the
  distinctness that the independence conjunct needs is exactly distinctness of the `u`'s.
* **N5 (cosmetic, consistency; `EG/Spec/Stage1/Pool.lean` conjunct 2).** The middle inequality
  `Σ_{l ∈ Icc 3 R} (M_l)⁻¹ ≤ 2/D_*` is `TowerBMStatement`'s last conjunct (`Σ_{l ∈ Icc 1 R} 1/M_l ≤
  2/D_*`) after `one_div` and dropping `l = 1, 2` (all terms `≥ 0`). The proof should reuse
  `TowerBMStatement`; no change to the Spec.
* **N6 (cosmetic; `s7a.md` "Common reading").** State that the setting item "no VX-parts" has no
  Lean content (as `JVps.lean`, `Cost.lean` do; the fidelity review's R2).
* **N7 (coverage, unchanged from H10).** Not exhibited: a `RunHyp` run with a classed port of a
  round `l ≥ 3`, and an ultra hub under `I.Valid`. I checked that neither is contradictory: the
  former needs s2:propExists with `R ≥ 3`; the latter is consistent with every field of
  `RoundInput.Valid` (see the table), it merely needs `n ≥ 2^{407}` or so. `CCPartner`/`CCMax`
  are exercised only in their trivial instance (no PAR objects): a `Live`-style input with one live
  `J^par` item between two JV-good ports would give a non-trivial atom (fidelity review R5).

## 6. Math findings

* **T0 (s7:lemUltra (i), `UltraIndepStatement`, first conjunct).** "These items lie at `N` distinct
  ports, because distinct items at `h` are distinct edges `hu` and `G` is simple" is definitional in
  the encoding (V1). No manuscript action; recorded so that no one looks for a missing lemma.
* No T1–T3 findings: no statement appears false and no manuscript step appears wrong.
