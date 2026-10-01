# Clean-room review of the s7a Specs (lens: fidelity-first, model A)

Reviewer: clean-room statement reviewer. I did not edit any Lean file.
Inputs:
* the status note `work/p2s/s7a.md`;
* the Spec files `EG/Spec/Stage1/Pool.lean`, `EG/Spec/Quot/{Cand,CandDef,RoundStep,CC,Ultra}.lean`;
* the test file `EGTest/Spec_s7a.lean`;
* the locked Defs they read: `EG/Defs/Stage1/{Pool,Law,COL}.lean`, `EG/Defs/Quot/{Cand,Schedule,Round,Xprime}.lean`, `EG/Defs/Chain/Design.lean`, `EG/Defs/Gamma/Full.lean` (`RunHyp`), `EG/Defs/Prob/FinDist.lean`;
* the TeX: `proofs/manuscript/s7.tex` lines 1–925 (defPool, defCand, lemCand with its proof, defSchedule, consRound, the preamble of "Quotient size and payments", lemCC and lemUltra with their proofs) and `s2.tex` s2:lemTower.

**Verdict: approve.** All 14 statements are faithful back-translations of the TeX. I found no vacuity, no hidden Γ hypothesis and no duplicate. The remarks below are cosmetic or minor, and none of them requires changing a statement.

## 1. Checks run

* `python3 -I scripts/lint.py`: 0 findings.
* Duplicate check: `grep -rn "\[s7:(defPool|defCand|lemCand|consRound|lemCC|lemUltra)\]" EG/Spec`.
  * Outside the six files, the only hits are docstring references in `Simple.lean`, `Lift.lean` and `Num/CC.lean`.
  * `Num/CC.lean` holds the numerics of the proof of CC (iii), not the lemma itself.
  * No statement is duplicated.
* Scratch file `…/scratchpad/S7aVac.lean`, compiled against the built modules with `lake env lean`: 0 errors. It checks:
  1. the disjointness conjunct of `PoolLawStatement` for an arbitrary label family (proved);
  2. `listOf 1 3` on `Fin 12` has 3 elements, and `listOf 1 4` is empty. So `card = 3` in `RoundListsLawStatement` really forces `3i+2 < 4M`, and the first conjunct needs `3k_h ≤ 4M`. That is s7:lemWellDef (ii), and it holds under `I.Valid` (see §3.4);
  3. `ccPartner b o` is the unmarked end whenever `b o false ≠ b o true`.
* `FinDist` equality is extensional in the weights (the finite support is a `Prop` field). So the conjunct `(law G run).map Outcome.pool = poolLaw G run` is not a structural trap.

## 2. Setting, hypotheses, Γ

* The run-level Specs (`PoolLawStatement`, `CandCountStatement`, `CandSubsetStatement`) take `RunHyp N0 Dstar G run`. That is `Gamma1 ∧ Gamma3 ∧ N0Cond ∧ n ≥ N0 ∧ d_1 ≥ D_* ∧ run.Valid`: no Γ2(b),(c) and no Γ4.
* `CandCountStatement` and `CandSubsetStatement` also take `IsDesignation run G δ`. This matches the s7 section setting ("a designation δ is fixed").
* The setting item "there are no VX-parts (𝒱 = ∅)" has no Lean content. VX-parts are not defined in the formalization, as `JVps.lean` and `Cost.lean` record. `s7a.md` does not mention this item (remark R2).
* The round-level Specs take `I.Valid` and `R.Valid`. `RoundInput.Valid` is a locked Defs structure. None of its fields is a Γ2(b),(c) statement. The Γ consequences it carries (`M_ge`, `Hcd_ge`) are the manuscript's derived facts.

## 3. Statement by statement (TeX, back-translation, verdict)

### 3.1 `PoolLawStatement` [s7:defPool]: faithful

TeX (quoted in the file): "This is a probability distribution: for each `l` we have `Σ_{r=1}^{l−2} π_{l,r} = 1−2^{−(l−2)} < 1`, and `Σ_l q_l ≤ Σ_l M_l^{-1} ≤ 2/D_* < 1` … `P(v∈Pool_l) = q_l(1−2^{−(l−2)}) ≤ q_l` … pairwise disjoint … unique `r` … independent of all other stage-1 data".

Back-translation. Under `RunHyp`:
1. For every `l ≥ 3`, `Σ_{r=1}^{l−2} 2^{−(l−1−r)} = 1−2^{−(l−2)} < 1`. The sum is over `r ∈ [1,l]` with `r+2 ≤ l`.
2. The chain `Σ_{l=3}^R M_l^{−2} ≤ Σ_{l=3}^R M_l^{−1} ≤ 2/D_* < 1` holds.
3. `poolMass < 1`.
4. The pool marginal of the stage-1 law is the product law.
5. The point probabilities `q_lπ_{l,r}` and `1 − poolMass` are as stated.
6. `P(v ∈ Pool_l) = q_l(1−2^{−(l−2)}) ≤ q_l` for `v ∈ V(G)` and `3 ≤ l ≤ R`.
7. Deterministic disjointness holds for every label family.
8. `r(w)` exists and is unique.
9. `IndepFun (col, zone, js) pool`.

Checks:
* The exponents are integer (`zpow`), with no ℕ-subtraction.
* `(l,r) ∈ poolIdx` is exactly `3 ≤ l ≤ R, 1 ≤ r, r+2 ≤ l`.
* `Σ_{l∈[3,R]} M_l^{-1} ≤ Σ_{l≤R} M_l^{-1} ≤ 2/D_*` is s2:lemTower(b).
* `2/D_* < 1` comes from `D_* > 2` (Γ1).
* The point probabilities need the `dite` guard `poolMass ≤ 1`, which follows from item 3.
* The strict `< 1` is the TeX's own argument (H5), so it is not a strengthening beyond the TeX.

### 3.2 `CandSubsetStatement` [s7:defCand]: faithful

TeX: "Since `LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)` and `H_Y` is a graph on `V(Y)`, automatically `Cand_l(u) ⊆ N_{H_Y}(u)` and `N_{H_Y}(u) ⊆ V(Y)`". The section setting adds "`Y(u) ∈ anc_l(u)` … `r(u) ≤ l−2` and `u ∈ V(Y(u))`".

Back-translation. Let `u` be a classed port of round `l ≥ 3`, and let `Y = δ l u`. Then:
* `Y` is an ancestor;
* `1 ≤ r(Y) ≤ l−2`;
* `u ∈ V(Y)`;
* for every outcome `ω`, `Cand_l(u) ⊆ N_{H_Y}(u) ⊆ V(Y)`, with the record's LJV pinned to `ω` by `hS`.

These are exactly the claimed facts, and they are the fields `cls_anc`, `cls_round`, `cls_mem` and part of `ljv_in` that `ofPast` consumes.

### 3.3 `CandCountStatement` [s7:lemCand]: faithful

TeX (i)–(iv) is quoted in the file.

Back-translation:
* (i)
  * For every `ω`, `|Cand_l(u)| = Σ_{w∈N_{H_Y}(u)} 1[plab(w)=(l,r)]·1[uw∈LJV_{Y,l}]`. This is the proof's display. It is also the Lean encoding of "a sum … one for each `w`".
  * The summands are `iIndepFun` under the stage-1 law.
  * `P(summand = 1) = q_l π_{l,r} p_Y`.
* (ii)
  * `E|Cand| = candMean`, where `candMean = q_lπ_{l,r}p_Y deg_{H_Y}(u)`.
  * `λ_r^{96}2^{−(l−r)}/M_l^2 ≤ candMean`.
  * `2Hcd_l ≤ λ_r^{96}2^{−(l−r)}/M_l^2`.
* (iii) `P(JVBad) ≤ exp(−Hcd_l/4)`.
* (iv) The first part is stated for every stage record `S` and every label family `π`: `¬JVBad → Hcd_l ≤ |Cand|`. The second part is `2^{10}M_l^{10} ≤ Hcd_l`.

Checks:
* The Bernoulli probability is exact: `(l,r) ∈ poolIdx` since classed ports only exist for `l ≤ R`, and `r(Y)+2 ≤ l ≤ R` puts `l` in `I^JV(Y)`.
* Membership of `uw` in `LJV_{Y,l}` reads only the label of the edge `uw` (`lentClass` via `selectSet`). So the independence claim is true in the encoding.
* (iv) in the general form is true: `u` is classed, so `¬JVBad ⟺ |Cand| ≥ candMean/2 ≥ Hcd_l` by (ii). It is stronger than the TeX's "for the outcome" but equivalent in content (H4), and it is the consumer's form (`good_cand`).
* Γ: none beyond `RunHyp`.

### 3.4 `RoundStep.lean` [s7:consRound]: faithful

* **`RoundRulesExistStatement`** means: for a valid past, every non-ultra hub with `c ≥ 1` has `c ≤ k_h⌈Hcd/8⌉`, and valid rules exist. This is the TeX's "Rules with these arguments exist" and "This is possible because `k_h⌈Hcd_l/8⌉ ≥ c^live_h`". It is proved in the test file.
* **`RoundListsLawStatement`.**
  * I recomputed the count. A uniform permutation `η` maps the blocks `{3i,3i+1,3i+2}` (`i < k`) onto prescribed disjoint 3-sets `A_i` with probability `6^k(4M−3k)!/(4M)! = 6^k/(4M)_{3k}`. This is the reciprocal of the number of ordered sequences of `k` disjoint 3-subsets, so the claim is exactly "uniformly random sequence".
  * The first conjunct ("pairwise disjoint 3-subsets of `[4M]` for every `L`") needs `3k_h ≤ 4M`. That holds under `I.Valid`: `k_h ≤ ⌈8M/7⌉` and `M ≥ 2^{40}`, which is `WellDefListsStatement`.
  * `h ∈ G.verts` is implied by `c^live_h ≥ 1`, because live items are edges of `G` (`J_sub`). So `etaAt` reads the random `η_h`, not the identity fallback.
  * The independence clause over `↥I.hubs` reads `η_h` (non-ultra) or `ζ_{h,·}` (ultra) only, so it is true. It covers both TeX sentences.
* **`RoundInjectionStatement`.**
  * `e2Junc` reads index `i` of `e` in `e2Order L u`, then entry `i` of the `≺_u`-sorted `C(u) = Cand(u)∖Used(u)`.
  * `C(u) ⊆ Pool ⊆ V(G)` and `u ∈ V(G)` (`pool_sub`, `ports_sub`), so the sorted list is the uniformly ordered `C(u)`. Under a uniform order, the probability of a prescribed injective image is `1/(|C|)_{|E'|}`.
  * Independence over ports holds because the map at `u` reads only `O u`.
  * If `|E'(u)| > |C(u)|`, no admissible `f` exists and the clause is vacuous. Well-definedness is carried separately by `WellDefE2Statement` (see R3).
* **`RoundMarkovStatement`** is Markov's inequality for the non-negative `copies`, `payrd` under `roundLaw`, plus a union bound. It is faithful. The hypotheses `I.Valid`, `R.Valid` are unused but harmless (H8).

### 3.5 `CC.lean` [s7:lemCC]: faithful

* **Atoms (H2/CC-ATOMS).**
  * Every port carries at most one `κ`-end, because greedy colouring separates objects that share a port, and the two ends of an object are distinct: `u ≠ v` for an edge, and a cherry's pairing list is `Nodup`.
  * So the TeX's port-indexed indicators and the end-indexed indicators generate the same atoms. The conditioned law factorizes over ports, which is what makes (i) true.
  * `ccPartner b o = b o false` selects the unmarked end (checked in the scratch file).
* **(i)**
  * Partner ports are injective on `S_w`.
  * The partner junctions are `iIndepFun` under the conditioned law.
  * The point probabilities are `1/|C'|` on `C' = (Cand(v_o)∖Used(v_o))∖{w}`.
  * Each point probability is `≤ 3/Hcd`. This needs `|C'| ≥ Hcd/2−1 ≥ Hcd/3`, using `WellDefE2` at the partner port. That port is a port carrying a live item, since PAR objects are made of live items.
* **(ii)**
  * The max is over `w' ∈ Pool_l∖{w}`. This loses nothing: junctions are candidates, and candidates are in `Pool`.
  * The bound `t·1[S≠∅] + 6e|S|/Hcd + 4e2^{−t}|S|` is verbatim, with `t : ℕ` and `t ≥ 1`.
* **(iii)** `E_orders[#PAR-tagged vertices of Q_l] ≤ 3M(t^CC+1)|Pool| + 44.7nM/Hcd + 29.8n/M` holds for every `L`, with `t^CC = ⌈2log₂M⌉` (`Xprime.tCC`). This is verbatim, and it is the form the consumer s7:lemUHsplit (ii) averages over the lists.

### 3.6 `Ultra.lean` [s7:lemUltra]: faithful

* **(i)**
  * The injectivity of `Prod.snd` on the items of the fixed `h` is trivially true. The TeX says the same ("because distinct items at `h` are distinct edges").
  * The junctions are independent.
  * For each item, `|C(u)| ≥ Hcd/2` and the junction is uniform on `C(u)`. The TeX's existential "a set of size at least `Hcd/2`" is instantiated with the set named in its own proof. This is slightly stronger than the TeX, and faithful to the proof.
* **(ii)** For `N ≥ 1`, `E[max_{w∈Pool} m_κ(h,w)] ≤ log₂N + 2e(2N/Hcd) + 8`.
* **(iii)** `E[#hub-side HUB copies of h] ≤ 4M(log₂c_h+8) + 4e c_h/Hcd`.
* **(iv)** The sum over `h ∈ D_l` with `c_h > θ^ult` is `≤ 320·nM^3(log₂θ^ult+8)/λ^{95}`.

All constants, the log base (`Real.logb 2`) and `e = exp 1` match. `λ > 0` follows from `Hcd_ge`, so the division is meaningful.

## 4. Mathematics re-derived (no error found)

I re-derived the following:
* **s7:lemCand.**
  * (ii): the exponent bookkeeping `2^{−(l−1−r)}/2 = 2^{−(l−r)}` and the reduction to `λ_r^{96} ≥ 2^{l−r−2}λ_{l−2}^{95}`.
  * (iii): Chernoff with `δ = 1/2`, `exp(−μ/8) ≤ exp(−Hcd/4)`.
  * (iv): `2^{13}M^{12} ≤ λ^{95}`, using `λ ≥ M^{1/1.6} ≥ 2^{25}`.
* **Uniform-sequence count.** `(4M)_{3k}/6^k`.
* **Lemma CC (ii).**
  * For `j ≥ T`, `j ≥ 2eμ_{w'}`.
  * `E[m1{m≥T}] ≤ eμ2^{2−T}`.
  * `max ≤ T−1+Σ`.
  * `T−1 ≤ max(t−1, 6e|S|/Hcd)`.
* **Lemma CC (iii).** `6e·2.74 = 44.69`, `4e·2.74 = 29.79`, and `2^{−t} ≤ M^{−2}`.
* **Lemma Ultra (ii).**
  * With `T = max(⌈2eμ*⌉, ⌈log₂N⌉+1)`: `eμ_w/j ≤ 1/2`, `(eN/T)2^{2−T} ≤ 2e/T`, and `T−1 ≤ log₂N+2eμ*+1`.
* **Lemma Ultra (iv).**
  * `x²g'(x) = 1/ln2 − 8 − log₂x < 0`.
  * `λ^{95}/M ≥ 2^{13}M^{11} ≥ 2^{453}`, which gives `θ ≥ λ^{95}/(57M)`.
  * `4·1.37·57 = 312.36`.
  * `4e·1.37·8 = 119.17`, and `119.2/16 = 7.45`.
  * `312.36 + 7.5 < 320`.

There are no math findings.

## 5. Remarks (no statement change required)

* **R1 (cosmetic, `EG/Spec/Quot/CC.lean`, module docstring, "Formal reading" (i)).** The docstring says the uniform formula "forces `C ≠ ∅` and 'the junction is some element of `C`' almost surely". That is true only when `C' ≠ ∅`. For `C' = ∅` the formula gives probability 0 everywhere, which is consistent with the junction being `none`. The degenerate case is excluded by `WellDefE2Statement`. Suggested wording: "when `C' ≠ ∅` (Lemma s7:lemWellDef (v)), this forces …".
* **R2 (cosmetic, `work/p2s/s7a.md` "Common reading").** Say that the s7 setting item "no VX-parts (𝒱 = ∅)" has no Lean content, as `JVps.lean` and `Cost.lean` do.
* **R3 (minor, `s7a.md` H7).** Record the other degenerate case. In `RoundInjectionStatement` (and in CC (i)), if `|E'(u)| > |C(u)|` the uniform clause is vacuous or allows `none`. The existence of the junctions is `WellDefE2Statement`, which a consumer must combine with these Specs.
* **R4 (minor, coverage; already hazard H1 / TRIAGE §3 item 31).** Every round-level Spec of this chunk is conditional on `I.Valid`, and the bridge `(RoundInput.ofPast …).Valid` is still not stated as a Spec. Until it is, CC, Ultra, RoundStep and the P1 run-level Specs cannot be discharged at the run level. The integrator should keep this on the obligation list.
* **R5 (minor, non-vacuity coverage, `EGTest/Spec_s7a.lean`).** The test input `Live.I` has no PAR objects, and its only port has `E'(1) = ∅`. So `CCPartnerStatement`, `CCMaxStatement` and `RoundInjectionStatement` are exercised only in instances where their conclusions are trivial. A small valid input with one live `J^par` item (two JV-good ports with large candidate sets) would exercise a non-trivial atom. H10 (`RunHyp` with `R ≥ 3`, and ultra hubs) stays unchecked, as the author says.
