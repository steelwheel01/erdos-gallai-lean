# GAMMA: the constants N₀, D_* and the galactic conditions Γ1–Γ4. Stage 1: definitions and statements

Unit GAMMA, stage 1. This stage delivers:
- the Defs of TRIAGE §3 item 14 (`EG/Defs/Gamma/Full.lean`) and the combined predicate `GammaCond` (item 34);
- the Specs of every node of the unit;
- stage-1 reductions and API lemmas, all trivial;
- non-vacuity tests.

The unit has **no declared inputs and no `sorry`**. Fix round 1 added the three proofs that stage 1 had deferred: the Lib lemma `EG.Vortex.eventually_size`, the eventual form of column 3 of the COL-JV table, and the limits `ε_1, ε_2 → 0`. From them and the stage-1 reductions, `EG.exists_N0`, `EG.exists_gammaCond` and the full non-vacuity test `EGTest/GammaFull.lean` are proved. Every statement of the unit is now a theorem.

The proof being formalized is a CANDIDATE proof of the Erdős–Gallai cycle decomposition conjecture. It has been reviewed only by AI, so nothing here says the conjecture is solved.

Sources:
- the manuscript v6.1:
  - `proofs/manuscript/s1.tex` 1519–1780: s1:defConstants, s1:remOrder, s1:condGamma, s1:tabOrder;
  - `s3.tex`: s3:lemCOLJVev;
  - `s4.tex` 206, 463, 678: the size conditions;
  - `s5.tex` 9: setting; `s5.tex` 399: s5:remConstants;
  - `s7.tex` 10: setting; s7:lemGammaSat;
- `work/p2/TRIAGE.md` §2.4, §2.6, §3 items 12–14 and 34;
- `work/p2/nodes_s1.json` (s1:defConstants, s1:condGamma), `nodes_s7b.json` (s7:lemGammaSat), `nodes_s3b.json` (s3:lemCOLJVev);
- `work/p2d/params.md` (D-VX-1, D-VX-2, and the route to `eventually_size`);
- `work/p2d/quot.md` (open item 1: `GammaCond` outside the locked `Main/Gamma.lean`).

## 1. Status

| file | content | state |
|---|---|---|
| `EG/Defs/Gamma/Full.lean` | NEW Defs: `Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp` | compiles |
| `EG/Defs/Main/GammaCond.lean` | NEW Def: `GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` | compiles |
| `EG/Spec/Gamma/N0.lean` | `VortexEventuallySizeStatement`, `N0EventuallyStatement`, `N0ExistsStatement` | compiles |
| `EG/Spec/Gamma/Sat.lean` | `Col3EventuallyStatement`, `GammaSatItemsStatement`, `GammaSatEpsStatement`, `GammaSatStatement`, `GammaCondExistsStatement` | compiles |
| `EG/Lib/Gamma/Full.lean` | API (trivial): projections, upward closure, `RunHyp.gamma2a`, `RunHyp.gammaCond`, `GammaCond.of_gamma134` | **proved** |
| `EG/Lib/Vortex/Size.lean` (fix round 1) | `EG.Vortex.eventually_size` (+ `tendsto_etaTPV`, `tendsto_etaPV`, `tendsto_etaVX`, `eventually_L_cube_le`) | **proved** |
| `EG/Lib/Gamma/Col3.lean` (fix round 1) | `EG.COLTable.col3_of_le` (`col3 μ` for `μ ≥ 2^40`), `EG.COLTable.eventually_col3` | **proved** |
| `EG/Lib/Gamma/Eps.lean` (fix round 1) | `EG.tendsto_epsA`, `EG.Chain.tendsto_epsCONC`, `EG.Quot.tendsto_epsX`, `EG.Quot.tendsto_FQ`, `EG.Quot.tendsto_eps1`, `EG.Quot.tendsto_eps2` | **proved** |
| `EG/Proof/Gamma/N0.lean` | reductions `n0Eventually_of_size`, `n0Exists_of_eventually`; final `vortexEventuallySize`, `eventually_N0Cond`, `exists_N0` | **proved** |
| `EG/Proof/Gamma/Sat.lean` | reductions `gammaSatItems_of_col3`, `gammaSat_of_items_eps`, `gammaCondExists_of`; `tendsto_logb_logb_atTop`; final `col3_eventually`, `gammaSat_items`, `gammaSat_eps`, `gammaSat`, `exists_gammaCond` | **proved** |
| `EGTest/ProbeGAMMA.lean` | cheap non-vacuity and negative tests | compiles, 0 sorry |
| `EGTest/GammaFull.lean` (fix round 1) | `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D`, `∀ N0, ∃ D, GammaCond N0 D`, `∃ N0, N0Cond N0` | compiles, 0 sorry |

Checks run:
- `lake build` of each module;
- `scripts/check.sh` on each file and on `EGTest/ProbeGAMMA.lean`: 0 errors and 0 sorry;
- `python3 -I scripts/lint.py`: 0 findings;
- the axiom scan of `EG.Proof.Gamma.Sat`, `EG.Proof.Gamma.N0` and `EG.Lib.Gamma.Full`: 954 constants, 0 `sorryAx`, 0 violations.

Stage 1 did not write `EG/Lib/Vortex/Size.lean` and `EGTest/GammaFull.lean`; fix round 1 wrote them (see "Fix round 1" below). The stage-1 test (`EGTest/ProbeGAMMA.lean`, first example) chains every reduction from the three statements `VortexEventuallySizeStatement`, `Col3EventuallyStatement` and `GammaSatEpsStatement`, which are now theorems.

## 2. Nodes: manuscript label → Lean

| label | Lean statement | proof | notes |
|---|---|---|---|
| s1:defConstants (ii), "an explicit inequality in `N`, which holds for all sufficiently large `N`" | `EG.Spec.VortexEventuallySizeStatement` | **done**: `EG.Vortex.eventually_size` (Lib, required by TRIAGE §3 item 14); `EG.vortexEventuallySize` | the size conditions of s4:lemTPV, s4:lemPV, s4:thmVXp |
| s1:defConstants (ii), "Every requirement on `N_0` … is an eventuality" | `EG.Spec.N0EventuallyStatement` | **done**: `EG.eventually_N0Cond` (via `EG.n0Eventually_of_size`) | |
| s1:defConstants (ii), "So such an `N_0` exists" | `EG.Spec.N0ExistsStatement` | **done**: `EG.exists_N0` (via `EG.n0Exists_of_eventually`) | the name fixed by TRIAGE |
| s3:lemCOLJVev (iii) | `EG.Spec.Col3EventuallyStatement` | **done**: `EG.col3_eventually` (`EG.COLTable.eventually_col3`, threshold `μ ≥ 2^40`) | all 13 rows at once |
| s7:lemGammaSat (i) | `EG.Spec.GammaSatItemsStatement` | **done**: `EG.gammaSat_items` (via `EG.gammaSatItems_of_col3`, from COLJVev(iii) and the existing `EG.eventually_gamma1Items`) | |
| s7:lemGammaSat (ii) | `EG.Spec.GammaSatEpsStatement` | **done**: `EG.gammaSat_eps` (`EG.Quot.tendsto_eps1`, `tendsto_eps2`) | `ε_1, ε_2 → 0` |
| s7:lemGammaSat (iii) | `EG.Spec.GammaSatStatement` | **done**: `EG.gammaSat` (via `EG.gammaSat_of_items_eps`) | stated for every real `N0` (H2) |
| s7:lemGammaSat "In particular a constant `D_*` … exists" + s1:defConstants (ii), (iii) | `EG.Spec.GammaCondExistsStatement` | **done**: `EG.exists_gammaCond` (via `EG.gammaCondExists_of`); tested in `EGTest/GammaFull.lean` | the non-vacuity of the main theorem's hypotheses |
| s1:condG1 "So Γ1 is upward closed in `D_*`" | (API) `EG.Gamma1.mono`, `EG.Gamma1f.mono` | **done** | |
| s1:condG2 "(a) is immediate from Γ1" | (API) `EG.Gamma1.gamma2a`, `EG.RunHyp.gamma2a` | **done** | from the existing `Gamma1core.gamma2a` |
| s1:tabOrder "every requirement is upward closed in `N_0`" | (API) `EG.N0Cond.mono` | **done** | |

## 3. Declared inputs

**None.**

Every node is pure real analysis on locked definitions:
- the vortex size predicates;
- the COL-JV column 3;
- the explicit ε-functions of s2, s5, s6 and s7.

The unit is required to have no `sorry`. The only external facts the proof stage needs are already proved Lib lemmas:
- `EG.eventually_gamma1Items` (items (a)–(e));
- `EG.Light.tendsto_epsU`, `EG.Light.tendsto_epsChain` (`= ε_K`);
- the log* growth `EG.logStar_isLittleO_loglog`, `EG.logStar_le_two_add_loglog`;
- `EG.Vortex.two_pow_mul_exp_neg_le`.

s3:lemCOLJVev (iii) is not declared as an input. It is a node of this unit, because Γ1(f) needs it and no other unit's closure contains it (P-4 has only COL-JV rows 4, 7, 8, which are s3:lemCOLJV (ii)). If an s3 unit later writes `EG/Spec/Lend/COLJVev.lean`, the (iii) part there should be proved from `EG.Spec.Col3EventuallyStatement`, or the other way round (open question Q3).

## 4. Defs used

Locked:
- `EG.Gamma1core`, `Gamma1Items`, `Gamma1a`–`Gamma1e`, `Gamma2a` (`EG/Defs/Gamma/Core.lean`);
- `EG.Gamma4`, `EG.cEG` (`EG/Defs/Main/Gamma.lean`);
- `EG.COLTable.col3`, `row` (`EG/Defs/Lend/COLTable.lean`);
- `EG.Vortex.L`, `etaTPV`, `etaPV`, `etaVX`, `TPVSize`, `PVSize`, `VXSize` (`EG/Defs/Vortex.lean`);
- `EG.Quot.eps1`, `eps2`, `epsX`, `FQ`, `thetaQ` (`EG/Defs/Quot/Constants.lean`);
- `EG.Chain.epsK`, `epsCONC`, `EG.Light.epsU`, `EG.HB.epsA`, `EG.HB.psiPool`;
- `EG.HB.Run`, `Run.d`, `Run.Valid` (`EG/Defs/HB/Run.lean`);
- `EG.FGraph.card`;
- `EG.Cp`, `EG.Aexp`.

**New Defs files** (this unit was authorized to create them; not under `EG/Defs/Probe/`):

| file | declarations |
|---|---|
| `EG/Defs/Gamma/Full.lean` | `EG.Gamma1f`, `EG.Gamma1`, `EG.N0Cond`, `EG.Gamma3`, `EG.RunHyp` |
| `EG/Defs/Main/GammaCond.lean` | `EG.GammaCond` |

`GammaCond` is in a new file because `EG/Defs/Main/Gamma.lean` (with `Gamma4`, `cEG`) was locked before `Gamma1` and `Gamma3` existed. See `work/p2d/quot.md`, open item 1; that file's docstring announces the addition. The shapes are exactly those of TRIAGE §2.4, §2.6 and D-VX-1.

## 5. Back-translation (TeX ↔ Lean ↔ plain mathematics)

`log₂` is `Real.logb 2`. `N` is a natural number wherever it is a vertex count.

### Definitions

**`Gamma1f D`** := `∀ μ : ℝ, logb 2 (logb 2 D) ≤ μ → COLTable.col3 μ`.
- TeX (s1:condG1 (f), inside "for every real `μ ≥ log₂log₂D_*`, with `λ := 2^μ`"): "for every row of the COL-JV table …, every inequality in column 3 of that row holds at `λ`, where `M̄ := (Aμ)^{2A}` and `k̄ := 192λ³ + (4/3)M̄²`".
- Plain: for every real `μ ≥ log₂log₂D`, all 18 column-3 inequalities of rows 1–13 hold at `λ = 2^μ`.

**`Gamma1 D`** := `Gamma1core D ∧ Gamma1f D`.
- TeX (Γ1): "`D_* > 2` …; and for every real `μ ≥ log₂log₂D_*` … (a)–(f) hold".
- Plain: `D > 2`, and items (a)–(f) hold at every real `μ ≥ log₂log₂D`. The `D > 2` is inside `Gamma1core`.

**`N0Cond N0`** := `2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N:ℝ) → TPVSize N ∧ PVSize N ∧ VXSize N`.
- TeX (s1:defConstants (ii)): "`N_0 ≥ 2^{40}` … and `N_0` at least each of the absolute size thresholds required in the proofs of Lemma s4:lemTPV, Lemma s4:lemPV and Theorem s4:thmVXp … every other requirement asks that an explicit inequality in `N` … hold for every `N ≥ N_0`". s4 adds: "the finitely many explicit inequalities listed as *size conditions* in the three proofs of this section hold for every `N ≥ N_0`".
- Plain: `N_0 ≥ 2^40`, and every natural `N ≥ N_0` satisfies the size conditions (i) `L ≥ 2^10`, (ii) `N ≥ L³` and (iv) `η(N) ≤ 1/100` of all three vortex proofs, where `L = log₂N`. Condition (iii) is derived from (i) (D-VX-2).

**`Gamma3 N0 D`** := `2 * N0 ≤ logb 2 D ^ Cp`, with `Cp = 103` as a natural-number power.
- TeX (s1:condG3): "`(log₂ D_*)^{C'} ≥ 2 N_0`".
- Plain: `(log₂D)^103 ≥ 2N_0`.

**`RunHyp N0 D G run`** := `Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧ N0 ≤ G.card ∧ D ≤ run.d G 1 ∧ run.Valid G D`.
- TeX (setting of s5): "`G` is a graph on `n ≥ N_0` vertices with `d_1 ≥ D_*`; `D_*` satisfies Γ1–Γ4; a valid `HB^tp` run on `G` is fixed". The setting of s7 is the same.
- Plain: `N_0` as in (ii); `D` satisfies Γ1 and Γ3; `|V(G)| ≥ N_0`; the average degree of round 1 (`graph G 1 = G`) is at least `D`; and the run is valid for `D`.
- By design (TRIAGE §2.6), Γ2(a) is derived (`RunHyp.gamma2a`), and Γ4 is added by the statements that use it (`RunHyp.gammaCond`).

**`GammaCond N0 D`** := `Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D`.
- TeX (s1:defConstants (iii)): "`D_*` is a constant satisfying Γ1–Γ4 of Condition s1:condGamma".
- Plain: `D` satisfies Γ1 (a)–(f), `D ≥ 2^117`, `(log₂D)^103 ≥ 2N_0`, `ε_1(D) ≤ 6` and `ε_2(D) ≤ 1/4`.
- Γ2(b),(c) are not fields ("Each of (a)–(c) is implied by Γ1 …"). They quantify over runs and failure probabilities, and they are lemmas of s2, s3 and s5.

### Statements

**`VortexEventuallySizeStatement`** := `∀ᶠ N : ℕ in atTop, TPVSize N ∧ PVSize N ∧ VXSize N`.
- TeX: "every other requirement asks that an explicit inequality in `N`, which holds for all sufficiently large `N`, hold for every `N ≥ N_0`".
- Plain: there is `N_1` such that every natural `N ≥ N_1` satisfies all size conditions of the three vortex proofs.

**`N0EventuallyStatement`** := `∀ᶠ N0 : ℝ in atTop, N0Cond N0`.
- TeX: "Every requirement on `N_0` in this item is an eventuality: it holds for every sufficiently large value of `N_0`".
- Plain: every sufficiently large real `N_0` is admissible.

**`N0ExistsStatement`** := `∃ N0 : ℝ, N0Cond N0`.
- TeX: "So such an `N_0` exists".
- Plain: an admissible `N_0` exists.

**`Col3EventuallyStatement`** := `∀ᶠ μ : ℝ in atTop, COLTable.col3 μ`.
- TeX (s3:lemCOLJVev (iii)): "for each row …, every inequality in column 3 holds at `λ = 2^μ` for all sufficiently large real `μ`".
- Plain: there is `μ_0` such that all 18 column-3 inequalities hold at every real `μ ≥ μ_0`. Taking all rows at once is equivalent, since there are finitely many rows.

**`GammaSatItemsStatement`** := `(∀ᶠ μ in atTop, Gamma1Items μ ∧ col3 μ) ∧ ∃ μ₁, 1 ≤ μ₁ ∧ (∀ μ ≥ μ₁, Gamma1Items μ ∧ col3 μ) ∧ ∀ D, 2 < D → μ₁ ≤ log₂log₂D → Gamma1 D`.
- TeX (s7:lemGammaSat (i)): "each item (a)–(f) of Γ1 holds for all sufficiently large real `μ`; hence there is `μ_1 ≥ 1` such that all of them hold for every `μ ≥ μ_1`, and Γ1 holds for every `D_* > 2` with `log₂log₂D_* ≥ μ_1`".
- Plain: literally the three clauses. The per-item eventualities are stated as one conjunction, which is equivalent.

**`GammaSatEpsStatement`** := `Tendsto Quot.eps1 atTop (𝓝 0) ∧ Tendsto Quot.eps2 atTop (𝓝 0)`.
- TeX (s7:lemGammaSat (ii)): "`ε_1(D_*) → 0` and `ε_2(D_*) → 0` as `D_* → ∞`".
- Plain: literally that.

**`GammaSatStatement`** := `∀ N0 : ℝ, ∀ᶠ D : ℝ in atTop, GammaCond N0 D`.
- TeX (s7:lemGammaSat (iii), with "Let `N_0` be as in Definition s1:defConstants(ii)"): "there is `D_0` such that every `D_* ≥ D_0` satisfies Γ1–Γ4 simultaneously".
- Plain: for every real `N_0` there is `D_0` such that every `D ≥ D_0` satisfies Γ1–Γ4 with respect to `N_0`. This is stronger than the TeX (H2).

**`GammaCondExistsStatement`** := `∃ N0 D : ℝ, N0Cond N0 ∧ GammaCond N0 D`.
- TeX: "In particular a constant `D_*` as in Definition s1:defConstants(iii) exists", together with "So such an `N_0` exists".
- Plain: admissible constants `N_0` and `D_*` exist. So the hypotheses of the main theorem (blueprint `MainExplicit`: `N0Cond N0 → GammaCond N0 D → …`) are not vacuous.

## 6. Hazards

**H1 (T0, `N_0` is real).**
- The manuscript's parenthetical "(redundant: size condition (i), `L ≥ 2^{10}`, already forces `N_0 ≥ 2^{1024}`)" is exact only for an integer `N_0`.
- With a real `N0` and `N` ranging over ℕ, `N0Cond N0` depends only on `⌈N0⌉`. The exact consequence is `N0 > 2^{1024} − 1`. For example, `N0Cond (2^{1024} − 1/2) ↔ N0Cond (2^{1024})`, and the right side is expected to hold (the route of §8).
- Lean has the weaker `n0Cond_forces : N0Cond N0 → 2^{1023} < N0` (EGTest).
- No proof uses the parenthetical, since the manuscript calls it redundant. Nothing changes; at most the wording could say "`⌈N_0⌉ ≥ 2^{1024}`".

**H2 (strengthening of s7:lemGammaSat (iii)).**
- `GammaSatStatement` quantifies over every real `N0`, without `N0Cond N0`. This follows the blueprint ("in Lean: any real N0").
- The TeX proof uses only that `N_0` is fixed ("Γ3 holds for every `D_* ≥ 2^{(2N_0)^{1/C'}}`"). The Lean reduction `gammaSat_of_items_eps` confirms that no hypothesis on `N0` is needed.
- Nothing is weakened.

**H3 (`GammaCond` does not contain `N0Cond`).** Statements about the main theorem need both hypotheses, `N0Cond N0` and `GammaCond N0 D`, as in the blueprint's `MainExplicit`. `GammaCondExistsStatement` checks them jointly.

**H4 (`RunHyp` omits Γ4 and Γ2(a)).**
- This is by design (TRIAGE §2.6).
- The s5 and s7 settings say "Γ1–Γ4", so a Spec whose proof uses Γ4 must add `Gamma4 D`. These are thmJVps, `C0_le` (s7:propCost, "`C_0 ≤ D_*/2 + 1091` under Γ4"), thmMainProof, **s7:lemUHsplit (iv)** ("`θ_Q ≤ 1/4` by condition Γ4", s7.tex 1120 and its proof 1190; added in fix round 1, also in TRIAGE §2.6), plus any s5 statement using s5:remConstants (b) ("`745 ≥ 1 + 2·369 + ε_K(D_*)` whenever `ε_K(D_*) ≤ 6`. This holds under Γ4"). The remark itself says the slack "is not needed", because s5:lemKRED carries `ε_K` separately.
- Reviewers of s5–s7 Specs should check that Γ4 is added wherever it is used.

**H5 (`RunHyp` forces `R ≥ 1`).**
- `Run.Valid` contains `d_{R+1} < D`, and `graph G 1 = G` because round 0 is not a round. So `D ≤ run.d G 1` excludes `R = 0`.
- The manuscript agrees: "`d_1 ≥ D_*`" means round 1 exists.

**H6 (junk ranges).**
- For `D ≤ 1`, `logb 2 D ≤ 0` and `(logb 2 D)^{103} ≤ 0`, so `Gamma3 N0 D` is false for `N0 > 0`.
- For `D ∈ (1, 2]`, the ray of `Gamma1f` starts at `μ ≤ 0`, where row 1 fails (EGTest: `¬ Gamma1f 2`).
- Every use pairs `Gamma1f` with `Gamma1core` (`D > 2`). `Gamma1f.mono` takes `2 < D` explicitly.

**H7 (Γ4 is not vacuous).** At `D_* = 4`, `ε_1(4) > 6`, since `614/4 = 153.5` and the other terms are non-negative (EGTest `eps1_four_gt`). So Γ4 is a genuine condition, as are Γ1 (`¬ Gamma1 16`), Γ3 (`¬ Gamma3 (2^900) (2^256)`) and `N0Cond` (`¬ N0Cond (2^40)`).

**H8 (truth of the open statements, checked on paper).**
- Size conditions (`N = 2^L`):
  - each η term is `2^{O(L)}·N^{-3}`, or `N·L·e^{-cL^4}`, or `N L e^{-3L²/(32 log₂L)}`, or `L e^{-N/(5000L)}`;
  - each tends to 0, because `3L²/(32 log₂L) − L·ln2 → ∞`;
  - `L ≥ 2^{10}` and `N ≥ L³` are eventual.
- Column 3: every row is type (E) or dominated by one, and row 1's first inequality is `λ^{1/2} > 257(1 + (6μ+20)/λ)^{102}`.
- `ε_1` and `ε_2`: every summand tends to 0:
  - `ε_K`, `ε_U`: existing Lib limits;
  - `ε_A ~ 1/log log D`;
  - `ε_CONC`: `log*D/log D`, `log*D/log log D` (`logStar_isLittleO_loglog`), `(2log*D + 2)/(log D)^{1/2}`;
  - `ψ(D)`, `60/D`, `10.3/D`;
  - `F(log₂D) = (3184 + 30400 log₂log₂D)(log₂D)^{-90.2}`.

  No counterexample risk is known.

## 7. Open questions

**Q1.** `RunHyp` non-vacuity (a graph with a valid run and `d_1 ≥ D_* ≥ 2^{2^{256}}`) is not cheap. It belongs to s2:propExists, not to this unit.

**Q2.** The blueprint placed GammaSat in `EG/Spec/Main/GammaSat.lean` and named the proof `EG.gammaSat`. This unit uses `EG/Spec/Gamma/Sat.lean`, with the final theorem names planned as follows:
- `EG.col3_eventually : Spec.Col3EventuallyStatement`;
- `EG.gammaSat_items`;
- `EG.gammaSat_eps`;
- `EG.gammaSat : Spec.GammaSatStatement`;
- `EG.exists_gammaCond : Spec.GammaCondExistsStatement`;
- `EG.exists_N0 : Spec.N0ExistsStatement`;
- `EG.eventually_N0Cond`.

The integrator may move them.

**Q3.** s3:lemCOLJVev (i) and (ii) (the type-(E) route) are not stated here. Only (iii) is used by Γ1(f). If an s3 unit states the whole lemma, the two (iii) statements must agree; they are syntactically the same eventuality.

**Q4.** The Γ4-using s5 statements (H4) have to be identified by the s5 statement authors. A Spec of s7:lemUHsplit (iv) on `RunHyp` must add `Gamma4 D`, or drop the clause `θ_Q ≤ 1/4` and derive it where used.

## 8. Plan for the proof stage (no declared inputs; about 400–600 lines) — DONE in fix round 1

(Kept for the record. Deviations: step 1 used the asymptotic route (every `η → 0`) instead of the explicit iff `TPVSize N ↔ 2^{10} ≤ L N`; step 2 used the direct route for `μ ≥ 2^{40}` with `s = 7 + log₂μ`, `μ ≥ 2^{18}s`, `M̄ ≤ 2^{210s}`, `k̄ ≤ 2^{8+3μ}`; the files are `EG/Lib/Gamma/Col3.lean` and `EG/Lib/Gamma/Eps.lean`.)

1. **`EG/Lib/Vortex/Size.lean`: `EG.Vortex.eventually_size`** (route of `work/p2d/params.md`).
   - For `L = L N ≥ 2^{10}`, show `N ≥ L³` from `N = 2^L ≥ L³`.
   - Bound every η term by `2^{-20}` using `two_pow_mul_exp_neg_le` and `log₂L ≤ L/16`.
   - Prove `TPVSize N ↔ 2^{10} ≤ L N`, and the same for PV and VX.
   - Conclude with `L N → ∞`.
2. **`EG/Lib/Gamma/Col3.lean`: `∀ᶠ μ, col3 μ`.**
   - Either the type-(E) route of the TeX, or directly: each row reduces, via `Real.rpow` in `μ`, to `polynomial(μ) ≤ 2^{cμ}` eventually (`isLittleO_pow_exp`-style or `tendsto_pow_mul_exp_neg_atTop_nhds_zero`).
   - Row 1 needs `(λ + 6μ + 20)^{102} ≤ (2λ)^{102}` for `μ ≥ 6`.
3. **`EG/Lib/Gamma/Eps.lean`: the limits.**
   - `tendsto_epsA`, `tendsto_epsCONC`, `tendsto_FQ_logb`, `tendsto_psiPool`, `tendsto_epsX`;
   - then `tendsto_eps1`, `tendsto_eps2` by `Tendsto.add`/`const_mul`.
4. **Final theorems.** `EG/Proof/Gamma/N0.lean` gets `eventually_N0Cond`, `exists_N0`. `EG/Proof/Gamma/Sat.lean` gets `col3_eventually`, `gammaSat_items`, `gammaSat_eps`, `gammaSat`, `exists_gammaCond`. All come from the stage-1 reductions.
5. **`EGTest/GammaFull.lean`.** `example : ∃ N0 D, N0Cond N0 ∧ GammaCond N0 D := EG.exists_gammaCond`, plus `∀ N0, ∃ D, GammaCond N0 D`.

## 8a. Math findings

- **T0 (H1).** Real `N_0`: "forces `N_0 ≥ 2^{1024}`" holds only as `N_0 > 2^{1024} − 1`. It is harmless (a redundant remark).
- No T1, T2 or T3 finding. Every statement of the unit is believed true (H8).

## Fix round 1 (review `work/p2b/GAMMA.review1.md`, verdict REVISE: 1 major, 2 minor, 2 cosmetic)

All five items verified against the TeX and the code. No statement and no definition body changed.

| Item | Verdict | Action |
|---|---|---|
| M1 (missing proofs `eventually_size`, `exists_N0`, `EGTest/GammaFull.lean`) | valid (stage-1 deferral was not a reason: the lemmas are provable) | **fixed**. New `EG/Lib/Vortex/Size.lean`: `EG.Vortex.eventually_size` (asymptotic route: `L → ∞`; `L^k N^{-m} ≤ L^k/N → 0`; `N ≤ e^L`, so `N L e^{-f} ≤ L e^{-L}` when `f ≥ 2L`; `log₂L ≤ 3L/64` eventually for `η_VX`; `N ≥ L^3` for its last term). New `EG/Lib/Gamma/Col3.lean`: `col3_of_le` (every `μ ≥ 2^{40}`) and `eventually_col3`. New `EG/Lib/Gamma/Eps.lean`: `tendsto_eps1`, `tendsto_eps2` (every summand; `ε_CONC` via `log* ≤ 2 + log log` and `log* = o(log log)`). `EG/Proof/Gamma/N0.lean`: `vortexEventuallySize`, `eventually_N0Cond`, `exists_N0`. `EG/Proof/Gamma/Sat.lean`: `col3_eventually`, `gammaSat_items`, `gammaSat_eps`, `gammaSat`, `exists_gammaCond`. New `EGTest/GammaFull.lean`: `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` and `∀ N0, ∃ D, GammaCond N0 D`. |
| m1 (Γ4 list misses s7:lemUHsplit (iv)) | valid (s7.tex 1119–1120 "`θ_Q ≤ 1/4` by condition Γ4", repeated at 1190; `\deps` of UHsplit lists s1:condG4) | **fixed**: added to H4, Q4, TRIAGE §2.6 and the `RunHyp` docstring. |
| m2 (`RunHyp` docstring cuts the s7 setting) | valid (s7.tex 10–13 continues with the designation `δ` and `𝒱 = ∅`; s5.tex 9 with the stage-1 lending data) | **fixed** (docstring only; the definition body is unchanged): the module docstring of `EG/Defs/Gamma/Full.lean` quotes the full settings, and the `RunHyp` docstring says these hypotheses are not included and must be carried by the s5/s6/s7 Specs. `Full.lean` is this unit's own new Defs file and is not in `LOCK.json`. |
| c1 (Main/Gamma.lean text; Sat.lean header) | valid | Sat.lean: **fixed** (the module docstring now starts with the PROTECTED FILE line and names the proof files; statements unchanged). `EG/Defs/Main/Gamma.lean` is locked (in `LOCK.json`): **not edited**; for the integrator at the next approved edit: replace "is added here (additively) once that file exists" by "is in `EG/Defs/Main/GammaCond.lean`". |
| c2 (H1 wording on real `N_0`) | valid, no Lean change | **not an issue** for Lean (as the reviewer says). The manuscript wording could say "forces every `N ≥ N_0` to be at least `2^{1024}`" (T0, harmless; recorded in §8a). |

Checks after the fixes:
- `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0`: success.
- `scripts/check.sh` on `EG/Lib/Vortex/Size.lean`, `EG/Lib/Gamma/Col3.lean`, `EG/Lib/Gamma/Eps.lean`, `EG/Proof/Gamma/N0.lean`, `EG/Proof/Gamma/Sat.lean`, `EG/Spec/Gamma/Sat.lean`, `EGTest/GammaFull.lean`, `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors, 0 warnings, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`, modules `EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps EG.Lib.Vortex.Size EG.Lib.Gamma.Full`): 1136 constants, 0 `sorryAx`, 0 violations.

Files touched: new `EG/Lib/Vortex/Size.lean`, `EG/Lib/Gamma/Col3.lean`, `EG/Lib/Gamma/Eps.lean`, `EGTest/GammaFull.lean`; edited `EG/Proof/Gamma/N0.lean`, `EG/Proof/Gamma/Sat.lean`, `EG/Spec/Gamma/Sat.lean` (module docstring only), `EG/Defs/Gamma/Full.lean` (docstrings only), `EGTest/ProbeGAMMA.lean` (docstring only), `work/p2/TRIAGE.md` (§2.6), this note.
Root imports for the integrator: `EG.lean` should add `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.Col3`, `EG.Lib.Gamma.Eps`; `EGTest.lean` should add `EGTest.GammaFull`.

## Proof round 1 (stage 3, 2026-09-29; retry run)

State: **every node of the unit is proved, with 0 `sorry` and no declared inputs.** Fix round 1 had already written all proof files, so this round re-verified them against the current tree. No file was changed apart from this note.

| node | Lean theorem | state |
|---|---|---|
| TRIAGE §3 item 14 Defs | `EG/Defs/Gamma/Full.lean` (`Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`) | compiles, re-read against s1.tex 1519–1780 (Γ3 = s1.tex 1662 `(\log_2 D_*)^{C'} \ge 2N_0`) |
| TRIAGE §3 item 34 | `EG/Defs/Main/GammaCond.lean` (`GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D`) | compiles |
| Lib (required) | `EG.Vortex.eventually_size` (`EG/Lib/Vortex/Size.lean`) | **proved** |
| s1:defConstants (ii) | `EG.vortexEventuallySize`, `EG.eventually_N0Cond`, `EG.exists_N0` | **proved** |
| s3:lemCOLJVev (iii) | `EG.col3_eventually` (via `EG.COLTable.col3_of_le`, `μ ≥ 2^40`) | **proved** |
| s7:lemGammaSat (i), (ii), (iii) | `EG.gammaSat_items`, `EG.gammaSat_eps`, `EG.gammaSat` | **proved** |
| s7:lemGammaSat "in particular" | `EG.exists_gammaCond` | **proved** |
| non-vacuity | `EGTest/GammaFull.lean`: `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D`, `∀ N0, ∃ D, GammaCond N0 D` | compiles, 0 sorry |

What remains: nothing in this unit. There are no stuck goals.

Checks run in this round:
- `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Full`: success (2277 jobs).
- `scripts/check.sh` on `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`, modules `EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps EG.Lib.Vortex.Size EG.Lib.Gamma.Full EG.Defs.Main.GammaCond`): 1136 constants, 0 `sorryAx`, 0 violations.

Still for the integrator (unchanged from fix round 1):
- `EG.lean` should add `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.Col3`, `EG.Lib.Gamma.Eps`.
- `EGTest.lean` should add `EGTest.GammaFull`.
- In the locked `EG/Defs/Main/Gamma.lean`, the docstring still says `GammaCond` "is added here (additively) once that file exists". It should point to `EG/Defs/Main/GammaCond.lean`.

## Fix round 1 — re-run review (`work/p2b/GAMMA.review1.md`, re-run 2026-09-29, verdict APPROVE: 0 major, 2 minor, 3 cosmetic)

Every item was checked against the tree and the TeX. No Lean file was changed in this round: all five items are for the integrator, deferred to the s2 unit, or need no change.

| Item | Verification | Verdict / action |
|---|---|---|
| m1 (root files and `LOCK.json`) | Confirmed: `EG.lean` imports only `EG.Defs.Gamma.Core`, `EG.Defs.Main.Gamma`, `EG.Lib.Found.Gamma`, `EG.Lib.Vortex.Params` of this area. It does not import `EG.Defs.Gamma.Full`, `EG.Defs.Main.GammaCond`, `EG.Spec.Gamma.{N0,Sat}`, `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.{Full,Col3,Eps}` or `EG.Proof.Gamma.{N0,Sat}`. `EGTest.lean` does not import `EGTest.GammaFull` or `EGTest.ProbeGAMMA`. `LOCK.json` has 0 entries for them. | **valid, integrator action** (not fixed here: the task forbids edits to `EG.lean`, `EGTest.lean`, and `LOCK.json`, which is integrator-owned). This round built and checked every module that must be added (see the checks below), so adding the imports will not break the build. Imports to add: `EG.lean` needs `EG.Defs.Gamma.Full`, `EG.Defs.Main.GammaCond`, `EG.Spec.Gamma.N0`, `EG.Spec.Gamma.Sat`, `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.Full`, `EG.Lib.Gamma.Col3`, `EG.Lib.Gamma.Eps`, `EG.Proof.Gamma.N0`, `EG.Proof.Gamma.Sat`. `EGTest.lean` needs `EGTest.GammaFull` and `EGTest.ProbeGAMMA` (if not already tracked). At the statement freeze, lock the Defs `Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`, `GammaCond` and the Specs of `EG/Spec/Gamma/{N0,Sat}.lean`. |
| m2 (non-vacuity of `RunHyp`) | Confirmed. `RunHyp` needs `run.Valid G D` (`EG/Defs/HB/Run.lean` 257): every round `l ∈ [1,R]` needs `Round.Valid`, which is a maximal family of edge-disjoint long cycles, an `s = 0` recursion that stops exactly at `(2^{-5},0)`-expanders, and τ-runs on the large pieces. It also needs `D ≤ d_1` with `D ≥ 2^{2^{256}}`, and `RunHyp` forces `R ≥ 1`. Building such a run is exactly s2:propExists, a node of the s2 unit. | **valid, deferred** to the s2 unit: once s2:propExists is proved, add `example : ∃ N0 D V G run, RunHyp N0 D G run` to `EGTest/GammaFull.lean` (or to an s2 test file). This cannot be done here without a `sorry` (the unit has no sorry at all) and without redoing s2. Until then the non-vacuity of `Gamma1 ∧ Gamma3 ∧ N0Cond` alone is covered by `EGTest/GammaFull.lean` (`GammaCond` implies `Gamma1 ∧ Gamma3`). |
| c1 (docstring of the locked `EG/Defs/Main/Gamma.lean`) | Confirmed (line 20: "…here (additively) once that file exists"). | **valid, integrator action**. The file is locked and was not edited. At the next approved edit, replace the text with "`GammaCond` is in `EG/Defs/Main/GammaCond.lean`". |
| c2 (Γ2(a) kept as a field of `GammaCond`) | `Gamma1core.gamma2a` derives it. s1.tex condGamma says (a)–(c) are "listed separately for traceability", and defConstants (iii) lists Γ1–Γ4. | **not an issue**. The field matches the manuscript's list. It is redundant but harmless, and removing it would change a definition for no gain. |
| c3 (s1.tex 1525 and 1764: "`L ≥ 2^{10}` already forces `N_0 ≥ 2^{1024}`") | Confirmed. `N_0` is real, and the size conditions quantify over natural `N ≥ N_0`, so the exact consequence is `N_0 > 2^{1024} − 1`. `N0Cond` states `2^40 ≤ N0` explicitly, and no proof uses the remark. | **not an issue for Lean** (T0, recorded in §8a). Optional manuscript wording: "forces every `N ≥ N_0` to be at least `2^{1024}`". |

Checks in this round:
- `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Full EG.Defs.Main.GammaCond EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat`: success (2277 jobs).
- `scripts/check.sh` on `EGTest/GammaFull.lean` and on `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`, modules `EG.Proof.Gamma.Sat`, `EG.Proof.Gamma.N0`, `EG.Lib.Vortex.Size`, `EG.Defs.Main.GammaCond`): 1136 constants, 0 `sorryAx`, 0 violations.

Files touched in this round: this note only.

## Proof round 1 — re-verification (stage 3, 2026-09-29, second retry)

No Lean file changed. Every node is still proved with 0 `sorry`, and the unit still has no declared inputs.
- `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Full EG.Defs.Main.GammaCond EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat EG.Lib.Vortex.Size`: success (2277 jobs).
- `scripts/check.sh` on `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`; modules `EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Vortex.Size EG.Lib.Gamma.Full EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps EG.Defs.Main.GammaCond`): 1136 constants, 0 `sorryAx`, 0 violations.

Nothing remains and no goal is stuck. The integrator actions (root imports, the `LOCK.json` entries, the docstring of the locked `Main/Gamma.lean`) are unchanged from the section above.

## Fix round 1 — re-verification (2026-09-30, same re-run review: 2 minor, 3 cosmetic)

The review items are the same five as in the section "Fix round 1 — re-run review" above. Each was checked again against the current tree, and the verdicts there still hold:
- m1 (root imports, `LOCK.json`): still **valid, integrator action**. `EG.lean` and `EGTest.lean` still lack the imports listed above, and `LOCK.json` still has no entries for the new Defs/Specs. This unit may not edit these files. All modules to be added build.
- m2 (`RunHyp` non-vacuity): still **valid, deferred to the s2 unit**, which will need s2:propExists. It cannot be done here without a `sorry`.
- c1 (docstring of the locked `EG/Defs/Main/Gamma.lean`, line 20): still **valid, integrator action**. The file is locked and was not edited.
- c2 (redundant `Gamma2a` field): **not an issue**. It matches the list in s1 defConstants (iii) and condGamma.
- c3 (s1.tex "forces `N_0 ≥ 2^{1024}`"): **not an issue for Lean**. It is a T0 manuscript wording remark, with the optional rewording recorded above.

Checks: `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Full EG.Defs.Main.GammaCond EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat EG.Lib.Vortex.Size` succeeded (2277 jobs). `scripts/check.sh` returned rc=0 with 0 sorry on `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`. Lint reported 0 findings. The axiom scan covered 1136 constants, with 0 `sorryAx` and 0 violations. No Lean file was changed.

## Fix round 2 (review `work/p2b/GAMMA.review2.md`, verdict APPROVE: 0 major, 2 minor, 3 cosmetic)

Each item was verified against the current tree and the TeX. No statement and no definition body changed.

| Item | Verification | Verdict / action |
|---|---|---|
| m1 (root files, `LOCK.json`) | Confirmed again: of this unit, `EG.lean` imports only `EG.Defs.Gamma.Core`, `EG.Defs.Main.Gamma`, `EG.Lib.Found.Gamma`; `EGTest.lean` imports neither `EGTest.GammaFull` nor `EGTest.ProbeGAMMA`; `LOCK.json` has 0 entries for `Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`, `GammaCond` or the Specs of `EG/Spec/Gamma/{N0,Sat}.lean`. | **valid, integrator action** (the task forbids edits to the root files, and `LOCK.json` is integrator-owned). All modules to add build (checks below). `EG.lean` should add `EG.Defs.Gamma.Full`, `EG.Defs.Main.GammaCond`, `EG.Spec.Gamma.N0`, `EG.Spec.Gamma.Sat`, `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.Full`, `EG.Lib.Gamma.Col3`, `EG.Lib.Gamma.Eps`, `EG.Proof.Gamma.N0`, `EG.Proof.Gamma.Sat`; `EGTest.lean` should add `EGTest.GammaFull`, `EGTest.ProbeGAMMA`. At the freeze, lock the six Defs and the 8 Specs. |
| m2 (`RunHyp` non-vacuity) | Confirmed: needs a graph with a valid `HB^tp` run and `d_1 ≥ D_* ≥ 2^{2^{256}}`, i.e. s2:propExists. | **valid, deferred to the s2 unit** (cannot be done here without a `sorry`). Once s2:propExists is proved, add `example : ∃ N0 D V G run, RunHyp N0 D G run` to `EGTest/GammaFull.lean` or an s2 test file. |
| c1 (docstring of the locked `EG/Defs/Main/Gamma.lean`, line 20) | Confirmed (lines 18–20). | **valid, integrator action**; the file is locked and was not edited. Replace with "`GammaCond` is in `EG/Defs/Main/GammaCond.lean`" at the next approved edit. |
| c2 (`Gamma3` satisfiable at negative `D`) | Confirmed: `Real.logb 2 (-(2^300)) = 300` and `300^{103} ≥ 2^{41}`. Every use in the unit (`GammaCond`, `RunHyp`) is conjoined with `Gamma1 D` (`2 < D`). | **fixed (docstring only)**: the `Gamma3` docstring in `EG/Defs/Gamma/Full.lean` (this unit's own file, not in `LOCK.json`) now notes the junk range and that a Spec taking `Gamma3` alone must add `2 < D` or `Gamma1 D`. Definition body unchanged. |
| c3 (s1.tex 1525/1764, "forces `N_0 ≥ 2^{1024}`") | Confirmed: for real `N_0` and natural `N ≥ N_0` the exact consequence is `N_0 > 2^{1024} − 1` (`n0Cond_forces`). No proof uses the remark. | **not an issue for Lean** (T0 manuscript wording; optional rewording "forces every `N ≥ N_0` to be at least `2^{1024}`", recorded in §8a). |

Checks after the fix:
- `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Full EG.Defs.Main.GammaCond EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat EG.Lib.Vortex.Size`: success (2277 jobs).
- `scripts/check.sh` on `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings. `grep sorry` on the unit's files: only the docstring phrase "No `sorry`".

Files touched: `EG/Defs/Gamma/Full.lean` (docstring of `Gamma3` only), this note.

## Proof round 1 — re-verification (stage 3, 2026-09-30, third retry)

No Lean file changed; the only working-tree change to Lean since the last commit is the docstring of `Gamma3` from fix round 2 (body unchanged). Every node is still proved with 0 `sorry`; no declared inputs; nothing remains, no stuck goal.
- `lake build EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Gamma.Full EG.Defs.Main.GammaCond EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat EG.Lib.Vortex.Size EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps`: success (2277 jobs).
- `scripts/check.sh` on `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`; `EG.Proof.Gamma.Sat EG.Proof.Gamma.N0 EG.Lib.Vortex.Size EG.Lib.Gamma.Full EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps EG.Defs.Main.GammaCond`): 1136 constants, 0 `sorryAx`, 0 violations.
Integrator actions unchanged (root imports, `LOCK.json` entries, docstring of the locked `Main/Gamma.lean`).
