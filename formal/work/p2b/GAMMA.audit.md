# GAMMA: independent audit (Defs item 14 `EG/Defs/Gamma/Full.lean` + `GammaCond`, `EG.Vortex.eventually_size`)

Auditor: independent reader, 2026-09-30 (re-run after fix round 2; replaces the audit of the same
name in git history at `fc84210`). No Lean file in the repository was edited; the only file written
is this note. My own checks compile from the scratchpad (`GammaAudit3.lean`, `lake env lean`,
`LEAN_NUM_THREADS=2`: rc=0, 0 errors). The proof being formalized is a CANDIDATE proof of the
Erdős–Gallai cycle decomposition conjecture, reviewed only by AI; nothing here says the conjecture is
solved.

Inputs read: `work/p2b/GAMMA.md` (all rounds through "Proof round 1 — re-verification, third
retry"), `GAMMA.review1.md` (re-run version in the tree, committed `41e8a4e`; the REVISE version is
at `3278dd4`), `GAMMA.review2.md` (2026-09-30 version in the working tree; the 2026-09-29 version is
at `fc84210`); every Lean file GAMMA.md lists: `EG/Defs/Gamma/Full.lean`, `EG/Defs/Main/GammaCond.lean`,
`EG/Spec/Gamma/{N0,Sat}.lean`, `EG/Lib/Gamma/{Full,Col3,Eps}.lean`, `EG/Lib/Vortex/Size.lean`,
`EG/Proof/Gamma/{N0,Sat}.lean`, `EGTest/{ProbeGAMMA,GammaFull}.lean`; the locked Defs they use
(`EG/Defs/Gamma/Core.lean`, `EG/Defs/Main/Gamma.lean`, `EG/Defs/Vortex.lean` 55–116,
`EG/Defs/Lend/COLTable.lean`, `EG/Defs/Quot/Constants.lean` (`epsX`, `FQ`, `eps2`, `eps1`),
`EG/Defs/Chain/Constants.lean` (`epsCONC`, `epsK`), `EG/Defs/Light/Constants.lean` (`epsU`),
`EG/Defs/HB/Run.lean` (`graph`, `d`, `Valid`, `epsA`, `psiPool`), `EG/Defs/HB/Round.lean` (`d`));
`EG/Lib/Found/Gamma.lean`, `EG/Lib/Vortex/Params.lean` (`cond_iii`, `L_pow`); `work/p2/TRIAGE.md`
§2.4, §2.6, §3 items 14 and 34; `work/p2d/params.md` D-VX-1, D-VX-2; `work/p2d/quot.md` open item 1.
TeX (v6.1): `s1.tex` 1519–1780 (defConstants, remOrder, condGamma, tabOrder); `s3.tex` 1137–1200
(tabCOLJV), 1357–1446 (lemCOLJVev and proof); `s4.tex` 145–156, 178–186, 203–210, 434–441, 460–466,
657–664, 675–682 and every line mentioning `N_0` / "size condition"; `s5.tex` 5–16, 395–412;
`s7.tex` 5–16, 1047–1053, 1108–1120, 1280–1286, 1440–1515; `s2.tex` 1168–1173.

## Verdict: APPROVE (unit complete; one T0 finding, harmless; nothing above T0)

| audit item | result |
|---|---|
| (1) sorry frontier = declared inputs | **yes**: declared inputs = ∅ and frontier = ∅. Axiom scan `--prefix EG --cross-check` over the unit's 10 modules: "inspected 1136 constants under [EG]; 0 use sorryAx; 0 meta-scan hits; 0 violations". `#print axioms` on all 10 final theorems: `[propext, Classical.choice, Quot.sound]`. |
| (2) Specs unchanged after review | **yes**: the eight `def …Statement` bodies and the six definition bodies are character-for-character those quoted in review 1 §1 and review 2 §1. `EG/Spec/Gamma/N0.lean` and `EG/Defs/Main/GammaCond.lean` are unchanged since `1e0e84a` (before the first review commit `3278dd4`); `git diff 3278dd4 HEAD` on `EG/Spec/Gamma/Sat.lean` and `EG/Defs/Gamma/Full.lean` is 3 + 13 lines, all inside `/-! -/` / `/-- -/` docstrings; the only working-tree Lean change of the unit is the `Gamma3` docstring (fix round 2, c2), body unchanged. |
| (3) hidden weakening | **none**: the final theorems are closed terms re-elaborated against the *unfolded* Spec `Prop`s; the definitions unfold by `Iff.rfl` to the reviewed shapes; one *strengthening* (`GammaSatStatement` for every real `N0`, and `¬ GammaCond N0 16` for every `N0` shows the dropped hypothesis does not trivialise it); junk ranges of the bare `Gamma1f`/`Gamma3` recorded, none used bare. |
| (4) refutation target covered | **yes**: `EG.Vortex.eventually_size` is proved with the exact statement of TRIAGE §3 item 14 line 289; the Defs shapes are literally TRIAGE §2.4/§2.6; `EG.exists_N0`, `EG.col3_eventually`, `EG.gammaSat_{items,eps}`, `EG.gammaSat`, `EG.exists_gammaCond` proved; `EGTest/GammaFull.lean` compiles (rc=0, 0 sorry). |
| (5) math findings | one T0 (real `N_0` in a redundant parenthetical), confirmed by my own Lean proof of the exact consequence `N0Cond N0 → 2^{1024} − 1 < N0`; no T1/T2/T3/suspect item reported by anyone or found by me. |

## 1. Sorry frontier and hygiene (re-run by me)

- No other `lake`/`lean` process was running when I started. `lake build EG.Proof.Gamma.Sat
  EG.Proof.Gamma.N0 EG.Lib.Gamma.Full EG.Defs.Main.GammaCond EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat
  EG.Lib.Vortex.Size EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps`: "Build completed successfully (2277 jobs)",
  rc=0.
- `lake env lean --run scripts/Axioms.lean --prefix EG --cross-check` over `EG.Proof.Gamma.Sat
  EG.Proof.Gamma.N0 EG.Lib.Vortex.Size EG.Lib.Gamma.Full EG.Lib.Gamma.Col3 EG.Lib.Gamma.Eps
  EG.Defs.Main.GammaCond EG.Defs.Gamma.Full EG.Spec.Gamma.N0 EG.Spec.Gamma.Sat`: 1136 constants,
  0 `sorryAx`, 0 meta-scan hits, 0 violations. This is the transitive `EG` closure, so the previously
  proved Lib facts the unit uses (`eventually_gamma1Items`, `gamma1Items_of_le`, `loglog_mono`,
  `Light.tendsto_epsU`, `Light.tendsto_epsChain`, `logStar_isLittleO_loglog`,
  `logStar_le_two_add_loglog`, `TPVSize.cond_iii` etc.) carry no stub either.
- `#print axioms` (scratch) on `EG.exists_gammaCond`, `EG.exists_N0`, `EG.Vortex.eventually_size`,
  `EG.gammaSat`, `EG.gammaSat_items`, `EG.gammaSat_eps`, `EG.col3_eventually`, `EG.eventually_N0Cond`,
  `EG.vortexEventuallySize`, `EG.COLTable.col3_of_le`: each `[propext, Classical.choice, Quot.sound]`.
- `scripts/check.sh EGTest/GammaFull.lean 1200` and `EGTest/ProbeGAMMA.lean`: rc=0, errors=0,
  sorry-warnings=0.
- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- `grep` for `sorry`, `DECLARED INPUT`, `axiom`, `admit` over the unit's 12 files: only the docstring
  phrase "No `sorry`" (6 hits). Declared inputs: none (GAMMA.md §3). Frontier ∅ = declared set ∅.
- Module headers: `module` + `public import`; `@[expose] public section` in the two Defs and two Spec
  files; `public section` in Lib and Proof; the two tests are non-module files. Unit Lean files total
  1162 lines, none near the 1500 limit.

## 2. No Spec changed after its review

- Commit order (dates): `1e0e84a` (21:05) < `3a26761` (~21:20) < `3278dd4` (21:24, first reviews)
  < `41e8a4e` (22:27) < `fc84210` (23:17) < HEAD `ed552cf`.
- `EG/Spec/Gamma/N0.lean` and `EG/Defs/Main/GammaCond.lean`: single commit `1e0e84a`; `git diff
  1e0e84a HEAD` on them is empty.
- `EG/Spec/Gamma/Sat.lean`: changed at `3a26761` (before the first review) and `41e8a4e` (after);
  `git diff 3278dd4 HEAD` shows 3 changed lines, all in the module docstring (PROTECTED FILE line,
  proof-file names). `EG/Defs/Gamma/Full.lean`: 13 changed lines since `3278dd4`, all inside the module
  docstring and the `RunHyp` docstring (s7-setting quotation, Γ4 user list). No `def` line changed.
- Working tree (`git status`): the only Lean change of the unit is `EG/Defs/Gamma/Full.lean`, a
  4-line addition to the `Gamma3` docstring (fix round 2 c2, junk-range note); `def Gamma3 … :=
  2 * N0 ≤ logb 2 D ^ Cp` is unchanged. Other working-tree changes are `work/p2b/*.md` only.
- Text comparison: the 8 statement bodies and 6 definition bodies in the tree are those quoted in
  review 1 §1, review 2 §1 and GAMMA.md §5, and my scratch re-derives each by `Iff.rfl`.
- `scripts/lock.py check`: 865 locked constants, 153 locked files, **1 violation: `CONVENTIONS.md`**
  (a locked non-Lean file changed by another probe's T0 row; not this unit). Every locked `EG/Defs/**`
  file the unit depends on is intact. The unit's 6 Defs and 8 Specs are reported `PENDING: unlocked`
  (integrator locks them at the freeze; §6 A1).

## 3. Back-translation and hidden-weakening check (my own)

Conventions: `log₂ = Real.logb 2` (s1.tex 730: all logarithms base 2); `N : ℕ` (vertex count,
D-VX-1); `N0, D, μ : ℝ`; `Cp = 103`, `Aexp = 105` (`rfl`, scratch).

### Definitions

| Lean | plain mathematics | TeX | audit |
|---|---|---|---|
| `Gamma1f D := ∀ μ, log₂log₂D ≤ μ → COLTable.col3 μ` | all 18 column-3 inequalities of rows 1–13 at `λ = 2^μ`, every real `μ ≥ log₂log₂D` | Γ1(f) (s1.tex 1613–1619) under "for every real `μ ≥ log₂log₂D_*`, with `λ := 2^μ`" | faithful. I compared all 13 `row` bodies with the table at s3.tex 1147–1163: row 1 both parts strict (`257(λ+6μ+20)^{102} < λ^{205/2}`, `2^{111} < λ^{1/2}`); rows 2–7, 9–13 as printed (`42.1 = 421/10`, `64.4 = 322/5`, `3.3 = 33/10`, `1.6 = 8/5`); row 8's five parts incl. `64((2λ)^6+1) ≤ λ^{99}`; `M̄ = (Aμ)^{2A}`, `k̄ = 192λ³ + (4/3)M̄²` as in the caption. `col3` quantifies `1 ≤ i ≤ 13` only, so the `True` junk rows do not enter. Non-strict `≤` on the ray as in the TeX. |
| `Gamma1 D := Gamma1core D ∧ Gamma1f D` | `D > 2`, and (a)–(f) on the ray | Γ1 | faithful; `2 < D` and (a)–(e) are in the locked `Gamma1core`, re-read against s1.tex 1602–1612 (`2^8`, `2^{14}Aμ³ ≤ 2^μ`, `2A log₂(Aμ) ≤ 1.6μ`, `2log₂μ + 8 ≤ μ`, `2^{240}(Aμ)^{46A} ≤ (2^μ)^{36}`). |
| `N0Cond N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → TPVSize N ∧ PVSize N ∧ VXSize N` | `N_0 ≥ 2^{40}`, and every natural `N ≥ N_0` satisfies the size conditions of the TPV, PV, VX⁺ proofs | defConstants (ii); s4.tex 151–153 "hold for every `N ≥ N_0`" | faithful. Each size predicate lists (i) `2^{10} ≤ L`, (ii) `L³ ≤ N`, (iv) `η ≤ 1/100` (s4.tex 206, 463, 678); (iii) `4β ≤ L` is "a consequence of (i)" in the TeX itself and is derived in Lib (`TPVSize.cond_iii`, `PVSize.cond_iii`, `VXSize.cond_iii`; D-VX-2), so nothing is dropped. The three `η` match s4.tex 183, 439, 662 term by term (`2LN^{-5} + 2^{96}L^{31}N^{-3} + NLe^{-3L^4/8}`; `2^{95}L^{31}N^{-3} + NLe^{-L^4/16}`; `2LN^{-5} + 2^{95}L^{28}N^{-3} + NLe^{-3L²/(32log₂L)} + Le^{-N/(5000L)}`; my scratch spells `TPVSize` out by `Iff.rfl`). I grepped s1–s7 for every `\Nzero\ge` / `\ge\Nzero`: besides `2^{40}`, the `2^{1024}` remark and the size thresholds, every hit is a consequence (`P_R/2 ≥ N_0` by Γ3) or a hypothesis (`n ≥ N_0`), never a requirement on `N_0`. |
| `Gamma3 N0 D := 2*N0 ≤ log₂D ^ Cp` | `(log₂D)^{103} ≥ 2N_0` | Γ3 (s1.tex 1662) | faithful, non-strict as in TeX, natural-number power (`Iff.rfl` against `^ (103 : ℕ)`). |
| `RunHyp N0 D G run := Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧ N0 ≤ G.card ∧ D ≤ run.d G 1 ∧ run.Valid G D` | Γ1, Γ3, admissible `N_0`, `n ≥ N_0`, `d_1 ≥ D_*`, a valid run for `D_*`; Γ4 not included | s5.tex 9, s7.tex 10–13; TRIAGE §2.6 (identical text) | faithful to the binding design. Scratch: `run.graph G 1 = G` (round 0 is not a round) and `run.d G 1 = 2|E(G)|/|V(G)|` by `simp [HB.Run.graph, IsRound, Round.d]`, so this is the manuscript's `d_1` (s2:defHBtp (R0)); `Valid` (Run.lean 257) contains no Γ; `RunHyp → 1 ≤ run.R` reproduced from `Valid.2 : d_{R+1} < D` and `D ≤ d_1`. The docstring says which parts of the settings are *not* in `RunHyp` (Γ4, stage-1 data, designation, `𝒱 = ∅`). |
| `GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` | Γ1, `D ≥ 2^{117}`, Γ3, `ε_1(D) ≤ 6 ∧ ε_2(D) ≤ 1/4` | defConstants (iii) "Γ1–Γ4" | faithful. Γ2(b),(c) quantify over runs / failure probabilities; the TeX says they are implied by Γ1 and "listed separately for traceability" (s1.tex 1652–1657): correctly not fields (TRIAGE §2.4). The locked `Gamma4` uses `Quot.eps1/eps2`; I re-read them against s7.tex 1283 (`ε_1 = ε_K + 169ε_A + 252/D + 1.5ε_CONC + 3ε_X + 9/D`), 1116 (`ε_2 = 12ε_X + 4(3ε_A + 60/D + 2F(log₂D))`), 1049–1051 (`ε_X = ε_U + 10.3/D + 2.1(6log₂D+12)/D`), 1111 (`F(x) = (3184 + 30400log₂x)x^{-90.2}`), Γ4 bullet (`ε_CONC`, matches `Chain.epsCONC`), s2.tex 1170 (`ε_A = 31ε/(C' log log D)`): all match; the Γ4 bullet arithmetic is consistent (`252 + 9 + 3·10.3 = 291.9`, `12·10.3 + 4·60 = 363.6`, `4·3 = 12`, `4·2F = 8F`). |

### Statements

| Lean | plain | TeX | audit |
|---|---|---|---|
| `VortexEventuallySizeStatement := ∀ᶠ N : ℕ in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` | `∃ N_1 ∀ N ≥ N_1` (natural): all size conditions (scratch: `eventually_atTop` form) | (ii) "an explicit inequality in `N`, which holds for all sufficiently large `N`"; s4.tex 153 | faithful; identical to TRIAGE §3 item 14 line 289 |
| `N0EventuallyStatement := ∀ᶠ N0 : ℝ in atTop, N0Cond N0` | every large real `N_0` is admissible | (ii) "eventuality … for every sufficiently large value of `N_0`" | faithful |
| `N0ExistsStatement := ∃ N0 : ℝ, N0Cond N0` | | (ii) "So such an `N_0` exists" | faithful |
| `Col3EventuallyStatement := ∀ᶠ μ in atTop, col3 μ` | | COLJVev (iii), per row | equivalent (13 rows; finite conjunction of eventualities) |
| `GammaSatItemsStatement` | eventually `(a)–(e) ∧ (f)`; `∃ μ₁ ≥ 1`: all items for `μ ≥ μ₁`, and `Γ1 D` for every `D > 2` with `log₂log₂D ≥ μ₁` (same `μ₁`) | GammaSat (i) (s7.tex 1450–1453) | faithful clause by clause: `1 ≤ μ₁`, `2 < D` strict, `≥` non-strict, `μ₁` shared |
| `GammaSatEpsStatement := Tendsto eps1 atTop (𝓝 0) ∧ Tendsto eps2 atTop (𝓝 0)` | | GammaSat (ii) | faithful |
| `GammaSatStatement := ∀ N0 : ℝ, ∀ᶠ D in atTop, GammaCond N0 D` | for every real `N_0`, all large `D` satisfy Γ1–Γ4 (scratch: `∀ N0, ∃ D0, ∀ D ≥ D0, GammaCond N0 D`) | GammaSat (iii) with "`N_0` as in (ii)" | **strengthening** (no `N0Cond N0` hypothesis); it implies the TeX form. The TeX proof uses `N_0` only in the threshold `2^{(2N_0)^{1/C'}}`; the Lean reduction `gammaSat_of_items_eps` uses `(log₂D)^{103} → ∞` and no property of `N0`. Scratch: `¬ GammaCond N0 16` for every real `N0` (Γ1(a) fails at `μ = 2`), so a negative or tiny `N0` does not trivialise it. |
| `GammaCondExistsStatement := ∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` | admissible `N_0` and `D_*` exist jointly | "In particular … exists" + "such an `N_0` exists" | faithful; scratch: `GammaCond N0 D → 2 < D ∧ 2^{117} ≤ D` and `N0Cond N0 → 0 < N0`, so it cannot be met in a junk region |

### Weakening hunt (negative results)

- The ten final theorems are closed terms; my scratch re-elaborates each against the *unfolded* Spec
  `Prop` (`example : ∀ᶠ N : ℕ in atTop, … := Vortex.eventually_size`, etc.). No auxiliary hypothesis,
  extra parameter, `Fact`, `variable` binder or local instance.
- The reductions in `EG/Proof/Gamma/*.lean` take hypotheses only of the form `Spec.XStatement`, and
  each such `X` is proved in the same files; the Lib proofs (`Size.lean`, `Col3.lean`, `Eps.lean`)
  assume nothing beyond Mathlib and the previously proved `EG` Lib lemmas listed in §1.
- Cross-unit uses (grep over `EG/`, `EGTest/`, `EGCheck/`): `RunHyp` in `EG/Spec/Chain/JSLC.lean`
  (line 112) and `EG/Proof/Chain/JSLCCtx.lean`; `N0Cond` mentioned in `EG/Defs/Probe/P4A/PVHyp.lean`
  (docstring); `RunHyp` mentioned in `EGTest/ProbeP2J.lean` (docstring). No use of the bare `Gamma1f`
  or `Gamma3` outside the unit.
- Junk ranges (not weakenings; recorded so later Specs do not trip on them): `Real.logb` is evaluated
  on `|x|`, so `Gamma3 N0 D` holds at negative `D` (scratch: `Gamma3 1 (-4)`), and `Gamma1f D` alone
  is as easy as `Gamma1f |D|`. Every use pairs them with `Gamma1core` (`2 < D`) inside
  `Gamma1`/`GammaCond`/`RunHyp`; `Gamma1f.mono` takes `2 < D` explicitly; the `Gamma3` docstring
  (fix round 2) now says so.
- Negative tests re-run (`EGTest/ProbeGAMMA.lean`, rc=0): `¬Gamma1 2`, `¬Gamma1 16`, `¬Gamma1f 2`
  (row 1 fails at `μ = 0`), `¬N0Cond 0`, `¬N0Cond (2^40)`, `n0Cond_forces : N0Cond N0 → 2^{1023} < N0`,
  `¬Gamma3 (2^900) (2^256)`, `¬Gamma2a 4`, `¬Gamma4 4` (`ε_1(4) > 6`), `¬GammaCond N0 4`. Positive:
  `Gamma3 (2^40) (2^256)`, `Gamma2a (2^117)`, `col3 μ` for `μ ≥ 2^40`. Each condition is genuine and
  they are jointly satisfiable (`EGTest/GammaFull.lean`).
- Proof routes differ from the TeX and from the route sketched in TRIAGE/params.md (asymptotic
  `η → 0` instead of explicit `2^{-20}` bounds; a direct power-of-two comparison for `μ ≥ 2^{40}`
  instead of the type-(E) route; `log* ≤ 2 + log log` for `ε_CONC`). They prove the same statements,
  a legitimate proof choice. I read the routes for sanity: `Col3.lean` uses `s = 7 + log₂μ ≥ 47`,
  `2^{18}s ≤ μ`, `Aμ ≤ 2^s` (`105 ≤ 2^7`), `M̄^n ≤ 2^{210sn}`, `M̄² ≤ 2^{3μ}`, `k̄ ≤ 2^{8+3μ}`,
  row 1 via `λ + 6μ + 20 ≤ 2^{1+μ}` and `257 < 2^9`, `111 ≤ μ/2`; row 13 is `Gamma1e` via
  `gamma1Items_of_le` (`μ ≥ 2^{20}`). `Size.lean`: `N ≤ e^L` (from `log 2 < 1`), `L^k N^{-m} ≤
  L^k/N → 0`, `NLe^{-f} ≤ Le^{-L}` when `f ≥ 2L` (`3L^4/8 ≥ 2L` for `L ≥ 2`, `L^4/16 ≥ 2L` for `L ≥ 4`,
  `3L²/(32log₂L) ≥ 2L` once `log₂L ≤ 3L/64`), and `Le^{-N/(5000L)} ≤ Le^{-L}` from `N ≥ L³`,
  `L ≥ 5000`. `Eps.lean`: every summand of `ε_1`, `ε_2` tends to 0. All arithmetic is kernel-checked;
  nothing is assumed.

## 4. Refutation target

The unit's targets (task text: "Defs item 14: `EG/Defs/Gamma/Full.lean` (+ `GammaCond`) and
`EG.Vortex.eventually_size`"; TRIAGE §3 item 14) are the definitions of the standing constants and the
non-vacuity of the standing hypotheses of the main theorem, with the required Lib lemma:

| target | proved statement | status |
|---|---|---|
| `EG.Vortex.eventually_size` (TRIAGE: "Required Lib lemma (not optional)") | `∀ᶠ N : ℕ in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` — the exact TRIAGE line-289 statement | proved, standard axioms |
| Defs item 14 shapes (`Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`) and item 34 (`GammaCond`) | bodies identical to TRIAGE §2.4, §2.6 | compile; faithful (§3) |
| `N_0` exists (s1:defConstants (ii)) | `EG.exists_N0`, `EG.eventually_N0Cond` | proved |
| Γ1(f) satisfiable / COLJVev (iii) | `EG.col3_eventually`; `EG.COLTable.col3_of_le` (`μ ≥ 2^{40}`) | proved |
| s7:lemGammaSat (i), (ii), (iii) | `EG.gammaSat_items`, `EG.gammaSat_eps`, `EG.gammaSat` | proved |
| `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` | `EG.exists_gammaCond`; `EGTest/GammaFull.lean` | proved / compiles |

Correctly *not* claimed: the non-vacuity of `RunHyp` (needs a graph with a valid `HB^tp` run and
`d_1 ≥ D_* ≥ 2^{2^{256}}`: s2:propExists, another unit; reviews m2); COLJVev (i), (ii) (the type-(E)
route; not a node here, GAMMA.md Q3); the explicit thresholds `TPVSize N ↔ 2^{10} ≤ L N` of params.md
(a suggested route, not a required statement; nothing downstream uses it — §6 A5).

## 5. Classification of the math findings

Only one finding was reported (author H1/§8a; review 1 c3/§6; review 2 c3/§6). I found none other.

**F1 — T0 (encoding: real `N_0`), harmless. Confirmed.**
- Claim (s1.tex 1525 and tabOrder row 2 at 1764 — `grep 2^{1024}` finds exactly these two places):
  "size condition (i), `L ≥ 2^{10}`, already forces `N_0 ≥ 2^{1024}`".
- My evidence: `N0Cond N0` requires (i) for every natural `N ≥ N0`, i.e. `N ≥ 2^{1024}` for every
  such `N`; equivalently `⌈N_0⌉ ≥ 2^{1024}`, i.e. `N_0 > 2^{1024} − 1`. My scratch proves exactly
  this, `N0Cond N0 → (2 : ℝ)^{1024} − 1 < N0` (via `L (2^{1024} − 1) < 1024`), which is sharper than
  the tree's `n0Cond_forces` (`2^{1023} < N0`). For an integer `N_0` this is the TeX's
  `N_0 ≥ 2^{1024}`; for a real `N_0` (the TeX never says `N_0` is an integer; Lean has `N0 : ℝ`) the
  literal claim fails at `N_0 = 2^{1024} − 1/2` as soon as `N0Cond (2^{1024})` holds (expected from
  `eventually_N0Cond`; only `N = 2^{1024}` is checked pointwise in `EGTest/Params`). The
  parenthetical is labelled "redundant", and no proof uses it.
- Class: T0 (PLAN §7, encoding). Lean action: none. Optional wording: "forces every `N ≥ N_0` to be
  at least `2^{1024}`" or "`⌈N_0⌉ ≥ 2^{1024}`".

Arithmetic re-checked on paper (agrees with both reviewers): GammaSat (i): for `μ ≥ 1`,
`0 ≤ log₂μ ≤ log₂(Aμ)`, so the type-(E) forms of (b), (d) imply the items; (e) after `log₂` is
`36μ ≥ 240 + 46A log₂(Aμ)`; (iii): `D_1 = 2^{2^{μ_1}} ≥ 4 > 2` from `μ_1 ≥ 1`, and the threshold
`2^{(2N_0)^{1/C'}}` needs `N_0 > 0` (given by `N_0 ≥ 2^{40}`; Lean does not need it). COLJVev (i):
`v_0` is the larger root of `av² − 2cv − (b + c log₂A)`, and `log₂μ = 2log₂v < 2v` for `v ≥ 1`;
(ii) row 1: `φ ≥ 0.5μ − 111`, crude form `μ > 222`. Every formal statement of the unit is in any case
proved with standard axioms, so its truth does not rest on these paper checks.

No T1, T2, T3 or suspect item.

## 6. Observations for the integrator (not findings against the unit)

- **A1 (integration gap, unchanged).** `EG.lean` imports `EG.Defs.Gamma.Core`, `EG.Defs.Main.Gamma`,
  `EG.Defs.Vortex`, `EG.Lib.Found.Gamma`, `EG.Lib.Vortex.Params` but none of `EG.Defs.Gamma.Full`,
  `EG.Defs.Main.GammaCond`, `EG.Spec.Gamma.{N0,Sat}`, `EG.Lib.Gamma.{Full,Col3,Eps}`,
  `EG.Lib.Vortex.Size`, `EG.Proof.Gamma.{N0,Sat}`; `EGTest.lean` imports neither `EGTest.GammaFull`
  nor `EGTest.ProbeGAMMA`; `lock.py check` lists the unit's 6 Defs constants, 8 Spec constants and 4
  files as `PENDING: unlocked`. Until added, CI does not compile the unit and its statements are not
  frozen. The build in §1 shows the additions are safe.
- **A2 (outside this unit).** `scripts/lock.py check` reports the locked file `CONVENTIONS.md` as
  changed (its only violation); re-hash after approval of that T0 row.
- **A3 (cosmetic, locked file).** `EG/Defs/Main/Gamma.lean` 18–20 still says `GammaCond` "is added
  here (additively) once that file exists"; it is in `EG/Defs/Main/GammaCond.lean`.
- **A4 (rule for later Specs).** `Gamma1f` and `Gamma3` alone are junk-permissive (§3); Specs must use
  them through `Gamma1`/`GammaCond`/`RunHyp` or add `2 < D`. Γ4 is not in `RunHyp` and must be added
  by thmJVps, `C0_le`, thmMainProof, s7:lemUHsplit (iv) (TRIAGE §2.6); `EG/Spec/Chain/JSLC.lean`
  already takes `RunHyp` and its reviewers should confirm it needs no Γ4.
- **A5 (not delivered, not required).** The explicit characterisation `TPVSize N ↔ 2^{10} ≤ L N` (and
  PV, VX) sketched in params.md/TRIAGE line 289 as a *route* is not proved; the unit proves the
  required eventuality directly. If a later unit ever needs a concrete admissible `N_0` (e.g.
  `N0Cond (2^{1024})`), it will have to prove it separately; nothing in the tree needs it now.
