# GAMMA: clean-room review, round 2 (Specs, new Defs, `eventually_size`, tests) — 2026-09-30

Reviewer: clean-room Spec reviewer, round 2. No Lean file in the repository was edited. The scratch
checks are in the session scratchpad (`GammaRev2.lean`, outside the repo); they compile against the
built oleans with `lake env lean` (no `lake build` was started: other agents were building). The
proof being formalized is a CANDIDATE proof that has been reviewed only by AI. Nothing here says
the conjecture is solved.

**Verdict: APPROVE.** No major issue. 2 minor items (both carried over from round 1, both still
open and both outside this unit's authority: integrator / s2 unit) and 3 cosmetic items. No
statement and no definition needs a change.

Scope (as in `work/p2b/GAMMA.md` §1):
- Defs: `EG/Defs/Gamma/Full.lean` (`Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`),
  `EG/Defs/Main/GammaCond.lean` (`GammaCond`);
- Specs: `EG/Spec/Gamma/N0.lean` (3 statements), `EG/Spec/Gamma/Sat.lean` (5 statements);
- the required Lib lemma `EG.Vortex.eventually_size` (`EG/Lib/Vortex/Size.lean`) and
  `EG.exists_N0` (`EG/Proof/Gamma/N0.lean`);
- tests `EGTest/GammaFull.lean`, `EGTest/ProbeGAMMA.lean`.

TeX read directly (v6.1): `s1.tex` 730 (log base), 1519–1780 (defConstants, remOrder, condGamma,
tabOrder); `s3.tex` 1137–1200 (tabCOLJV), 1350–1380 (lemCOLJVev); `s4.tex` 145–210, 430–466,
655–682 (size conditions, the three `η`) and a scan of every use of `N_0` / "size condition" in s4;
`s5.tex` 5–16 (setting), 395–412 (remConstants); `s7.tex` 5–16 (setting), 1051, 1116, 1283
(`ε_X`, `ε_2`, `ε_1`), 1440–1515 (lemGammaSat and proof); `s2.tex` 1171 (`ε_A`); `s5.tex` 140, 360
(`ε_U`, `ε_K`).

## 1. Fidelity (back-translation)

Throughout `log = log₂` (s1.tex 730: "All logarithms have base 2"); Lean `Real.logb 2`.

### Definitions

| Lean | plain mathematics | TeX (quoted) | verdict |
|---|---|---|---|
| `Gamma1f D := ∀ μ : ℝ, logb 2 (logb 2 D) ≤ μ → COLTable.col3 μ` | every real `μ ≥ log₂log₂D` satisfies the 18 column-3 inequalities of rows 1–13 at `λ = 2^μ` | condG1 (f): "for every real `μ ≥ log₂log₂D_*`, with `λ := 2^μ` … for every row of the COL-JV table …, every inequality in column 3 of that row holds at `λ`, where `M̄ := (Aμ)^{2A}` and `k̄ := 192λ³ + (4/3)M̄²`" | faithful: non-strict `≤`, real `μ`, `λ = 2^μ` (`COLTable.lam`, rpow), `Mbar = (Aμ)^{2A}`, `kbar = 192λ³ + 4/3·M̄²` |
| `COLTable.row 1..13`, `col3` (locked, Lend unit) | the 18 inequalities | tabCOLJV column 3 | re-checked all 13 rows myself against s3.tex 1147–1170: row 1 both parts strict `<`, `102.5 = 205/2`, `1/2`; row 4 `42.1 = 421/10`; row 7 `64.4 = 322/5`; row 8 five parts; row 9 `3.3 = 33/10`; row 12 `1.6 = 8/5`; row 13 = G*. `col3` bounds the index by `1 ≤ i ≤ 13` (no junk rows). Agree |
| `Gamma1 D := Gamma1core D ∧ Gamma1f D` | `D > 2` and (a)–(f) on the whole ray | condG1: "`D_* > 2` …; and for every real `μ ≥ log₂log₂D_*` … (a) … (f)" | faithful (`Iff.rfl` in the scratch file against the spelled-out form) |
| `N0Cond N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N:ℝ) → TPVSize N ∧ PVSize N ∧ VXSize N` | `N_0 ≥ 2^40`; every vertex count `N ≥ N_0` satisfies (i) `L ≥ 2^10`, (ii) `N ≥ L³`, (iv) `η ≤ 1/100` of each of the three proofs | defConstants (ii) "`N_0 ≥ 2^{40}` … and `N_0` at least each of the absolute size thresholds required in the proofs of Lemma s4:lemTPV, Lemma s4:lemPV and Theorem s4:thmVXp"; s4.tex 151: "chosen so large that the finitely many explicit inequalities listed as *size conditions* in the three proofs of this section hold for every `N ≥ N_0`" | faithful. Real `N_0`, natural `N` (D-VX-1). (iii) is "a consequence of (i)" (s4.tex 181, 463, 678) and is derived in `EG/Lib/Vortex/Params.lean`. I scanned s4 for size facts used outside the listed (i)–(iv) (lines 213, 243–246, 372–373, 488–491, 596–597, 706, 727, 791): every one is (i), (ii), (iii) or (iv), or a hypothesis on `s`, not on `N`. So `N0Cond` lists everything the three proofs ask of `N` |
| `etaTPV`, `etaPV`, `etaVX` (locked) | the three `η` | s4.tex 183, 439, 662 | re-checked term by term: `2LN^{-5} + 2^{96}L^{31}N^{-3} + NLe^{-3L^4/8}`; `2^{95}L^{31}N^{-3} + NLe^{-L^4/16}`; `2LN^{-5} + 2^{95}L^{28}N^{-3} + NLe^{-3L^2/(32 log₂L)} + Le^{-N/(5000L)}`. Agree |
| `Gamma3 N0 D := 2 * N0 ≤ logb 2 D ^ Cp` | `(log₂D)^{103} ≥ 2N_0` | condG3 "`(log₂ D_*)^{C'} ≥ 2 N_0`" | faithful; `Iff.rfl` against `(logb 2 D) ^ (103 : ℕ)` (natural power, not rpow) |
| `RunHyp N0 D G run := Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧ N0 ≤ G.card ∧ D ≤ run.d G 1 ∧ run.Valid G D` | `N_0` admissible; `D` satisfies Γ1, Γ3; `n = |V(G)| ≥ N_0`; `d_1 = 2|E(G)|/n ≥ D`; the run is valid for `D` | s5.tex 9: "Throughout, `G` is a graph on `n ≥ N_0` vertices with `d_1 ≥ D_*`; `D_*` satisfies Γ1–Γ4 …; a valid `HB^tp` run on `G` is fixed"; s7.tex 10 likewise | faithful to TRIAGE §2.6. `run.graph G 1 = G` is `rfl` and `Round.d H = 2|E(H)|/|H|` (s2:defHBtp (R0)), so `run.d G 1` is the manuscript's `d_1`. Γ4 deliberately omitted (added by thmJVps, `C0_le`, thmMainProof, s7:lemUHsplit (iv)); Γ2(a) derived (`RunHyp.gamma2a`). The docstring says what is *not* in the bundle (stage-1 data, designation, `𝒱 = ∅`) |
| `GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` | Γ1 (a)–(f); `D ≥ 2^{117}`; `(log₂D)^{103} ≥ 2N_0`; `ε_1(D) ≤ 6 ∧ ε_2(D) ≤ 1/4` | defConstants (iii) "`D_*` is a constant satisfying Γ1–Γ4"; condGamma: Γ2 "Each of (a)–(c) is implied by Γ1 … listed separately for traceability" | faithful. Γ2(b),(c) quantify over runs / failure probabilities and are lemmas (s2:lemTower (b), s3:lemCOL, s5:lemE1); they are correctly not fields. `Gamma4` (locked) is `eps1 D ≤ 6 ∧ eps2 D ≤ 1/4`; `eps1`, `eps2` (locked, Quot unit) match s7.tex 1283 and 1116 verbatim; `epsX` (1051), `epsA` (s2 1171), `epsU` (s5 140), `epsK` (s5 360 = `ε_ch`), `epsCONC` (Γ4 bullet / s6:thmCONCL) spot-checked, agree |

### Statements

| Lean | plain mathematics | TeX (quoted) | verdict |
|---|---|---|---|
| `VortexEventuallySizeStatement := ∀ᶠ N : ℕ in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` | there is `N_1` with all size conditions at every natural `N ≥ N_1` | defConstants (ii) "an explicit inequality in `N`, which holds for all sufficiently large `N`" | faithful; literally the required Lib statement of TRIAGE §3 item 14 |
| `N0EventuallyStatement := ∀ᶠ N0 : ℝ in atTop, N0Cond N0` | every sufficiently large real `N_0` is admissible | "Every requirement on `N_0` in this item is an *eventuality*: it holds for every sufficiently large value of `N_0`" | faithful (`eventually_atTop` gives the `∃ M, ∀ N0 ≥ M` form; checked) |
| `N0ExistsStatement := ∃ N0 : ℝ, N0Cond N0` | an admissible `N_0` exists | "So such an `N_0` exists" | faithful |
| `Col3EventuallyStatement := ∀ᶠ μ : ℝ in atTop, col3 μ` | all 18 inequalities at every large real `μ` | lemCOLJVev (iii) "for each row …, every inequality in column 3 holds at `λ = 2^μ` for all sufficiently large real `μ`" | faithful; per-row vs joint eventuality is equivalent for 13 rows |
| `GammaSatItemsStatement` | (∀ᶠ μ, (a)–(f)) ∧ ∃ μ₁ ≥ 1, (∀ μ ≥ μ₁, (a)–(f)) ∧ ∀ D > 2, log₂log₂D ≥ μ₁ → Γ1 D | lemGammaSat (i) "each item (a)–(f) … holds for all sufficiently large real `μ`; hence there is `μ_1 ≥ 1` such that all of them hold for every `μ ≥ μ_1`, and Γ1 holds for every `D_* > 2` with `log₂log₂D_* ≥ μ_1`" | faithful clause by clause; all inequalities non-strict as in the TeX, `D > 2` strict as in the TeX |
| `GammaSatEpsStatement := Tendsto eps1 atTop (𝓝 0) ∧ Tendsto eps2 atTop (𝓝 0)` | `ε_1, ε_2 → 0` as the real `D → ∞` | lemGammaSat (ii) | faithful |
| `GammaSatStatement := ∀ N0 : ℝ, ∀ᶠ D : ℝ in atTop, GammaCond N0 D` | for every real `N_0` there is `D_0` with Γ1–Γ4 at every `D ≥ D_0` | lemGammaSat (iii), under "Let `N_0` be as in Definition (ii)": "there is `D_0` such that every `D_* ≥ D_0` satisfies Γ1–Γ4 simultaneously" | a strengthening (the hypothesis `N0Cond N0` is dropped), as the docstring says; the TeX proof uses `N_0` only in "`D_* ≥ 2^{(2N_0)^{1/C'}}`". Checked: unfolds to `∀ N0, ∃ D0, ∀ D ≥ D0, GammaCond N0 D`. Nothing weakened |
| `GammaCondExistsStatement := ∃ N0 D : ℝ, N0Cond N0 ∧ GammaCond N0 D` | admissible `N_0`, `D_*` exist jointly | "In particular a constant `D_*` as in Definition s1:defConstants(iii) exists" with (ii) "So such an `N_0` exists" | faithful; this is the non-vacuity of the main theorem's standing hypotheses |

Every Spec docstring starts with its manuscript label and quotes the TeX. `N_0` uses outside s1/s4/s5/s7 (s2.tex 723; s6.tex 683, 762, 803) are all "`n ≥ N_0`" hypotheses or "`≥ N_0` by Γ3": none adds a requirement on `N_0`.

## 2. Vacuity

Scratch file (compiles, 0 errors):
- `Gamma1 D → 2 < D`; `GammaCond N0 D → 2 < D ∧ 2N_0 ≤ (log₂D)^{103}`; `N0Cond N0 → ∀ N ≥ N0, 2^{10} ≤ L N`.
- `RunHyp … → 1 ≤ run.R` (from `D ≤ d_1` and `d_{R+1} < D`); `run.graph G 1 = G` by `rfl`.
- `¬ GammaCond (-1) 16`: even for a negative `N_0` (where Γ3 is automatic) `GammaCond` is a real condition (Γ1(a) fails at `μ = log₂log₂16 = 2`).
- Junk range (c2 below): `Gamma3 (2^40) (-(2^300))` holds, because `Real.logb` takes `|D|`. Harmless: every use of `Gamma3` in this unit (`GammaCond`, `RunHyp`) is conjoined with `Gamma1 D`, hence `D > 2`.

`EGTest/ProbeGAMMA.lean` (re-checked: rc=0, 0 sorry): `¬ Gamma1 2`, `¬ Gamma1 16`, `¬ Gamma1f 2`, `¬ N0Cond 0`, `¬ N0Cond (2^40)`, `n0Cond_forces : N0Cond N0 → 2^{1023} < N0`, `¬ Gamma3 (2^900) (2^256)`, `¬ Gamma4 4` (via `6 < ε_1(4)`), `¬ GammaCond N0 4`. So no condition is trivially true.

`EGTest/GammaFull.lean` (re-checked: rc=0, 0 sorry): `∃ N0, N0Cond N0`; `∀ᶠ N0, N0Cond N0`; `∀ N0, ∃ D, GammaCond N0 D`; `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D`; `col3 μ` for every `μ ≥ 2^{40}`. So the hypotheses are not contradictory, and each of the four Specs that stage 1 had left open is now a theorem.

Not tested: non-vacuity of `RunHyp` (needs s2:propExists; m2).

## 3. Declared inputs

None, and none needed. `#print axioms` on `EG.exists_gammaCond`, `EG.gammaSat`, `EG.exists_N0`,
`EG.Vortex.eventually_size`, `EG.col3_eventually`, `EG.gammaSat_eps`: `[propext, Classical.choice,
Quot.sound]` only. Axiom scan (`--prefix EG`, modules `EG.Proof.Gamma.Sat EG.Proof.Gamma.N0
EG.Lib.Vortex.Size EG.Defs.Main.GammaCond`): 1136 constants, 0 `sorryAx`, 0 meta-scan hits,
0 violations. `grep sorry` on the unit's files finds only the docstring phrase "No `sorry`".

s3:lemCOLJVev (iii) is a node of this unit (proved, `EG.COLTable.col3_of_le` for `μ ≥ 2^{40}`),
not an input. Nothing that the unit was to prove is hidden among inputs.

## 4. Hygiene

- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- Module headers: `module` + `public import`; `@[expose] public section` in the two Defs files and
  both Spec files; `public section` in Lib and Proof. Tests are non-module files.
- `scripts/check.sh` on `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`: rc=0, 0 errors,
  0 sorry (this round).
- No locked file was edited by the unit (`EG/Defs/Main/Gamma.lean` untouched; `git status` shows
  only `work/p2b/*.md` modified).

## 5. Issues

**m1 (minor, integrator; carried over, still open).** The unit's modules are still not reachable
from the root files, and not locked: `EG.lean` imports none of `EG.Defs.Gamma.Full`,
`EG.Defs.Main.GammaCond`, `EG.Spec.Gamma.{N0,Sat}`, `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.{Full,Col3,Eps}`,
`EG.Proof.Gamma.{N0,Sat}` (it imports only `EG.Defs.Gamma.Core`, `EG.Defs.Main.Gamma`,
`EG.Defs.Vortex`, `EG.Lib.Found.Gamma`, `EG.Lib.Vortex.Params` of this area); `EGTest.lean` does not
import `EGTest.GammaFull` / `EGTest.ProbeGAMMA`; `LOCK.json` has 0 entries for the new Defs and
Specs. Until then CI neither compiles nor lock-checks them. Not fixable by this unit.

**m2 (minor, deferred to the s2 unit; carried over).** `RunHyp` non-vacuity is untested; it needs
s2:propExists (a graph with a valid run and `d_1 ≥ D_* ≥ 2^{2^{256}}`). Track with s2.

**c1 (cosmetic, integrator).** Docstring of the locked `EG/Defs/Main/Gamma.lean` (line 20) still
says `GammaCond` "is added here (additively) once that file exists"; it lives in
`EG/Defs/Main/GammaCond.lean`.

**c2 (cosmetic, new; no change needed).** `Gamma3 N0 D` is satisfiable at negative `D`
(`Real.logb 2 D = logb 2 |D|`): `Gamma3 (2^40) (-(2^300))` holds. It is always used together
with `Gamma1 D` (`D > 2`), so nothing is affected; a note in the `Gamma3` docstring would suffice.
Any future Spec that takes `Gamma3` alone should add `2 < D` (or `Gamma1 D`).

**c3 (cosmetic, T0; carried over).** s1.tex 1525 / 1764: "size condition (i), `L ≥ 2^{10}`,
already forces `N_0 ≥ 2^{1024}`". For a real `N_0` and natural `N ≥ N_0` the exact consequence is
`N_0 > 2^{1024} − 1` (Lean: `n0Cond_forces : N0Cond N0 → 2^{1023} < N0`). No proof uses the remark.

**Note N1 (unchanged, for the s5–s7 reviewers).** `RunHyp` omits Γ4: thmJVps, `C0_le`,
thmMainProof and s7:lemUHsplit (iv) ("`θ_Q ≤ 1/4` by condition Γ4") must add `Gamma4 D`. Γ2(b),(c)
are not fields of `GammaCond` and must never appear as hypotheses or declared inputs elsewhere.

## 6. Math findings on the manuscript

- **T0 (c3):** the real-`N_0` wording of the parenthetical in defConstants (ii) / tabOrder step 2.
  Harmless.
- Re-checked on paper, no gap found: s7:lemGammaSat (i) (each of (b)–(e) is dominated by a
  type-(E) inequality; `D_1 = 2^{2^{μ_1}} ≥ 4`), (ii) (`ε_U = 2462 (log₂D)^{-205}`,
  `ε_K = 614/D + log₂(2A log₂(A log₂log₂D))/(371 (log₂log₂D)²)`, `ε_A`, `ε_CONC` with
  `log* = o(log log)`, `F(x) → 0`, `ψ`, `O(1/D)` terms all tend to 0), (iii) (`D_0` as the max of
  four thresholds, Γ3 from `D ≥ 2^{(2N_0)^{1/C'}}` with `N_0 ≥ 2^{40} > 0`); s3:lemCOLJVev (iii);
  s4: the three proofs use no size fact beyond the listed (i)–(iv).
- No T1, T2 or T3 finding.
