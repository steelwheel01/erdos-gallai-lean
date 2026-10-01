# GAMMA: clean-room review, round 1 (Specs and new Defs) — re-run 2026-09-29

Reviewer: clean-room Spec reviewer, round 1 (re-run). This file replaces the earlier round-1
review of the same name; that version is still in git history (commit 3278dd4). No Lean file
was edited. The scratch checks are in the session scratchpad (`GammaRev.lean`, outside the
repo). The proof being formalized is a CANDIDATE proof that has been reviewed only by AI.
Nothing here says the conjecture is solved.

**Verdict: APPROVE.** No major issue was found. There are 2 minor items and 3 cosmetic items, and
all of them are for the integrator (§5).

Scope:
- the new Defs `EG/Defs/Gamma/Full.lean` (`Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`) and
  `EG/Defs/Main/GammaCond.lean` (`GammaCond`);
- the Specs `EG/Spec/Gamma/N0.lean` and `EG/Spec/Gamma/Sat.lean`;
- the required Lib lemma `EG.Vortex.eventually_size`;
- the non-vacuity tests `EGTest/GammaFull.lean` and `EGTest/ProbeGAMMA.lean`.

The TeX passages were read directly:
- s1.tex 1519–1780: defConstants, remOrder, condGamma, tabOrder, and the log-base convention at 730;
- s3.tex 1182 (tabCOLJV) and 1357ff (lemCOLJVev);
- s4.tex 151–155, 181–184, 206, 437–440, 463, 659–663, 678;
- s5.tex 9 (setting) and 399 (remConstants);
- s7.tex 10 (setting) and 1447–1510 (lemGammaSat and its proof).

## 1. Fidelity (back-translation)

`log₂` is `Real.logb 2`, and `log = log₂` throughout the manuscript (s1.tex 730: "All logarithms
have base 2").

| Lean | plain mathematics | TeX | verdict |
|---|---|---|---|
| `Gamma1f D := ∀ μ, logb 2 (logb 2 D) ≤ μ → COLTable.col3 μ` | every real `μ ≥ log₂log₂D` satisfies all column-3 inequalities of rows 1–13 at `λ = 2^μ` | condG1 (f): "for every real `μ ≥ log₂log₂D_*`, with `λ := 2^μ` … for every row of the COL-JV table …, every inequality in column 3 of that row holds at `λ`" | faithful (non-strict `≤`, real `μ`) |
| `COLTable.col3 μ` (locked, Lend unit) | the 18 inequalities of rows 1–13 | tabCOLJV column 3 | spot-checked all 13 rows against s3.tex 1182: exponents, constants, strict `<` in row 1 (both parts), five parts in row 8, `M̄ = (Aμ)^{2A}`, `k̄ = 192λ³ + (4/3)M̄²` all agree; 2+5+11 = 18 |
| `Gamma1 D := Gamma1core D ∧ Gamma1f D` | `D > 2`, and (a)–(f) hold on the ray `μ ≥ log₂log₂D` | condG1 | faithful |
| `N0Cond N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → TPVSize N ∧ PVSize N ∧ VXSize N` | `N_0 ≥ 2^40`, and every vertex count `N ≥ N_0` satisfies size conditions (i) `L ≥ 2^10`, (ii) `N ≥ L³`, (iv) `η(N) ≤ 1/100` of all three vortex proofs | defConstants (ii); s4.tex 151: "`N_0` is chosen so large that the finitely many explicit inequalities listed as *size conditions* in the three proofs … hold for every `N ≥ N_0`" | faithful; (iii) is derived from (i) (`TPVSize.cond_iii` etc. in `EG/Lib/Vortex/Params.lean`) |
| `etaTPV`, `etaPV`, `etaVX` (locked) | the three `η` | s4.tex 183, 439, 662 | re-checked term by term: faithful |
| `Gamma3 N0 D := 2 * N0 ≤ logb 2 D ^ Cp` | `(log₂D)^{103} ≥ 2N_0` | condG3 "`(log₂D_*)^{C'} ≥ 2N_0`" | faithful; `Cp : ℕ = 103`, a natural-number power (checked `Iff.rfl`) |
| `RunHyp N0 D G run := Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧ N0 ≤ G.card ∧ D ≤ run.d G 1 ∧ run.Valid G D` | `N_0` admissible; `D` satisfies Γ1 and Γ3; `n = |V(G)| ≥ N_0`; `d_1 = 2|E(G)|/n ≥ D`; the run is valid for `D` | s5.tex 9, s7.tex 10 | faithful to TRIAGE §2.6. Γ2(a) is derived; Γ4, the stage-1 data, the designation and `𝒱 = ∅` are left to the Specs, as the docstring says. `run.graph G 1 = G` holds by `rfl`, and `RunHyp` forces `R ≥ 1` (checked in the scratch file) |
| `GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` | Γ1 (a)–(f), `D ≥ 2^117`, Γ3, and `ε_1(D) ≤ 6 ∧ ε_2(D) ≤ 1/4` | defConstants (iii); condGamma | faithful. Γ2(b),(c) are not fields, as the TeX says: "Each of (a)–(c) is implied by Γ1 … listed separately for traceability" (see note N1) |
| `VortexEventuallySizeStatement := ∀ᶠ N : ℕ in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` | the size conditions hold for all large vertex counts | defConstants (ii) "an explicit inequality in `N`, which holds for all sufficiently large `N`" | faithful; exactly the TRIAGE §3 item 14 shape |
| `N0EventuallyStatement := ∀ᶠ N0 : ℝ in atTop, N0Cond N0` | every large real `N_0` is admissible | "it holds for every sufficiently large value of `N_0`" | faithful |
| `N0ExistsStatement := ∃ N0, N0Cond N0` | an admissible `N_0` exists | "So such an `N_0` exists" | faithful |
| `Col3EventuallyStatement := ∀ᶠ μ : ℝ in atTop, col3 μ` | all 18 inequalities hold for all large real `μ` | lemCOLJVev (iii) | faithful (finitely many rows, so per-row ⇔ joint) |
| `GammaSatItemsStatement` | (∀ᶠ μ, (a)–(f)) ∧ ∃ `μ₁ ≥ 1`, (∀ μ ≥ μ₁, (a)–(f)) ∧ ∀ D > 2, `log₂log₂D ≥ μ₁` → Γ1 D | lemGammaSat (i) | faithful clause by clause, non-strict as in the TeX |
| `GammaSatEpsStatement := Tendsto eps1 atTop (𝓝 0) ∧ Tendsto eps2 atTop (𝓝 0)` | `ε_1, ε_2 → 0` as `D → ∞` | lemGammaSat (ii) | faithful. It relies on the locked `Quot.eps1/eps2`, which are reviewed in the Quot unit |
| `GammaSatStatement := ∀ N0 : ℝ, ∀ᶠ D in atTop, GammaCond N0 D` | for every real `N_0` there is `D_0` such that every `D ≥ D_0` satisfies Γ1–Γ4 | lemGammaSat (iii) "Let `N_0` be as in (ii) … there is `D_0` …" | a strengthening: the hypothesis on `N_0` is dropped. The TeX proof uses only that `N_0` is fixed ("`D_* ≥ 2^{(2N_0)^{1/C'}}`"), and for `N_0 ≤ 0` Γ3 is automatic once `D ≥ 1`. Nothing is weakened |
| `GammaCondExistsStatement := ∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` | admissible `N_0` and `D_*` exist jointly | "In particular a constant `D_*` as in Definition s1:defConstants(iii) exists" + (ii) | faithful; this is the non-vacuity of the main theorem's hypotheses |

Every Spec docstring starts with its manuscript label and quotes the TeX.

Completeness of `N0Cond`. I searched every section for the other places that `N_0` is used:
- s2.tex 723; s5.tex 9, 185, 332; s6.tex 683, 762, 803;
- s7.tex 10, 1368, 1405–1427, 1448, 1504–1535;
- s4.tex 160, 401, 646, and the unused remark at 803.

None of them puts a requirement on `N_0` other than `N_0 ≥ 2^{40}` and the size conditions. Every other use is either `n ≥ N_0` as a hypothesis or `c_EG ≥ N_0/2`. So `N0Cond` lists all the requirements of defConstants (ii).

## 2. Vacuity

Checked in the scratch file (it compiles; the oleans were newer than the sources):
- `Gamma1 D → 2 < D` and `Gamma1 D → 2^8 ≤ log₂log₂D`, so Γ1 is a real condition.
- `GammaCond N0 D → 2N_0 ≤ (log₂D)^{103}`.
- `N0Cond N0 → ∀ N ≥ N0, 2^10 ≤ L N`.
- `RunHyp … → 1 ≤ run.R`.

`EGTest/ProbeGAMMA.lean` has further negative tests: `¬ Gamma1 16`, `¬ Gamma1f 2`, `¬ N0Cond (2^40)`, `¬ Gamma3 (2^900) (2^256)` and `¬ GammaCond N0 4` (through `ε_1(4) > 6`). So no condition is trivially true.

`EGTest/GammaFull.lean` proves `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` and `∀ N0, ∃ D, GammaCond N0 D`. So the hypotheses are not contradictory.

The one hypothesis bundle whose non-vacuity is not tested is `RunHyp`, which needs a graph with a valid run (see m2).

## 3. Declared inputs

There are none, and none are needed: every node of the unit is proved. `#print axioms` on
`EG.exists_gammaCond`, `EG.Vortex.eventually_size`, `EG.exists_N0` and `EG.gammaSat` gives
`[propext, Classical.choice, Quot.sound]` only, so no `sorryAx` from another unit's stubs gets in.
`grep sorry` finds only docstring text ("No `sorry`.").

s3:lemCOLJVev (iii) is correctly a node of this unit (it is proved as `col3_eventually`) and not an input.

## 4. Hygiene

- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- The module headers follow AGENTS.md: `module`; `@[expose] public section` in Defs and Spec, `public section` in Lib and Proof.
- The files are small: Lib, Proof and Col3/Eps come to 889 lines in total.
- The unit did not edit locked files. `Main/Gamma.lean` was left untouched.

## 5. Issues

**m1 (minor, integrator).** The new modules are not reachable from the root files:
- `EG.lean` does not import `EG.Defs.Gamma.Full`, `EG.Defs.Main.GammaCond`, `EG.Spec.Gamma.*`, `EG.Lib.Vortex.Size`, `EG.Lib.Gamma.*` or `EG.Proof.Gamma.*`;
- `EGTest.lean` does not import `EGTest.GammaFull`;
- `LOCK.json` has no entry for the new Defs and Specs (0 matches).

Until the integrator adds these, CI neither compiles nor lock-checks them.

**m2 (minor, deferred).** The non-vacuity of `RunHyp` is not tested. It needs s2:propExists, a graph with a valid run and `d_1 ≥ D_* ≥ 2^{2^{256}}` (GAMMA.md Q1). The non-vacuity test for `RunHyp` should be tracked with the s2 unit.

**c1 (cosmetic).** The docstring of the locked `EG/Defs/Main/Gamma.lean` still says `GammaCond` "is added here (additively) once that file exists". It should point to `EG/Defs/Main/GammaCond.lean`, at the next approved edit.

**c2 (cosmetic).** `GammaCond` keeps Γ2(a) as a field although `Gamma1core.gamma2a` derives it. This matches the manuscript's list and does no harm.

**c3 (cosmetic, T0).** The manuscript says "`L ≥ 2^{10}` already forces `N_0 ≥ 2^{1024}`". For a real `N_0` the exact consequence is `N_0 > 2^{1024} − 1`. No proof uses the remark, and nothing changes in Lean.

**Note N1 (for the other units' reviewers).** Γ2(b),(c) are absent from `GammaCond`, so the lemmas s2:lemTower (b), s3:lemCOL and s5:lemE1 (b),(c) must be proved from Γ1 in their own units. They must never become hypotheses or declared inputs there. Otherwise a hidden hypothesis appears that is not in the main theorem.

**Note N2 (for the other units' reviewers).** Every Spec on `RunHyp` that uses Γ4 has to add `Gamma4 D`. These are thmJVps, `C0_le`, thmMainProof and s7:lemUHsplit (iv), as in TRIAGE §2.6.

## 6. Math findings on the manuscript

- **T0 (c3).** The real `N_0` in the parenthetical of defConstants (ii) and tabOrder step 2. It is harmless.
- I re-checked these proofs on paper and found no gap:
  - s7:lemGammaSat (i)–(iii): the reduction of (b), (d) and (e) to type-(E) inequalities, and `D_1 = 2^{2^{μ_1}} ≥ 4`;
  - s3:lemCOLJVev (i): the root `v_0`, and the bound `log μ = 2 log v < 2v`;
  - row 1 of (ii): `φ ≥ 0.5μ − 111`, and the crude form `μ > 222`.
- There is no T1, T2 or T3 finding.
