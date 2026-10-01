# P2-D [params] definition review, round 2 (clean-room)

Reviewer: clean-room definition reviewer (round 2), 2026-09-26. Scope: `EG/Defs/Link/Star.lean`,
`EG/Defs/Vortex.lean`, `EG/Defs/Lend/COLTable.lean` (TRIAGE §3 items 11–13), their Lib files
(`EG/Lib/Link/Star.lean`, `EG/Lib/Vortex/Params.lean`, `EG/Lib/Lend/COLTable.lean`) and
`EGTest/Params.lean`, after the round-1 fixes recorded in `work/p2d/params.md` ("Fix round 1").
No Lean file in the repository was edited; all scratch work is in the session scratchpad.

**Verdict: APPROVE (ready to lock).** Every definition back-translates to the manuscript text
(v6.1) exactly; the definitions are total with documented junk values; the manuscript's implicit
`p_*` is shown (in Lib) to be the explicit `Star.p`; the three size predicates and `col3` are
non-vacuous (proved in the test suite at `N = 2^{1024}` and `μ = 2^{13}`); and every downstream
use in blueprints s1, s3a, s3b, s4, s5, s6b, s7b and TRIAGE §2.4/§2.7/§2.8 is statable with the
given types (re-checked by elaborating each shape, appendix). No major issue. Two minor items
(both orchestration / follow-up, not Defs defects) and three cosmetic ones.

## What was checked

- **Sources.** AGENTS.md, CONVENTIONS.md (the "Parameters of s3/s4" bullets added in fix round 1),
  TRIAGE §2.4, §2.7, §2.8, §2.11, §3; blueprints s3a (eqStar, P13\*, L17\*, P18\*), s3b (tabCOLJV,
  lemCOLJV, lemCOLJVev, lemCOL, L9ρ, T16\*), s4 (convVortex, TPV, PV, VX⁺, the size-predicate and
  J-floor notes), s1 (defConstants(ii), Γ1, N0Cond), s5 (defStages, lemChild, lemDemoted), s6b and
  s7b (N0Cond, `col3`, GammaSat shape). Manuscript: s3.tex 216–284 (eqStar, (S1)–(S6), P13\* check),
  288–295 (P13\* hypotheses), 405–413 (L17\*), 601–612 (P18\*), 692–705 (L9ρ), 792–830 (T16\*),
  1073–1075 (defCOL(iii): J_Y, k_own), 1137–1185 (table and caption), 1355–1380 (lemCOLJVev),
  1400–1445 (its proof, row by row); s4.tex 23–45, 150–215, 398–470, 645–690, 802–814;
  s1.tex 566–580 (convGraphs), 1519–1540 (defConstants), 1603–1619 (Γ1); s5.tex 9–15, 76–92;
  s2.tex 609 (L_Y).
- **Build.** `lake build EGTest.Params`: up to date, success (2173 jobs). `python3 scripts/lint.py`:
  0 findings. The design note's axiom scan (258 constants, 0 `sorryAx`) was not repeated.
- **Scratch file** `Review2.lean` (appendix; `lake env lean`, rc = 0): junk values, boundary
  semantics of the `J` floors, and every downstream Spec shape listed below.

## Back-translation (definition by definition)

### `EG/Defs/Link/Star.lean` — [s3:eqStar]

Manuscript: "Let n ≥ 2 be the number of vertices of the graph at hand, L := log n, ε′ ∈ [2^{-7},1]
…, ρ ∈ (0,1] … and t ≥ 1 …. Throughout, ℓ_*, d_*, λ_*, Δ_*, M_* and K_* are integers." (log = log₂,
s1:convGraphs.)

| Lean | manuscript | ok |
|---|---|---|
| `L n : ℝ := logb 2 n` | "L := log n" | ✓ |
| `ell n : ℕ := ⌊2^10 L^3⌋₊` | "ℓ_* := ⌊2^{10}L^3⌋" (argument ≥ 2^{10} in the domain) | ✓ |
| `g n ε' := ε'/(8 L^2)` | "g_* := ε′/(8L^2)" | ✓ |
| `q ρ := 9/10 ρ` | "q_* := 0.9ρ" | ✓ |
| `p n ρ := 1 − ((1−ρ)/(1−9/10 ρ))^{1/(ℓ−1)}` (rpow) | "p_* ∈ (0,1] given by (1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)" | ✓ via Lib (below) |
| `d n ρ : ℕ := ⌈1/p⌉₊`, `lam n ρ : ℕ := ⌈6/p⌉₊` | "d_* := ⌈1/p_*⌉, λ_* := ⌈6/p_*⌉" | ✓ |
| `Delta n ρ : ℕ := lam + ⌈(d:ℝ)(lam:ℝ)/3⌉₊` | "Δ_* := λ_* + ⌈d_*λ_*/3⌉" | ✓ |
| `sigma n ε' := 24 L^2/ε'` | "σ_* := 24L^2/ε′" | ✓ |
| `theta n ε' ρ := 2^19 (ell n)^2 L^3/(ε' ρ^2)` | "θ_* := 2^{19}ℓ_*^2L^3/(ε′ρ^2)" (ℓ_* the integer) | ✓ |
| `mu n ε' ρ := ε'/(6 θ L^2)` | "μ_* := ε′/(6θ_*L^2)" | ✓ |
| `sbar n ρ t := 2^28 t L^8/ρ` | "s̄_* := 2^{28}tL^8/ρ" | ✓ |
| `M ρ : ℕ := ⌈(21/10)/ρ⌉₊` | "M_* := ⌈2.1/ρ⌉" | ✓ |
| `K n ε' ρ t : ℕ := ⌈6 s̄ θ L^2/ε'⌉₊` | "K_* := ⌈6 s̄_* θ_* L^2/ε′⌉" | ✓ |

- **`p_*` (D-STAR-1).** The manuscript defines `p_*` implicitly and proves in (S2) that it exists
  and is unique. `Star.p` is the explicit root, and the Lib proves under `n ≥ 2`, `0 < ρ ≤ 1`:
  `p_pos`, `p_le_one`, `one_sub_p_pow` (the defining equation with the *natural-number* power
  `ℓ_* − 1`, exactly the manuscript's power), `p_unique` (any `x ≤ 1` solving it equals `p_*`; the
  restriction `x ≤ 1` is the manuscript's "p_* ∈ (0,1]" and is necessary, since for even `ℓ_*−1` the
  equation has the second root `2 − p_*`), `existsUnique_p`, and `p_one` (ρ = 1 gives base 0 and
  `p_* = 1`, as the manuscript's bijection argument gives). So `Star.p` *is* `p_*`. Faithful.
- **Types.** The six manuscript integers are `ℕ`; all ceiling arguments are positive and the floor
  argument is ≥ 2^{10} in the domain, so `Nat.ceil`/`Nat.floor` coincide with the integer
  ceiling/floor. P13\* takes `λ_*, d_* ≥ 1`, `Δ_* ≥ λ_*` as integers (`one_le_d`, `one_le_lam`,
  `lam_le_Delta`), T16\* colours with `Fin K_*` (`K_pos`, `K_ne_zero`), L9ρ uses `ell` as a ball
  radius (`EG.ball : FGraph V → ℕ → …`) and `M` as a natural. All type-correct.
- **Arguments.** Each function takes exactly the inputs its formula uses, in the order
  `(n, ε', ρ, t)` (`M ρ`, `q ρ`, `theta n ε' ρ`, `K n ε' ρ t`), as blueprint s3a's lean_shape
  and TRIAGE §2.11 prescribe.
- **Junk (D-STAR-4).** Checked: `L 0 = L 1 = 0`, `ell 1 = 0`, `p 2 0 = 0`, `d 2 0 = 0`, `M 0 = 0`.
  All s3 Spec shapes in the blueprints carry `2 ≤ n`, `0 < ρ ≤ 1`, `2^{-7} ≤ ε' ≤ 1`, `1 ≤ t`
  (CONVENTIONS bullet "Star parameters are junk outside …"). Documented in the file header.
- **P13\* parameter check** (s3.tex 281–283: "σ_* = 24L²/ε′ holds with equality, and
  Δ_* − λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3 = 8d_*λ_*L²/(ε′σ_*)"): `sigma` is definitionally
  `24 L^2/ε'` and `dlam_div_three_le` gives the second inequality; I re-derived
  `8 d λ L²/(ε' σ_*) = dλ/3` in the scratch file.
- **`t_{0*}`** is defined inside the proof of L9ρ ("The integer t_{0*} is defined inside the proof",
  s3.tex 240 and 740); correctly absent from Defs.

### `EG/Defs/Vortex.lean` — [s4:convVortex] and the three statements

| Lean | manuscript | ok |
|---|---|---|
| `L N : ℝ := logb 2 N` (`N : ℕ`) | "N := \|Z\| and L := log₂\|Z\|" | ✓ |
| `etaTPV N = 2L N^{-5} + 2^{96}L^{31}N^{-3} + N L e^{-3L^4/8}` | (s4:eqTPVprob) | ✓ verbatim |
| `etaPV N = 2^{95}L^{31}N^{-3} + N L e^{-L^4/16}` | (s4:eqPVprob) | ✓ verbatim |
| `etaVX N = 2L N^{-5} + 2^{95}L^{28}N^{-3} + N L e^{-3L^2/(32 log₂L)} + L e^{-N/(5000L)}` | (s4:eqVXprob) | ✓ verbatim |
| `TPVSize N := 2^{10} ≤ L ∧ L^3 ≤ N ∧ etaTPV N ≤ 1/100` | "(i) L ≥ 2^{10}; (ii) N ≥ L^3; (iii) 4·48 ≤ L (a consequence of (i)); (iv) η_TPV(N) ≤ 1/100" | ✓ ((iii) derived: `cond_iii`) |
| `PVSize`, `VXSize` | same with (iii) 4·64, 4·13 and η_PV, η_VX | ✓ |
| `tpvJ N = vxJ N = ⌊logb 2 (L/6)⌋₊` | TPV, VX⁺: "J := ⌊log₂(L/6)⌋" | ✓ |
| `pvJ N = ⌊logb 2 (L/8)⌋₊` | PV: "J := ⌊log₂(L/8)⌋"; s3:defCOL(iii) "J_Y := ⌊log(L_Y/8)⌋" with L_Y = log\|V(Y)\| (s2.tex 609) | ✓ |
| `pvM N = ⌈L^6⌉₊`, `pvB N = ⌈2^7 L^2 m⌉₊` | PV: "m := ⌈L^6⌉, b := ⌈2^7L^2m⌉"; s5:defStages: "m_Y := ⌈L_Y^6⌉, b_Y := ⌈2^7L_Y^2m_Y⌉" | ✓ |

- **`N : ℕ` (D-VX-1).** Correct reading of "N := |Z|" and of defConstants(ii) ("hold for every
  N ≥ N_0", N a vertex count). TRIAGE §2.4 and CONVENTIONS now record it (fix round 1, M1), so
  the blueprint shapes `TPVSize (O.card : ℝ)` are superseded; `TPVSize O.card`, `PVSize O.card`,
  `VXSize O.card` and `N0Cond N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N : ℝ) → …` elaborate (appendix).
- **(iii) omitted (D-VX-2).** Implied by (i) (4·64 = 256 ≤ 1024) and derived in Lib; each predicate
  is equivalent to the manuscript's list (i)–(iv). Not a weakening.
- **`J` (D-VX-3).** `Nat.floor` of the real `log₂(L/c)`: equal to the manuscript's floor whenever
  `L ≥ c`, which (i) guarantees; below that it is the junk value 0 (the manuscript's floor would be
  negative). Boundary semantics checked at exact powers: `pvJ (2^16) = 1`, `pvJ (2^2048) = 8`,
  `tpvJ (2^12) = 1`, `tpvJ (2^6) = 0`, `tpvJ 2 = 0`. The two-sided bounds the proofs use
  (`6·2^J ≤ L < 12·2^J`, `8·2^J ≤ L < 16·2^J`) are `tpvJ_bounds`, `pvJ_bounds`, `vxJ_bounds`.
  The junk value 0 is in fact convenient downstream: `k_own := 4·pvJ|Y| + 1 ≥ 1` for *every*
  ancestor (TRIAGE §2.7 COL-EMPTY-INDEX), so `Fin k_own` is never empty (see C3).
- **Run-specific names (D-VX-4).** `tpvJ`, `vxJ` separate (`vxJ_eq_tpvJ : rfl`), per CONV-SYMBOL-CLASH.
- **Scope (D-VX-5).** With the deterministic TPV/VX⁺ Specs (TRIAGE §2.8) the TPV/VX⁺ run
  parameters k, m, b, t never enter a statement (the sets A(w) are chosen inside the proof), so
  only `pvJ`, `pvM`, `pvB` are needed in Defs; `etaTPV`/`etaVX` remain for the Tier-2 probability
  Specs. Correct.
- **Junk.** `L 0 = 0`; `¬ PVSize 0`; in `etaVX` the divisor `32 log₂ L` is 0 at `L = 1` (N = 2),
  giving `exp 0 = 1` — harmless, (i) excludes it; documented ("positive under (i)").
- **Non-vacuity and eventuality.** `TPVSize (2^1024) ∧ PVSize (2^1024) ∧ VXSize (2^1024)` is proved
  in the tests without evaluating large numerals. I re-derived independently that for every
  natural `N` with `L ≥ 2^{10}` all three η's are far below `1/100`: the worst term is
  `N L e^{-3L²/(32 log₂L)}` with exponent `(L + log₂L) ln 2 − 3L²/(32 log₂L) ≤ 717 − 9830` at
  `L = 1024`, decreasing in `L`; `2^{96}L^{31}N^{-3} = 2^{96 + 31 log₂L − 3L}` is `< 2^{-2600}`;
  and `L^3 ≤ 2^L`. So each predicate is equivalent to `2^{10} ≤ L N` on `ℕ`, and the eventuality
  `∀ᶠ N in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` is true (M2 below: not yet proved in Lean).

### `EG/Defs/Lend/COLTable.lean` — [s3:tabCOLJV], Γ1(f), [s3:lemCOLJVev]

- `lam μ = 2^μ` (rpow; caption "λ = 2^μ") ✓. `Mbar μ = ((Aexp:ℝ)·μ)^(2·Aexp)` = (Aμ)^{210}
  (caption "M̄ := (Aμ)^{2A}, with A = 105") ✓, with `A = EG.Aexp` so that row 13 is
  *definitionally* `EG.Gamma1e` ("Row 13 is G\*"; `row13_iff_gamma1e : Iff.rfl` re-checked).
  `kbar μ = 192 λ^3 + (4/3) M̄^2` ✓.
- **Column 3, cell by cell against s3.tex 1143–1160** (repeating round 1 independently):
  row 1 `λ^{102.5} > 257(λ+6μ+20)^{102}` ∧ `λ^{1/2} > 2^{111}` (both strict) ✓; 2 `λ^{103} ≥ M̄^{13}` ✓;
  3 `λ^{99} ≥ 640k̄` ✓; 4 `λ^{42.1} ≥ 2^{193}·12^5` ✓; 5 `λ^{72} ≥ 3·2^{167} k̄ M̄^{21}` ✓;
  6 `λ^{84} ≥ 2^{110} M̄^{15}` ✓; 7 `λ^{64.4} ≥ 2^{127}·12^4` ✓; 8 (a) `λ^{58} ≥ 2^{194}`,
  (b) `λ^{62} ≥ 2^{186}(μ+1)`, (c) `λ^{62} ≥ 2^{190}(μ+1)`, (d) `λ^{58} ≥ 2^{191}` and
  `λ^{99} ≥ 64((2λ)^6+1)` ✓ (five inequalities); 9 `k̄ ≤ λ^{3.3}` ✓; 10 `2k̄ ≤ λ^4` ✓;
  11 `λ^{95} ≥ 2^{13} M̄^{12}` ✓; 12 `M̄ ≤ λ^{1.6}` ✓; 13 `λ^{36} ≥ 2^{240}(Aμ)^{46A}` ✓.
  Total 2 + 5 + 11 = 18, as Γ1(f) states. Decimal exponents are exact rationals under `rpow`
  (205/2, 1/2, 421/10, 322/5, 33/10, 8/5); integer exponents are `npow` (equal for λ > 0).
  Row 8(b) is marked "not used" in column 2 of the manuscript but is part of column 3, hence of
  Γ1(f); keeping it is faithful (and required, since Γ1(f) says "every row").
- **Column 4** (`triple`): all 13 triples match the TeX, including row 8's `c = 1` (not a
  multiple of A) and row 12's `(1.6, 0, 2A)` = `(8/5, 0, 2·Aexp)`. `triple_spec` gives
  "a_i > 0 and b_i, c_i ≥ 0" for `1 ≤ i ≤ 13`.
- `TypeE a b c μ := 0 ≤ aμ − b − c·log₂(Aμ)` ✓ (lemCOLJVev: "reads aμ − b − c log(Aμ) ≥ 0", A = 105,
  log = log₂; the side conditions a > 0, b, c ≥ 0 are hypotheses of the Spec, as the design note
  says). `v0 a b c := (c + √(c² + a(b + c log₂A)))/a` ✓ (lemCOLJVev(i)); the radicand is ≥ 0 for the
  table triples (checked for row 13 in the scratch file), so `Real.sqrt` is not in its junk regime.
- `col3 μ := ∀ i, 1 ≤ i → i ≤ 13 → row i μ` = Γ1(f) at `μ` ✓; `col3_iff` spells out the 13 rows.
- **Numbering (D-COL-1).** Rows 1…13 as in the manuscript, `row 0 = row (14+k) = True`,
  `triple = (0,0,0)` there; CONVENTIONS now warns to bound the index (fix round 1, C2). Checked
  `row 0 μ`, `row 100 μ`, `triple 0 = (0,0,0)`, `TypeE 0 0 0 μ`.
- **Non-vacuity.** `col3 8192` is now in the test suite (fix round 1, M2; builds with 0 warnings).
  Sanity at the other end: `¬ row 1 0`, `¬ col3 0` (tests) and `¬ row 12 6` (scratch; expected,
  since Γ1(a) already needs μ ≥ 256).
- **Row 12 ↔ Γ1(c).** `row12_iff_gamma1c` (μ > 0) bridges `M̄ ≤ λ^{8/5}` with the locked
  `Gamma1c` (`1.6 * μ`); CONVENTIONS records the two literals (fix round 1, C3).

## Downstream uses (all statable; elaborated in the appendix)

| Consumer | Shape checked |
|---|---|
| s3a StarFacts (S1)–(S6) | `ell_le`/`lt_ell`; the (S2) defining equation and uniqueness (`existsUnique_p`); `(Delta:ℝ) ≤ 2/p² + 8.34/p + 2.34`; `112/p² ≤ theta`; `sbar/mu ≤ K`; `(K:ℝ) ≤ 2^(836/10) t L^19/ρ³`; `2K(θ+1) ≤ 2^(1306/10) t L^28/ρ^5`; `6 ≤ lam·p` (derived from `six_div_p_le_lam`, `p_pos`) |
| s3a StarUnionLaw | `fun i : Fin (ell n) => if (i:ℕ)+1 < ell n then p n ρ else q ρ` |
| s3a P13\* (with eqStar values) | `sigma n ε' ≥ 24L²/ε'` (rfl) and `(Delta:ℝ) − lam ≥ 8 d lam L²/(ε' sigma)` (from `dlam_div_three_le`) |
| s3a L17\* | `G.IsWellExpanding (theta G.card ε' ρ) U`, `8·(d·lam) ≤ s₁`, `(EG.ball G (ell G.card) U V).card`, `exp (−7|U| L)` |
| s3a P18\* | `|F| ≤ mu·|U|`, `ε'|U|/(3θL²) ≤ |U'|`, `theta + 1 ≤ s₁` |
| s3b L9ρ | `(n:ℝ)/(M ρ) + 2 ≤ |V|`, `|F| ≤ sbar·|U|`, `G.IsPathConnected (2^12 L^4) t V` |
| s3b T16\* | `FinDist.randColouring ↥X.edges (K X.card ε' ρ t)` with `NeZero` from `K_ne_zero` |
| s4 TPV / VX⁺ (deterministic) | `TPVSize O.card`, `2^150 L^42 ≤ s`; `VXSize O.card`, `2^146 L^38 logb 2 (L N) ≤ s` (and the 2^151 branch) |
| s4 PV | `R : Fin (pvJ O.card) × Fin 4 → FGraph V`, `2·(pvM:ℝ) ≤ sO`, `(A w).card = pvM`, multiplicity `≤ pvB`, `arcs.length ≤ 4(pvJ+1)N` |
| s4 Tier-2 probability Specs | `1/2 − etaTPV N ≤ prob`, `1 − etaVX N ≤ prob` |
| s1 / TRIAGE §2.4 N0Cond | `2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N:ℝ) → TPVSize N ∧ PVSize N ∧ VXSize N` |
| s3:defCOL(iii) / TRIAGE §2.7 | `Option (Fin (pvJ N) × Fin 4) ≃ Fin (4·pvJ N + 1)` (built via `Fintype.equivFinOfCardEq`) |
| s5 defStages / lemCOL(e) | `2·(pvM Y.card : ℝ) ≤ s'`, `2^145 L^41 ≤ s'` (m_Y, b_Y are `pvM`, `pvB` at `|V(Y)|`) |
| s1 Γ1(f) | `Gamma1f D := ∀ μ, logb 2 (logb 2 D) ≤ μ → col3 μ` |
| s3b COLJV | `(klend:ℝ) ≤ kbar (logb 2 λ)`, `col3 (logb 2 λ)` (also at λ_{l−2}) |
| s3b COLJVev (i)–(iii) | `max 1 (v0 a b c ^ 2) ≤ μ → TypeE a b c μ`; `6 ≤ μ → 1 ≤ i → i ≤ 13 → TypeE (triple i).1 … μ → row i μ`; `∀ᶠ μ in atTop, row i μ`; `∀ᶠ μ in atTop, col3 μ` |
| s7b GammaSat (i) | `∃ μ₁, 1 ≤ μ₁ ∧ ∀ μ ≥ μ₁, Gamma1Items μ ∧ col3 μ` |

`Star.L n = Vortex.L n` is `rfl`, so s3 results applied inside a vortex run (with n := N) need no
rewriting.

## Issues

### Minor (orchestration / follow-up; not Defs defects)

- **M1 (root imports; carried over from round 1, C4).** `EG.lean` and `EGTest.lean` still do not
  import `EG.Defs.Link.Star`, `EG.Defs.Vortex`, `EG.Defs.Lend.COLTable`, `EG.Lib.Link.Star`,
  `EG.Lib.Vortex.Params`, `EG.Lib.Lend.COLTable`, `EGTest.Params` (the files are also untracked in
  git). Until the orchestrator adds them, CI does not build or lint these modules and
  `scripts/lock.py` cannot see them. Fix: add the seven imports when committing.
- **M2 (eventuality of the size predicates; owner: Gamma/Full).** `N0Cond N0` is satisfiable only
  if `∀ᶠ N in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` holds. It is true (derivation above:
  each predicate is equivalent to `2^{10} ≤ L N`), but it is not in Lean, and the test suite only
  covers the single point `N = 2^{1024}`. Since every s5–s7 Spec assumes `N0Cond N0`, the fact
  should be proved before `EG.exists_N0` is used; the design note already lists it as a follow-up
  with a proof route (bound each η term by `2^{-20}` using `two_pow_mul_exp_neg_le` and
  `log₂L ≤ L/16` for `L ≥ 1024`). Fix: record it as a required Lib lemma
  (`EG.Lib.Vortex.Params.eventually_size`) on the Gamma/Full task, not as an optional item.

### Cosmetic

- **C1.** `EG.COLTable.Mbar_nonneg` takes `hμ : 0 ≤ μ`, but `Mbar μ = (Aμ)^{210}` is non-negative
  for every real `μ` (even exponent). Harmless; a hypothesis-free version (`even_two_mul … |>.pow_nonneg`)
  would save a side goal in COLJVev.
- **C2.** `EG/Lib/Link/Star.lean` declares `private theorem exp_pos` inside `namespace EG.Star`
  with `open Real`, shadowing `Real.exp_pos` (overload resolved by type, and the lemma is private,
  so nothing downstream is affected). Rename, e.g. `one_div_ell_sub_one_pos`.
- **C3.** The junk value `pvJ N = 0` for `L N < 8` makes `k_own = 4·pvJ|Y| + 1 = 1` for tiny
  ancestors, so `Fin k_own` is never empty. This is exactly what TRIAGE §2.7 (COL-EMPTY-INDEX)
  needs; worth one sentence in the Stage1/COL design note so its author does not add a separate
  guard.

## Appendix: scratch file `Review2.lean` (scratchpad; `lake env lean`, rc = 0)

```lean
import EG.Lib.Link.Star
import EG.Lib.Vortex.Params
import EG.Lib.Lend.COLTable
import EG.Defs.Graph
import EG.Defs.Walk
import EG.Defs.Expander
import EG.Defs.Prob.FinDist

open EG Real

namespace Review2

/-! ## Junk values (outside the domain) -/
example : Star.L 0 = 0 := by simp [Star.L]
example : Star.L 1 = 0 := by simp [Star.L]
example : Star.ell 1 = 0 := by simp [Star.ell, Star.L]
example : Star.p 2 0 = 0 := by
  rw [Star.p_eq]; norm_num
example : Star.d 2 0 = 0 := by rw [Star.d]; simp [Star.p_eq]
example : Star.M 0 = 0 := by rw [Star.M]; simp
-- `p_* = 1` at `ρ = 1` (the base is 0)
example : Star.p 3 1 = 1 := Star.p_one (by norm_num)
example : Vortex.L 0 = 0 := by simp [Vortex.L]
example : Vortex.tpvJ 2 = 0 := by
  unfold Vortex.tpvJ Vortex.L
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, Real.logb_self_eq_one (by norm_num)]
  exact Nat.floor_of_nonpos (Real.logb_nonpos (by norm_num) (by norm_num) (by norm_num))
example : ¬ Vortex.PVSize 0 := by rintro ⟨h, -⟩; simp [Vortex.L] at h; norm_num at h
example (μ : ℝ) : COLTable.row 0 μ := trivial
example (μ : ℝ) : COLTable.row 100 μ := COLTable.row_of_gt (by norm_num) μ
example : COLTable.triple 0 = (0, 0, 0) := rfl
example (μ : ℝ) : COLTable.TypeE 0 0 0 μ := by simp [COLTable.TypeE]

/-! ## Boundary semantics of the floors (J at exact powers) -/
example : Vortex.pvJ (2 ^ 16) = 1 := by
  rw [Vortex.pvJ, Vortex.L_pow]; norm_num
example : Vortex.tpvJ (2 ^ 12) = 1 := by
  rw [Vortex.tpvJ, Vortex.L_pow]; norm_num
example : Vortex.tpvJ (2 ^ 6) = 0 := by
  rw [Vortex.tpvJ, Vortex.L_pow]; norm_num
example : Vortex.pvJ (2 ^ 2048) = 8 := by
  rw [Vortex.pvJ, Vortex.L_pow, show ((2048 : ℕ) : ℝ) / 8 = 2 ^ (8 : ℕ) by norm_num,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num
-- Star.L and Vortex.L agree definitionally
example (n : ℕ) : Star.L n = Vortex.L n := rfl

/-! ## Downstream Spec shapes: s3a / s3b -/
section Star
variable {V : Type} [DecidableEq V]

-- (S2) union law: `V_i` is `p_*`-random for `i < ℓ_*`, `V_{ℓ_*}` is `q_*`-random
noncomputable def unionLawProb (n : ℕ) (ρ : ℝ) (i : Fin (Star.ell n)) : ℝ :=
  if (i : ℕ) + 1 < Star.ell n then Star.p n ρ else Star.q ρ

-- P13* parameter check with the (eqStar) values
example (n : ℕ) (ε' ρ : ℝ) (hn : 2 ≤ n) (hε : 0 < ε') :
    Star.sigma n ε' ≥ 24 * Star.L n ^ 2 / ε' ∧
    (Star.Delta n ρ : ℝ) - Star.lam n ρ ≥
      8 * (Star.d n ρ : ℝ) * Star.lam n ρ * Star.L n ^ 2 / (ε' * Star.sigma n ε') := by
  refine ⟨le_of_eq rfl, ?_⟩
  have h := Star.dlam_div_three_le n ρ
  have hL := Star.L_pos hn
  have : 8 * (Star.d n ρ : ℝ) * Star.lam n ρ * Star.L n ^ 2 / (ε' * Star.sigma n ε') =
      (Star.d n ρ : ℝ) * Star.lam n ρ / 3 := by
    unfold Star.sigma; field_simp; ring
  rw [this]; exact h

-- L17*: well-expanding with θ_*, ball of radius ℓ_*, exp(-7|U|L)
example (G : FGraph V) (F : Finset (Sym2 V)) (ε' ρ : ℝ) (U W : Finset V) : Prop :=
  G.IsWellExpanding (Star.theta G.card ε' ρ) U ∧
  8 * ((Star.d G.card ρ : ℝ) * Star.lam G.card ρ) ≤ (1 : ℝ) ∧
  (EG.ball G (Star.ell G.card) U W).card ≤ W.card / 2 ∧
  Real.exp (-(7 * U.card * Star.L G.card)) ≤ 1

-- P18*: `|F| ≤ μ_* |U|`, `|U'| ≥ ε'|U|/(3θ_*L^2)`, `s_1 ≥ θ_* + 1`
example (n : ℕ) (ε' ρ s₁ : ℝ) (U U' F : Finset V) : Prop :=
  (F.card : ℝ) ≤ Star.mu n ε' ρ * U.card ∧
  ε' * U.card / (3 * Star.theta n ε' ρ * Star.L n ^ 2) ≤ U'.card ∧
  Star.theta n ε' ρ + 1 ≤ s₁

-- L9ρ: `|V| ≥ n/M_* + 2`, `|F| ≤ s̄_*|U|`, `(2^12 L^4, t)`-path connected
example (G : FGraph V) (ρ t : ℝ) (Vs U : Finset V) (F : Finset (Sym2 V)) : Prop :=
  (G.card : ℝ) / (Star.M ρ : ℝ) + 2 ≤ Vs.card ∧
  (F.card : ℝ) ≤ Star.sbar G.card ρ t * U.card ∧
  G.IsPathConnected (2 ^ 12 * Star.L G.card ^ 4) t Vs

-- T16*: colouring `E(X)` with `K_*` colours (needs `NeZero`)
noncomputable example (X : FGraph V) (ε' ρ t : ℝ) (hn : 2 ≤ X.card) (hε : 0 < ε')
    (h0 : 0 < ρ) (ht : 0 < t) :=
  haveI : NeZero (Star.K X.card ε' ρ t) := ⟨Star.K_ne_zero hn hε h0 ht⟩
  EG.FinDist.randColouring (↥X.edges) (Star.K X.card ε' ρ t)

-- StarFacts (S3), (S4), (S5) shapes (rpow exponent 83.6)
example (n : ℕ) (ε' ρ t : ℝ) : Prop :=
  (Star.Delta n ρ : ℝ) ≤ 2 / Star.p n ρ ^ 2 + 8.34 / Star.p n ρ + 2.34 ∧
  112 / Star.p n ρ ^ 2 ≤ Star.theta n ε' ρ ∧
  Star.sbar n ρ t / Star.mu n ε' ρ ≤ Star.K n ε' ρ t ∧
  (Star.K n ε' ρ t : ℝ) ≤ (2 : ℝ) ^ (836 / 10 : ℝ) * t * Star.L n ^ 19 / ρ ^ 3 ∧
  2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1) ≤ (2 : ℝ) ^ (1306 / 10 : ℝ) * t * Star.L n ^ 28 / ρ ^ 5
-- (S6) λ_* p_* ≥ 6 derivable
example (n : ℕ) (ρ : ℝ) (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (6 : ℝ) ≤ Star.lam n ρ * Star.p n ρ := by
  have hp := Star.p_pos hn h0 h1
  have := Star.six_div_p_le_lam n ρ
  rw [div_le_iff₀ hp] at this; exact this
end Star

/-! ## Downstream Spec shapes: s4 / s1 / s5 -/
section Vortex
variable {V : Type} [DecidableEq V]

def N0Cond' (N0 : ℝ) : Prop :=
  2 ^ 40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N : ℝ) → Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N

-- PV hypotheses (blueprint s4 lines 270–290)
example (O : FGraph V) (R : Fin (Vortex.pvJ O.card) × Fin 4 → FGraph V) (M : FGraph V)
    (A : V → Finset V) (sO : ℝ) (arcs : List (List V)) : Prop :=
  Vortex.PVSize O.card ∧
  2 * (Vortex.pvM O.card : ℝ) ≤ sO ∧
  (∀ w ∈ O.verts, A w ⊆ O.nbrs w ∧ (A w).card = Vortex.pvM O.card) ∧
  (∀ u, (O.verts.filter (fun w => u ∈ A w)).card ≤ Vortex.pvB O.card) ∧
  arcs.length ≤ 4 * (Vortex.pvJ O.card + 1) * O.card

-- TPV / VX+ thresholds
example (O : FGraph V) (s : ℝ) : Prop :=
  Vortex.TPVSize O.card ∧ (2 : ℝ) ^ 150 * Vortex.L O.card ^ 42 ≤ s
example (O : FGraph V) (s : ℝ) : Prop :=
  Vortex.VXSize O.card ∧
  ((2 : ℝ) ^ 146 * Vortex.L O.card ^ 38 * logb 2 (Vortex.L O.card) ≤ s ∨
   (2 : ℝ) ^ 151 * Vortex.L O.card ^ 38 * logb 2 (Vortex.L O.card) ≤ s)

-- s5:defStages / lemCOL(e): `m_Y = ⌈L_Y^6⌉`, `b_Y = ⌈2^7 L_Y^2 m_Y⌉`, `2⌈L^6⌉ ≤ s'`
example (Y : Finset V) (s' : ℝ) : Prop :=
  2 * (Vortex.pvM Y.card : ℝ) ≤ s' ∧ (2 : ℝ) ^ 145 * Vortex.L Y.card ^ 41 ≤ s'
-- own-class index of s3:defCOL(iii): k_own = 4 J_Y + 1 and the bijection
noncomputable example (N : ℕ) : Option (Fin (Vortex.pvJ N) × Fin 4) ≃ Fin (4 * Vortex.pvJ N + 1) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_option, Fintype.card_prod]; ring)
-- Tier-2 fidelity: probability bound shape
example (N : ℕ) (pr : ℝ) : Prop := 1 / 2 - Vortex.etaTPV N ≤ pr ∧ 1 - Vortex.etaVX N ≤ pr
end Vortex

/-! ## Downstream Spec shapes: Gamma1f, COLJV, COLJVev, GammaSat -/
def Gamma1f' (D : ℝ) : Prop := ∀ μ : ℝ, logb 2 (logb 2 D) ≤ μ → COLTable.col3 μ
example (lam : ℝ) (klend : ℕ) : Prop :=
  (klend : ℝ) ≤ COLTable.kbar (logb 2 lam) ∧ COLTable.col3 (logb 2 lam)
example : Prop :=
  (∀ a b c μ : ℝ, 0 < a → 0 ≤ b → 0 ≤ c → max 1 (COLTable.v0 a b c ^ 2) ≤ μ →
      COLTable.TypeE a b c μ) ∧
  (∀ μ : ℝ, 6 ≤ μ → ∀ i : ℕ, 1 ≤ i → i ≤ 13 →
      COLTable.TypeE (COLTable.triple i).1 (COLTable.triple i).2.1 (COLTable.triple i).2.2 μ →
      COLTable.row i μ) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ 13 → ∀ᶠ μ in Filter.atTop, COLTable.row i μ) ∧
  (∀ᶠ μ in Filter.atTop, COLTable.col3 μ)
example : Prop := ∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ → Gamma1Items μ ∧ COLTable.col3 μ
-- Row 13 is G* definitionally; row 12 ↔ Γ1(c)
example (μ : ℝ) : COLTable.row 13 μ ↔ Gamma1e μ := Iff.rfl
example (μ : ℝ) (h : 0 < μ) : COLTable.row 12 μ ↔ Gamma1c μ := COLTable.row12_iff_gamma1c h

/-! ## Column-4 sanity: v0 for row 13 is well defined (radicand ≥ 0) -/
example : 0 ≤ (COLTable.triple 13).2.2 ^ 2 +
    (COLTable.triple 13).1 * ((COLTable.triple 13).2.1 + (COLTable.triple 13).2.2 * logb 2 (Aexp : ℝ)) := by
  have : (0 : ℝ) ≤ logb 2 (Aexp : ℝ) := Real.logb_nonneg (by norm_num) (by norm_num [Aexp])
  simp only [COLTable.triple]; positivity

-- A numeric point: `M̄(6) = 630^210`; row 12 fails at μ = 6 (as expected: Γ1(a) needs μ ≥ 256)
example : COLTable.Mbar 6 = (630 : ℝ) ^ 210 := by norm_num [COLTable.Mbar, Aexp]
example : ¬ COLTable.row 12 6 := by
  rw [COLTable.row12_iff_gamma1c (by norm_num), Gamma1c]
  intro h
  have : (1 : ℝ) ≤ logb 2 ((Aexp : ℝ) * 6) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num [Aexp])]; norm_num [Aexp]
  norm_num [Aexp] at h this; linarith

end Review2
```
