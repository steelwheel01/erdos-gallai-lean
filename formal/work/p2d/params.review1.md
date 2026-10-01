# P2-D [params] definition review, round 1 (clean-room)

Reviewer: clean-room definition reviewer, 2026-09-26. Scope: `EG/Defs/Link/Star.lean`,
`EG/Defs/Vortex.lean`, `EG/Defs/Lend/COLTable.lean` (TRIAGE §3 items 11–13), with their Lib files
and `EGTest/Params.lean`, as described in `work/p2d/params.md`. No Lean file in the repository was
edited.

**Verdict: APPROVE.** Every definition back-translates exactly to the manuscript text (v6.1), is
total with documented junk values, and every downstream use listed in blueprints s3a, s3b, s4, s1
and TRIAGE can be stated with it. No major issue. Three minor and four cosmetic items follow at the
end; none blocks the lock.

## What was checked

- **Sources.** AGENTS.md, CONVENTIONS.md, TRIAGE (§2.4, §2.7, §2.8, §3), blueprints s3a (eqStar,
  P13\*, L17\*, P18\*), s3b (tabCOLJV, lemCOLJV, L9ρ, T16\*), s4 (convVortex, TPV, PV, VX⁺, remark),
  s1 (defConstants/N0Cond, Gamma1), s5/s7b (uses of `pvJ`, `N0Cond`, `col3`); manuscript s3.tex
  216–284 (eqStar, (S1)–(S6), P13\* parameter check), 1137–1185 (table and caption), 1355–1380
  (lemCOLJVev), 1073 (J_Y, k_own); s4.tex 23–45, 150–215, 398–470, 645–690; s1.tex 1519–1540
  (defConstants (ii)), 1603–1619 (Γ1 (c), (e), (f)); s2.tex 609 (L_Y); s5.tex 9, 80 (J_Y, m_Y, b_Y).
- **Build.** `lake build EGTest.Params`: success (2173 jobs, 0 errors). `python3 scripts/lint.py`:
  0 findings. `scripts/Axioms.lean --prefix EG EG.Lib.Link.Star EG.Lib.Vortex.Params
  EG.Lib.Lend.COLTable`: 255 constants, 0 `sorryAx`, 0 violations.
- **Scratch tests** (session scratchpad, `lake env lean`, all pass):
  - `Col3Witness.lean`: **`EG.COLTable.col3 8192` holds** (all 13 rows, 18 inequalities, at
    μ = 2^13, λ = 2^8192). This is the non-vacuity of Γ1(f), which the submission did not test.
    Full text in the appendix.
  - `Usability.lean`: the following shapes elaborate against the Defs:
    `N0Cond' N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N:ℝ) → TPVSize N ∧ PVSize N ∧ VXSize N`;
    `Gamma1f' D := ∀ μ, logb 2 (logb 2 D) ≤ μ → COLTable.col3 μ`; the PV own-class family
    `R : Fin (Vortex.pvJ O.card) × Fin 4 → FGraph V`; the bijection
    `Option (Fin (pvJ N) × Fin 4) ≃ Fin (4 * pvJ N + 1)` (TRIAGE §2.7 `ownIdx`); the s3a
    `StarFactsStatement` fragments ((S1), (S2) defining equation, (S5) first clause, the P13\*
    check); `G.IsWellExpanding (Star.theta G.card ε' ρ) U`; `Star.L n = Vortex.L n` (rfl); the
    lemCOLJVev(ii) shape `∀ μ ≥ 6, ∀ i, 1 ≤ i → i ≤ 13 → TypeE (triple i)… μ → row i μ`;
    junk values `Star.ell 1 = 0`, `Star.p 2 0 = 0`.

## Back-translation, definition by definition

### `EG/Defs/Link/Star.lean` (s3:eqStar)

Manuscript: "Let n ≥ 2 …, L := log n, ε′ ∈ [2^{-7},1] …, ρ ∈ (0,1] … and t ≥ 1 … ℓ_*, d_*, λ_*,
Δ_*, M_* and K_* are integers." (`log = log₂`.)

| Lean | back-translation | manuscript | ok |
|---|---|---|---|
| `L n = logb 2 n` | log₂ n | "L := log n" | ✓ |
| `ell n = ⌊2^10 L^3⌋₊` | ⌊2^{10}L³⌋ (L ≥ 1 in domain, so ℕ-floor = floor) | "ℓ_* := ⌊2^{10}L^3⌋" | ✓ |
| `g n ε' = ε'/(8L²)` | | "g_* := ε′/(8L^2)" | ✓ |
| `q ρ = 9/10·ρ` | | "q_* := 0.9ρ" | ✓ |
| `p n ρ = 1 − b^{1/(ℓ−1)}`, b = (1−ρ)/(1−0.9ρ) | explicit root | "p_* ∈ (0,1] given by (1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)" | ✓ (see below) |
| `d = ⌈1/p⌉₊`, `lam = ⌈6/p⌉₊` | | "d_* := ⌈1/p_*⌉, λ_* := ⌈6/p_*⌉" | ✓ |
| `Delta = lam + ⌈d·lam/3⌉₊` (product in ℝ of casts) | | "Δ_* := λ_* + ⌈d_*λ_*/3⌉" | ✓ |
| `sigma = 24L²/ε'` | | "σ_* := 24L^2/ε′" | ✓ |
| `theta = 2^19 ℓ² L³/(ε'ρ²)` with ℓ = `ell n` (the integer) | | "θ_* := 2^{19}ℓ_*^2L^3/(ε′ρ^2)" | ✓ |
| `mu = ε'/(6 θ L²)` | | "μ_* := ε′/(6θ_*L^2)" | ✓ |
| `sbar = 2^28 t L^8/ρ` | | "s̄_* := 2^{28}tL^8/ρ" | ✓ |
| `M ρ = ⌈(21/10)/ρ⌉₊` | | "M_* := ⌈2.1/ρ⌉" | ✓ |
| `K = ⌈6 s̄ θ L²/ε'⌉₊` | | "K_* := ⌈6 s̄_* θ_* L^2/ε′⌉" | ✓ |

- **p_\* (D-STAR-1).** In the domain, ℓ_* ≥ 1024, b ∈ [0,1) and the exponent 1/(ℓ_*−1) > 0, so
  `p ∈ (0,1]`; `one_sub_p_pow` gives the defining equation with the natural power `ℓ_* − 1` (the
  manuscript's power), and `p_unique` (restricted to x ≤ 1, correctly: for x > 1 and even ℓ_*−1
  the equation has a second root, which the manuscript excludes by "p_* ∈ (0,1]"). At ρ = 1,
  b = 0 and `0^{positive} = 0` gives p = 1 (`p_one`), matching the manuscript. The explicit
  closed form is the manuscript's p_\*. Faithful.
- **Types.** The six integers are ℕ (all ceilings are of positive reals in the domain, and the
  floor is of a real ≥ 1024), so ℕ-rounding coincides with ℤ-rounding. P13\* takes λ, d, Δ as
  naturals, T16\* colours with `K_*` colours (`Fin K`), L9ρ uses `M_*` as a natural and `ell` as a
  ball radius (ℕ): all type-correct.
- **Argument order/dependency.** Each function takes exactly the inputs its formula uses
  (`M ρ`, `q ρ`, `theta n ε' ρ`, `K n ε' ρ t` …); the blueprint lean_shape (s3a) is reproduced
  verbatim except `Delta`, whose cast placement `((d:ℝ)*(lam:ℝ))/3` equals the blueprint's
  `((d*lam : ℕ):ℝ)/3` by `Nat.cast_mul`. Fine.
- **Junk (D-STAR-4).** Outside n ≥ 2, ρ ∈ (0,1], ε′ ∈ [2^{-7},1], t ≥ 1 the values are junk
  (e.g. `ell 1 = 0`, `p 2 0 = 0`, `d 2 0 = 0`); every s3 Spec shape in the blueprints carries these
  hypotheses (STAR-DOMAIN). Documented.
- **Downstream uses.** P13\* check, L17\* (`8·(d·lam) ≤ s₁`, `IsWellExpanding (theta …)`,
  `ball … (ell G.card)`), P18\* (`theta`, `mu`), L9ρ (`ell`, `sbar`, `M`), T16\* (`K`, `theta`,
  `mu`, `sbar`, (S5)), StarFacts, StarUnionLaw (`if i+1 < ell then p else q`): all statable.
  `t_{0*}` is proof-internal ("defined inside the proof of Lemma 9_ρ"), correctly absent.

### `EG/Defs/Vortex.lean` (s4:convVortex and the three statements)

| Lean | manuscript | ok |
|---|---|---|
| `L N = logb 2 N` | "N := \|Z\| and L := log₂\|Z\|" | ✓ |
| `etaTPV` = 2L·N^{-5} + 2^96 L^31 N^{-3} + N L e^{−3L⁴/8} | (s4:eqTPVprob) verbatim | ✓ |
| `etaPV` = 2^95 L^31 N^{-3} + N L e^{−L⁴/16} | (s4:eqPVprob) verbatim | ✓ |
| `etaVX` = 2L N^{-5} + 2^95 L^28 N^{-3} + N L e^{−3L²/(32 log₂ L)} + L e^{−N/(5000L)} | (s4:eqVXprob) verbatim | ✓ |
| `TPVSize N` = (i) 2^10 ≤ L ∧ (ii) L³ ≤ N ∧ (iv) η_TPV ≤ 1/100 | "Size conditions. We use: (i) L ≥ 2^{10}; (ii) N ≥ L^3; (iii) 4·48 ≤ L (a consequence of (i)); (iv) η_TPV(N) ≤ 1/100" | ✓ |
| `PVSize`, `VXSize` | same with 4·64, 4·13 and η_PV, η_VX | ✓ |
| `tpvJ = vxJ = ⌊logb 2 (L/6)⌋₊`, `pvJ = ⌊logb 2 (L/8)⌋₊` | "J := ⌊log₂(L/6)⌋", "J := ⌊log₂(L/8)⌋" | ✓ |
| `pvM = ⌈L⁶⌉₊`, `pvB = ⌈2^7 L² m⌉₊` | lemPV "m := ⌈L^6⌉, b := ⌈2^7L^2m⌉"; also s5 "m_Y := ⌈L_Y^6⌉, b_Y := ⌈2^7L_Y^2m_Y⌉" | ✓ |

- **(iii) omitted (D-VX-2).** (iii) is implied by (i) (4·64 = 256 ≤ 1024), derived in Lib, so each
  predicate is equivalent to the manuscript's full list. Fine.
- **N : ℕ (D-VX-1).** Correct reading: N = |Z| is a vertex count, and the manuscript's N_0
  requirement is "an explicit inequality in N … hold for every N ≥ N_0" over vertex counts. The
  resulting Spec hypotheses are `TPVSize O.card` (the blueprint's `TPVSize (O.card : ℝ)` no longer
  typechecks; see minor item M1).
- **J floor.** ⌊log₂(L/c)⌋ via `Nat.floor` of the real log: equal to the manuscript floor for
  L ≥ c; junk 0 below (the manuscript's floor would be negative there; never in the domain,
  since (i) gives L ≥ 1024, and ancestors in s3:defCOL have L_Y ≥ log(λ^103/2) ≫ 8). `pvJ` is the
  `J_Y` of s3:defCOL(iii) with L_Y = log₂|V(Y)| (s2.tex:609 "L_Y := log|V(Y)|"), as TRIAGE §2.7
  (PV-OWNCLASS-INDEX) requires; I checked `Fin (pvJ N) × Fin 4` and the `ownIdx` bijection
  elaborate.
- **Non-vacuity and eventuality.** The submission proves all three predicates at N = 2^1024 and
  refutes them at N = 2 and 2^1023. I re-derived that for every N with L ≥ 2^10 all three η's are
  ≤ 2^{-19} (the dominating term is N L e^{−3L²/(32 log₂L)} ≤ 2^{L + log L − 1.44·3L²/(32 log L)},
  exponent ≤ −13000 at L = 1024 and decreasing), so each predicate is equivalent to L ≥ 2^10 on ℕ
  and `∀ᶠ N in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` is true (needed for `EG.exists_N0`; not
  proved here, correctly deferred).
- **Scope (D-VX-5).** With the deterministic TPV/VX⁺ Specs (TRIAGE §2.8) only `pvJ`, `pvM`, `pvB`
  enter a statement; the TPV/VX⁺ run parameters k, m, b, t are proof-internal (Lib). Correct.

### `EG/Defs/Lend/COLTable.lean` (s3:tabCOLJV, Γ1(f), s3:lemCOLJVev)

- `lam μ = 2^μ` (rpow; caption "λ := λ_r and μ := log λ", Γ1 "λ := 2^μ") ✓; `Mbar μ = (Aμ)^{2A}`
  with natural exponent `2·Aexp = 210` ✓; `kbar = 192λ³ + (4/3)M̄²` ✓.
- **Column 3, compared cell by cell with s3.tex:1143–1160:** row 1 (strict, both the main and the
  crude inequality), 2, 3, 4 (421/10), 5, 6, 7 (322/5), 8 (a)–(d) with (d) split in two (five
  inequalities), 9 (33/10), 10, 11, 12 (8/5), 13 (46A, 36). Count 2 + 5 + 11 = 18, as Γ1(f) says.
  All ✓. Row 1 as a conjunction is the reading Γ1(f) fixes ("two in row 1").
- **Column 4** (`triple`), all 13 triples ✓ (row 8 has c = 1, not a multiple of A; checked).
- `TypeE a b c μ := 0 ≤ aμ − b − c·log₂(Aμ)` ✓ ("a μ − b − c log(Aμ) ≥ 0", A = 105, log = log₂);
  `v0` ✓ (sqrt of a negative radicand is junk 0 only outside a > 0, b, c ≥ 0).
- `col3 μ := ∀ i, 1 ≤ i → i ≤ 13 → row i μ` = Γ1(f) at μ ✓. `row 13 ↔ Gamma1e` is `Iff.rfl`
  ("Row 13 is G\*") and `row 12 ↔ Gamma1c` for μ > 0 ("row 12 is item (c)") ✓.
- **Non-vacuity:** `col3 8192` proved (appendix). Mathematically every row is eventually true
  (polylog(μ) vs 2^{cμ}; row 1 is λ^{1/2} vs 257(1 + (6μ+20)/λ)^{102}), consistent with lemCOLJVev.
- **Uses:** `Gamma1f`, COLJV (`col3 (logb 2 (run.lam G r))`), COLJVev (i)–(iii), GammaSat: all
  statable (checked in `Usability.lean`).

## Issues

### Minor

- **M1 (usability, orchestration; not a Defs defect).** D-VX-1 changes the argument of the size
  predicates to `N : ℕ`. TRIAGE §2.4 (`N0Cond N0 := … ∀ N ≥ N0, TPVSize N …`), blueprint s1
  (`EG.N0Cond (N0 : ℝ) … ∀ N : ℝ, N0 ≤ N → EG.S4.TPVSize N …`, line 1271) and blueprint s4
  (`EG.Vortex.TPVSize (O.card : ℝ)`, lines 187, 272, 348; `pvJ` as `Nat.log 2 ⌊L/8⌋₊`, line 126)
  still show the real-argument shapes and old namespace. Fix: record in TRIAGE §2.4 that the
  predicates take `N : ℕ`, that `N0Cond N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N : ℝ) → …`, and that
  Specs write `TPVSize O.card`.
- **M2 (tests).** `EGTest/Params.lean` has no positive test for `col3` (only `¬ col3 0` and row 4
  at μ = 20). Since Γ1 = Gamma1core ∧ Gamma1f and an unsatisfiable `col3` would make every Spec
  that assumes Γ1 vacuous, the witness should be in the test suite before the lock. Fix: paste the
  appendix (`col3_8192`, 141 lines, compiles in ~5 s, no large numeral is evaluated) into
  `EGTest/Params.lean`.
- **M3 (Lib API).** T16\* colours E(X) with `K_*` colours (`randColouring ↥X.edges (Star.K …)`),
  which needs `0 < Star.K n ε' ρ t` (blueprint s3b T16-STEP1-PRODUCT: "K_* needs a NeZero
  instance"). The Lib has `div_le_K` but no `K_pos`. Fix: add
  `K_pos (hn : 2 ≤ n) (hε : 0 < ε') (h0 : 0 < ρ) (ht : 0 < t) : 0 < K n ε' ρ t`
  (`Nat.ceil_pos` + `sbar_pos`, `theta_pos`, `L_pos`); optionally `ell_pos`.

### Cosmetic

- **C1.** Short names shared across namespaces: `Star.L`/`Vortex.L`, `Star.lam`/`COLTable.lam`,
  `Star.M` (and `run.M` in s2). Specs must not `open` two of these namespaces at once. A sentence in
  CONVENTIONS.md would prevent ambiguous-identifier surprises.
- **C2.** D-COL-1 (1-based `ℕ` rows with junk `True` outside 1…13) deviates from the blueprint's
  `Fin 13`. It is safe for every statement shape in the blueprints (all quantify with `1 ≤ i ≤ 13`
  or go through `col3`), but a future statement of the form "∃ i, ¬ row i μ" or "∀ i, row i μ"
  without the bounds would silently include junk rows. Worth one line in CONVENTIONS.md.
- **C3.** `Gamma1c` (Core, locked) writes `1.6 * μ` (`OfScientific`) while row 12 uses `8/5`; the
  Lib bridges them (`row12_iff_gamma1c`), so nothing to change, just noted for Spec authors.
- **C4.** The root imports (`EG.lean`: the three Defs and three Lib modules; `EGTest.lean`:
  `EGTest.Params`) are still to be added by the orchestrator, as the design note says; until then
  CI does not build these files.

## Appendix: `col3` witness (scratch file `Col3Witness.lean`, compiles with `lake env lean`)

```lean
import EG.Lib.Lend.COLTable

open EG EG.COLTable Real

namespace Scratch

theorem tp {a b : ℕ} (h : a ≤ b) : (2:ℝ)^a ≤ 2^b := pow_le_pow_right₀ (by norm_num) h

theorem hL : lam 8192 = (2:ℝ)^(8192:ℕ) := by
  rw [lam, show (8192:ℝ) = ((8192:ℕ):ℝ) by norm_num, Real.rpow_natCast]

theorem hR (q : ℝ) (k : ℕ) (h : 8192 * q = k) : lam 8192 ^ q = (2:ℝ)^k := by
  rw [lam, ← Real.rpow_mul (by norm_num), h, Real.rpow_natCast]

theorem hN (k : ℕ) : lam 8192 ^ k = (2:ℝ)^(8192*k) := by rw [hL, ← pow_mul]

theorem lam_ge_one : 1 ≤ lam 8192 := by rw [hL]; exact one_le_pow₀ (by norm_num)

theorem hRle (q q' : ℝ) (k : ℕ) (h : 8192 * q' = k) (hq : q' ≤ q) : (2:ℝ)^k ≤ lam 8192 ^ q := by
  rw [← hR q' k h]; exact Real.rpow_le_rpow_of_exponent_le lam_ge_one hq

theorem hA : (Aexp:ℝ) * 8192 ≤ 2^20 := by norm_num [Aexp]

theorem hM : Mbar 8192 ≤ 2^4200 := by
  rw [Mbar]
  calc ((Aexp:ℝ) * 8192) ^ (2 * Aexp) ≤ ((2:ℝ)^20) ^ (2 * Aexp) :=
        pow_le_pow_left₀ (by positivity) hA _
    _ = 2^4200 := by rw [← pow_mul, show 20 * (2 * Aexp) = 4200 by norm_num [Aexp]]

theorem hMp (k : ℕ) : Mbar 8192 ^ k ≤ 2^(4200*k) := by
  rw [pow_mul]; exact pow_le_pow_left₀ (Mbar_nonneg (by norm_num)) hM k

theorem hK : kbar 8192 ≤ 2^24585 := by
  rw [kbar, hN 3]
  have h1 : (192:ℝ) * 2^(8192*3) ≤ 2^24584 := by
    rw [show (24584:ℕ) = 8 + 8192*3 by norm_num, pow_add]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have h2 : (4/3:ℝ) * Mbar 8192 ^ 2 ≤ 2^24584 := by
    calc (4/3:ℝ) * Mbar 8192 ^ 2 ≤ 2 * 2^(4200*2) :=
          mul_le_mul (by norm_num) (hMp 2) (pow_nonneg (Mbar_nonneg (by norm_num)) 2) (by norm_num)
      _ = 2^(1 + 4200*2) := by rw [pow_add, pow_one]
      _ ≤ 2^24584 := tp (by norm_num)
  calc _ ≤ (2:ℝ)^24584 + 2^24584 := add_le_add h1 h2
    _ = 2^24585 := by rw [← two_mul, ← pow_succ']

theorem col3_8192 : col3 8192 := by
  rw [col3_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- row 1
    rw [row1_iff]
    constructor
    · have hb : lam 8192 + 6 * 8192 + 20 ≤ (2:ℝ)^8193 := by
        have h2 : (2:ℝ)^8193 = 2^8192 * 2 := pow_succ 2 8192
        rw [hL, h2]
        have : (6 * 8192 + 20 : ℝ) ≤ 2^8192 := by
          calc (6 * 8192 + 20 : ℝ) ≤ 2^16 := by norm_num
            _ ≤ 2^8192 := tp (by norm_num)
        clear h2
        generalize (2:ℝ)^8192 = x at *
        linarith
      have hpos : 0 ≤ lam 8192 + 6 * 8192 + 20 := by linarith [lam_pos 8192]
      calc 257 * (lam 8192 + 6 * 8192 + 20) ^ 102 ≤ 257 * ((2:ℝ)^8193)^102 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hb 102) (by norm_num)
        _ < 2^9 * ((2:ℝ)^8193)^102 := mul_lt_mul_of_pos_right (by norm_num) (by positivity)
        _ = 2^(9 + 8193*102) := by rw [pow_add, pow_mul]
        _ ≤ 2^839680 := tp (by norm_num)
        _ = lam 8192 ^ (205/2 : ℝ) := (hR _ _ (by norm_num)).symm
    · rw [hR (1/2) 4096 (by norm_num)]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
  · -- row 2
    rw [row2_iff, hN]; exact (hMp 13).trans (tp (by norm_num))
  · -- row 3
    rw [row3_iff, hN]
    calc 640 * kbar 8192 ≤ 2^10 * 2^24585 :=
          mul_le_mul (by norm_num) hK (by linarith [kbar_pos 8192]) (by positivity)
      _ = 2^(10 + 24585) := by rw [pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 4
    rw [row4_iff]
    calc (2:ℝ)^193 * 12^5 ≤ 2^193 * 2^20 := by gcongr; norm_num
      _ = 2^(193+20) := by rw [pow_add]
      _ ≤ 2^(8192*42) := tp (by norm_num)
      _ ≤ _ := hRle _ 42 _ (by norm_num) (by norm_num)
  · -- row 5
    rw [row5_iff, hN]
    calc 3 * (2:ℝ)^167 * kbar 8192 * Mbar 8192 ^ 21 ≤ 2^2 * 2^167 * 2^24585 * 2^(4200*21) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hK
            (kbar_pos _).le (by positivity)) (hMp 21) (pow_nonneg (Mbar_nonneg (by norm_num)) _)
            (by positivity)
      _ = 2^(2 + 167 + 24585 + 4200*21) := by rw [pow_add, pow_add, pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 6
    rw [row6_iff, hN]
    calc (2:ℝ)^110 * Mbar 8192 ^ 15 ≤ 2^110 * 2^(4200*15) := by gcongr; exact hMp 15
      _ = 2^(110 + 4200*15) := by rw [pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 7
    rw [row7_iff]
    calc (2:ℝ)^127 * 12^4 ≤ 2^127 * 2^15 := by gcongr; norm_num
      _ = 2^(127+15) := by rw [pow_add]
      _ ≤ 2^(8192*64) := tp (by norm_num)
      _ ≤ _ := hRle _ 64 _ (by norm_num) (by norm_num)
  · -- row 8
    rw [row8_iff, hN, hN]
    refine ⟨tp (by norm_num), ?_, ?_, tp (by norm_num), ?_⟩
    · calc (2:ℝ)^186 * (8192 + 1) ≤ 2^186 * 2^14 := by gcongr; norm_num
        _ = 2^(186+14) := by rw [pow_add]
        _ ≤ _ := tp (by norm_num)
    · calc (2:ℝ)^190 * (8192 + 1) ≤ 2^190 * 2^14 := by gcongr; norm_num
        _ = 2^(190+14) := by rw [pow_add]
        _ ≤ _ := tp (by norm_num)
    · rw [hN]
      have h1 : (1:ℝ) ≤ (2 * lam 8192) ^ 6 := one_le_pow₀ (by linarith [lam_ge_one])
      calc 64 * ((2 * lam 8192) ^ 6 + 1) ≤ 64 * (2 * (2 * lam 8192) ^ 6) := by gcongr; linarith
        _ = 2^(7 + 8193*6) := by
          have h2l : 2 * lam 8192 = (2:ℝ)^8193 := by rw [hL]; exact (pow_succ' 2 8192).symm
          rw [h2l, ← pow_mul, pow_add]; ring
        _ ≤ _ := tp (by norm_num)
  · -- row 9
    rw [row9_iff]
    exact hK.trans ((tp (by norm_num : 24585 ≤ 26624)).trans (hRle _ (13/4) _ (by norm_num) (by norm_num)))
  · -- row 10
    rw [row10_iff, hN]
    calc 2 * kbar 8192 ≤ 2 * 2^24585 := by gcongr; exact hK
      _ = 2^(24585+1) := by rw [pow_succ 2 24585, mul_comm]
      _ ≤ _ := tp (by norm_num)
  · -- row 11
    rw [row11_iff, hN]
    calc (2:ℝ)^13 * Mbar 8192 ^ 12 ≤ 2^13 * 2^(4200*12) := by gcongr; exact hMp 12
      _ = 2^(13 + 4200*12) := by rw [pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 12
    rw [row12_iff]
    exact hM.trans ((tp (by norm_num : 4200 ≤ 12288)).trans (hRle _ (3/2) _ (by norm_num) (by norm_num)))
  · -- row 13
    rw [row13_iff, hN]
    calc (2:ℝ)^240 * ((Aexp:ℝ) * 8192) ^ (46 * Aexp) ≤ 2^240 * ((2:ℝ)^20) ^ (46 * Aexp) := by
          gcongr; exact hA
      _ = 2^(240 + 20 * (46*Aexp)) := by rw [pow_add, ← pow_mul]
      _ ≤ _ := tp (by norm_num [Aexp])

end Scratch
```
