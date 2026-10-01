# P2-D [params]: parameter definitions of s3/s4 (TRIAGE §3, Defs order items 11–13): design note

Status: everything compiles with 0 errors, 0 warnings and 0 `sorry`.
- The lint is clean (`python3 scripts/lint.py`: 0 findings, on the seven files and on the whole tree).
- The axiom scan (`scripts/Axioms.lean --prefix EG EG.Lib.Link.Star EG.Lib.Vortex.Params EG.Lib.Lend.COLTable`, which covers the three Defs modules) inspects 255 constants and finds 0 `sorryAx` and 0 violations.
- No Spec statement and no proof of a manuscript lemma was written. The facts (S1)–(S6) are the future `StarFactsStatement` (blueprint s3a). s3:lemCOLJV and s3:lemCOLJVev are also not proved here.
- Manuscript: `proofs/manuscript/s3.tex` (eqStar at lines 216–284, table at 1137–1185, lemCOLJVev at 1355–1380), `s4.tex` (convVortex at 23–45, lemTPV at 159–207, lemPV at 400–464, thmVXp at 645–679), and `s1.tex` (condG1(f) at 1613–1619, defConstants(ii) at 1523–1540), all v6.1.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Link/Star.lean` | `EG.Defs.Link.Star` | `EG.Star.{L, ell, g, q, p, d, lam, Delta, sigma, theta, mu, sbar, M, K}` |
| `EG/Defs/Vortex.lean` | `EG.Defs.Vortex` | `EG.Vortex.{L, etaTPV, etaPV, etaVX, TPVSize, PVSize, VXSize, tpvJ, pvJ, vxJ, pvM, pvB}` |
| `EG/Defs/Lend/COLTable.lean` | `EG.Defs.Lend.COLTable` | `EG.COLTable.{lam, Mbar, kbar, row, col3, triple, TypeE, v0}` |
| `EG/Lib/Link/Star.lean` | `EG.Lib.Link.Star` | API: `p` characterization, ceiling bounds, positivity |
| `EG/Lib/Vortex/Params.lean` | `EG.Lib.Vortex.Params` | API: size-condition accessors, `J` bounds (s4:eqTPVJ, s4:eqPVJ), `m`/`b` ceilings, exponential tails |
| `EG/Lib/Lend/COLTable.lean` | `EG.Lib.Lend.COLTable` | API: rows one by one, `col3_iff`, row 12 ↔ Γ1(c), row 13 ↔ Γ1(e), column-4 signs |
| `EGTest/Params.lean` | `EGTest.Params` | unit tests and numeric sanity checks, including non-vacuity of the three size predicates at `N = 2^1024` |

Imports:
- Star and Vortex import only Mathlib (`Pow.Real`, `Log.Base`, and `Exp` for Vortex).
- COLTable imports `EG.Defs.Constants` (for `Aexp`). Its Lib file also imports `EG.Defs.Gamma.Core`.

Root imports for the orchestrator to add (I did not edit `EG.lean` or `EGTest.lean`):
- to `EG`: `EG.Defs.Link.Star`, `EG.Defs.Vortex`, `EG.Defs.Lend.COLTable`, `EG.Lib.Link.Star`, `EG.Lib.Vortex.Params`, `EG.Lib.Lend.COLTable`;
- to `EGTest`: `EGTest.Params`.

## `EG/Defs/Link/Star.lean` (s3:eqStar)

> "Let n ≥ 2 be the number of vertices of the graph at hand, L := log n, ε′ ∈ [2^{-7},1] its expansion parameter, ρ ∈ (0,1] a density and t ≥ 1 a multiplicity. … Throughout, ℓ_*, d_*, λ_*, Δ_*, M_* and K_* are integers." (`log = log₂`, s1:convGraphs(b).)

Each function takes exactly the inputs among `(n : ℕ) (ε' ρ t : ℝ)` that its formula uses, in that order (blueprint s3a lean_shape; STAR-PARAM-ORDER).

| Lean | type | manuscript text | body |
|---|---|---|---|
| `Star.L n` | ℝ | "L := log n" | `logb 2 n` |
| `Star.ell n` | ℕ | "ℓ_* := ⌊2^{10}L^3⌋" | `⌊2^10 * L^3⌋₊` |
| `Star.g n ε'` | ℝ | "g_* := ε′/(8L^2)" | literal |
| `Star.q ρ` | ℝ | "q_* := 0.9ρ" | `9/10 * ρ` |
| `Star.p n ρ` | ℝ | "p_* ∈ (0,1] given by (1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)" | `1 - ((1-ρ)/(1-9/10*ρ))^(1/((ell n:ℝ)-1))` (rpow) |
| `Star.d n ρ` | ℕ | "d_* := ⌈1/p_*⌉" | `⌈1/p⌉₊` |
| `Star.lam n ρ` | ℕ | "λ_* := ⌈6/p_*⌉" | `⌈6/p⌉₊` |
| `Star.Delta n ρ` | ℕ | "Δ_* := λ_* + ⌈d_*λ_*/3⌉" | `lam + ⌈(d:ℝ)*(lam:ℝ)/3⌉₊` |
| `Star.sigma n ε'` | ℝ | "σ_* := 24L^2/ε′" | literal |
| `Star.theta n ε' ρ` | ℝ | "θ_* := 2^{19}ℓ_*^2L^3/(ε′ρ^2)" | literal, with `(ell n : ℝ)^2` |
| `Star.mu n ε' ρ` | ℝ | "μ_* := ε′/(6θ_*L^2)" | literal |
| `Star.sbar n ρ t` | ℝ | "s̄_* := 2^{28}tL^8/ρ" | literal |
| `Star.M ρ` | ℕ | "M_* := ⌈2.1/ρ⌉" | `⌈(21/10)/ρ⌉₊` |
| `Star.K n ε' ρ t` | ℕ | "K_* := ⌈6 s̄_* θ_* L^2/ε′⌉" | `⌈6*sbar*theta*L^2/ε'⌉₊` |

`t_{0*}` is defined inside the proof of Lemma 9_ρ ("The integer t_{0*} is defined inside the proof"), so it is not a Defs constant. `IsWellExpanding` (the well-expanding predicate of Lemma 17\*) already exists in `EG/Defs/Graph.lean` (P2-D [small]).

Decisions.
- **D-STAR-1 (p_\* explicit; STAR-PSTAR-IMPLICIT).** The manuscript defines p_\* implicitly, and (S2) proves that it exists and is unique. The Defs use the explicit root `1 − b^{1/(ℓ_*−1)}`, with `b := (1−ρ)/(1−0.9ρ)`.
  - Faithfulness is proved in Lib for `n ≥ 2` and `0 < ρ ≤ 1`: `p_pos`, `p_le_one`, `one_sub_p_pow` (the defining equation with the natural power `ℓ_* − 1`), `p_unique` (every `x ≤ 1` with `(1−x)^{ℓ_*−1} = b` equals `p_*`) and `existsUnique_p`.
  - So `Star.p` *is* the manuscript's p_\*.
  - At `ρ = 1`, `b = 0` and `p_* = 1` (`p_one`).
- **D-STAR-2 (types).** The six manuscript integers are ℕ, via `Nat.floor`/`Nat.ceil`. Their arguments are positive in the domain, so `⌈·⌉₊` agrees with the integer ceiling. The rest are ℝ. Decimals are exact rationals (`9/10`, `21/10`).
- **D-STAR-3 (Δ_\*).** `d_*λ_*/3` is computed in ℝ from the casts of the natural numbers `d_*` and `λ_*`.
- **D-STAR-4 (totality).** The definitions are total. Outside `n ≥ 2`, `ρ ∈ (0,1]`, `ε' ∈ [2^{-7},1]` and `t ≥ 1` their values are junk: for example `n ≤ 1` gives `L = 0`, `ℓ_* = 0`, and the exponent of p becomes −1. Statements must carry the domain hypotheses (STAR-DOMAIN).

Lib API (`EG/Lib/Link/Star.lean`):
- `L_eq`, `one_le_L`, `L_pos`, `L_nonneg`.
- `ell_le` and `lt_ell` (the floor bounds of (S1)); `two_pow_ten_le_ell`, `two_le_ell`, `cast_ell_sub_one`.
- `base_nonneg`, `base_lt_one`, `p_eq`, `p_pos`, `p_le_one`, `one_sub_p_pow`, `p_unique`, `p_spec`, `existsUnique_p`, `p_one`.
- Ceilings: `one_div_p_le_d`, `d_lt`, `one_le_d`, `six_div_p_le_lam`, `lam_lt`, `one_le_lam`, `lam_le_Delta`, `Delta_eq`, `dlam_div_three_le` (the P13\* check "Δ_*−λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3"), `le_M`, `M_lt`, `M_pos`, `div_le_K`.
- Positivity: `q_pos`, `g_pos`, `sigma_pos`, `theta_pos`, `mu_pos`, `sbar_pos`.

## `EG/Defs/Vortex.lean` (s4:convVortex and the three statements)

> [s4:convVortex] "Inside one run of Lemma TPV, Lemma PV or Theorem VX⁺ below (a *vortex run*), Z denotes the vertex set of the run, N := |Z| and L := log₂|Z|. … None of these symbols has a meaning outside the run in which it is defined."

| Lean | manuscript text |
|---|---|
| `Vortex.L N := logb 2 N` | "N := \|Z\| and L := log₂\|Z\|" |
| `etaTPV N` | (s4:eqTPVprob) "η_TPV(N) := 2LN^{-5} + 2^{96}L^{31}N^{-3} + NL e^{-3L^4/8}" |
| `etaPV N` | (s4:eqPVprob) "η_PV(N) := 2^{95}L^{31}N^{-3} + NL e^{-L^4/16}" |
| `etaVX N` | (s4:eqVXprob) "η_VX(N) := 2LN^{-5} + 2^{95}L^{28}N^{-3} + NL e^{-3L^2/(32 log₂L)} + L e^{-N/(5000L)}" |
| `TPVSize N := 2^10 ≤ L ∧ L^3 ≤ N ∧ etaTPV N ≤ 1/100` | TPV proof: "Size conditions. We use: (i) L ≥ 2^{10}; (ii) N ≥ L^3; (iii) 4·48 ≤ L (a consequence of (i)); (iv) η_TPV(N) ≤ 1/100." |
| `PVSize N` | PV proof: the same, with "(iii) 4·64 ≤ L" and η_PV |
| `VXSize N` | VX⁺ proof: the same, with "(iii) 4·13 ≤ L" and η_VX |
| `tpvJ N := ⌊logb 2 (L/6)⌋₊` | lemTPV "J := ⌊log₂(L/6)⌋" |
| `pvJ N := ⌊logb 2 (L/8)⌋₊` | lemPV "J := ⌊log₂(L/8)⌋"; also s3:defCOL(iii) "J_Y := ⌊log(L_Y/8)⌋" |
| `vxJ N := ⌊logb 2 (L/6)⌋₊` | thmVXp "J := ⌊log₂(L/6)⌋" |
| `pvM N := ⌈L^6⌉₊` | lemPV "m := ⌈L^6⌉" |
| `pvB N := ⌈2^7 L^2 m⌉₊` | lemPV "b := ⌈2^7L^2m⌉" |

Decisions.
- **D-VX-1 (N : ℕ).** The size predicates, the η's and the parameters take `N : ℕ`, since the manuscript's N is `|Z|`. A Spec writes `TPVSize Z.card`, with no cast. This deviates from the blueprints:
  - blueprint s4 proposed `TPVSize (N : ℝ)`;
  - blueprint s1 proposed `N0Cond (N0 : ℝ) := 2^40 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N → …`.

  The Gamma/Full author should write `N0Cond N0 := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N : ℝ) → TPVSize N ∧ PVSize N ∧ VXSize N`. That is exactly the manuscript's "for every N ≥ N_0", with N a vertex count.
- **D-VX-2 (condition (iii) omitted).** The manuscript calls (iii) "a consequence of (i)". The predicates list (i), (ii) and (iv), as TRIAGE §2.4 says, and the Lib derives (iii) (`TPVSize.cond_iii` etc.). So each predicate is equivalent to the full list (i)–(iv).
- **D-VX-3 (J).** `J = Nat.floor (logb 2 (L/c))`, which is the literal "⌊log₂(L/c)⌋".
  - For L ≥ c the real log is ≥ 0, so this is the manuscript floor. For L < c it is junk 0 (never used, since (i) gives L ≥ 1024).
  - Lib proves the bounds the proofs use: `tpvJ_bounds` (6·2^J ≤ L < 12·2^J, s4:eqTPVJ), `pvJ_bounds` (8·2^J ≤ L < 16·2^J, s4:eqPVJ), `vxJ_bounds`, `one_le_*J`, `*J_le_logb`.
  - Blueprint CONV-J-FLOOR's alternative, `Nat.log 2 ⌊L/c⌋₊`, was not used: it equals our definition for L ≥ c, but it is less literal.
- **D-VX-4 (run-specific names; CONV-SYMBOL-CLASH).** `tpvJ` and `vxJ` have the same formula but are separate definitions, since they are symbols of different runs. `vxJ_eq_tpvJ` is `rfl`.
- **D-VX-5 (scope).** Only `pvJ`, `pvM` and `pvB` occur in a statement:
  - the PV own classes are indexed by `Fin (pvJ N) × Fin 4`;
  - the PV hypotheses say `|A(w)| = m` and multiplicity ≤ b;
  - `tpvJ` and `vxJ` are included as the task asks.

  The other run parameters (k, m and b of TPV/VX⁺, and t) occur only inside proofs and belong in `EG/Lib/Vortex/Labels.lean`.
- **D-VX-6 (encoding).** `N^{-5}` and `N^{-3}` are `zpow` of `(N : ℝ)`. `e^x` is `Real.exp`. `log₂ L` in η_VX is `logb 2 (L N)`.

Lib API (`EG/Lib/Vortex/Params.lean`):
- `L_eq`, `L_nonneg`, `L_pow` (`L (2^k) = k`), `one_lt_of_L_pos`.
- `{TPV,PV,VX}Size.cond_i/.cond_ii/.cond_iii/.cond_iv/.one_lt`.
- `two_pow_floor_logb_le`, `lt_two_pow_floor_logb_succ`, `one_le_floor_logb`, `floor_logb_div_bounds`, `floor_logb_div_le_logb`, plus the J lemmas above.
- `le_pvM`, `pvM_lt`, `le_pvB`, `pvB_lt`.
- `exp_neg_le_two_rpow_neg` (e^{−x} ≤ 2^{−x}) and `two_pow_mul_exp_neg_le`.

## `EG/Defs/Lend/COLTable.lean` (s3:tabCOLJV; item (f) of Γ1; s3:lemCOLJVev)

> [s1:condG1](f) "for every row of the COL-JV table (Table s3:tabCOLJV), every inequality in column 3 of that row holds at λ, where M̄ := (Aμ)^{2A} and k̄ := 192λ^3+(4/3)M̄^2 as in the caption of that table. (Row 13 is G\*, and the inequality of row 12 is item (c). … column 3 consists of 18 explicit inequalities, two in row 1, five in row 8 and one in each other row …)"

| Lean | manuscript text |
|---|---|
| `lam μ := 2^μ` (rpow) | caption "λ = 2^μ" |
| `Mbar μ := (Aexp·μ)^(2·Aexp)` | "M̄ := (Aμ)^{2A}, with A = 105" |
| `kbar μ := 192 λ^3 + 4/3 M̄^2` | "k̄ := 192λ^3 + (4/3)M̄^2" |
| `row i μ`, `1 ≤ i ≤ 13` | column 3 of row i, verbatim (the full list is quoted in the file header and next to each match arm) |
| `col3 μ := ∀ i, 1 ≤ i → i ≤ 13 → row i μ` | Γ1(f) at μ |
| `triple i` | column 4 "(a_i,b_i,c_i)" |
| `TypeE a b c μ := 0 ≤ aμ − b − c·log₂(Aμ)` | lemCOLJVev "of type (E) if it reads aμ − b − c log(Aμ) ≥ 0" |
| `v0 a b c := (c + √(c^2 + a(b + c log₂A)))/a` | lemCOLJVev(i) "v_0 := (c+(c^2+a(b+c log A))^{1/2})/a" |

I re-checked the 18 column-3 inequalities against the TeX (s3.tex:1143–1160). Row 1 is strict (two inequalities), row 8 has five, and every other row has one.

Decisions.
- **D-COL-1 (numbering; deviation from blueprint s3b).** `row : ℕ → ℝ → Prop` is numbered 1…13 as in the manuscript, instead of the blueprint's `Fin 13` (0-based), to avoid off-by-one errors in reviews.
  - `row 0` and `row i` for `i ≥ 14` are `True`, and `triple` is `(0,0,0)` there (junk; `TypeE 0 0 0 μ` is true as well).
  - `col3` quantifies over `1 ≤ i ≤ 13` only.
  - `col3_iff` spells out the 13-fold conjunction, and `row1_iff` … `row13_iff` give each row explicitly (all `Iff.rfl`).
- **D-COL-2 (exponents).** The decimal exponents are exact rationals under `Real.rpow` of `λ > 0`: 205/2, 1/2, 421/10, 322/5, 33/10, 8/5. Integer exponents are `npow`. `M̄` has the ℕ exponent `2·Aexp = 210`, and row 13 has `46·Aexp = 4830`.
- **D-COL-3 (A = `EG.Aexp`).** A is `EG.Aexp` (s1:defConstants(i)), not the literal 105, so that row 13 is **definitionally** `EG.Gamma1e` (`row13_iff_gamma1e : row 13 μ ↔ Gamma1e μ := Iff.rfl`). This is the manuscript's "Row 13 is G\*".
  - "the inequality of row 12 is item (c)" is `row12_iff_gamma1c` (for μ > 0; proved by taking log₂).
- **D-COL-4 (column 2 not here).** The requirements of column 2 are informal in the table. They are asserted in precise form by the COLJV Spec (blueprint s3b C1–C13, hazard TAB-COL2-INFORMAL). The column-4 triples are data only; they are not part of Γ1.
- **Name.** Following TRIAGE §2.4 there is one table predicate, `EG.COLTable.col3`. The Gamma/Full author defines `Gamma1f D := ∀ μ ≥ log₂log₂D, COLTable.col3 μ`. The name `EG.S3.COLJVcol3` is dropped.

Lib API (`EG/Lib/Lend/COLTable.lean`): `lam_eq`, `lam_pos`, `Mbar_eq`, `Mbar_nonneg'` (every real μ), `Mbar_nonneg`, `kbar_eq`, `kbar_pos`, `row1_iff` … `row13_iff`, `row_zero`, `row_of_gt`, `col3.row`, `col3_iff`, `row13_iff_gamma1e`, `row12_iff_gamma1c`, `triple_spec` ("a_i > 0 and b_i, c_i ≥ 0").

## Tests (`EGTest/Params.lean`)

- **(eqStar) at n = 2, ρ = ε′ = t = 1** (so L = 1, ℓ_\* = 1024, p_\* = 1): d = 1, λ = 6, Δ = 8, σ = 24, g = 1/8, θ = 2^39 (the (S4) upper bound 2^{39}L^9/(ε′ρ^2) is attained), μ = 1/(6·2^39), s̄ = 2^28, K = 6·2^67 = s̄/μ (the (S5) lower bound is attained).
- **Other (eqStar) values.** ℓ_\*(4) = 8192; M_\*(1) = 3, M_\*(1/2) = 5, M_\*(1/10) = 21.
- **p_\* at ρ = 1/2.** (1−p)^{1023} = 10/11, 0 < p < 1, and uniqueness.
- **Vortex at N = 2^1024** (L = 1024):
  - tpvJ = vxJ = 7 and pvJ = 7, with the (s4:eqTPVJ)/(s4:eqPVJ) bounds; pvM = 2^60 and pvB = 2^87.
  - **`TPVSize`, `PVSize` and `VXSize` all hold at 2^1024.** This is the non-vacuity of the size predicates. No numeral 2^1024 is evaluated: large powers are compared through their exponents, and e^{−x} ≤ 2^{−x} handles the tails.
- **Negative Vortex tests.** `¬TPVSize 2` and `¬VXSize (2^1023)` (both fail condition (i)).
- **COL table.**
  - Values: λ(0) = 1, λ(10) = 1024, M̄(0) = 0, k̄(0) = 192.
  - Row 1 fails at μ = 0, hence `¬col3 0`; row 4 holds at μ = 20.
  - There are no rows 0 and 14; row 13 ↔ Γ1(e) and row 12 ↔ Γ1(c).
  - Column 4: sample triples. For row 1, TypeE(1/2,112,0) holds at μ = 224 and fails at 223, and v_0^2 = 224 (consistent with lemCOLJVev(i)).

## Not done / follow-ups

- **Eventuality of the size predicates.** `∀ᶠ N in atTop, TPVSize N ∧ PVSize N ∧ VXSize N` is the input to `EG.exists_N0` (TRIAGE §3 item 14). It is not proved here; only the single point N = 2^1024 is.
  - A route: show that every η term is ≤ 2^{-20} whenever L ≥ 2^10. Use log₂L ≤ L/16 for L ≥ 1024, via ln y ≤ 4y^{1/4}, together with `two_pow_mul_exp_neg_le`. Then `TPVSize N ↔ 2^10 ≤ L N`, which is the blueprint remark "every size condition follows from (i)".
  - Estimated at 150–250 lines. It belongs with Gamma/Full, where it is a **required** lemma `EG.Vortex.eventually_size` (TRIAGE §3 item 14; fix round 2).
- **(S1)–(S6) and the (S2) union law.** These are Spec material (`StarFactsStatement`, `StarUnionLawStatement`, blueprint s3a) and are not proved here. The Lib provides the definitional characterizations they need.
- **Manuscript.** No defect found; there is no T1/T2 item. The only reading choice is D-STAR-1 (explicit p_\*), which the Lib shows is equivalent to the text.

## Fix round 1 (review `work/p2d/params.review1.md`, verdict APPROVE; 3 minor, 4 cosmetic)

All seven items verified; six fixed, one (C4) is for the orchestrator. No Defs file changed.

| Item | Verdict | Action |
|---|---|---|
| M1 (TRIAGE/blueprints show real-argument size predicates, `EG.S4`, `pvJ` via `Nat.log`) | valid | TRIAGE §2.4 now records D-VX-1: `N : ℕ`, Specs write `EG.Vortex.TPVSize O.card`, namespace `EG.Vortex`, `pvJ N = ⌊logb 2 (L N / 8)⌋₊`, and `N0Cond (N0 : ℝ) := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N : ℝ) → Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N`, marked as superseding blueprint s1:1271 and s4:122–126, 187, 272, 348. I re-checked in a scratch file that this `N0Cond` shape and `TPVSize s.card` elaborate. Also a bullet in CONVENTIONS.md. The blueprints themselves were not edited (TRIAGE is binding over them). |
| M2 (no positive `col3` test) | valid | The reviewer's witness is in `EGTest/Params.lean`, namespace `EGTest.Params.Col3Witness`, plus `example : col3 8192`. One change: in row 8(d) the step `… ; ring` evaluated `2^49158` (an "exponent exceeds threshold" warning); it now generalizes `2^(8193*6)` before `norm_num; ring`, so the file builds with 0 warnings. Γ1(f) is thus non-vacuous at μ = 2^13. |
| M3 (no `K_pos`) | valid | `EG/Lib/Link/Star.lean`: `ell_pos (hn : 2 ≤ n) : 0 < ell n`, `K_pos (hn : 2 ≤ n) (hε : 0 < ε') (h0 : 0 < ρ) (ht : 0 < t) : 0 < K n ε' ρ t` (`Nat.ceil_pos` with `sbar_pos`, `theta_pos`, `L_pos`), and `K_ne_zero` (for `NeZero`, needed by `Fin (K …)` colourings). Tests: `0 < K 2 1 1 1`, a `NeZero (K 2 (1/2) (1/2) 1)` instance term, `0 < ell 2`. |
| C1 (shared short names) | valid | CONVENTIONS.md: never `open` more than one of `EG.Star`, `EG.Vortex`, `EG.COLTable`; use qualified names. |
| C2 (junk rows 0 and ≥ 14) | valid | CONVENTIONS.md: always bound the row index by `1 ≤ i ≤ 13` or use `col3`. D-COL-1 unchanged. |
| C3 (`1.6` vs `8/5`) | valid, no code change | Noted in CONVENTIONS.md (bridge `row12_iff_gamma1c`). |
| C4 (root imports) | valid, orchestrator | Not done by me (root files are off limits). Still to add: to `EG.lean` `EG.Defs.Link.Star`, `EG.Defs.Vortex`, `EG.Defs.Lend.COLTable`, `EG.Lib.Link.Star`, `EG.Lib.Vortex.Params`, `EG.Lib.Lend.COLTable`; to `EGTest.lean` `EGTest.Params`. |

Checks after the fixes: `lake build EGTest.Params` succeeds with 0 errors and 0 warnings (the witness compiles in about 8 s);
`scripts/check.sh EG/Lib/Link/Star.lean` rc=0; `python3 scripts/lint.py`: 0 findings; axiom scan
(`--prefix EG EG.Lib.Link.Star EG.Lib.Vortex.Params EG.Lib.Lend.COLTable`): 258 constants, 0 `sorryAx`, 0 violations.
Files touched: `EG/Lib/Link/Star.lean`, `EGTest/Params.lean`, `CONVENTIONS.md`, `work/p2/TRIAGE.md` (§2.4), this note.

## Fix round 2 (review `work/p2d/params.review2.md`, verdict APPROVE; 2 minor, 3 cosmetic)

All five items verified. Three are fixed in Lean, two are recorded (one needs the orchestrator). No Defs file changed.

| Item | Verdict | Action |
|---|---|---|
| m1 (root imports; carried over from C4) | valid, orchestrator | Root files are off limits for me, so this is not done here. Still to add: to `EG.lean` `EG.Defs.Link.Star`, `EG.Defs.Vortex`, `EG.Defs.Lend.COLTable`, `EG.Lib.Link.Star`, `EG.Lib.Vortex.Params`, `EG.Lib.Lend.COLTable`; to `EGTest.lean` `EGTest.Params`. The seven files must also be committed. |
| m2 (`eventually_size` unproved; `N0Cond` depends on it) | valid | Now recorded as a **required** Lib lemma on the Gamma/Full task: TRIAGE §3 item 14 gives the name `EG.Vortex.eventually_size`, the statement, the dependency (`EG.exists_N0` and every s5–s7 Spec with `N0Cond`) and the proof route. The "Not done" section above points there. I have not proved it (this is Gamma/Full scope, estimated at 150–250 lines). |
| c1 (`Mbar_nonneg` hypothesis) | valid | `EG/Lib/Lend/COLTable.lean`: new `Mbar_nonneg' (μ : ℝ) : 0 ≤ Mbar μ`, proved by `(even_two_mul Aexp).pow_nonneg _`. `Mbar_nonneg` is kept for any concurrent callers (its hypothesis is now unused, `_hμ`); it is derived from the new lemma and its docstring points to it. The three uses in `EGTest/Params.lean` now call `Mbar_nonneg' _`. |
| c2 (private `exp_pos` shadows `Real.exp_pos`) | valid | Renamed to `one_div_ell_sub_one_pos` in `EG/Lib/Link/Star.lean`, with both call sites updated. |
| c3 (`kown ≥ 1` from the `pvJ` junk value) | valid | There is no Stage1/COL design note yet (item 15 has not started), so I put the sentence where its author has to read: TRIAGE §2.7 (1a `col`) and TRIAGE §3 item 15 ("design note must state …"). The sentence: `kown Y = 4·pvJ|Y| + 1 ≥ 1` for every ancestor because `pvJ` is a `Nat.floor` (0 when `L_Y < 16`), so `Fin (kown Y)` is never empty and needs no guard. |

Checks after the fixes:
- `lake build EG.Lib.Link.Star EG.Lib.Lend.COLTable EGTest.Params`: success, 0 errors, 0 warnings.
- `python3 scripts/lint.py`: 0 findings.

Files touched: `EG/Lib/Link/Star.lean`, `EG/Lib/Lend/COLTable.lean`, `EGTest/Params.lean`, `work/p2/TRIAGE.md` (§2.7, §3 items 14 and 15), this note.
