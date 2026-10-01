# Blocker M-INTEGER: M_l real in (R2), used as a count everywhere else

Status: **resolved by the proposed definition, classification T1** (definition/proof repair; no statement changes, no statement false).
Scope checked: every occurrence of `M_` in `proofs/manuscript/s1.tex`–`s7.tex` (v6), grep `M_` (313 lines, of which `M_I` in s1 and `M_*` in s3 are unrelated symbols), plus the `\bar M` bounds of Γ1 and the COL-JV table.

## 1. The defect

(R2) (s2.tex:511) defines `M_l := max(2^40, 2^16 T log^4 T)` with `T = d_l log^2 d_l`, a real number (in general irrational). The manuscript then uses M_l as a natural number:

- s3:defCOL (s3.tex:1048, 1075–1077, 1092): `K^JS_l := M_l^2` is the NUMBER of JS classes (`0 <= j < K^JS_l`), and the label law assigns probability `rho_l = M_l^-4` to each of the `K^JS_l` values with `P(*) = 1 - M_l^-2`. That needs `K^JS_l · rho_l = M_l^-2` exactly (s3.tex:1135, s6.tex:414, 426). With real M_l the index set `{0,...,K^JS_l - 1}` has `⌈M_l^2⌉` elements and the stated `P(*)` is wrong.
- s7:defSchedule / s7:consRound / s7:lemWellDef (s7.tex:183–184, 263, 270, 280–297, 338–351, 403, 436, 518, 808, 856, 1102): palettes `[3M_l]`, `[4M_l]`, bijections `eta_h : [4M_l] -> [4M_l]`, 3-subsets of `[4M_l]`, `K^HUB_l = 4M_l`, binomials `binom(K, s-1)`.
- s6:lemJSLC (s6.tex:464–605): `t^JS_l = 2M_l + 2`, depths `min(K^JS, ...)`, "`M_l - 1` cherry systems", pads `⌈(M_l-1)/2⌉ <= ⌈M_l/2⌉`, and `max(2M_l-2, (M_l-1)+⌈M_l/2⌉) = 2M_l-2` (an identity for integers `M_l >= 2`).
- s5:lemParent (s5.tex:244, 248): `ncl_l = 14(J̄_l+1)M_l` is an index range for classes.

So the manuscript as written is ill-defined at these places (not merely a Lean typing issue). Hence not T0.

## 2. Proposed repair (manuscript change to (R2))

    M_l := ⌈ max(2^40, 2^16 T_l log^4 T_l) ⌉ ∈ ℕ,   Λ_l := log_2 M_l (of this integer).

Everything else in (R2) unchanged (`s_l = ⌈Λ_l^σ⌉`, `τ_l = ⌈128 s_l log^2 M_l⌉`). Lean: `MOf d : ℕ := ⌈max (2^40) (2^16 * TOf d * logb 2 (TOf d) ^ 4)⌉₊` (as in blueprint_s2a.md:504). Also update the symbol table row s1.tex:1813.

The only two facts about the ceiling that are needed: (C1) `M_l >= max(2^40, B_l)`, `B_l := 2^16 T log^4 T` (all lower-bound uses); (C2) `M_l <= max(2^40, B_l) + 1` (the two upper-bound derivations below). Note that under Γ2(a) `B_l >= 2^16 · 2^117 · 117^4 > 2^160`, so the `2^40` branch never binds and `M_l = ⌈B_l⌉`.

## 3. Every use, checked with the integer definition

Legend: OK = statement and written proof unchanged (monotone lower bound, or inequality derived from `M_l <= d_l^2` / `M_l <= λ_{l-2}^{1.6}` / `M_l >= 2^40` / `M_{l-1} >= 2M_l`); PATCH = statement true, the written proof needs one extra line.

### s2

| where | use | verdict |
|---|---|---|
| s2:defHBtp (R2), 511–514 | definition | changed as in §2 |
| s2:lemCap(ii), 627–629, 662–673 | `|piece| <= 2^16 T log^4 T <= M_l`; `|Z^0| <= M_l`; degree `<= |Z^0|-1 <= M_l-1`; `τ_l >= 128 s_l log^2 M_l >= 128 s_l log^2 |piece|` | OK by (C1). Text: "M_l = max(...) by (R2)" (line 662) becomes "M_l >= max(...)". Trivial wording PATCH. |
| s2:propStructure(i), 761 | `M_r >= 2^16 T log^4 T >= T >= d_r`, so `Λ_r >= λ_r`, `s_r >= λ_r^100` | OK (C1) |
| s2:propDegRec, 911–980 | `M_l <= d_l^2`, `Λ_l <= 2x`, `s_l <= P_l`, `d_{l+1} <= ... <= 7x^103` | PATCH: the proof shows `max(2^40, B) <= 2^20 x^6 2^x <= 2^{2x}` and concludes `M_l <= 2^{2x}`. With the ceiling one needs `⌈B⌉ <= B + 1 <= 2^{2x}`, i.e. `2^x(2^x - 2^20 x^6) >= 1`, true since `x >= 2^256` gives `2^x >= 2^20 x^6 + 1` (`x >= 21 + 6 log x`). `d_l^2 = 2^{2x}` is not an integer in general, so this line is genuinely needed. All later lines use only `log M_l <= 2x`: OK. |
| s2:lemLacunary remark, 1049–1055 | `M_l <= λ_{l-2}^{1.6}` example | OK (not used) |
| s2:lemTower(b), 1139–1145, 1191–1228 | `M_r <= d_r^2`; `λ_r <= Λ_r <= 2λ_r`; `L_Y <= log M_r`; `M_l <= (A log λ_{l-2})^{2A} <= λ_{l-2}^{1.6}`; `P_{l-2} >= M_l^13`; `P_{l-2}/2 >= M_l log^4 M_l`; `M_{l-1} >= 2M_l`; `Σ 1/M_l <= 2/D_*`; `Σ ψ(M_l) <= 2.1 ψ(D_*)` | OK: all derived from `M_l <= d_l^2` (propDegRec, patched), `M_{l-1} >= d_{l-1}` (C1), `Λ_l >= 40`, `M_R >= d_R` (C1). `M_{l-1} >= d_{l-1} >= 2 y^{2A} >= 2 d_l^2 >= 2 M_l` unchanged. |
| s2:lemTower(c) | `τ_r <= 128 s_r Λ_r^2 + 1 <= 257 Λ_r^102`, `Λ_r <= 2λ_r` | OK |
| s2:propParentless, 1415, 1454–1456 | `P_{l-2}/2 >= M_l log^4 M_l >= |Z| L_Z^4`, `|Z| <= M_l` | OK |

### s1 (conditions, overview, tables)

| where | use | verdict |
|---|---|---|
| Γ2(b), 1590–1591 | `P_{l-2}/2 >= M_l log^4 M_l`, "including rounds with M_l = 2^40" | OK (= lemTower(b)); the `2^40` branch is vacuous under Γ2(a) either way |
| Γ4 pool term, 1640 | `Σ (6 log M_l + 12)/M_l <= 2.1 ψ(D_*)` | OK (lemTower(b)) |
| Γ1, 1556–1561 | only `\bar M = (Aμ)^{2A}`, no M_l | unaffected |
| overview 140–142, 345, 362, 434–448, 488–489 | informal restatements (`M_l - 1` pairs, `t_Y >= M_l`, multiplicity `2M_l-2`, `n/M_l` terms, density `M_l^-2`) | OK |
| tables 1813, 1839, 1861, 1881–1892, 1949–1952, 1996 | symbol table / fix log | 1813: record the ceiling (PATCH, editorial) |

### s3

| where | use | verdict |
|---|---|---|
| s3:defCOL(ii),(iv), 1048, 1075–1077, 1092, 1135 | `K^JS_l = M_l^2 ∈ ℕ` classes; `rho_l = M_l^-4`; `P(*) = 1 - M_l^-2`; `K^JS_l rho_l = M_l^-2 <= 1` | now well defined and exact (this is the point of the fix) |
| s3:defCOL, 1098–1103 | `t^JS_l = 2M_l + 2 ∈ ℕ`; `t_Y = ⌈λ_r^1.6⌉ >= M_l` from `M_l <= λ_{l-2}^1.6 <= λ_r^1.6` | OK |
| s3:lemCOLJV (B1) | `L_Y <= log M_r <= 2λ` | OK |
| (B2) | `M_l <= M = M_{r+2} <= \bar M`, `M_{l+1} <= M_l/2`, `M_l <= (A log λ_{l-2})^{2A}` | OK (lemTower(b)) |
| (B3)–(B5) | no M_l beyond `Λ_r` via lemTower(b) | OK |
| **(B6)** | `Λ_r <= λ + 6μ + 20` | **PATCH.** The written proof bounds `log(2^16 T log^4 T) <= 16 + λ + 2μ + 4(μ+1) = λ+6μ+20` using the crude `log T = λ+2μ <= 2λ`, i.e. it evaluates `log` of the real max with the bound attained exactly; with the ceiling, `Λ_r = log⌈B⌉` can exceed `log B`. Repair: `log⌈B⌉ <= log B + 1/(B ln 2) <= log B + 2^-160`, and `log B = 16 + λ + 2μ + 4 log(λ+2μ) <= λ + 6μ + 16 + 4 log(1 + 2μ/λ) <= λ + 6μ + 16.01` (μ >= 2^8 by Γ1(a), so 2μ/λ < 2^-240). Slack ≈ 4. Statement unchanged; the column-3 inequality of row 1 (`λ^102.5 > 257(λ+6μ+20)^102`) is unchanged. (Same note as blueprint_s3b COLJV-B6-CEILING.) |
| (B7) | `t^JS_l = 2M_l+2 <= 3M_l <= 3M` (M_l >= 2^40), `rho_l^-1 = M_l^4 <= M^4` | OK |
| (i) counting | `|I^JS(Y)| = Σ_{l>=r+2} M_l^2 <= (4/3) M^2` | OK (now a genuine cardinality) |
| rows 2, 5, 6, 11, 12 | `P_{l-2} >= M_l^13`; T16* with `t <= 3M`, `rho >= M^-4`; failure sum over `(4/3)M^2` classes; `λ^95/(8M_l^2) >= 2^10 M_l^10`; `M_l <= λ_{l-2}^1.6` | OK: every column-2 requirement is monotone increasing in M_l and column 3 is in `\bar M`; only `M_l <= \bar M` is used, which follows from `M_l <= d_l^2` |
| s3:lemCOL(b), 1450–1454, 1543–1552 | T16* with `t = t^JS_l`, `rho = rho_l`; `rho_l N >= \bar M^-4 λ^103/2 >= L^2` | OK |
| s3:lemCOLJVev | only `\bar M` | unaffected |

### s4
No occurrence of M_l (the per-vertex bound in s4:lemPV(c) is by the degree; the `M_l - 1` is applied in s5).

### s5

| where | use | verdict |
|---|---|---|
| s5:lemParent (ii), 219–223 | `4·14(J̄_l+1)M_l(M_l+1)ν_l + cap_l` | OK |
| (F-a), (F-b), (F-d), 241–244 | `|Z| <= M_l`, `L_Z <= log M_l`, `J_Z+1 <= log log M_l`, `ncl_l = 14(J̄_l+1)M_l` (now an integer index range), arc ends `<= |Z|-1 <= M_l-1` | OK |
| Step 5, 276–278 | `M_l <= λ_{l-2}^1.6 <= λ_r^1.6 <= ⌈λ_r^1.6⌉ = t_Y`, multiplicity `M_l - 1 < t_Y` | OK |
| Step 9, 299–309 | `(ν_l-1)(M_l-1)`, `M_l+1 <= 2M_l`, `J̄+1 <= log log M_l <= M_l`, `P_{l-2} >= M_l^13` → `307 n/M_l`, `Σ <= 614 n/D_*`; `log M_l <= 2A log(A log λ_{l-2})` | OK |

### s6

| where | use | verdict |
|---|---|---|
| s6:defDesign, 254 | `γ_l = ⌊P_{l-2}/M_l⌋` | OK |
| s6:defLending, 403 | `X_U = ... + Σ (169 + M_l)|Lost_l|` | OK |
| s6:lemLost(i), 414, 426, 430 | `P(u ∈ Lost) <= K^JS_l rho_l + P(lend-bad) <= M_l^-2 + 2|V(Y)|^-2 <= 2M_l^-2`; `K^JS_l rho_l = M_l^2 · M_l^-4 = M_l^-2`; `2|V(Y)|^-2 <= 8 M_l^-26 <= M_l^-2` | OK, exact (no `+ M_l^-4` fallback term needed) |
| (K6), (iii), 416–438 | `E|Lost_l| <= 2n/M_l^2`; `Σ (338n/M_l^2 + 2n/M_l) <= (2 + 338/2^40)·2n/D_* <= 5.5n/D_*` | OK |
| s6:lemJSLC, 450–605 | `126 n/M_l`; `sco = (3g - 6M_l)^+`; `(M_l-1)|Lost_Z|`; degrees `<= M_l - 1`; `pad <= ⌈(M_l-1)/2⌉ <= ⌈M_l/2⌉`; demand `<= (M_l-1)+⌈M_l/2⌉`; `g <= m/2 + 2M_l - 4`; `k_0, k_i = min(K^JS, ...)`, `j < K^JS`; claim (c) `max(2M_l-2, (M_l-1)+⌈M_l/2⌉) = 2M_l-2 <= t = 2M_l+2` (integer identity for M_l >= 2); Step 8: `0.75, 13.7, 0.5` n/M_l and `16.44 n/M_l^12`, `14.95 + 16.44 M_l^-11 <= 15` | OK (all integer statements now literally true; numerics independent of integrality) |
| s6:lemJplus (J2), (ii), 636–658 | at most `M_l - 1` J-edges per vertex per part | OK |
| s6:thmMIXC, 786, 858–860 | `Σ 126 n/M_l <= 252 n/D_*` | OK |

### s7

| where | use | verdict |
|---|---|---|
| s7:defPool, 34–45 | `q_l = M_l^-2`, `Σ_l q_l <= Σ 1/M_l <= 2/D_* < 1` | OK |
| s7:defCand, 66; s7:lemCand (ii),(iv), 88–152 | `Hcd_l = λ_{l-2}^95/(8M_l^2)`; `E|Cand| >= λ_r^96 2^{-(l-r)}/M_l^2 >= 2Hcd_l` (M_l cancels); `Hcd_l >= 2^10 M_l^10` via `M_l <= λ_{l-2}^1.6`, `λ_{l-2} >= M_l^{1/1.6} >= 2^25` | OK |
| s7:defSchedule, 183–184, table 205–228 | `eta_h : [4M_l] -> [4M_l]` bijection, `zeta_{h,u}` 3-subset of `[4M_l]` | now well defined (point of the fix) |
| s7:consRound, 263–351 | PAR palette `[3M_l]`; `θ_ult = ⌊M_l Hcd_l/7⌋`; `K^HUB_l = 4M_l`; lists `{eta(3i-2), eta(3i-1), eta(3i)} ⊆ [4M_l]` needing `3k_h <= 4M_l`; `Used_κ(h)`, `κ ∈ [4M_l]`; layers `κ ∈ [3M_l]`, `[4M_l]` | well defined; side conditions proved in lemWellDef |
| s7:lemWellDef (i)–(v), 395–507 | `2(M_l-2) + (M_l-1)/2 < 3M_l`; `k_h <= ⌈8M_l/7⌉`, `3k_h <= 24M_l/7 + 3 <= 4M_l` (needs `M_l >= 21/4`); SDR union bound with `m <= M_l - 1 <= K/4`, `K = 4M_l >= 2^42 >= 10^4`, `binom(K, s-1)`, `s <= K+1`; `Hcd - (M_l - 2) - Hcd/8 > 0`; `Hcd - (M_l-1) >= Hcd/2 >= M_l > |E'(u)|` | OK (binomials now have integer K; every inequality needs only `M_l >= 2^40` and `Hcd_l >= 2^10 M_l^10`). The "near M_l = 19" numerics remark is marked not used. |
| s7:lemCC, 706–801 | `|J_l| <= n(M_l-1)`, `≤ 1.37 n M_l` objects; `t_CC = ⌈2 log M_l⌉`, `2^{-t} <= M_l^-2`; sum over `3M_l |Pool_l|` pairs; `3M_l(t_CC+1)|Pool_l| + 44.7 nM_l/Hcd + 29.8 n/M_l` | OK |
| s7:lemUltra, 808–878 | `4M_l` colours; `M_l Hcd_l/7 = λ^95/(56 M_l)`; `θ_ult >= λ^95/(57M_l)`, `θ_ult >= 2^8`; `312.36 + 7.5 < 320` | OK |
| s7:lemVstar, 884–909 | `X_V = 3M_l(t_CC+1)|Pool_l| + 4M_l Σ mult`; `E X_V <= (6 log M_l + 11.48) n/M_l`; `Σ ψ(M_l) <= 2.1 ψ(D_*)` | OK |
| s7:lemPay, 917–979 | `(M_l-1)|Lost_l|`; `ω_l(v) = M_l`; SDR `n(M_l-1)(4M_l)^-4 <= n/(256 M_l^3)`; `176 M_l^3/λ^95 <= λ^-1.6 <= 1/M_l`; `payrd_l <= 2n/M_l`, `Σ <= 4n/D_*` | OK |
| s7:defXprime / lemEXprime, 987–1048 | `X_pool` with `(M_l-1)·#JV-bad`; `q_l(Σ c_agg + n M_l) <= 2.37 n/M_l`; `exp(-Hcd/4) <= M_l^-3`; `(M_l-1) n M_l^-3 <= 0.03 n/M_l`; `Σ 2.4n/M_l <= 4.8n/D_*` | OK |
| s7:lemUHsplit, 1055–1135 | `det_l` terms `78 nM_l/Hcd`, `30 n/M_l`, `320 nM_l^3(log θ_ult + 8)/λ^95`; `Σ 30n/M_l <= 60n/D_*`; `M_l <= λ_{l-2}^1.6`, `λ_{l-2} >= 2^25`; F-sum | OK |
| s7:propCost, cost line (table s7:tabCost), 1240–1312 | `Σ_l (M_l-1)|Lost_l|`, `Σ(169 + M_l - 1)|Lost_l| + X_pool <= X_U + X_pool <= X'` | OK |
| s7 remarks, 1575 | multiplicity `2M_l - 2` | OK |

## 4. Result

- **No inequality fails** with `M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ ∈ ℕ`. Every use is either a lower bound on M_l (preserved by (C1)), a consequence of the four derived facts `M_l <= d_l^2`, `M_l <= (A log λ_{l-2})^{2A} <= λ_{l-2}^1.6`, `M_{l-1} >= 2M_l`, `M_l >= 2^40` (all re-proved under the ceiling), or an integer statement that is only well defined (or only an identity) for integer M_l.
- **Proof patches required** (statements unchanged):
  1. s2:propDegRec: `⌈B⌉ <= B + 1 <= 2^{2x}` (needs `2^x >= 2^20 x^6 + 1`; slack is huge).
  2. s3:lemCOLJV (B6): `log⌈B⌉ <= log B + 2^-160` and the true value `4 log(λ+2μ) <= 4μ + 0.01` in place of the crude `4(μ+1)`; slack about 4.
  3. s2:lemCap(ii) wording "M_l = max(...)" to "M_l >= max(...)"; s1 symbol table row 1813.
- **Exactness gained:** `K^JS_l rho_l = M_l^-2` holds exactly, so s6:lemLost(i) needs no `+M_l^-4` term (the fallback "ceilings at each use" of blueprint_s2a is not needed and is not recommended: it would change the label law and lemLost(i)).
- **Lean encoding:** `MOf d : ℕ`; state real inequalities with the cast `(MOf d : ℝ)`; `Λ_l = logb 2 (MOf d : ℝ)`; `K^JS := MOf^2 : ℕ`, `K^HUB := 4 * MOf : ℕ`, palettes `Fin (3*M)`, `Fin (4*M)`; `t^JS := 2*M+2 : ℕ`.

## 5. Classification

**T1 (minor).** The manuscript's (R2) is inconsistent with its uses (a genuine manuscript defect, not only a Lean encoding choice, so not T0): as written, `[4M_l]`, `K^JS_l` classes and the JS label law are ill-defined for non-integer M_l. The repair is a one-token definitional change (a ceiling in (R2)) under which every statement of s1–s7 that mentions M_l stays true as stated, and only two proof lines (propDegRec's `M_l <= d_l^2`, COL-JV (B6)) plus one wording need adjustment, each with large slack. No statement is false (not T2), nothing is fatal (not T3). The decision unblocks EG/Defs/HB/Run.lean (MOf), EG/Defs/Lend/COL.lean (KJS) and the s7 round-step definitions.

Affected labels (text changes): s2:defHBtp, s2:lemCap, s2:propDegRec, s3:lemCOLJV, s1:tabSymbols. Dependent (no text change, re-checked): s2:propStructure, s2:lemTower, s2:propParentless, s1:condG2, s1:condG4, s3:defCOL, s3:lemCOL, s5:lemParent, s6:defDesign, s6:defLending, s6:lemLost, s6:lemJSLC, s6:lemJplus, s6:thmMIXC, s7:defPool, s7:defCand, s7:lemCand, s7:defSchedule, s7:consRound, s7:lemWellDef, s7:lemCC, s7:lemUltra, s7:lemVstar, s7:lemPay, s7:defXprime, s7:lemEXprime, s7:lemUHsplit, s7:propCost.
