# Clean-room review of the s3b Specs — lens: vacuity and consumer form (model B)

Reviewed 2026-09-30 against manuscript v6.1 `proofs/manuscript/s3.tex` (the authority), the
status file `work/p2s/s3b.md`, blueprint `work/p2/blueprint_s3b.md`, TRIAGE §2.4, §2.6–2.8,
CONVENTIONS.md, and the locked Defs the Specs use (`EG/Defs/Link/Star.lean`, `Link/HBFamily.lean`,
`Lend/COLTable.lean`, `Stage1/COL.lean`, `HB/Run.lean`, `Gamma/Core.lean`, `Gamma/Full.lean`,
`Expander.lean`, `Graph.lean`, `Walk.lean`, `Prob/FinDist.lean`). No Lean file was edited.

Files reviewed (all NEW): `EG/Spec/Link/L9rho.lean`, `EG/Spec/Link/HB.lean`,
`EG/Spec/Link/T16sForced.lean`, `EG/Spec/Lend/COLJV.lean`, `EG/Spec/Lend/COLJVev.lean`,
`EG/Spec/Stage1/COL.lean`, test `EGTest/Spec_s3b.lean`. Reused existing Specs read for
consistency: `T16s.lean`, `COLJVCount.lean`, `COLJVRows.lean`, `COLa.lean`, `COLc.lean`,
`Gamma/Sat.lean`.

**Verdict: approve.** No statement is unfaithful, vacuous or hides a hypothesis; Γ2(b),(c) are
never assumed. The findings below are cosmetic/minor notes for the record, none requiring a
change before the freeze.

Checks run: `python3 -I scripts/lint.py` → 0 findings; the six Spec `.olean`s are present;
`LEAN_NUM_THREADS=2 scripts/check.sh EGTest/Spec_s3b.lean 900` → rc=0, 0 errors, 0 sorry.

---

## 1. `L9rhoStatement` ([s3:lemL9rho])

**TeX.** "Let `G` be an `n`-vertex graph with `n ≥ 2^{30}`, put `L := log n`, and let `t ≥ 1`
and `ρ ∈ (0,1]`. Take `ℓ_*`, `s̄_*` and `M_* = ⌈2.1/ρ⌉` from (s3:eqStar). Let `V ⊆ V(G)` with
`|V| ≥ ρn/2`, and suppose `ρn ≥ 84`. Then `|V| ≥ n/M_*+2`. Suppose that
`|B^{ℓ_*}_{G-F}(U,V)| > |V|/2` for every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with
`|F| ≤ s̄_*|U|`. Then `G` is `(2^{12}L^4,t)`-path connected through `V` in the multiset sense."

**Back-translation of the Lean.** For every finite simple graph `G` (any vertex type), finite
vertex set `W ⊆ V(G)`, reals `ρ, t` with `2^{30} ≤ |V(G)|` (ℕ), `0 < ρ ≤ 1`, `1 ≤ t`,
`ρ|V(G)|/2 ≤ |W|`, `84 ≤ ρ|V(G)|`: (1) `|V(G)|/⌈2.1/ρ⌉₊ + 2 ≤ |W|` (reals); and (2) if for every
nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with `|F| ≤ (2^{28} t L^8/ρ)|U|` the ball
`B^{⌊2^{10}L^3⌋₊}_{G−F}(U,W)` has more than `|W|/2` elements, then `G` is
`(2^{12}L^4, t)`-path connected through `W` in the indexed-family (multiset) sense of Def 7
(`IsPathConnected`: every finite indexed family of pairs of distinct vertices of `G` with each
vertex in at most `t` entries gets edge-disjoint paths of length `≤ 2^{12}L^4` with interior in
`W`).

**Fidelity.** Quantifier order, strictness (`>` in the ball hypothesis, `≥` elsewhere), constants,
`log = log₂` (`Real.logb 2`, `Star.L`), `ℓ_*`, `s̄_*`, `M_*` as the locked (eqStar) terms, real `t`,
natural `n`: all match. The (eqStar) domain condition `ε' ∈ [2^{-7},1]` is void (none of the three
parameters depends on `ε'`); `n ≥ 2` follows from `n ≥ 2^{30}`. The conjunction reading
(conclusion 1 unconditional, conclusion 2 under the ball condition) is the TeX's ("Then … .
Suppose that … . Then …"). `U ⊆ V(G)`, `F ⊆ E(G)`, `W ⊆ V(G)` kept (CONVENTIONS: balls contain
`U ∩ W`). Verified by hand: `n/M_* ≤ ρn/2.1` and `ρn/2 − ρn/2.1 = ρn/42 ≥ 2` iff `ρn ≥ 84`.

**Vacuity.** Hypotheses before the ball condition are satisfiable (test file: edgeless graph on
`2^{30}` vertices, `W = V(G)`, `ρ = t = 1`). The ball condition is not self-contradictory: with
`U = W`, `F = ∅` the ball equals `W` (one-vertex paths), so `|W| > |W|/2`; it is satisfiable in
substance by graphs of minimum degree `> s̄_*` (the consumer's `X`). Conclusion (2) is nontrivial
(a graph with `≥ 2^{30}` vertices has admissible families).

**Consumer form.** Theorem 16* Step 4 (s3.tex 870–882) applies it with `G := X`, `n = N`,
`V` the random set (on the support `V ⊆ V(X)`, blueprint T16-AE-SUBSET), the same real `t` and
`ρ`, and derives exactly "`N ≥ 2^{30}`, `|V| ≥ ρN/2`, `ρN ≥ 84`" plus the ball condition for
"every nonempty `U` and every `F ⊆ E(X)` with `|F| ≤ s̄_*|U|`". Match.

## 2. `HBStatement` ([s3:lemHB])

**TeX.** "Let `X` be an `N`-vertex `(ε′,s)`-expander with `N ≥ 2` and `2^{-7} ≤ ε′ ≤ 1`, and
put `L := log N`. Let `m` be an integer with `1 ≤ m` and `2m ≤ s`, and put `b := ⌈2mL^2/ε′⌉`.
… Then every vertex `w` has a set `A(w) ⊆ N_X(w)` with `|A(w)| = m`, such that every vertex of
`X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`."

**Back-translation.** For every graph `X`, reals `ε', s`, natural `m`: if `X` is an
`(ε',s)`-expander, `|V(X)| ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `1 ≤ m`, `2m ≤ s` (reals), then there is
`A : V → Finset V` with `A w ⊆ N_X(w)` and `|A w| = m` for every `w ∈ V(X)`, and for every vertex
`u`, at most `⌈2 m L^2/ε'⌉₊` of the `w ∈ V(X)` have `u ∈ A w`.

**Fidelity.** Exact. `m : ℕ` for "an integer with `1 ≤ m`"; `b` is `Nat.ceil` of a positive real
(the TeX ceiling); the count is over indices `w ∈ V(X)` as the TeX says ("the sets `A(w)`,
`w ∈ V(X)`"); "every vertex of `X`" is `∀ u : V`, equivalent since `A w ⊆ N_X(w) ⊆ V(X)`. The
sentence "Thus `b = ⌈64L^2m⌉`, …" is an evaluation, correctly not stated. `ε' ≤ 1`, `ε' ≥ 2^{-7}`
kept although the proof needs only `ε' > 0` (HB-EPS-UNUSED): not a weakening.

**Vacuity.** Conclusion satisfiable and `|A w| = m` is not vacuous (test file on `K_2`). The
hypotheses need an explicit expander (not cheaply constructed; noted by the unit). The lemma is
true: re-derived the Hall argument (s3.tex 925–1010) including the `|S'| > 2N/3` case handled by
`U ⊆ S'` with `|U| = ⌈|S'|/2⌉ ≤ 2N/3` for `N ≥ 2`; `nbrSet` is the external neighbourhood, as
Def 11 needs.

**Consumer form.** `IsHBFamily` is the shared predicate: s5:defStages fixes `A_Y` as
`Classical.epsilon` of `IsHBFamily (X_Y) (vm) (vb)` (`EG/Defs/Light/Stages.lean`, Spec
`EG/Spec/Light/Stages.lean`), and the PV hypothesis reads `IsHBFamily O (pvM N) (pvB N) A`
(`EG/Defs/Probe/P4A/PVHyp.lean`). With `ε' = 2^{-6}`, HB's `b = ⌈2 m L^2 / 2^{-6}⌉₊` equals
`pvB N = ⌈2^7 L^2 m⌉₊` after the real identity `2·m·L^2/2^{-6} = 2^7·L^2·m` (one `norm_num`/`ring`
rewrite inside `Nat.ceil`). s4 applies HB with `ε' = 2^{-6}` or `ε_O ≥ 2^{-7}` and `2m ≤ s`
(s4.tex 213, 410, 470, 683): within the Spec's hypotheses.

## 3. `T16sForcedStatement` ([s3:thmT16s] (b))

**TeX.** "(b) If `N ≥ 2`, the hypotheses force `ρN > 2^{27}L^{5.6}N^{4/5}`, because `s < N`.
In particular the hypothesis `ρN ≥ L^2` is implied by the others."

**Back-translation.** For every graph `X` with `|V(X)| ≥ 2` that is an `(ε',s)`-expander,
`2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `1 ≤ t`, `2^{135} t L^{28} ρ^{-5} ≤ s` (without `ρN ≥ L^2`):
`2^{27} L^{28/5} N^{4/5} < ρN` and `L^2 ≤ ρN`.

**Fidelity.** The stronger reading (drop `ρN ≥ L^2`, conclude it) is what the "In particular"
sentence asserts; the weaker reading follows. Powers `5.6 = 28/5`, `4/5` are `Real.rpow`; `ρ^{-5}`
`zpow`, as in `T16sStatement`. Verified: `IsExpander ε' s` with `ε' > 0`, `N ≥ 2` and `U = {v}`,
`F = edges at v` (`1 ≤ 1 ≤ 2N/3`, `nbrSet` of `{v}` in `X − F` empty) forces `deg v > s`, hence
`s < N`; then `ρ^5 N > ρ^5 s ≥ 2^{135} t L^{28} ≥ 2^{135} L^{28}` (uses `t ≥ 1`), so
`(ρN)^5 > 2^{135} L^{28} N^4`, i.e. `ρN > 2^{27} L^{5.6} N^{4/5}`; and `L ≥ 1`, `N^{4/5} ≥ 1`
give `≥ L^2`. Matches the manuscript's Step 0 (s3.tex 838–847).

**Vacuity.** Not contradictory: e.g. `K_N` with `N ≥ 2^{400}`, `ε' = 2^{-7}`, `s = N/6` is an
`(ε',s)`-expander with `s ≥ 2^{135} L^{28}`; not cheaply certified in Lean (noted by the unit).
No consumer (blueprint T16-STEP0-NO-RPOW: optional); harmless.

## 4. `COLJV.lean` ([s3:lemCOLJV] (ii), Table s3:tabCOLJV)

Hypotheses of every statement: `Gamma1 Dstar → run.Valid G Dstar` (TRIAGE §2.6). No `Gamma2`,
no `N0`, no `Dstar ≤ d_1` (implied by `Valid` for every round `l ∈ [1,R]`, in particular whenever
an ancestor or a round exists). `Gamma1 = Gamma1core ∧ Gamma1f`; `Gamma2a` etc. never appear.

- **Col3** (`∀ r ∈ Icc 1 R, col3 (log₂ λ_r)`). TeX: "every inequality in column 3 holds at
  … `μ = log λ_r` and, for rows 2, 11, 12, also at `μ = log λ_{l-2}` for every round
  `3 ≤ l ≤ R`". Since `l − 2 ∈ [1, R−2]` is a round, one statement covers both. `col3` bounds
  `1 ≤ i ≤ 13` (no junk rows). True under Γ1(f): `d_r ≥ D_* > 2` gives
  `log₂ log₂ d_r ≥ log₂ log₂ D_*`.
- **Row 1** `τ_r < θ^GC_r(Z^0_a)` (ℕ) for every round-`r` pre-part address: TeX
  "`θ^GC_r(Z^0) > τ_r` … row 1 for every round-`r` pre-part". Match; consumer s2 (lemCap (iv),
  s2.tex 1165, 1297) uses the same form.
- **Row 2** `M_l^{13} ≤ P_{l−2}` (ℕ) for `3 ≤ l ≤ R`: match (`l − 2` exact). Consumers (s5.tex
  303, s6.tex 430, 600) cite it in this form via lemTower(b).
- **Row 3** three levels for every ancestor: lent `40 k_lend L_Y ≤ s_Y/4` (TeX column 2), split
  `80 L_Y ≤ s_Y`, own `40 k_own L_Y ≤ s_r/8` (TeX proof of row 3; scope bullet "rows 3 and 8 for
  every ancestor `Y`"). Asserting the own level also for standalone `Y` is a harmless
  strengthening (k_own is total, `k_own ≤ L_Y ≤ 2λ`, `λ^{100}/8 ≥ 160λ^2`), consistent with the
  existing `COLJVRow8Statement`. Consumer: Lemma COL (a) needs exactly these three (s3.tex
  1528–1546; s5.tex 128).
- **Row 5** `2^{135}·(3M)·L_Y^{28}·M^{20} ≤ s_Y/(8 k_lend)` with `M = M_{r+2}`, for `r ≤ R−2`:
  literal column 2. `k_lend ≥ 1` there (`I^JV ≠ ∅`), so no division junk.
- **Row 6** `Σ_{l ∈ [r+2,R]} Σ_{j < K^JS_l} 2^{86} t^JS_l L_Y^{19} ρ_l^{-3} N^{-3} ≤ N^{-2}/4`:
  the precise form of "T16* failures over `I^JS(Y)` sum to at most `|V(Y)|^{-2}/4`" with the
  T16* bound at `t = t^JS_l`, `ρ = ρ_l` (s3.tex row-6 derivation and Lemma COL (b), 1548–1566).
  Per-`l` values are `≤` the manuscript's `M`-bounds, so the derivation covers it. Consumer form
  of COL (b): match (the sum over `I^JS(Y)` via the injective tag `LentTag.JS`).
- **Row 9** `k_lend ≤ λ_r^{33/10}` for every ancestor ("trivially when `k_lend = 0`"): match.
- **Row 11** `2^{10} M_l^{10} ≤ λ_{l−2}^{95}/(8 M_l^2)`: literal; consumer s7:lemCand(iv)
  (s7.tex 148–151) uses this form.
- **Row 12** `M_l ≤ λ_{l−2}^{8/5}`: literal; consumer s5.tex 276 same form.
- **Row 13** `Gamma1e (log₂ λ_r)` for every round: G* at `λ_r`; `row 13 μ ↔ Gamma1e μ` by
  `Iff.rfl`. Redundant with Col3 (and with `Gamma1core`), but faithful to the table's row list.
- **`COLJVStatement`**: conjunction of (i) (`COLJVCountStatement`, includes row 10), Col3, rows
  1–9, 11–13 (4, 7, 8 from `COLJVRows.lean`). Projections checked in the test file.

Vacuity: `Gamma1 D ∧ run.Valid G D` satisfiable (test: empty run, `EG.gammaSat`); runs with
ancestors need `d ≥ D_*` under Γ1 (galactic, not certifiable). Every row is nontrivial for such
runs; none reduces to `True` under the stated bounds (`1 ≤ i ≤ 13`, `3 ≤ l ≤ R`, `Y.1+2 ≤ R`).

## 5. `COLJVev.lean` ([s3:lemCOLJVev])

- **(i)** `∀ a b c, 0 < a → 0 ≤ b → 0 ≤ c → (∀ μ, max 1 (v0 a b c)^2 ≤ μ → TypeE a b c μ) ∧
  ∀ᶠ μ in atTop, TypeE a b c μ`. TeX: type (E) "`aμ − b − c log(Aμ) ≥ 0` with reals `a > 0`,
  `b, c ≥ 0`" (`TypeE` is `0 ≤ aμ − b − c logb 2 (105 μ)`), "holds for every
  `μ ≥ max{1, v_0^2}`, `v_0 := (c + (c^2 + a(b + c log A))^{1/2})/a`" (`COLTable.v0` uses
  `Real.sqrt` and `logb 2 105`), "in particular for all sufficiently large `μ`". Exact. Verified
  true (with `v = √μ ≥ max(1, v_0)`: `log(Aμ) ≤ log A + 2v`, and `a v^2 − 2cv − (b + c log A) ≥ 0`
  for `v ≥ v_0`).
- **(ii)** `∀ μ ≥ 6, ∀ i, 1 ≤ i → i ≤ 13 → TypeE (triple i) μ → row i μ`. Exact; the row bound
  excludes the junk rows. Spot-checked rows 1, 2, 4–13 by hand (rows 2, 6, 11, 12, 13 are exact
  `2^{·}` identities; rows 3, 5, 9, 10 use that the (E) hypothesis forces `μ ≳ 4000`; row 5 is
  tight: `2^{72μ−1} + 2^{72μ−9} ≤ 2^{72μ}`). No counterexample.
- **(iii)** per row `∀ᶠ μ, row i μ` for `1 ≤ i ≤ 13`; all-rows form is the existing
  `Col3EventuallyStatement` (equivalent, 13 rows). Consumer of (iii) is s7:lemGammaSat through
  `col3` (already proved, `EG.col3_eventually`). (i), (ii) have no Lean consumer; they are the
  lemma's literal content.
- Vacuity: (i) hypotheses satisfiable; (ii) hypothesis satisfiable (test: row 4 at `μ = 10`) and
  `row 4` unfolds to the real inequality; conclusion satisfiable (`col3_of_le`).

## 6. `COL.lean` ([s3:lemCOL])

**TeX** (s3.tex 1453–1512; see file docstring). **Back-translation of `COLStatement`.** Under
Γ1, for every valid run and every ancestor `Y` (round `r = Y.1`, `N = |V(Y)|`):
1. `R ≤ r+1 → k_lend(Y) = 0` ("If `r ≥ R−1`, then `k_lend(Y) = 0`");
2. `COLe` (the (e) inequalities; deterministic);
3. every `ω` in the support of `colLaw Y` satisfies `COLg` ("Item (g) always holds": partition
   facts, read on the support — blueprint COL-G-MEANING; the consumer-exclusivity sentence is a
   design rule, not data);
4. for every finite probability space and `D` with law `colLaw Y`:
   `P(COLa ∧ COLb ∧ COLe) ≥ 1 − N^{-2}/2` ("(a), (b) and (e) hold simultaneously with
   probability at least `1 − |V(Y)|^{-2}/2`");
5. if `Y` is light: for every such `D`, every family `Vs` jointly independent of `D`
   (`IndepFun D Vs`) with `Vs · i` a `ρ i`-random subset of `V(Y)` and `ρ i ≥ 1/(12 L_Y^5)` for
   each `i ∈ I^U(Y)`: `P(COLa ∧ COLb ∧ COLc ∧ COLe) ≥ 1 − N^{-2}` ("For every family as in (c),
   items (a), (b), (c) and (e) hold simultaneously with probability at least `1 − |V(Y)|^{-2}`").

`COLLemmaStatement := COLStatement ∧ COLcStatement` (item (c) alone, existing).

**Fidelity.** Exact, with these readings, all justified: (c)'s family is stated for light `Y`
("Let `Y` be light"); for standalone `Y`, `I^U = ∅` so `COLc` is vacuous and 5 would follow from
4. "Every statement about lent classes is vacuous" needs no clause (empty index sets). `COLe`
conjoined inside the events as the TeX says. `N^{-2}` integer power. The bounds are those of the
TeX proof (`P(¬a) ≤ N^{-2}/4`, `P(a ∧ ¬b) ≤ N^{-2}/4`, U-union `≤ N^{-2}/4`, total `3N^{-2}/4 ≤
N^{-2}`; s3.tex 1590–1600).

**Consistency.** Same "any `μ` with `μ.map D = colLaw`" form and same `IndepFun`/`IsRSubset`
clauses as `COLcStatement`/`COLcIndexStatement` (TRIAGE §2.7). Light guard `run.isLight G Y.1 Y.2`
vs `Y ∈ run.lightParts G` in `COLcStatement`: equivalent for `Y ∈ ancestors`
(`lightParts = parts.filter isLight`) — a one-line bridge. `Dstar ≤ d_1` omitted (implied by
`Valid` once an ancestor exists); `COLLemmaStatement` conjoins `COLcStatement` with that
redundant hypothesis unchanged — acceptable.

**Vacuity.** Hypotheses satisfiable (empty run); law hypothesis satisfiable (`D = id`);
conjunct 3 is already a Lib theorem (`COLg_of_mem_supp_colLaw`) — faithful, not a defect;
conjuncts 4, 5 are nontrivial (`N^{-2}/2 ≤ 1/2`). Conjunct 1 duplicates the first conjunct of
`COLJVCountStatement` (both TeX statements assert it) — cosmetic.

**Consumer form.** s6:defLending/lemLent ("an event of (a) or (b) fails … at most
`|V(Y)|^{-2}/2` by Lemma COL", s6.tex 393, 428) is conjunct 4 for every ancestor; s6:thmMIXC
uses (a) and (e) for standalone `Z` (`Own_Z` a `(2^{-5}, s_l/4)`-expander, `s_l/4 ≥ 2^{150}L^{42}`:
`COLa`, `COLe` unfold to this with `ancEps = 2^{-5}`, `ancS = s_r`); s5:lemChild uses (a), (e) for
light `Z` (`s' = s_l/(16 k_own)`); s5:lemE1 (c) uses `COLcStatement` with the zone family (dependent
across indices, independent of the colouring — matches `IndepFun D Vs` with no cross-index
independence). Match in all cases. Lean Spec consumers so far: `EG/Spec/Light/Zones.lean`
mentions `colLaw`; no Spec restates Lemma COL's bounds (no duplication).

## 7. Cross-cutting checks

- **Γ2(b),(c)** never assumed; only `Gamma1` (which contains `Gamma1core`, the source of Γ2(a)).
- **Reuse / duplication.** Existing Specs reused, not restated: `T16sStatement`,
  `COLJVCountStatement` (row 10 inside), `COLJVRow{4,7,8}Statement`, `Col3EventuallyStatement`,
  `COLaProbStatement`, `COLcStatement`. Redundancies (row 13 ⊂ Col3; `k_lend = 0` clause in two
  Specs) are faithful repetitions of the TeX, not conflicting statements.
- **Integer vs real.** `n, N, m, M_l, P_l, s_r, τ_r, θ^GC, k_lend, k_own, t^JS_l, ℓ_*, M_*` are
  ℕ; `t, ρ, ε', s, s_Y, L, λ, μ` are ℝ; decimal exponents exact rationals with `Real.rpow`. Matches
  the manuscript's declared types ("`ℓ_*`, … `M_*` are integers"; "`m` an integer").
- **Log base.** `Real.logb 2` everywhere (s1:convGraphs (b)).
- **Hygiene.** lint 0; every `…Statement` docstring begins with the manuscript label and quotes
  the TeX; module headers `module` / `public import` / `@[expose] public section`; qualified
  names (`Star.M`, `COLTable.col3`, `Stage1.klend`) — CONVENTIONS "Parameters of s3/s4" respected
  (only `EG.HB` opened).

## 8. Notes for the record (no action required)

| # | Severity | Where | Note |
|---|---|---|---|
| 1 | cosmetic | `COL.lean` conjunct 1 / `COLJVCount.lean` | `R ≤ r+1 → k_lend = 0` stated twice (TeX states it in both lemmas). |
| 2 | cosmetic | `COLJV.lean` `COLJVRow13Statement` | Implied by `COLJVCol3Statement` (`row 13 μ ↔ Gamma1e μ` by rfl) and by `Gamma1core`; kept as the table's row 13. |
| 3 | minor | `COL.lean` conjunct 5 vs `COLc.lean` | Light guard written `run.isLight G Y.1 Y.2` here, `Y ∈ run.lightParts G` there; equivalent for ancestors, one bridge lemma for the proof unit. |
| 4 | minor | `COLJV.lean` rows 3 (own level), and existing row 8 | Asserted for standalone `Y` too (`k_own` total); a true strengthening of the column-2 scope, consistent with the "rows 3 and 8 for every ancestor" bullet. |
| 5 | minor | `HB.lean` vs `pvB`/`vb` | Consumers' `b = ⌈2^7 L^2 m⌉₊` equals HB's `⌈2 m L^2/2^{-6}⌉₊` only after a real rewrite inside `Nat.ceil`; trivial, but the HB proof/consumer bridge must supply it. |
| 6 | minor | `T16sForced.lean` | No consumer; stronger reading verified true. |

## 9. Mathematical findings

None. Re-derived: L9ρ's first conclusion; T16*(b) from `δ(X) > s`; the HB Hall argument
including the `|S'| > 2N/3` case; COL-JV-ev (i) and (ii) for every row (row 5 is tight but
holds); Lemma COL's probability accounting. No statement appears false and no manuscript step
appears wrong in this chunk.
