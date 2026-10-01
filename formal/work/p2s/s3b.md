# P2 Specs, chunk s3b (Lemma 9_ρ, Theorem 16*, Lemma HB, COL-JV, COL): status

Manuscript v6.1 `proofs/manuscript/s3.tex` lines 692–1600 (a CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s3b.md`, `nodes_s3b.json`; data model TRIAGE §2.4 (col3, Γ1), §2.6
(s3 COL/COLJV take `Gamma1 D ∧ run.Valid G D`), §2.7 (Stage-1 law, "any μ with `μ.map D = colLaw`",
joint `IndepFun` for (c)), §2.8 (HB-FAMILY).

Result: 6 new Spec modules (22 new `…Statement` defs, 4 of them conjunctions that name a whole
lemma), 1 test file. No new Defs. No proofs, no stubs. No existing file edited. Existing Specs of
this chunk (T16*, COL-JV (i) and rows 4/7/8, COL-JV-ev (iii), COL (a)-bound and (c)) were reused
and are imported where the whole lemma is named.

Build and check:
- `lake build EG.Spec.Link.L9rho EG.Spec.Link.HB EG.Spec.Link.T16sForced EG.Spec.Lend.COLJVev`
  and `lake build EG.Spec.Lend.COLJV EG.Spec.Stage1.COL` succeed.
- `scripts/check.sh EGTest/Spec_s3b.lean` gives rc=0, 0 errors, 0 sorry (no warnings).
- `python3 -I scripts/lint.py` reports 0 findings.

Root imports for the orchestrator to add (I did not edit the root files):
- to `EG`: `EG.Spec.Link.L9rho`, `EG.Spec.Link.HB`, `EG.Spec.Link.T16sForced`,
  `EG.Spec.Lend.COLJV`, `EG.Spec.Lend.COLJVev`, `EG.Spec.Stage1.COL`;
- to `EGTest`: `EGTest.Spec_s3b`.

## Files

| File | Contents |
|---|---|
| `EG/Spec/Link/L9rho.lean` (new) | `L9rhoStatement` |
| `EG/Spec/Link/HB.lean` (new) | `HBStatement` |
| `EG/Spec/Link/T16sForced.lean` (new) | `T16sForcedStatement` (T16* item (b)) |
| `EG/Spec/Lend/COLJV.lean` (new) | `COLJVCol3Statement`, `COLJVRow{1,2,3,5,6,9,11,12,13}Statement`, `COLJVStatement` (whole lemma) |
| `EG/Spec/Lend/COLJVev.lean` (new) | `COLJVevTypeEStatement` (i), `COLJVevRowsStatement` (ii), `COLJVevEventuallyRowStatement` (iii per row), `COLJVevStatement` (whole lemma) |
| `EG/Spec/Stage1/COL.lean` (new) | `COLStatement` (probability bounds, (e), (g), the `k_lend = 0` clause), `COLLemmaStatement` (= `COLStatement ∧ COLcStatement`) |
| `EGTest/Spec_s3b.lean` (new) | non-vacuity checks |

## Table: label → Lean name → file → status

| label (kind) | Lean name | file | status |
|---|---|---|---|
| s3:lemL9rho (lemma) | `EG.Spec.L9rhoStatement` | `EG/Spec/Link/L9rho.lean` | **new** |
| s3:thmT16s (theorem), main statement | `EG.Spec.T16sStatement` | `EG/Spec/Link/T16s.lean` | existing (probe P4B). Reused; checked against the TeX, no problem. |
| s3:thmT16s (b) | `EG.Spec.T16sForcedStatement` | `EG/Spec/Link/T16sForced.lean` | **new** (no consumer; (a) is reflected by `T16sStatement` having no hypothesis on `N`; (c) is a proof remark, TRIAGE T16-C-META, not formalized) |
| s3:lemHB (lemma) | `EG.Spec.HBStatement` (conclusion `EG.IsHBFamily`, locked Defs `EG/Defs/Link/HBFamily.lean`) | `EG/Spec/Link/HB.lean` | **new** |
| s3:defCOL (definition) | Defs `EG.Stage1.*` | `EG/Defs/Stage1/COL.lean` | existing Defs (locked). No Spec (a definition). Embedded claims: "`t_Y ≥ M_l` for `r+2 ≤ l ≤ R`" is stated in consumer form by `EG.Spec.MlTyStatement` (`EG/Spec/Light/ParentRun.lean`, s5 setting); "label law well defined" is `EG.Stage1.jsWeight_sum` (Defs); the "Consequently" bullets (`T_j` disjoint, `ρ_l`-random, independent of the colouring, restricted colourings) are Lib API facts (`EG/Lib/Stage1/COL.lean`, e.g. `disjoint_Tj`), as the blueprint prescribes (COL-EMBEDDED-FACTS). |
| s3:tabCOLJV (table, supporting) | Defs `EG.COLTable.{lam, Mbar, kbar, row, col3, triple, TypeE, v0}` | `EG/Defs/Lend/COLTable.lean` | existing Defs (locked). No Spec (a table). Column 2 is asserted by the COL-JV Specs below. |
| s3:lemCOLJV (i) | `EG.Spec.COLJVCountStatement` (also contains row 10, "`p_Y ≥ λ^{-4}`") | `EG/Spec/Lend/COLJVCount.lean` | existing (probe P4A). Reused. |
| s3:lemCOLJV (ii), rows 4, 7, 8 | `EG.Spec.COLJVRow4Statement`, `COLJVRow7Statement`, `COLJVRow8Statement` | `EG/Spec/Lend/COLJVRows.lean` | existing (probe P4A). Reused. |
| s3:lemCOLJV (ii), column 3 | `EG.Spec.COLJVCol3Statement` | `EG/Spec/Lend/COLJV.lean` | **new** |
| s3:lemCOLJV (ii), rows 1, 2, 3, 5, 6, 9, 11, 12, 13 | `EG.Spec.COLJVRow{1,2,3,5,6,9,11,12,13}Statement` | `EG/Spec/Lend/COLJV.lean` | **new** |
| s3:lemCOLJV (whole) | `EG.Spec.COLJVStatement` (conjunction of all of the above) | `EG/Spec/Lend/COLJV.lean` | **new** |
| s3:lemCOLJVev (i) | `EG.Spec.COLJVevTypeEStatement` | `EG/Spec/Lend/COLJVev.lean` | **new** |
| s3:lemCOLJVev (ii) | `EG.Spec.COLJVevRowsStatement` | `EG/Spec/Lend/COLJVev.lean` | **new** |
| s3:lemCOLJVev (iii) | `EG.Spec.Col3EventuallyStatement` (all rows at once; proved, `EG.col3_eventually`) and `EG.Spec.COLJVevEventuallyRowStatement` (per row, literal) | `EG/Spec/Gamma/Sat.lean` (existing, unit GAMMA), `EG/Spec/Lend/COLJVev.lean` (new) | existing + **new** per-row form |
| s3:lemCOLJVev (whole) | `EG.Spec.COLJVevStatement` | `EG/Spec/Lend/COLJVev.lean` | **new** |
| s3:lemCOL (a) failure bound (proof step) | `EG.Spec.COLaProbStatement` | `EG/Spec/Stage1/COLa.lean` | existing (probe P4B). Proof-internal, reused. |
| s3:lemCOL (c) | `EG.Spec.COLcStatement` (+ per-index step `COLcIndexStatement`) | `EG/Spec/Stage1/COLc.lean` | existing (probe P4B). Reused. |
| s3:lemCOL (probabilities for (a),(b),(e) and (a),(b),(c),(e); (e); (g); "`k_lend = 0` if `r ≥ R-1`") | `EG.Spec.COLStatement` | `EG/Spec/Stage1/COL.lean` | **new** |
| s3:lemCOL (whole) | `EG.Spec.COLLemmaStatement` (`COLStatement ∧ COLcStatement`) | `EG/Spec/Stage1/COL.lean` | **new** |

Area choices: L9ρ, HB, T16*(b) in `Link` (next to `T16s`, `L15`); COL-JV and COL-JV-ev in `Lend`
(next to `COLJVCount`, `COLJVRows`); Lemma COL in `Stage1` (next to `COLa`, `COLc`, and the Defs
`EG/Defs/Stage1/COL.lean`). The blueprint's `EG/Spec/Lend/COL.lean` was not used, so that the three
COL Specs sit in one directory.

## New Specs: TeX statement and back-translation

Notation in the back-translations: `N = |V(X)|` or `|V(Y)|`, `L = log₂ N`, "valid run" = a run
`run` of `G` with `run.Valid G D`, "under Γ1" = with the hypothesis `Gamma1 D` (items (a)–(f) of
Γ1 at every `μ ≥ log₂log₂ D`, `D > 2`).

### s3:lemL9rho — `L9rhoStatement`

**TeX (s3.tex:692–707).** "Let `G` be an `n`-vertex graph with `n ≥ 2^{30}`, put `L := log n`, and
let `t ≥ 1` and `ρ ∈ (0,1]`. Take `ℓ_*`, `s̄_*` and `M_* = ⌈2.1/ρ⌉` from (s3:eqStar). Let
`V ⊆ V(G)` with `|V| ≥ ρn/2`, and suppose `ρn ≥ 84`. Then `|V| ≥ n/M_* + 2`. Suppose that
`|B^{ℓ_*}_{G-F}(U,V)| > |V|/2` for every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with
`|F| ≤ s̄_*|U|`. Then `G` is `(2^{12}L^4,t)`-path connected through `V` in the multiset sense of
[BM, Definition 7] … every multiset of pairs of distinct vertices of `G` in which each vertex lies
in at most `t` pairs can be joined by pairwise edge-disjoint paths of length at most `2^{12}L^4`
whose interior vertices lie in `V`."

**Back-translation.** For every vertex type, every finite simple graph `G` with `2^{30} ≤ |V(G)|`
(natural numbers), every vertex set `W` and reals `ρ, t` with `0 < ρ ≤ 1`, `1 ≤ t`, `W ⊆ V(G)`,
`ρ|V(G)|/2 ≤ |W|` and `84 ≤ ρ|V(G)|`:
(1) `|V(G)|/M_*(ρ) + 2 ≤ |W|` (reals, `M_*(ρ) = ⌈2.1/ρ⌉₊`), and
(2) if for every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with `|F| ≤ s̄_*(n,ρ,t)|U|` the ball
`B^{ℓ_*(n)}_{G-F}(U,W)` has more than `|W|/2` elements, then `G` is `(2^{12}L^4, t)`-path connected
through `W` (Def 7 with the multiset clause: every finite indexed family of pairs of distinct
vertices of `G` with every vertex an entry of at most `t` indices gets pairwise edge-disjoint paths,
one per index, of length `≤ 2^{12}L^4` with interior in `W`).

### s3:thmT16s (b) — `T16sForcedStatement`

**TeX (s3.tex:792–819).** "Let `X` be an `N`-vertex `(ε′,s)`-expander with `ε′ ∈ [2^{-7},1]`, and
put `L := log N`. Let `ρ ∈ (0,1]` and `t ≥ 1` … Suppose that `ρN ≥ L^2` and
`s ≥ 2^{135}tL^{28}ρ^{-5}`. … (b) If `N ≥ 2`, the hypotheses force `ρN > 2^{27}L^{5.6}N^{4/5}`,
because `s < N`. In particular the hypothesis `ρN ≥ L^2` is implied by the others; it is kept only
for comparison with [BM, Theorem 16]."

**Back-translation.** For every graph `X` with `N = |V(X)| ≥ 2` that is an `(ε′,s)`-expander, with
`2^{-7} ≤ ε′ ≤ 1`, `0 < ρ ≤ 1`, `1 ≤ t` and `2^{135}tL^{28}ρ^{-5} ≤ s` (no hypothesis `ρN ≥ L^2`):
`2^{27}L^{28/5}N^{4/5} < ρN` (real powers) and `L^2 ≤ ρN`.

### s3:lemHB — `HBStatement`

**TeX (s3.tex:910–921).** "Let `X` be an `N`-vertex `(ε′,s)`-expander with `N ≥ 2` and
`2^{-7} ≤ ε′ ≤ 1`, and put `L := log N`. Let `m` be an integer with `1 ≤ m` and `2m ≤ s`, and put
`b := ⌈2mL^2/ε′⌉`. Thus `b = ⌈64L^2m⌉`, `⌈128L^2m⌉` or `⌈256L^2m⌉` at `ε′ = 2^{-5}`, `2^{-6}` or
`2^{-7}`. Then every vertex `w` has a set `A(w) ⊆ N_X(w)` with `|A(w)| = m`, such that every vertex
of `X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`."

**Back-translation.** For every graph `X` that is an `(ε′,s)`-expander with `|V(X)| ≥ 2`,
`2^{-7} ≤ ε′ ≤ 1`, and every natural `m ≥ 1` with `2m ≤ s`: there is `A : V → Finset V` with
`A(w) ⊆ N_X(w)` and `|A(w)| = m` for every `w ∈ V(X)`, and, for every vertex `u`, at most
`⌈2mL^2/ε′⌉` vertices `w ∈ V(X)` have `u ∈ A(w)`.

### s3:lemCOLJV (ii) — `COLJVCol3Statement`, `COLJVRow{1,2,3,5,6,9,11,12,13}Statement`, `COLJVStatement`

**TeX (s3.tex:1185–1229, Table s3:tabCOLJV at 1150–1182; the full quotes are in the file
docstring).** "Assume condition Γ1. Let `Y` be an ancestor of round `r ≤ R`, and write
`λ := λ_r` and `μ := log λ`; if `r ≤ R-2`, write also `M := M_{r+2}`. … (ii) Every requirement in
column 2 and every inequality in column 3 of Table s3:tabCOLJV holds. … for each row every
inequality in column 3 holds at every `μ ≥ log log D_*` by Γ1(f); in particular it holds at
`μ = log λ_r` and, for rows 2, 11 and 12, also at `μ = log λ_{l-2}` for every round `3 ≤ l ≤ R` …
Rows 1, 3 and 8 … hold for every round `r ≤ R` …: row 1 for every round-`r` pre-part, and rows 3
and 8 for every ancestor `Y` of round `r` … Rows 4–7 and 10 … are asserted for `r ≤ R-2` … Row 9
holds for every `r ≤ R` … Rows 2, 11 and 12 concern `λ_{l-2}` for rounds `3 ≤ l ≤ R`, and row 13
is G*." Column 2: 1 `θ^GC_r(Z^0) > τ_r`; 2 `P_{l-2} ≥ M_l^{13}`; 3 `s_Y/4 ≥ 40k_lend L_Y` (the
proof names the other two levels `s_Y ≥ 80L_Y` and `s_r/8 ≥ 40k_own L_Y`); 5
`s_Y/(8k_lend) ≥ 2^{135}(3M)L_Y^{28}M^{20}`; 6 "T16* failures over `I^JS(Y)` sum to at most
`|V(Y)|^{-2}/4`" (per class `2^{86}tL^{19}ρ^{-3}N^{-3}`); 9 `k_lend(Y) ≤ λ^{3.3}`; 11
`λ_{l-2}^{95}/(8M_l^2) ≥ 2^{10}M_l^{10}`; 12 `M_l ≤ λ_{l-2}^{1.6}`; 13 G*
(`λ^{36} ≥ 2^{240}(Aμ)^{46A}`).

**Back-translation.** For every graph `G`, real `D` and run with `Gamma1 D` and `run.Valid G D`:
- Col3: for every round `r ∈ [1,R]`, all 18 column-3 inequalities hold at `μ = log₂ λ_r`.
- Row 1: for every round `r ∈ [1,R]` and every round-`r` pre-part address `a`:
  `τ_r < θ^GC_r(Z^0_a)` (naturals).
- Row 2: for every `3 ≤ l ≤ R`: `M_l^{13} ≤ P_{l-2}` (naturals).
- Row 3: for every ancestor `Y`: `40k_lend(Y)L_Y ≤ s_Y/4`, `80L_Y ≤ s_Y` and `40k_own(Y)L_Y ≤ s_r/8`.
- Row 5: for every ancestor `Y` with `r + 2 ≤ R`: `2^{135}·3M·L_Y^{28}M^{20} ≤ s_Y/(8k_lend(Y))`,
  `M = M_{r+2}`.
- Row 6: for every ancestor `Y` with `r + 2 ≤ R`:
  `Σ_{r+2 ≤ l ≤ R} Σ_{0 ≤ j < K^JS_l} 2^{86} t^JS_l L_Y^{19} ρ_l^{-3} N^{-3} ≤ N^{-2}/4`.
- Row 9: for every ancestor `Y`: `k_lend(Y) ≤ λ_r^{33/10}`.
- Row 11: for every `3 ≤ l ≤ R`: `2^{10}M_l^{10} ≤ λ_{l-2}^{95}/(8M_l^2)`.
- Row 12: for every `3 ≤ l ≤ R`: `M_l ≤ λ_{l-2}^{8/5}`.
- Row 13: for every round `r`: `Gamma1e (log₂ λ_r)`, i.e. `2^{240}(Aμ)^{46A} ≤ (2^μ)^{36}`.
- `COLJVStatement`: the conjunction of `COLJVCountStatement` (part (i), including row 10), Col3 and
  rows 1–9, 11–13 (rows 4, 7, 8 from `COLJVRows.lean`).

### s3:lemCOLJVev — `COLJVevTypeEStatement`, `COLJVevRowsStatement`, `COLJVevEventuallyRowStatement`, `COLJVevStatement`

**TeX (s3.tex:1357–1381).** "Call an inequality in a real variable `μ` of type (E) if it reads
`aμ - b - c log(Aμ) ≥ 0` with reals `a > 0` and `b, c ≥ 0` (here `A = 105` and `log = log₂`).
(i) An inequality of type (E) holds for every `μ ≥ max{1, v_0^2}`, where
`v_0 := (c + (c^2 + a(b + c log A))^{1/2})/a`. In particular, it holds for all sufficiently large
`μ`. (ii) Let `μ ≥ 6` be real, and put `λ := 2^μ`, `M̄ := (Aμ)^{2A}` and
`k̄ := 192λ^3 + (4/3)M̄^2`. Let `1 ≤ i ≤ 13`, and let `(a_i,b_i,c_i)` be the triple in column 4 of
row `i` of Table s3:tabCOLJV. If `a_iμ - b_i - c_i log(Aμ) ≥ 0`, then every inequality in column 3
of row `i` holds at `λ`. (iii) Consequently, for each row of Table s3:tabCOLJV, every inequality in
column 3 holds at `λ = 2^μ` for all sufficiently large real `μ`."

**Back-translation.** (i) For all reals `a > 0`, `b ≥ 0`, `c ≥ 0`: `aμ - b - c log₂(105μ) ≥ 0` for
every `μ ≥ max(1, v_0(a,b,c)^2)`, and for all sufficiently large `μ`. (ii) For every real `μ ≥ 6`
and every `1 ≤ i ≤ 13`: if the type-(E) inequality of the column-4 triple of row `i` holds at `μ`,
then the column-3 inequalities of row `i` hold at `μ`. (iii, per row) for every `1 ≤ i ≤ 13`, the
column-3 inequalities of row `i` hold for all sufficiently large `μ`. `COLJVevStatement` is
(i) ∧ (ii) ∧ (iii per row).

### s3:lemCOL — `COLStatement`, `COLLemmaStatement`

**TeX (s3.tex:1453–1512; full quote in the file docstring).** "Assume condition Γ1. Let `Y` be an
ancestor of round `r`, with the stage-1 lending data of Definition s3:defCOL. If `r ≥ R-1`, then
`k_lend(Y) = 0` and every statement below about lent classes is vacuous. (a) … (b) … (c) … (e) The
own-device thresholds hold. … (g) … The own classes partition `Own_Y`, and if `r ≤ R-2`, the lent
classes are pairwise edge-disjoint and partition `Lend_Y`. … Items (a), (b) and (e) hold
simultaneously with probability at least `1 - |V(Y)|^{-2}/2` over the stage-1 lending data of `Y`.
For every family as in (c), items (a), (b), (c) and (e) hold simultaneously with probability at
least `1 - |V(Y)|^{-2}`. Item (g) always holds."

**Back-translation.** For every graph `G`, real `D` and run with `Gamma1 D` and `run.Valid G D`,
and every ancestor `Y` (round `r = Y.1`):
1. if `R ≤ r + 1` then `k_lend(Y) = 0`;
2. the deterministic thresholds `COLe` of (e) hold;
3. every outcome `ω` in the support of `colLaw Y` satisfies the partition facts `COLg`;
4. for every finite probability space `μ` and random variable `D` with law `colLaw Y`, the event
   "`COLa(D ω)` ∧ `COLb(D ω)` ∧ `COLe`" has probability at least `1 - N^{-2}/2`;
5. if `Y` is light (`Y ∈ run.lightParts G`, the spelling of `COLcStatement`; fix round item 2):
   for every `μ`, `D` with law `colLaw Y`, every family `Vs` of random vertex
   sets indexed by lent tags with `Vs` jointly independent of `D`, and reals `ρ i` such that for
   each U-index `i ∈ I^U(Y)` the set `Vs · i` is a `ρ i`-random subset of `V(Y)` with
   `ρ i ≥ 1/(12L_Y^5)`: the event "`COLa ∧ COLb ∧ COLc(D ω, Vs ω) ∧ COLe`" has probability at
   least `1 - N^{-2}`.
`COLLemmaStatement` adds item (c) alone (`COLcStatement`: probability of `COLc` at least
`1 - N^{-2}/2`).

## Hazards and choices (T0 decisions)

1. **L9ρ, (eqStar) domain.** `ℓ_*`, `s̄_*`, `M_*` are the locked `EG.Star.ell/sbar/M`; none depends
   on `ε'`, so the (eqStar) domain condition on `ε'` is void; the others are hypotheses. The two
   conclusions are a conjunction (the first is unconditional). `U ⊆ V(G)`, `F ⊆ E(G)`,
   `W ⊆ V(G)` are kept (CONVENTIONS: balls contain `U ∩ W` even outside `V(H)`).
2. **L9ρ, universes.** `V : Type u`. The locked `HaxellStatement` is universe-polymorphic
   (`α : Type u`), so the blueprint hazard L9-HAXELL-UNIVERSE is resolved: the hypergraph lives
   on `ι ⊕ Sym2 V : Type (max 0 u) = Type u` (`ι : Type`, the index type of `IsPathConnected`).
3. **HB.** `m : ℕ`, `b = ⌈2mL^2/ε′⌉₊`; the conclusion is the shared `IsHBFamily` (counts indices
   `w ∈ V(X)`). The sentence "Thus `b = …`" is an evaluation, not stated. Hypotheses
   `ε′ ≤ 1`, `ε′ ≥ 2^{-7}` are kept though the proof uses only `ε′ > 0` (blueprint HB-EPS-UNUSED).
4. **T16*(b).** Stated without the hypothesis `ρN ≥ L^2` (the item says it is implied by the
   others) and with the "in particular" conclusion `L^2 ≤ ρN`; the reading with the hypothesis is
   weaker. `L^{5.6}`, `N^{4/5}` are `Real.rpow` with `28/5`, `4/5`. Checked by hand: `N > s`
   (min degree `> s` for `ε′ > 0`, `N ≥ 2`) gives `ρ^5N > 2^{135}tL^{28} ≥ 2^{135}L^{28}`, i.e.
   `(ρN)^5 > 2^{135}L^{28}N^4`.
5. **COL-JV, column 3.** "at `μ = log λ_r` and, for rows 2, 11, 12, at `μ = log λ_{l-2}`
   (`3 ≤ l ≤ R`)" is one statement "col3 at `log₂ λ_r` for every round `r`" (`l-2` is a round).
6. **COL-JV, row 3** states all three Lemma-15⁺ levels (TRIAGE E1-ROW3-GAP) for every ancestor, as
   the scope bullet says for row 3; for standalone `Y` the own level uses `k_own`, which Lean
   defines for every ancestor (TRIAGE §2.7) — the same choice as the existing `COLJVRow8Statement`
   (row 8 (d) with `k_own` for every ancestor). The inequality is true for every ancestor by the
   manuscript's own bound `k_own ≤ L_Y ≤ 2λ`.
7. **COL-JV, row 5** is the literal column 2 with `M = M_{r+2}`, not the per-`l` hypothesis of
   T16* (blueprint COLJV-COL2-PRECISION recommended per-`l`); the per-`l` form follows by (B7)
   inside the proof of Lemma COL (b). Row 6 is the double sum over `r+2 ≤ l ≤ R`,
   `j < K^JS_l` (= the sum over `I^JS(Y)` through the tag `LentTag.JS`, which is injective).
8. **COL-JV, row 10** is not restated: it is the last conjunct of the existing
   `COLJVCountStatement` with the same scope `r ≤ R-2`. Row 13 is `Gamma1e (log₂ λ_r)` for every
   round.
9. **COL-JV-ev.** Row index bounded `1 ≤ i ≤ 13` (rows 0, ≥ 14 are junk `True`). (i) includes the
   "in particular … for all sufficiently large `μ`" clause. (iii) is given per row
   (`COLJVevEventuallyRowStatement`, literal) in addition to the existing all-rows
   `Col3EventuallyStatement` (equivalent: 13 rows).
10. **COL, hypotheses.** `Gamma1 D ∧ run.Valid G D` (TRIAGE §2.6). The existing COL(a)/(c) Specs of
    probe P4B also assume `D_* ≤ d_1`; it follows from `run.Valid` whenever an ancestor exists
    (every round `l ∈ [1,R]` has `D_* ≤ d_l`), so it is omitted in the new Specs. The whole-lemma
    `COLLemmaStatement` conjoins `COLcStatement` as it is (with the extra, redundant hypothesis).
11. **COL, (g)** is read on the support of `colLaw Y` (off the support a lend edge may carry an
    index outside `lentIdx`); it is already a Lib theorem (`EG.Stage1.COLg_of_mem_supp_colLaw`),
    checked in the test file. Consumer exclusivity is a design rule (blueprint
    COL-CONSUMERS-NOT-A-PROPERTY), not stated.
12. **COL, (e)** is the deterministic `COLe` (inequalities only) and is also conjoined inside the
    events, as the text says "(a), (b) and (e) hold simultaneously". "Every statement about lent
    classes is vacuous" needs no statement (lent-class clauses hold when `lentIdx = ∅`); the
    clause `k_lend(Y) = 0` for `r ≥ R-1` is stated.
13. **COL, joint probability** is stated for light `Y` only ("for every family as in (c)", and (c)
    begins "Let `Y` be light"); for standalone `Y`, `I^U(Y) = ∅` and it would follow from the
    (a),(b),(e) bound.
14. **COL, `COLaProbStatement`** (existing) exports `P(¬(a)) ≤ N^{-2}/4`, not the blueprint's
    sharper `2(2+k+k_own)N^{-5}` (COL-EXPORT-A-BOUND). s5:lemE1(b) re-derives its bound; if the s5
    proof needs the `N^{-5}` form it must be added as a separate proof-step Spec.

## Findings on existing Specs (not edited)

- None wrong. `T16sStatement`, `COLJVCountStatement`, `COLJVRow{4,7,8}Statement`,
  `Col3EventuallyStatement`, `COLaProbStatement`, `COLcStatement`, `COLcIndexStatement` were read
  against the TeX; they are faithful.
- Minor inconsistency: `COLaProbStatement`, `COLcStatement`, `COLcIndexStatement` carry
  `Dstar ≤ run.d G 1`, while `COLJVCount/Rows` and the new Specs do not (harmless: implied by
  `run.Valid` when an ancestor exists).

## Non-vacuity checks (`EGTest/Spec_s3b.lean`)

- L9ρ: hypotheses before the ball condition hold for the edgeless graph on `2^{30}` vertices,
  `W = V(G)`, `ρ = t = 1`.
- HB: `IsHBFamily K2 1 1 N` holds on the one-edge graph; no family with `m = 2` exists there.
- COL-JV-ev: hypotheses of (i) satisfiable; the (ii) hypothesis holds for row 4 at `μ = 10`;
  `row 4` unfolds to the column-3 inequality; column 3 holds at `μ = 2^{40}`
  (`COLTable.col3_of_le`).
- COL-JV / COL: `∃ D, Gamma1 D ∧ run.Valid E2 D` for the run without rounds (from `EG.gammaSat`);
  `μ.map D = colLaw` satisfiable (`D = id`); the (g) conjunct is a theorem.
- The conjunctions project to their parts.
- Not checked: the expander hypotheses of HB and T16*(b) (no cheap explicit expander with
  `N ≥ 2`), the ball condition of L9ρ, and nonempty ancestor sets (a run with an ancestor needs
  `d ≥ D_*` with Γ1, far beyond explicit graphs).

## Mathematical findings

None. The statements were re-read against the TeX; T16*(b) and L9ρ's first conclusion were
re-derived (see items 4 and 1); the TRIAGE T1 item T16-C-META is already patched in v6.1 ("Apart
from Step 0 …").

## Fix round (reviews `s3b.review-fidelity-first.md`, `s3b.review-vacuity-and-consumer-form.md`)

All five items are minor. Each was checked against the Defs and the TeX. One statement changed, in
spelling only: the light guard of `COLStatement`. The test file gained three bridge checks.

1. **`COLLemmaStatement` conjoins `COLcStatement` with the extra `D_* ≤ d_1`.** This is not an issue
   for fidelity, and I did not change it. The equivalence holds: `Y ∈ lightParts ⊆ parts` gives
   `1 ≤ Y.1 ≤ R`, so `run.Valid` (clause at `l = 1`) gives `D_* ≤ d_1`. This is now checked in
   `EGTest/Spec_s3b.lean` (example "Item 1", from any ancestor). `COLcStatement`/`COLaProbStatement`
   belong to probe P4B, so I did not edit them. Dropping the hypothesis there is left to the
   integrator's cleanup pass, as the reviewer suggests.
2. **Two spellings of the light guard.** Fixed. `COLStatement` conjunct 5 now reads
   `Y ∈ run.lightParts G →`, the same as `COLcStatement`, so `COLLemmaStatement` uses one spelling.
   The meaning is unchanged: under `Y ∈ run.ancestors G` the guard is equivalent to
   `run.isLight G Y.1 Y.2` (`Run.mem_lightParts`, `Run.mem_ancestors`). The file docstring says so,
   and the bridge is checked in the test file (example "Item 2"). The only other user of
   `COLStatement` is the test file.
3. **Row 3 own level asserted for standalone `Y`.** Not an issue: it matches the TeX scope, and I
   made no change. The TeX says "rows 3 and 8 for every ancestor `Y` of round `r`", and `k_own =
   4J_Y+1` is total (Defs). s2.tex:1155 and 1210 give `L_Y ≤ Λ_r ≤ 2λ_r` for every ancestor, and
   s3.tex:1302 uses `k_own ≤ L_Y ≤ 2λ`, so `40k_own L_Y ≤ 160λ^2 ≤ λ^{100}/8 ≤ s_r/8` holds for
   standalone `Y` too. This is the same choice as the existing `COLJVRow8Statement` (hazard item 6).
4. **HB's `⌈2mL^2/ε'⌉₊` vs `pvB`/`vb` = `⌈2^7L^2m⌉₊`.** Not an issue for the Spec. `HBStatement` is
   the literal TeX bound, and the "Thus `b = …`" evaluation is not stated. The consumer rewrite is
   now checked in `EGTest/Spec_s3b.lean` (example "Item 4"):
   `⌈2·pvM N·(log₂ N)^2/2^{-6}⌉₊ = Vortex.pvB N`, by `unfold; congr 1; zpow_neg; norm_num; ring`.
   The s4/s5 proof units can copy it into a Lib lemma (I did not add a Lib file: they own that
   area).
5. **`T16sForcedStatement` has no consumer.** Not an issue; kept as an optional fidelity Spec. I
   re-checked the reviewer's argument (my hazard item 4): `ε' > 0` and `N ≥ 2` give `δ > s`, hence
   `s < N`. Then `ρ^5N > 2^{135}tL^{28} ≥ 2^{135}L^{28}`, i.e. `(ρN)^5 > 2^{135}L^{28}N^4`. Since
   `L ≥ 1` and `N^{4/5} ≥ 1`, this gives `ρN > 2^{27}L^{28/5}N^{4/5} ≥ L^2`.

Build/check after the fix round: `lake build EG.Spec.Stage1.COL` (and the other s3b Specs plus the
test imports) succeeds. `scripts/check.sh EGTest/Spec_s3b.lean 1200` gives rc=0, 0 errors, 0 sorry.
`python3 -I scripts/lint.py` gives 0 findings. Files changed: `EG/Spec/Stage1/COL.lean` (guard
spelling + docstring), `EGTest/Spec_s3b.lean` (three bridge examples + header), this file. No
Defs, no other unit's file, no root file edited.
