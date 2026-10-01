# Clean-room review of the s3b Specs (fidelity first, model A)

Reviewer scope: the 6 new Spec modules listed in `work/p2s/s3b.md`; reused Specs were read only to check
consistency. TeX: `proofs/manuscript/s3.tex` v6.1, lines 692-1600. No Lean file was edited.

Verdict: **approve**. No statement is unfaithful, vacuous or weakened. Four cosmetic or minor remarks
are listed below. There are no findings on the manuscript.

## Checks run
- `python3 -I scripts/lint.py`: 0 findings.
- Scratch file (scratchpad `S3bRev.lean`, importing `EG.Spec.Lend.COLJV`, `EG.Spec.Stage1.COL` and
  `EG.Spec.Link.T16sForced`) compiled with no errors and no sorry. It checks that:
  - (junk check for rows 5 and 6) `Y.1 + 2 ≤ run.R → 0 < Stage1.klend G run Y`. So
    `s_Y/(8k_lend)` in row 5 is a real division and never Lean's `x/0 = 0`.
  - `TypeE 1 0 0 μ` holds for `μ ≥ 1` (the hypotheses of (i) are not contradictory).
- I read `EGTest/Spec_s3b.lean`. Its checks are sound.

## Per statement

### L9rhoStatement ([s3:lemL9rho]): faithful
Back-translation: for every `G` with `n = |G| ≥ 2^30`, reals `0 < ρ ≤ 1` and `t ≥ 1`, and
`W ⊆ V(G)` with `ρn/2 ≤ |W|` and `84 ≤ ρn`, two things hold. (1) `n/⌈2.1/ρ⌉ + 2 ≤ |W|`. (2) Suppose that for
every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with `|F| ≤ s̄_*|U|` we have
`|B^{ℓ_*}_{G-F}(U,W)| > |W|/2`. Then `G` is `(2^{12}L^4, t)`-path connected through `W` (indexed
families, so the multiset form). This matches the TeX: the quantifiers are in the right order, the
inequalities are strict or non-strict as in the TeX, and `ℓ_* = ⌊2^{10}L^3⌋`,
`s̄_* = 2^{28}tL^8/ρ` and `M_* = ⌈2.1/ρ⌉` are the locked `Star.*` values.
- `ball` matches s1:convGraphs(d): it lies inside `W`, the start vertex is free, and paths go
  through `W`. `deleteEdges` keeps the vertices.
- I re-derived conclusion (1): `n/M_* ≤ ρn/2.1` and `ρn/2 - ρn/2.1 = ρn/42 ≥ 2`.
- I re-derived the claim's parameter bound: `64·3.1·2^{20} ≤ 2^{28}`.
- Non-vacuity of the ball hypothesis (by hand): take `K_n` with `n = 2^{100}`, `W = V`, `ρ = t = 1`.
  Then `s̄_* = 2^{81} < n`, and the ball has at least `n - s̄_* > n/2` vertices.

### T16sForcedStatement ([s3:thmT16s](b)): faithful (stronger reading, true)
The Spec drops the hypothesis `ρN ≥ L^2`. The TeX says it "is implied by the others", so this is the
right reading. I re-derived the rest:
- `ε' ≥ 2^{-7} > 0` and `N ≥ 2` let us use `U = {v}` in Def 11, which gives `δ > s`. Since
  `deg ≤ N-1`, we get `N > s`.
- Then `ρ^5 N > 2^{135}tL^{28} ≥ 2^{135}L^{28}`, which is `ρN > 2^{27}L^{28/5}N^{4/5}`.
- `L ≥ 1` then gives `L^2 ≤ ρN`.

The exponents 28/5 and 4/5 are `rpow`, and `ρ^{-5}` is `zpow`, as in `T16sStatement`. The
hypotheses can be satisfied: `K_N` with `N = 2^{400}`, `s = 2^{377}`, `ρ = t = 1`, `ε' = 1`.

### HBStatement ([s3:lemHB]): faithful
Back-translation: `X` is an `(ε',s)`-expander with `|X| ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, `m ∈ ℕ`, `m ≥ 1`
and `2m ≤ s`. Then there is `A` with `A(w) ⊆ N_X(w)` and `|A(w)| = m` for every `w ∈ V(X)`, and every
`u` lies in `A(w)` for at most `⌈2mL^2/ε'⌉` indices `w ∈ V(X)`. The Spec reuses the shared locked
`IsHBFamily`. "Thus `b = …`" is only an evaluation, so it is rightly not stated.
- The hypotheses can be satisfied (by hand): `K_7` is a `(1,2)`-expander. With `u ≤ 4` and at most
  `2u` deleted edges, at least `7-u-2 ≥ 1` outside vertices stay adjacent to `U`, and
  `u/log²7 ≤ 0.51`. So `m = 1` works.

### COL-JV ([s3:lemCOLJV] (ii)): faithful
- **Col3:** `col3(log₂λ_r)` for every round `r ∈ [1,R]`. This correctly merges "at `μ = log λ_r`"
  with "for rows 2, 11, 12 at `log λ_{l-2}`", because `l-2` is itself a round.
- **Row 1:** `τ_r < θ^GC_r(Z^0_a)` for every pre-part address of round `r`. It is strict, as in the TeX.
- **Row 2:** `M_l^{13} ≤ P_{l-2}` for `3 ≤ l ≤ R`.
- **Rows 11, 12:** stated for `3 ≤ l ≤ R`. Row 11 keeps the literal column-2 form
  `2^{10}M^{10} ≤ λ^{95}/(8M^2)`. Row 12 uses `rpow 8/5`.
- **Row 3:** all three Lemma-15⁺ levels, for every ancestor, matching the scope bullet.
- **Row 5:** literal, with `M = M_{r+2}` and the scope `r+2 ≤ R`.
- **Row 6:** the sum over `(l,j)`, `r+2 ≤ l ≤ R`, `j < M_l^2`, of `2^{86}t^JS_l L_Y^{19}ρ_l^{-3}N^{-3}`,
  bounded by `≤ N^{-2}/4`. The failure bound of T16* is correctly specialised: the class is an
  `N = |V(Y)|`-vertex graph, so `L = L_Y`. I re-derived the proof's chain
  `2^{88}M^{15}L^{19}N^{-3} ≤ 2^{107}λ^{19}M^{15}N^{-3}`.
- **Row 9:** for every ancestor. For `r ≥ R-1` it is trivially true (`0 ≤ λ^{3.3}`).
- **Row 13:** `Gamma1e(log₂λ_r)`.

The scopes match the three bullets of the TeX. `COLJVStatement` conjoins all the rows plus the
reused `COLJVCount` (which contains row 10) and `COLJVRow{4,7,8}`. No row is missing: rows 1–13, and
column 3.

### COL-JV-ev ([s3:lemCOLJVev]): faithful
- (i) keeps the side conditions `a > 0`, `b, c ≥ 0` and the threshold `max(1, v_0²)`, and adds the
  eventuality `atTop`.
- (ii) has `μ ≥ 6`, the row bound `1 ≤ i ≤ 13` (no junk rows), and the hypothesis `TypeE(triple i)`.
  It concludes `row i μ`.
- (iii) is stated per row.

I re-checked every row derivation of (ii) against the locked `COLTable.row`/`triple`: rows 1–13,
including the five sub-inequalities of row 8. The triples and the direction of every inequality match.

### COL ([s3:lemCOL]): faithful
- `k_lend = 0` if `R ≤ r+1`.
- `COLe` is deterministic.
- `COLg` holds on the support of `colLaw`.
- `P(a ∧ b ∧ e) ≥ 1 - N^{-2}/2` for every `μ`, `D` with `μ.map D = colLaw`.
- For light `Y` and every family `Vs` jointly independent of `D` (U-indices `ρ_i`-random with
  `ρ_i ≥ 1/(12L_Y^5)`, dependence across indices allowed): `P(a ∧ b ∧ c ∧ e) ≥ 1 - N^{-2}`.

These match the closing sentences of the lemma. `isLight` on `run.ancestors` is the same as the
`run.lightParts` used by `COLcStatement` (`lightParts = parts.filter isLight`, and
`ancestors = parts`). I checked the bounds against the proof: `P(¬a) ≤ N^{-2}/4`, the JS union and
the U union are each `≤ N^{-2}/4`, and (e) holds deterministically.

## Consistency and hygiene
- Only `Gamma1 D ∧ run.Valid G D` is assumed. No Γ2(b),(c) and no other hidden hypothesis.
- All Defs are reused; no new Defs.
- Existing Specs are reused, not restated. The one exception is the per-row (iii), noted below.
- Docstrings start with the labels and quote the TeX.

## Remarks (none blocking)
1. (cosmetic) `COLJVevEventuallyRowStatement` is logically equivalent to the existing
   `Col3EventuallyStatement` (13 rows). That makes two Specs with the label [s3:lemCOLJVev](iii).
   The docstring says so, which is acceptable. The integrator may prefer to keep only one.
2. (cosmetic) `COLJVRow3Statement`'s own level `s_r/8 ≥ 40k_own L_Y` is also asserted for standalone
   `Y`, where the TeX draws no own classes. It is stronger than the TeX's use and true, because
   `k_own ≤ L_Y ≤ 2λ`. This is the same choice as the existing `COLJVRow8Statement`.
3. (minor) `COLLemmaStatement` conjoins `COLcStatement`, which has the extra hypothesis
   `D_* ≤ d_1`. The two are equivalent, because a light part exists only if `R ≥ 1`, and `run.Valid`
   then gives `D_* ≤ d_1`. The inconsistency is already reported in s3b.md.
4. (cosmetic) `T16sForcedStatement` has no consumer. It is fine as a record of (b).
