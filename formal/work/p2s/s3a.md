# P2 Specs, chunk s3a (monotonicity, Lemma 15⁺, multisets, (eqStar), P13*, L17*, P18*/L19*): status

Manuscript v6.1 `proofs/manuscript/s3.tex` lines 1–688 (a CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s3a.md`, `nodes_s3a.json`; data model TRIAGE §2.5 (universes),
§2.11 (Star.lean owned by s3a, `IsWellExpanding` in `EG/Defs/Graph.lean`), CONVENTIONS
"Parameters of s3/s4".

Result: 6 new Spec modules (15 new `…Statement` defs), 1 test file. No new Defs (everything needed
exists in the locked `EG/Defs/**`). No proofs, no stubs, no existing file edited.

Build and check:
- `lake build EG.Spec.Link.Monotone EG.Spec.Link.Multiset EG.Spec.Link.Star EG.Spec.Link.P13s
  EG.Spec.Link.L17s EG.Spec.Link.P18s` succeeds.
- `scripts/check.sh EGTest/Spec_s3a.lean` gives rc=0, 0 errors, 0 sorry warnings.
- `python3 -I scripts/lint.py` reports 0 findings.

Root imports for the orchestrator to add (I did not edit the root files):
- to `EG`: `EG.Spec.Link.Monotone`, `EG.Spec.Link.Multiset`, `EG.Spec.Link.Star`,
  `EG.Spec.Link.P13s`, `EG.Spec.Link.L17s`, `EG.Spec.Link.P18s`;
- to `EGTest`: `EGTest.Spec_s3a`.

## Table: label → Lean name → file → status

| label (kind) | Lean name | file | status |
|---|---|---|---|
| s3:lemMonotone (lemma) | `EG.Spec.MonotoneStatement` | `EG/Spec/Link/Monotone.lean` | **new** (traceability Spec; the content is already proved in Lib: `IsExpander.of_le`, `IsExpander.mono`, `IsPathConnected.mono`, `exists_paths`, `exists_paths_sigma` in `EG/Lib/Found/Graph.lean`) |
| s3:lemL15p (lemma) | `EG.Spec.L15pStatement` | `EG/Spec/Link/L15.lean` | existing (locked candidate, proved by `EG.l15p`). Re-read against the TeX: faithful. |
| s3:remMultiset (remark) | `EG.Spec.MultisetCountStatement` | `EG/Spec/Link/Multiset.lean` | **new** (the counting step, the remark's one mathematical claim; items 1, 2, 5 are built into `FGraph.IsPathConnected`, item 3 is commentary) |
| s3:eqStar (definitions) | `EG.Star.{L, ell, g, q, p, d, lam, Delta, sigma, theta, mu, sbar, M, K}` | `EG/Defs/Link/Star.lean` | existing Defs (locked) |
| s3:eqS1 | `EG.Spec.StarS1Statement` | `EG/Spec/Link/Star.lean` | **new** |
| s3:eqS2 (existence, uniqueness) | `EG.Spec.StarS2PStatement` | `EG/Spec/Link/Star.lean` | **new** |
| s3:eqS2 (numeric part) | `EG.Spec.StarS2NumStatement` | `EG/Spec/Num/StarInputs.lean` | existing (unit NUM, proved). Reused. |
| s3:eqS2 (union law) | `EG.Spec.StarUnionLawStatement` | `EG/Spec/Link/Star.lean` | **new** |
| s3:eqS3 | `EG.Spec.StarS3Statement` (+ `NumStarS3MarginStatement`) | `EG/Spec/Num/StarInputs.lean` | existing (unit NUM, proved). Reused. |
| s3:eqS4 | `EG.Spec.StarS4Statement` | `EG/Spec/Link/Star.lean` | **new** |
| s3:eqS5 | `EG.Spec.StarS5Statement` | `EG/Spec/Link/Star.lean` | **new** |
| s3:eqS6 | `EG.Spec.StarS6Statement` | `EG/Spec/Link/Star.lean` | **new** |
| s3:eqStar (P13* parameter check, paragraph after (S6)) | `EG.Spec.StarP13sParamsStatement` | `EG/Spec/Link/Star.lean` | **new** (in the hypothesis form of `P13sStatement`) |
| s3:propP13s (proposition) | `EG.Spec.P13sStatement` | `EG/Spec/Link/P13s.lean` | **new** |
| s3:lemL17s (lemma) | `EG.Spec.L17sStatement` | `EG/Spec/Link/L17s.lean` | **new** |
| s3:lemL17s (proof steps, numeric) | `NumL17s…Statement` (12 statements) | `EG/Spec/Num/L17s.lean` | existing (unit NUM). Not the lemma's statement; recorded for completeness. |
| s3:lemP18s (lemma: Prop 18*, Lemma 19*) | `EG.Spec.P18sStatement` | `EG/Spec/Link/P18s.lean` | **new** |

The blueprint's single `StarFactsStatement` is split into one Spec per fact, because (S2)-numeric
and (S3) were already stated (and proved) by unit NUM; restating them would duplicate locked text.

## New Specs: TeX statement and back-translation

Common reading for all s3a Specs: `n = G.card`, `L = log₂ n` (`Real.logb 2`, or `EG.Star.L n`,
which is that by definition), `exp` natural. Parameters of (eqStar) are the locked
`EG.Star.*` at `(n, ε', ρ, t)`. `V` (the vertex type) is `Type u`; the probability space `Ω` of
L17*/P18* is `Type v` (see T0-UNIV).

### s3:lemMonotone — `MonotoneStatement`

**TeX.** "(i) Let `H` be an `(ε',s)`-expander and let `H' ⊇ H` be a graph with `V(H') = V(H)`. Then
`H'` is an `(ε',s)`-expander. Moreover, every `(ε',s)`-expander is an `(ε'',s')`-expander whenever
`ε'' ≤ ε'` and `s' ≤ s`. (ii) Path connectivity is monotone. Let `G ⊆ G'` be graphs with
`V(G)=V(G')`, let `V ⊆ V' ⊆ V(G)`, and suppose `ℓ ≤ ℓ'` and `t' ≤ t`. If `G` is `(ℓ,t)`-path
connected through `V`, then `G'` is `(ℓ',t')`-path connected through `V'`. (iii) Whether a graph `X`
is `(ℓ,t)`-path connected through a set `V` depends only on the pair `(X,V)`. On this event,
required paths exist for every multiset `𝒫` of pairs of distinct vertices of `X` in which each
vertex lies in at most `t` pairs. In particular, `𝒫` may be chosen after `X` and `V` are revealed
[…] (adaptively). If several multisets `𝒫_1,…,𝒫_q` are given and every vertex lies in at most `t`
pairs of the union multiset `𝒫_1+⋯+𝒫_q`, then one application of the property to this union joins
all their pairs by pairwise edge-disjoint paths through `V` of length at most `ℓ` (joint routing)."

**Lean, back-translated.** For every vertex type:
1. for all graphs `H ≤ H'` with `V(H) = V(H')` and all reals `ε', s`: `H` an `(ε',s)`-expander ⇒
   `H'` an `(ε',s)`-expander;
2. for all `H` and reals with `ε'' ≤ ε'`, `s' ≤ s`: `(ε',s)`-expander ⇒ `(ε'',s')`-expander;
3. for all `G ≤ G'` with `V(G) = V(G')`, `W ⊆ W' ⊆ V(G)`, `ℓ ≤ ℓ'`, `t' ≤ t` (reals): `G`
   `(ℓ,t)`-path connected through `W` ⇒ `G'` `(ℓ',t')`-path connected through `W'`;
4. for every `X`, `W`, reals `ℓ, t`, every finite family of finite index types `ι k` (`k ∈ κ`) and
   pairs `P k i` of distinct vertices of `X` such that every vertex `v` is an entry of at most `t`
   pairs in total (sum over `k` of the occurrence counts): if `X` is `(ℓ,t)`-path connected through
   `W`, there are paths `Q k i` joining `P k i` in `X`, through `W`, of length `≤ ℓ`, pairwise
   edge-disjoint over all `(k,i)`;
5. for any two finite probability spaces with random graphs `X, X'` and random sets `W, W'` such
   that `(X,W)` and `(X',W')` have the same law, `P(X is (ℓ,t)-path connected through W)` is the
   same on both.

### s3:remMultiset — `MultisetCountStatement`

**TeX.** "Its counting step also holds when pairs are counted with multiplicity. The step says that
a maximal subfamily `I' ⊆ I` of pairwise vertex-disjoint pairs satisfies `2t|I'| ≥ |I|`. It holds
because every pair of `I` meets one of the `2|I'|` vertices covered by `I'`, and each vertex lies
in at most `t` pairs, counted with multiplicity."

**Lean, back-translated.** Let `P : ι → V × V` be a finite family of pairs of distinct vertices in
which every vertex is an entry of at most `t` pairs (`t` real, occurrences counted). Let
`I' ⊆ I ⊆ ι` be such that the vertex sets `{x_i, y_i}` (`i ∈ I'`) are pairwise disjoint and, for
every `i ∈ I \ I'`, the sets `{x_j, y_j}` (`j ∈ I' ∪ {i}`) are not pairwise disjoint. Then
`|I| ≤ 2t|I'|`.

### s3:eqS1 — `StarS1Statement`

**TeX.** "(S1) `2^{10}L^3−1 < ℓ_* ≤ 2^{10}L^3` and `ℓ_* ≥ 2^{10}`."

**Lean.** For every `n ≥ 2`: `2^{10}L^3 − 1 < ℓ_* ≤ 2^{10}L^3` (reals) and `2^{10} ≤ ℓ_*` (ℕ).
Proved in `EGTest/Spec_s3a.lean` from the Lib API (fidelity check).

### s3:eqS2 — `StarS2PStatement` and `StarUnionLawStatement`

**TeX.** "(S2) The number `p_*` exists, is unique, and satisfies `p_* ≥ 0.1ρ/ℓ_*`, so
`p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`. If `V_1,…,V_{ℓ_*}` are independent random subsets of a set `S`, where
`V_i` is `p_*`-random for `i < ℓ_*` and `V_{ℓ_*}` is `q_*`-random, then `V_1 ∪ ⋯ ∪ V_{ℓ_*}` is a
`ρ`-random subset of `S`." (with (eqStar): "`p_* ∈ (0,1]` given by
`(1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)`")

**Lean (`StarS2PStatement`).** For `n ≥ 2`, `0 < ρ ≤ 1`: the (explicit) `p_*` satisfies
`0 < p_* ≤ 1` and `(1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)` (natural power), and every `x ∈ (0,1]` with
`(1−x)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)` equals `p_*`. Proved in the test file (fidelity check). The middle
claim is the existing `StarS2NumStatement`.

**Lean (`StarUnionLawStatement`).** For any finite probability space `μ`, finite set `S`, `n ≥ 2`,
`0 < ρ ≤ 1`, and layers `V_i : Ω → Finset α` (`i ∈ Fin ℓ_*`) that are mutually independent
(`iIndepFun`), with layer `i` a `p_*`-random subset of `S` when `i + 1 < ℓ_*` and a `q_*`-random
subset of `S` for the last layer: the union `⋃_i V_i` is a `ρ`-random subset of `S` (its law is
`rsubset S ρ`).

### s3:eqS4 — `StarS4Statement`

**TeX.** "(S4) `8d_*λ_* ≤ 112p^{-2} ≤ θ_*` and `θ_* ≤ 2^{39}L^9/(ε'ρ^2) ≤ 2^{46}L^9ρ^{-2}`."

**Lean.** For `n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`: `8d_*λ_* ≤ 112 p_*^{-2}`,
`112 p_*^{-2} ≤ θ_*`, `θ_* ≤ 2^{39}L^9/(ε'ρ^2)`, `2^{39}L^9/(ε'ρ^2) ≤ 2^{46}L^9ρ^{-2}` (reals).

### s3:eqS5 — `StarS5Statement`

**TeX.** "(S5) `K_* ≥ s̄_*/μ_*`; `K_* ≤ (6·2^{81}+1)tL^{19}ρ^{-3} ≤ 2^{83.6}tL^{19}ρ^{-3}`;
`2K_*(θ_*+1) ≤ 2^{130.6}tL^{28}ρ^{-5}`; and `40K_*L ≤ 2K_*(θ_*+1)`. Proof: […] Likewise
`θ_*+1 ≤ (2^{46}+1)L^9ρ^{-2}`, and `log(2(6·2^{81}+1)(2^{46}+1)) < 130.6`. Finally
`θ_* ≥ 2^{19}L^3 ≥ 20L`."

**Lean.** For `n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `1 ≤ t`:
`s̄_*/μ_* ≤ K_*`; `K_* ≤ (6·2^{81}+1)tL^{19}ρ^{-3}`;
`(6·2^{81}+1)tL^{19}ρ^{-3} ≤ 2^{83.6}tL^{19}ρ^{-3}` (rpow);
`2K_*(θ_*+1) ≤ 2(6·2^{81}+1)(2^{46}+1)tL^{28}ρ^{-5}` (the proof's intermediate bound);
`2K_*(θ_*+1) ≤ 2^{130.6}tL^{28}ρ^{-5}` (rpow); `40K_*L ≤ 2K_*(θ_*+1)`.

### s3:eqS6 — `StarS6Statement`

**TeX.** "(S6) `σ_* ≥ 24`, `λ_*p ≥ 6` and `1 ≤ d_*p ≤ 1+p ≤ 2`."

**Lean.** For `n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`: `24 ≤ σ_*`, `6 ≤ λ_*p_*`, `1 ≤ d_*p_*`,
`d_*p_* ≤ 1 + p_*`, `1 + p_* ≤ 2`. Proved in the test file (fidelity check).

### s3:eqStar, P13* check — `StarP13sParamsStatement`

**TeX.** "The values `σ_*,λ_*,Δ_*,d_*` of (eqStar) satisfy the parameter hypotheses of
Proposition 13* below: `σ_* = 24L^2/ε'` holds with equality, and
`Δ_*−λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3 = 8d_*λ_*L^2/(ε'σ_*)`."

**Lean.** For `n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`: `σ_* = 24L^2/ε'`;
`d_*λ_*/3 ≤ Δ_* − λ_*`; `d_*λ_*/3 = 8d_*λ_*L^2/(ε'σ_*)`; and the hypotheses of `P13sStatement`
verbatim: `0 < σ_*`, `1 ≤ λ_*`, `1 ≤ d_*`, `λ_* ≤ Δ_*`, `24L^2/ε' ≤ σ_*`,
`8d_*λ_*L^2/(ε'σ_*) ≤ Δ_* − λ_*`. Proved in the test file (fidelity check).

### s3:propP13s — `P13sStatement`

**TeX.** "Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, and put
`L := log n`. Let `W ⊆ V(G)` with `1 ≤ |W| ≤ 2n/3`, and let `F ⊆ E(G)` with `|F| ≤ s_1|W|/4`. Let
`σ_* > 0` be real and let `λ_*,d_* ≥ 1` and `Δ_* ≥ λ_*` be integers such that
`σ_* ≥ 24L^2/ε'`, `Δ_*−λ_* ≥ 8d_*λ_*L^2/(ε'σ_*)`, `s_1 ≥ 8d_*λ_*`. Then `G−F` contains one of the
following: (a) at least `|W|/σ_*` vertex-disjoint stars, each with exactly `λ_*` leaves, its
centre in `W` and all its leaves in `V(G)\W`; or (b) a bipartite subgraph `H ⊆ G−F` with sides `W`
and `X ⊆ V(G)\W`, such that `|X| ≥ ε'|W|/(2L^2)`, every vertex of `X` has degree exactly `d_*` in
`H`, and every vertex of `W` has degree at most `Δ_*` in `H`."

**Lean, back-translated.** For every graph `G` that is an `(ε',s₁)`-expander with `|G| ≥ 2`,
`2^{-7} ≤ ε' ≤ 1`, every `W ⊆ V(G)` with `1 ≤ |W| ≤ 2|G|/3`, every `F ⊆ E(G)` with
`|F| ≤ s₁|W|/4`, every real `σ > 0` and naturals `λ, d ≥ 1`, `Δ ≥ λ` with `σ ≥ 24L^2/ε'`,
`8dλL^2/(ε'σ) ≤ Δ − λ` (real) and `8dλ ≤ s₁`: either
(a) there are `C ⊆ W` with `|C| ≥ |W|/σ` and sets `lv(c)` (`c ∈ C`) with `|lv(c)| = λ`,
`lv(c) ⊆ V(G) \ W`, every `x ∈ lv(c)` adjacent to `c` in `G − F`, and the `lv(c)` pairwise disjoint;
or (b) there are `X ⊆ V(G) \ W` and a graph `H ≤ G − F` with `V(H) = W ∪ X`,
`E(H) ⊆ E_G(W, X)`, `|X| ≥ ε'|W|/(2L^2)`, `deg_H(x) = d` for `x ∈ X`, and `deg_H(w) ≤ Δ` for
`w ∈ W`.

### s3:lemL17s — `L17sStatement`

**TeX.** "Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, let
`ρ ∈ (0,1]`, take the parameters of (eqStar) with `L := log n`, and assume `s_1 ≥ 8d_*λ_*`. Let
`V_1,…,V_{ℓ_*}` be independent random subsets of `V(G)`, where `V_i` is `p_*`-random for `i < ℓ_*`
and `V_{ℓ_*}` is `q_*`-random, and put `V := V_1 ∪ ⋯ ∪ V_{ℓ_*}`. By (S2), `V` is a `ρ`-random subset
of `V(G)`. Call `U ⊆ V(G)` well-expanding if `|Nbr_G(U)| ≥ θ_*|U|`. Then for every well-expanding
`U` and every `F ⊆ E(G)` with `|F| ≤ |U|`, `P(|B^{ℓ_*}_{G−F}(U,V)| ≤ |V|/2) ≤ exp(−7|U|L)`. Since
this event depends only on `V`, the same bound holds for every `ρ`-random subset `V` of `V(G)`."

**Lean, back-translated.** For every graph `G` that is an `(ε',s₁)`-expander with `|G| ≥ 2`,
`2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `8d_*λ_* ≤ s₁`, every finite probability space `μ` and random set
`R` that is a `ρ`-random subset of `V(G)`; for every `U ⊆ V(G)` and `F ⊆ E(G)` with `|F| ≤ |U|`
and `θ_*|U| ≤ |N_G(U)|`: `μ(|B^{ℓ_*}_{G−F}(U, R)| ≤ |R|/2) ≤ exp(−7|U| log₂ n)`.

### s3:lemP18s — `P18sStatement`

**TeX.** "Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, let
`ρ ∈ (0,1]`, take the parameters of (eqStar) with `L := log n`, and assume `s_1 ≥ θ_*+1`.
(i) (Proposition 18*.) Every `U ⊆ V(G)` with `1 ≤ |U| ≤ 2n/3` contains a set `U'` with
`|Nbr_G(U')| ≥ θ_*|U'|` and `|U'| ≥ ε'|U|/(3θ_*L^2)`. (ii) (Lemma 19*.) Let `V` be a `ρ`-random
subset of `V(G)`. With probability at least `1−n^{-6}` the following holds: for every nonempty
`U ⊆ V(G)` and every `F ⊆ E(G)` with `|F| ≤ μ_*|U|`, `|B^{ℓ_*}_{G−F}(U,V)| > |V|/2`."

**Lean, back-translated.** For every graph `G` that is an `(ε',s₁)`-expander with `|G| ≥ 2`,
`2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1` and `θ_* + 1 ≤ s₁`:
(i) every `U ⊆ V(G)` with `1 ≤ |U| ≤ 2n/3` has a subset `U'` with `θ_*|U'| ≤ |N_G(U')|` and
`ε'|U|/(3θ_*L^2) ≤ |U'|`;
(ii) for every finite probability space `μ` and `ρ`-random subset `R` of `V(G)`:
`1 − n^{-6} ≤ μ(for all nonempty U ⊆ V(G) and all F ⊆ E(G) with |F| ≤ μ_*|U|:
|R|/2 < |B^{ℓ_*}_{G−F}(U, R)|)`.

## Hazards and choices (T0 decisions)

| ID | Where | Decision |
|---|---|---|
| T0-L17-FORM | `L17sStatement` | Stated in the lemma's final form ("for every `ρ`-random subset `V` of `V(G)`", any finite space). The layered form is the special case obtained with `StarUnionLawStatement` ((S2)). Quantifier order: `∀ U F`, then the probability bound (not the single event of Lemma 19*). |
| T0-UNIV | `L17s`, `P18s`, `StarUnionLaw`, `Monotone` (law conjunct), `MultisetCount` | Universe-polymorphic: vertex type `Type u`, probability space / index type `Type v` (TRIAGE §2.5 asks for `Type`; this is more general and instantiates at `Type`). Needed because the consumer `EG.Spec.T16sStatement` (probe P4B) is stated for `V : Type u`, `Ω : Type v`, and T16*'s proof may apply P18*(ii) on a product space in `Type (max u v)`. |
| T0-P13-ENCODING | `P13sStatement` | Blueprint encoding P13-STAR-ENCODING: (a) centres `C ⊆ W` + leaf map `lv` with `|lv c| = λ`, `lv c ⊆ V(G)\W`, `(G−F)`-adjacency, `PairwiseDisjoint` on `C` (equivalent to vertex-disjoint stars since centres lie in `W` and leaves outside); (b) an `FGraph H` with `H ≤ G − F`, `V(H) = W ∪ X`, `E(H) ⊆ E_G(W,X)`, degrees `H.deg`. `λ, d, Δ : ℕ`; `Δ − λ` in `ℝ`. Satisfiability of each alternative checked in the test file. |
| T0-STAR-SPLIT | `EG/Spec/Link/Star.lean` | One Spec per fact instead of the blueprint's single `StarFactsStatement`, because (S2)-numeric and (S3) already exist (unit NUM, `EG/Spec/Num/StarInputs.lean`, proved). Each fact carries only the (eqStar) domain hypotheses on the inputs it mentions. |
| T0-S5-EXACT | `StarS5Statement` | Both the TeX's rpow bounds (`2^{83.6}`, `2^{130.6}`, written `(2:ℝ)^(83.6:ℝ)`) and the exact products (`(6·2^{81}+1)`, and the proof's intermediate `2(6·2^{81}+1)(2^{46}+1)`) are conjuncts. The intermediate is an extra (true) conjunct not in the statement line of (S5); Theorem 16*'s proof can compare it with `2^{135}` by `norm_num` (blueprint STAR-S5-RPOW). Margins: `log₂(6·2^{81}+1) ≈ 83.585`, `log₂(2(6·2^{81}+1)(2^{46}+1)) ≈ 130.585`. |
| T0-S2-P | `StarS2PStatement` | "`p_*` exists, is unique" is stated about the explicit Defs `Star.p`: it lies in `(0,1]`, solves the defining equation, and is the only solution in `(0,1]` (proved in the test file from `p_pos`, `p_le_one`, `one_sub_p_pow`, `p_unique`). |
| T0-S2-LAYERS | `StarUnionLawStatement` | Layers indexed by `Fin ℓ_*` (0-based), manuscript `V_i` = layer `i−1`; "`i < ℓ_*`" is `(i : ℕ) + 1 < ℓ_*`. Independence is `FinDist.iIndepFun` of the layers; the laws via `IsRSubset` (no proof terms in the statement). Hypotheses shown satisfiable (product space). |
| T0-P13-PARAMS | `StarP13sParamsStatement` | The paragraph after (S6) is stated with the hypotheses of `P13sStatement` written verbatim (`Real.logb 2 n`), so Lemma 17*'s proof can pass them without rewriting. |
| T0-MON-LAW | `MonotoneStatement`, last conjunct | "Depends only on the pair `(X,V)`" is automatic in Lean (the predicate is a function of `(X, W)`); its probabilistic use (equal laws of `(X,W)` ⇒ equal probability of the event) is stated as a conjunct (blueprint MON-MARGINAL). |
| T0-MON-II | `MonotoneStatement` (ii) | Keeps the manuscript's `V' ⊆ V(G)` (the Lib lemma `IsPathConnected.mono` does not need it; consumers use the Lib lemma). |
| T0-MON-JOINT | `MonotoneStatement` (iii) | Joint routing with the multiplicity bound on the SUM over the multisets (blueprint MON-JOINT-MULT); one multiset is `κ = Unit`. Index types in `Type` (as in `IsPathConnected`); `exists_paths` / `exists_paths_sigma` cover any universe. |
| T0-MULT-HYP | `MultisetCountStatement` | The multiplicity hypothesis is over the whole family (as the TeX: "each vertex lies in at most `t` pairs"); maximality of `I'` is literal (inclusion-maximal among pairwise vertex-disjoint subfamilies of `I`). The blueprint's weaker-hypothesis Lib form (cover only) is for the proof. |
| note | `L17sStatement` | `U ⊆ V(G)` and `F ⊆ E(G)` kept (CONVENTIONS: one-vertex paths put `u ∉ V(G)` into balls). `U = ∅` gives the trivial bound 1. |
| note | `P18sStatement` | Hypothesis `θ_* + 1 ≤ s₁` exactly (RT2-I12). (ii): the quantifiers over `U`, `F` are inside the event (P18-SINGLE-EVENT). |

## Existing Specs re-read (no problem found)

- `L15pStatement` (`EG/Spec/Link/L15.lean`): matches the TeX (both conjuncts, `[NeZero k]`,
  colours `Fin k`, `N^{-5}` as zpow).
- `StarS2NumStatement`, `StarS3Statement` (`EG/Spec/Num/StarInputs.lean`): match (S2)-numeric and
  (S3) of the TeX.

## Non-vacuity (EGTest/Spec_s3a.lean)

Checked: (eqStar) domain hypotheses satisfiable; `StarS1`, `StarS2P`, `StarS6`,
`StarP13sParams` PROVED from the locked Defs' Lib API; `StarUnionLaw` hypotheses satisfiable
(product space, coordinate layers); `MultisetCount` hypotheses satisfiable with the conclusion
holding; `IsRSubset R G.verts ρ` satisfiable; the P13* parameter hypotheses satisfiable and both
alternatives (a), (b) satisfiable on the path `0—1—2`; the Lemma 19* event non-contradictory; the
joint-routing hypotheses satisfiable.

Not checked: joint satisfiability of the expansion hypotheses (`P13s`, `L17s`: an expander with
`s₁ ≥ 8d_*λ_* ≥ 8`, `n ≥ 2`; `P18s`: `s₁ ≥ θ_* + 1 > 2^{39}`, only for huge `n`). No cheap library
expander with `s > 0` exists; nonempty well-expanding `U` needs `n > θ_*`.

## Math findings

None. No statement of the chunk appears false; the blueprint's re-derivations (including the
(S5) margins and the P13* parameter identity, which the test file proves) were rechecked at the
statement level.

## Fix round

Reviews: `s3a.review-fidelity-first.md` (the only review file present next to this status file).
One item raised, checked against the TeX (`s3.tex`, Remark s3:remMultiset) and the blueprint
(MS-COUNTING-HYP).

1. (minor) "`MultisetCountStatement` bounds the multiplicity over the whole family `ι`, whereas
   the counting step needs only the count within `I`." — **not an issue** (no change). Reasons:
   (a) fidelity: the TeX sentence is "each vertex lies in at most `t` pairs, counted with
   multiplicity", said of the multiset `𝒫` (the whole family `(x_i,y_i)_{i∈[r]}` of B-M Lemma 9,
   of which `I` is a subfamily), so the global count is the literal reading; restricting it to `I`
   would state a (true) strengthening that the remark does not assert; (b) truth: re-derived, each
   `i ∈ I` meets a vertex covered by `I'` (for `i ∉ I'` by maximality, since `I'` itself is pairwise
   disjoint the failing pair involves `i`), there are at most `2|I'|` such vertices, and each lies in
   at most `t` pairs of `ι ⊇ I`, so `|I| ≤ 2t|I'|`; (c) consumers: the only use is the counting step
   inside the proof of Lemma 9_ρ (and s6:lemJSLC through it), where the global bound holds anyway
   (it is the path-connectivity multiplicity hypothesis); per the blueprint (MS-COUNTING-HYP) the
   proof-side Lib lemma will take the cover property and the count over `I` only, and derive this
   Spec from it. The reviewer itself marks the item "Fine" with no fix.

Files changed in this round: this file only. No Lean file, Defs, other unit's file or root file
edited, so the build/check results above stand; `python3 -I scripts/lint.py` re-run: 0 findings.
