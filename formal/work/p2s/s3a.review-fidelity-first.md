# Clean-room review of the s3a Specs (fidelity first, model B)

Reviewer scope: the 6 new Spec modules listed in `work/p2s/s3a.md` (`EG/Spec/Link/{Monotone,
Multiset, Star, P13s, L17s, P18s}.lean`, 15 `…Statement` defs); the reused Specs
(`EG/Spec/Link/L15.lean`, `EG/Spec/Num/StarInputs.lean`) and the consumers (`T16s.lean`,
`L9rho.lean`) were read only for consistency. TeX: `proofs/manuscript/s3.tex` v6.1, lines 1–688.
No Lean file was edited.

Verdict: **approve**. Every new statement is a faithful back-translation of its TeX passage; none is
vacuous or weakened; no hidden hypothesis (in particular no Γ item at all appears in this chunk).
Five cosmetic/minor remarks are listed at the end. There are no findings on the manuscript.

## Checks run
- `python3 -I scripts/lint.py`: 0 findings.
- `lake build EG.Spec.Link.Multiset EG.Spec.Link.Star EG.Lib.Link.Star`: success.
- Scratch file (scratchpad `S3aRev.lean`, importing the Multiset and Star Specs and
  `EG.Lib.Link.Star`), compiled with 0 errors and 0 sorries. It proves:
  - the maximality clause of `MultisetCountStatement` is non-degenerate: with `I' = ∅` it forces
    `I = ∅` (a one-element family is trivially pairwise disjoint), so the conclusion `|I| ≤ 0` is
    never demanded of a nonempty `I`;
  - the last conjunct of `StarS4Statement` (`2^{39}L^9/(ε'ρ²) ≤ 2^{46}L^9ρ^{-2}`) from the locked
    Defs;
  - the last conjunct of `StarS5Statement` (`40K_*L ≤ 2K_*(θ_*+1)`, i.e. `θ_* ≥ 20L`) from the
    locked Defs.
- I read `EGTest/Spec_s3a.lean`; its checks are sound (S1, S2-P, S6 and the P13* parameter
  identity are PROVED there, so those four Specs agree with the locked definitions by construction).
- Numeric margins re-computed: `log₂(6·2^{81}+1) = 83.585 ≤ 83.6`,
  `log₂(2(6·2^{81}+1)(2^{46}+1)) = 130.585 ≤ 130.6`.

## Per statement

### MonotoneStatement ([s3:lemMonotone]): faithful
Back-translation (for every vertex type `V`):
1. `H ≤ H'`, `V(H) = V(H')`, `H` an `(ε',s)`-expander ⇒ `H'` an `(ε',s)`-expander — TeX (i), first
   sentence ("`H' ⊇ H` with `V(H') = V(H)`").
2. `ε'' ≤ ε'`, `s' ≤ s`, `(ε',s)`-expander ⇒ `(ε'',s')`-expander — TeX (i), second sentence. No sign
   conditions on the parameters, as in the TeX.
3. `G ≤ G'`, `V(G) = V(G')`, `W ⊆ W' ⊆ V(G)`, `ℓ ≤ ℓ'`, `t' ≤ t`, `G` `(ℓ,t)`-p.c. through `W` ⇒ `G'`
   `(ℓ',t')`-p.c. through `W'` — TeX (ii) verbatim, including `V' ⊆ V(G)`.
4. Joint routing: finitely many finite families `P k : ι k → V × V` of pairs of distinct vertices
   of `X`, each vertex in at most `t` pairs of the SUM over `k` of the occurrence counts; if `X` is
   `(ℓ,t)`-p.c. through `W` then there are paths of `X` for every `(k,i)`, through `W`, of length
   `≤ ℓ`, pairwise edge-disjoint across all `(k,i)`. This is the TeX's last sentence of (iii) ("every
   vertex lies in at most `t` pairs of the union multiset `𝒫_1+⋯+𝒫_q`"); the single-multiset
   sentence is the case `κ = Unit`. "Chosen adaptively" is automatic (the conclusion is a `∀`).
5. Two finite spaces on which `(X,W)` has the same law give the same probability of "`X` is
   `(ℓ,t)`-p.c. through `W`" — the probabilistic reading of "depends only on the pair `(X,V)`"
   (T0-MON-LAW). The deterministic reading is automatic in Lean.
- `IsExpander`, `IsPathConnected`, `IsPathBetween`, `IsThrough`, `pathLength`, `walkEdges` are the
  locked Defs of s1:citDef11, s1:citDef7, s1:convGraphs(d). The `≤` on `FGraph` is
  `verts ⊆ ∧ edges ⊆`, so "`H' ⊇ H`" is exactly `H ≤ H'`.
- The lemma is already proved in Lib (`IsExpander.of_le`, `IsExpander.mono`,
  `IsPathConnected.mono`, `exists_paths_sigma`); the Spec is a traceability record. Fine.

### MultisetCountStatement ([s3:remMultiset], counting step): faithful
Back-translation: `P : ι → V × V` a finite family of pairs of distinct vertices, every vertex an
entry of at most `t` indices (`t` real, occurrences counted, over the whole family, as the TeX's
"each vertex lies in at most `t` pairs, counted with multiplicity"); `I' ⊆ I ⊆ ι`; the vertex sets
`{x_i,y_i}` (`i ∈ I'`) pairwise disjoint; for every `i ∈ I \ I'` the sets over `I' ∪ {i}` are not
pairwise disjoint (inclusion-maximality, literal). Then `|I| ≤ 2t|I'|` (real).
- True (re-derived): each `i ∈ I \ I'` meets a vertex covered by `I'` (the failing pair must involve
  `i`, since `I'` itself is pairwise disjoint and `i ∉ I'`); each of the `2|I'|` covered vertices
  lies in one pair of `I'` and hence in at most `t − 1` pairs of `I \ I'`; so
  `|I| ≤ |I'| + 2(t−1)|I'| ≤ 2t|I'|`. If `I' = ∅` then `I = ∅` (scratch check), and `t` may be
  anything.
- Items 1, 2, 5 of the remark are built into `IsPathConnected` (checked against its docstring and
  body: indexed family, one path per index, ends only required in `V(G)`, `t` counts occurrences);
  item 3 is commentary. Nothing is missing.

### StarS1Statement ([s3:eqS1]): faithful (proved in the test file)
`2^{10}L^3 − 1 < ℓ_* ≤ 2^{10}L^3` (reals) and `2^{10} ≤ ℓ_*` (ℕ), for `n ≥ 2`. `L = Star.L n =
logb 2 n` by `rfl`. The TeX hypothesis is only `n ≥ 2`; correct.

### StarS2PStatement ([s3:eqS2], existence/uniqueness): faithful (proved in the test file)
For `n ≥ 2`, `0 < ρ ≤ 1`: `0 < p_* ≤ 1`, `(1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)` (ℕ exponent; `ℓ_* ≥ 2^{10}`
so the truncated subtraction is harmless), and every `x ∈ (0,1]` solving the equation equals
`p_*`. This is exactly "`p_* ∈ (0,1]` given by … exists, is unique". The literal `0.9` is the
real `9/10` of the Defs (the test proves the bridge). The numeric part (`p_* ≥ 0.1ρ/ℓ_*`,
`p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`) is the reused `StarS2NumStatement`, which I re-read: it matches.

### StarUnionLawStatement ([s3:eqS2], union law): faithful
Any finite space `μ`, any finite `S : Finset α`, layers `Vs ω : Fin ℓ_* → Finset α`, mutually
independent (`iIndepFun`), layer `i` a `p_*`-random subset of `S` when `i+1 < ℓ_*` (manuscript
`V_{i+1}`, `i+1 < ℓ_*`) and a `q_*`-random one for the last layer; conclusion: the union of all
layers is a `ρ`-random subset of `S` (`IsRSubset … S ρ`, i.e. its law is `rsubset S ρ`).
- TeX: "If `V_1,…,V_{ℓ_*}` are independent random subsets of a set `S`, where `V_i` is `p_*`-random
  for `i < ℓ_*` and `V_{ℓ_*}` is `q_*`-random, then `V_1 ∪ ⋯ ∪ V_{ℓ_*}` is a `ρ`-random subset of
  `S`." The 0-based reindexing is exact (`Fin ℓ_*` has `ℓ_*` layers, the last is index `ℓ_*−1`).
- True: an element of `S` avoids all layers with probability `(1−p_*)^{ℓ_*−1}(1−0.9ρ) = 1−ρ`, and the
  element indicators are jointly independent because the layers are independent and each layer's
  law is a product; a.s. every layer is `⊆ S`.
- Hypotheses satisfiable (test file: product space with coordinate layers).

### StarS4Statement ([s3:eqS4]): faithful
Four real inequalities under `n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`: `8d_*λ_* ≤ 112p_*^{-2}`,
`112p_*^{-2} ≤ θ_*`, `θ_* ≤ 2^{39}L^9/(ε'ρ^2)`, `2^{39}L^9/(ε'ρ^2) ≤ 2^{46}L^9ρ^{-2}`. `p^{-2}` is
`(p)⁻¹^2` as in `StarInputs`; `ρ^{-2}` is zpow. Exactly the TeX chain. Re-derived:
`d_*λ_* ≤ (p^{-1}+1)(6p^{-1}+1) ≤ 14p^{-2}`; `112p^{-2} ≤ 11200ℓ_*^2ρ^{-2} ≤ 2^{19}ℓ_*^2L^3/(ε'ρ^2)`;
`ℓ_*^2 ≤ 2^{20}L^6`; `ε' ≥ 2^{-7}`. The last conjunct is proved in my scratch file.

### StarS5Statement ([s3:eqS5]): faithful, with one extra (true) conjunct
Under `n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `1 ≤ t`: `s̄_*/μ_* ≤ K_*`;
`K_* ≤ (6·2^{81}+1)tL^{19}ρ^{-3}`; `(6·2^{81}+1)tL^{19}ρ^{-3} ≤ 2^{83.6}tL^{19}ρ^{-3}` (rpow);
`2K_*(θ_*+1) ≤ 2(6·2^{81}+1)(2^{46}+1)tL^{28}ρ^{-5}` (the proof's intermediate, extra);
`2K_*(θ_*+1) ≤ 2^{130.6}tL^{28}ρ^{-5}` (rpow); `40K_*L ≤ 2K_*(θ_*+1)`.
- All four TeX claims are present with the TeX's constants and rpow exponents; the extra
  conjunct is the TeX proof's own bound and is true (margins re-computed above). Stating it does
  not weaken anything. `t ≥ 1` is needed for "the rounding adds at most `1 ≤ tL^{19}ρ^{-3}`" and is
  the (eqStar) domain hypothesis.
- Re-derived: `6s̄_*θ_*L^2/ε' ≤ 6·2^{28}·2^{39}·2^{14}·tL^{19}ρ^{-3}`; `θ_* ≥ 2^{19}L^3 ≥ 20L`
  (scratch file proves the last conjunct).

### StarS6Statement ([s3:eqS6]): faithful (proved in the test file)
`24 ≤ σ_*`, `6 ≤ λ_*p_*`, `1 ≤ d_*p_*`, `d_*p_* ≤ 1+p_*`, `1+p_* ≤ 2`: the TeX's chain
`σ_* ≥ 24`, `λ_*p ≥ 6`, `1 ≤ d_*p ≤ 1+p ≤ 2` split into its links. The TeX proof needs only
`ε' ≤ 1 ≤ L`; the Spec carries the full (eqStar) domain, which is fine (it is how consumers hold it).

### StarP13sParamsStatement ([s3:eqStar], paragraph after (S6)): faithful (proved in the test file)
`σ_* = 24L^2/ε'`; `d_*λ_*/3 ≤ Δ_* − λ_*`; `d_*λ_*/3 = 8d_*λ_*L^2/(ε'σ_*)`; then the six parameter
hypotheses of `P13sStatement` verbatim (I compared token by token: `0 < σ`, `1 ≤ λ`, `1 ≤ d`,
`λ ≤ Δ`, `24·logb 2 n^2/ε' ≤ σ`, `8dλ·logb 2 n^2/(ε'σ) ≤ Δ − λ`). The TeX's
"`Δ_*−λ_* = ⌈d_*λ_*/3⌉`" is the definition (`Star.Delta_eq`); its consequence `≥ d_*λ_*/3` is
stated. The hypothesis `s_1 ≥ 8d_*λ_*` of P13* is about `s_1`, not a parameter, and is correctly
left to L17*'s hypothesis.

### P13sStatement ([s3:propP13s]): faithful
Hypotheses, in order: `G` an `(ε',s₁)`-expander, `2 ≤ n`, `2^{-7} ≤ ε' ≤ 1`, `W ⊆ V(G)`,
`1 ≤ |W|` (ℕ), `|W| ≤ 2n/3` (ℝ), `F ⊆ E(G)`, `|F| ≤ s₁|W|/4`, `σ > 0` real, `λ, d ≥ 1`, `Δ ≥ λ`
(naturals, hence positive integers as in the TeX), `σ ≥ 24L^2/ε'`, `8dλL^2/(ε'σ) ≤ Δ − λ` (real
difference), `8dλ ≤ s₁`. All fourteen TeX hypotheses, none extra.
- (a): centres `C ⊆ W` with `|C| ≥ |W|/σ`, each centre `c` with exactly `λ` leaves `lv c ⊆ V(G) \ W`,
  every leaf adjacent to `c` in `G − F`, leaf sets pairwise disjoint over `C`. Vertex-disjointness of
  the stars is equivalent: centres are distinct elements of `W`, leaves lie outside `W`, leaf sets are
  disjoint. "At least `|W|/σ_*` stars" is `|W|/σ ≤ |C|` (non-strict, as the TeX).
- (b): `X ⊆ V(G) \ W`, `H ≤ G − F`, `V(H) = W ∪ X`, `E(H) ⊆ E_G(W,X)` (every edge joins `W` to `X`;
  `edgesBetween` is used on the disjoint pair `W`, `X`, per CONVENTIONS), `|X| ≥ ε'|W|/(2L^2)`,
  `deg_H(x) = d` on `X`, `deg_H(w) ≤ Δ` on `W`. `H.deg` counts `H`-neighbours; since `H`'s edges have
  their ends in `V(H)`, this is the degree in `H`. This is "a bipartite subgraph `H ⊆ G − F` with
  sides `W` and `X`".
- I re-read the TeX proof and confirmed the statement's constants are what the proof delivers
  (`|X| ≥ 2ε'|W|/(3L^2) ≥ ε'|W|/(2L^2)`; `39λ_* < 1` contradiction in Case 1). Both alternatives
  are shown satisfiable in the test file; the hypotheses are jointly satisfiable (e.g. `K_n`,
  `n = 2^{10}`, `ε' = 1`, `s₁ = 48`, `λ = 6`, `d = 1`, by hand).

### L17sStatement ([s3:lemL17s]): faithful (final form, T0-L17-FORM)
Back-translation: `G` an `(ε',s₁)`-expander, `2 ≤ n`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`,
`8d_*λ_* ≤ s₁`; any finite space `μ` and `R` a `ρ`-random subset of `V(G)`; for every `U ⊆ V(G)`,
`F ⊆ E(G)` with `|F| ≤ |U|` (ℕ) and `θ_*|U| ≤ |Nbr_G(U)|`:
`P(|B^{ℓ_*}_{G−F}(U,R)| ≤ |R|/2) ≤ exp(−7|U|·log₂ n)`.
- This is the lemma's closing sentence ("the same bound holds for every `ρ`-random subset `V` of
  `V(G)`"), which is the strongest form the TeX asserts; the layered form is its special case via
  `StarUnionLawStatement`. Quantifier order (`U`, `F` fixed, then the probability) is the TeX's.
- `IsWellExpanding θ U := θ|U| ≤ |nbrSet U|` with `nbrSet` the outside neighbourhood in `G` (not
  `G − F`): the TeX's "Call `U ⊆ V(G)` well-expanding if `|Nbr_G(U)| ≥ θ_*|U|`". `ball` is
  s1:convGraphs(d) (ends free, interior in `R ω`, ball `⊆ R ω`), `deleteEdges` keeps the vertices,
  `ℓ_* = Star.ell n : ℕ` is the radius. `exp` is `Real.exp`, `L = Real.logb 2 n` — base 2 as
  s1:convGraphs(b). `U = ∅` gives probability `≤ 1 = exp 0`, as the TeX says.
- Consumer form: P18s(ii)'s union bound needs exactly this shape (per pair `(U',F')`, event on the
  same `R`); `T16sStatement` passes `Ω : Type v`, matched here.

### P18sStatement ([s3:lemP18s]): faithful
Under `G` an `(ε',s₁)`-expander, `2 ≤ n`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `θ_* + 1 ≤ s₁` (exactly the
RT2-I12 form; not `θ_* ≤ s₁`):
- (i) every `U ⊆ V(G)` with `1 ≤ |U|` (ℕ) and `|U| ≤ 2n/3` (ℝ) has `U' ⊆ U` with
  `θ_*|U'| ≤ |Nbr_G(U')|` and `ε'|U|/(3θ_*L^2) ≤ |U'|`. Matches Proposition 18* (the proof even
  gives strict `>`; the TeX states `≥`).
- (ii) for every finite space and every `ρ`-random subset `R` of `V(G)`:
  `1 − n^{-6} ≤ P(∀ nonempty U ⊆ V(G), ∀ F ⊆ E(G), |F| ≤ μ_*|U| → |R|/2 < |B^{ℓ_*}_{G−F}(U,R)|)`.
  The quantifiers over `U`, `F` are inside the event, as the TeX ("With probability at least
  `1−n^{-6}` the following holds: for every …"); `n^{-6}` is zpow; `>` is strict as in the TeX.
- The proof's chain was re-checked at the statement level: `2μ_* = ε'/(3θ_*L^2)` (so (i) supplies
  a well-expanding `U'` with `|U'| ≥ 2μ_*|U| ≥ |F|`), `e_G ≥ 2` from `δ(G) > s₁ ≥ 1` (needs
  `ε' > 0` and `n ≥ 2`, both hypotheses; T0-def11-eps), pair count `≤ n^{3u}`, `7 log₂ e = 10.099`,
  `Σ_{u≥1} n^{-7.09u} ≤ n^{-6}` for `n ≥ 2`. The `[n/2, 2n/3]`-integer step holds for every `n ≥ 2`.
- The event is exactly the ball hypothesis of `L9rhoStatement` (same `ball`/`deleteEdges`/
  `Star.ell` shape, `W = R ω`), so the consumer form is right; the thresholds `μ_*` vs `s̄_*` are
  bridged by T16*, as intended.

## Vacuity
- No contradictory hypotheses: the (eqStar) domain is satisfiable; `IsRSubset R G.verts ρ` is
  satisfiable (`rsubset`); expander hypotheses with `s₁ ≥ 8d_*λ_*` (P13s, L17s) and `s₁ ≥ θ_*+1`
  (P18s) are satisfiable by complete graphs (`n = 2^{10}` resp. `n ≈ 2^{110}`, by hand — no Lean
  example, as s3a.md says).
- No trivially true conclusions: `MultisetCount`'s maximality is non-degenerate (scratch);
  Monotone's law conjunct is an equality of two `prob`s on different spaces; the P13s alternatives
  and the Lemma-19* event are checked non-contradictory in the test file.
- The Statement-level facts S1, S2-P, S6, P13sParams are PROVED in the test file: they are true of
  the locked Defs, which is the fidelity check for the `0.9`/`9/10` literal, the ℕ exponent and the
  hypothesis shape. S4 and S5 are true (re-derived above; two conjuncts machine-checked).

## Consistency and hygiene
- Reuse: `Star.*` (locked Defs), `IsWellExpanding` from `EG/Defs/Graph.lean` (not redefined),
  `ball`, `deleteEdges`, `edgesBetween`, `deg`, `IsExpander`, `IsPathConnected`, `FinDist`,
  `IsRSubset`, `iIndepFun`, `map`, `prob`. `StarS2NumStatement` and `StarS3Statement` are reused,
  not restated; no duplicated statement. `L15pStatement` is untouched.
- No Γ hypothesis anywhere in the chunk (none is stated in the TeX either); in particular no
  Γ2(b),(c). No hidden hypothesis: every Lean hypothesis is traceable to the quoted TeX sentence.
- Docstrings begin with the manuscript label and quote the statement. Module headers are
  `module` / `public import` / `@[expose] public section`. `scripts/lint.py`: 0 findings.
- Universe choices (`V : Type u`, `Ω`/`ι : Type v`, index types of joint routing in `Type`) match
  `T16sStatement` and `IsPathConnected`.

## Remarks (none blocking)
1. (cosmetic) `Star.L n` and `Real.logb 2 n` are mixed across the Star Specs (`StarP13sParams`
   uses `Real.logb` to match `P13sStatement`; S1/S4/S5/S6 use `Star.L`). They are `rfl`-equal
   (`Star.L_eq`); a consumer may need one `rw [Star.L_eq]`.
2. (cosmetic) `StarS5Statement` carries the proof's intermediate bound
   `2(6·2^{81}+1)(2^{46}+1)tL^{28}ρ^{-5}` as a fifth conjunct. It is not in the (S5) statement line
   but is asserted by its proof and is true; the docstring says so.
3. (minor) `MultisetCountStatement` bounds the multiplicity over the whole family `ι`, as the TeX
   sentence does; the counting step only needs the count within `I`. This is the faithful
   (weaker-conclusion) form; the blueprint's Lib form covers the proof. Fine.
4. (cosmetic) `MonotoneStatement` (iii), joint routing, takes `κ : Type` and `ι : κ → Type`
   (universe 0), like `IsPathConnected`; the Lib lemma `exists_paths_sigma` is universe-polymorphic,
   and consumers use the Lib lemma, so nothing is lost.
5. (cosmetic) `P13sStatement` (a) leaves `lv` total on `V`; values outside `C` are irrelevant. The
   TeX's "vertex-disjoint stars" and the encoding are equivalent, as argued above.

## Math findings
None. All numerical claims of (S1)–(S6), of the P13* parameter paragraph, and the constants of
the proofs of P13*, L17* (Steps 0–5: `273ℓ_*uL`, `2^{19}/28200 > 18.59`, `0.09/4.2 > 1/47`,
`2^{10}e^{-11} < 0.02`, `1/412 − 1/413 > 2^{-36}`) and L19* (`n^{3u}` pair count, `10.09`,
`n^{-6}`) were re-derived and hold with the stated margins.
