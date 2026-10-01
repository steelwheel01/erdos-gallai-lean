# Clean-room review of the s6a Specs (lens: fidelity-first, model B)

Reviewed: `work/p2s/s6a.md`; the Spec files it lists, `EG/Spec/Chain/{Gate,MED,EqLpt,PAR,HCCP,CONC,ConcTower}.lean`;
the probe Defs `EG/Defs/Probe/P2E/Par.lean`, `EG/Defs/Probe/P3B/TowerFns.lean`; the locked Defs they read,
`EG/Defs/Chain/{Cluster,HCCP,EqLpt,Design}.lean`, `EG/Defs/{Orient,Objects,Walk,Components,Log}.lean`,
`EG/Defs/Gamma/Core.lean`, `EG/Defs/HB/{Run,Round}.lean` (`graph`, `d`, `tau`, `Std`, `Z0`, `DupStar`, `parts`,
`stdParts`, `ancestors`, `anc`, `classed`, `tauOf`, `MOf`, `sOf`); the TeX `proofs/manuscript/s6.tex` lines 1–333
(v6.1) and s2:lemTower(a) (s2.tex 1144–1150); the blueprint hazard index (`work/p2/blueprint_s6a.md` §3), TRIAGE
§2.6, §2.9, and the probe notes `work/p2b/P2E.md`, `work/p2b/P3B.md` (deviations and T0 sections); the test file
`EGTest/Spec_s6a.lean`. I edited no Lean file.

**The chunk introduces no new Spec, no new Defs file, and edits nothing** (status file, confirmed: every label of
the chunk maps to a pre-existing Spec, each with a `sorry`-free proof in `EG/Proof/Chain/`). So this review
re-checks the eleven existing statements the chunk maps to against the TeX, with the fidelity-first lens.

**Verdict: approve.** I found no fidelity defect: every statement is at least as strong as the TeX sentence it
carries, with the recorded T0 encodings (below) and no hidden hypothesis. No Γ2(b),(c) anywhere; the only Γ item
used is `Gamma1core` (CONC (iii), the two sums, the tower facts, `KStar`). Lint: `python3 -I scripts/lint.py`
= 0 findings. I re-ran `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/Spec_s6a.lean 1200`: rc=0, 0 errors,
0 sorry. The oleans of the seven Spec modules are newer than their sources (built 2026-09-26 … 2026-09-29).
Minor remarks (cosmetic, no Spec change): C1–C4 below.

## 1. Fidelity (back-translation next to the TeX)

Since every Spec is proved, a fidelity defect could only be a *weakening* (hidden hypothesis, weaker
conclusion, lost quantifier). I looked for exactly that.

### `GateStatement`, `GatePreciseStatement` [s6:lemGATE]
Back-translation. For every finite simple graph `G`, edge set `F ⊆ E(G)`, arc set `A` that is an orientation of
`F` (every arc a non-loop whose edge is in `F`; every edge of `F` has exactly one arc), balanced at every
vertex (`outDeg = inDeg` for all `v : V`), and `W ⊆ A` with `A \ W` acyclic: (first) there is a list `D` of
objects decomposing `F` (well-formed, edge-disjoint, edges exactly `F`), `|D| ≤ |W|`, every object a cycle
with all edges in `E(G)`; (precise) there is a list of vertex lists `cs`, each a directed cycle of `A`, of
length ≥ 3, a well-formed cycle object, all edges in `E(G)`, containing an arc of `W`; the concatenated arc
lists are duplicate free and equal `A` as a set; `|cs| ≤ |W|`.
TeX: "Let `F ⊆ E(G)` and let `F⃗` be an orientation of `F` with `d⁺(v) = d⁻(v)` at every vertex `v`. Let
`𝒲` be a set of arcs of `F⃗` such that `F⃗ − 𝒲` is acyclic. Then `F` decomposes into at most `|𝒲|` cycles of
`G`. More precisely, `F⃗` is the arc-disjoint union of directed cycles, each of length at least 3, each the
orientation of a cycle of `G`, and each containing an arc of `𝒲`; there are at most `|𝒲|` of them."
Checked: `IsBalanced` is global, as the TeX says ("at every vertex"); `W ⊆ A` is the TeX "set of arcs of
`F⃗`"; "orientation of a cycle of `G`" = `IsDirCycle A c ∧ (Obj.cycle c).WF ∧ cycleEdges c ⊆ G.edges`;
"decomposes" = `IsDecomp` of [s1:defObject] (objects WF). Nothing weaker than the TeX. Faithful.

### `MedStatement` (a), `MedExcStatement` (b) [s6:lemMED]
Back-translation (a). For every cluster `K` that is parity-clean (every hub has even bead degree) and every
`rk : V → ℕ` injective on the ports: `medOrient rk` is admissible (an acyclic orientation of the beads,
balanced at every hub), and there is `pot : V → ℝ` with `0 < pot v < 1` on `V(K) = A ∪ U` and
`pot a.1 < pot a.2` for every arc of `medOrient rk`.
(b). For every parity-clean `K` and every admissible `O`: for every port `u`, `|exc(u)| ≤ deg_B(u)` and
`exc(u) − deg_B(u)` is even (in ℤ); `Σ_{u ∈ U} exc(u) = 0` (ℤ); `(Φ(K) : ℝ) ≤ b(K)`.
TeX: "Let `𝒦` be a parity-clean cluster and `≺` a linear order on `U_𝒦`. (a) `MED(≺)` is an admissible
orientation. There is a function `pot : A_𝒦 ∪ U_𝒦 → (0,1)` that strictly increases along every arc of
`MED(≺)`. (b) For every admissible orientation of `𝒦`, in particular for `MED(≺)`, and every port `u`:
`|exc(u)| ≤ deg_{B_𝒦}(u)` and `exc(u) ≡ deg_{B_𝒦}(u) (mod 2)`. Moreover `Σ_{u∈U_𝒦} exc(u) = 0` and
`Φ(𝒦) ≤ b(𝒦)`."
Checked: the order `≺` as a rank injective on the ports loses nothing (every linear order of a finite set is of
this form) and `medOrient` reads `rk` only through comparisons between ports (`beadNbrs h ⊆ ports` for a hub
`h`, by `no_hub_hub` + `ends_mem`; the port–port clause compares two ports). `pot` is required on `K.verts`,
the TeX domain; all arcs of `medOrient` have both ends in `K.verts` (its definition filters
`K.verts ×ˢ K.verts`). (b) quantifies over every admissible `O`, as the TeX; the standing "parity-clean" is
kept (it is implied by admissibility, so the consumer form is unaffected). `b(K)` is the real
`Σ_h deg(h)/2 + e(B[U])` — exact, no ℕ-division. Faithful.

### `EqLptStatement`, `EqLptExistsStatement` [s6:lemEQLPT]
Back-translation. For all `m, k : ℕ` with `1 ≤ k ≤ m`, loads `Φ : Fin m → ℝ` antitone and ≥ 0: (exists) some
`σ : Fin m → Fin k` is a greedy placement (`IsGreedyLPT`: item `i` goes to a layer of minimum load among the
loads just before `i`, and to an empty layer whenever one is empty just before `i`); (lemma) every greedy `σ`
is onto and `L_j − L_{j'} ≤ Φ_1` for all layers `j, j'` (`L_j = Σ_{σ i = j} Φ i`, `Φ_1 = Φ ⟨0,_⟩`).
TeX: "Let `Φ_1 ≥ … ≥ Φ_m ≥ 0` be loads of `m` items, and let `1 ≤ k ≤ m`. Place the items in the order
`1, …, m` into `k` initially empty layers. Each item goes to a layer of currently minimum load, and to an
empty layer whenever one exists. Then all `k` layers are non-empty, and the final layer loads satisfy
`max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`."
Checked: `∀ j j', L_j − L_{j'} ≤ Φ_1` is `max − min ≤ Φ_1` (the layers are non-empty as a type since
`k ≥ 1`); reals, not ℕ (EQ-REAL-VS-NAT); the rule is a relation and the lemma is for *every* greedy placement,
which is the faithful "then"; existence is the proof's first sentence, stated separately. Faithful.

### `ParExistsStatement`, `ParStatement` [s6:lemPAR]
Back-translation. For every edge set `E` and vertex sets `V_a, V_b` disjoint with every edge of `E` of the form
`s(a,b)`, `a ∈ V_a`, `b ∈ V_b`: (exists) every odd component (component of `(V(E),E)` with an odd number of
edges) contains an edge of `E` that is a non-bridge or pendant (an end of `E`-degree 1), and some `J'` is an
admissible choice (`IsParChoice`: `J' ⊆ E`, exactly one edge of `J'` in each odd component and none in the
other components, every edge of `J'` non-bridge or pendant); (lemma) for every such `J'`: `|J'| ≤ #odd`,
`#odd ≤ |V(E)|/2` (reals), and there are disjoint `S_a, S_b` with `S_a ∪ S_b = E \ J'`, every `v ∈ V_b` of
even `S_a`-degree and every `u ∈ V_a` of even `S_b`-degree.
TeX: "Let `E_ab` be a bipartite graph with sides `V_a, V_b` … In each odd component choose one edge that is
either a non-bridge or a pendant edge … of that component; such an edge exists. Let `J'` be the set of chosen
edges. Then, for *every* such choice, `|J'| ≤ #{odd components} ≤ |V(E_ab)|/2`, and there is a partition
`E_ab ∖ J' = S_a ⊔ S_b` such that every vertex of `V_b` has even `S_a`-degree and every vertex of `V_a` has even
`S_b`-degree."
Checked: `Disjoint V_a V_b` is the content of "bipartite with sides" and is needed (blueprint counterexample
PAR-SIDES-DISJOINT, `V_a = V_b = {x,y,z}`, `E = {xy,yz}`); the consumer (JS-LC) has disjoint sides. "Of that
component" for non-bridge/pendant is the global predicate on `E`, which is equivalent (Components docstring).
Components are those of `(V(E),E)` (`edgeComps`), so no isolated singleton is counted as odd. Faithful.

### `HccpStatement` [s6:lemHCCP]
Back-translation. For every graph `G` and system `S` (`k`, `N` clusters `K i` with orientations `O i` and layers
`lay i : Fin k`, junction sets `T j`, padding `pad`, path families `P j : List (List V)`) with `S.Valid G`:
`k ≥ 1`; each `O i` admissible; beads ⊆ `E(G)`; the `T j` pairwise disjoint; `pad = 0` on all ports if
`k = 1`; hub∪port sets of distinct indices disjoint, and disjoint from every `T j`; every cluster
parity-clean; every path of `P j` a path of `G` from a vertex of `LayP_j` to a vertex of `LayP_{(j+1) mod k}`
with interior in `T j`; every `u ∈ LayP_j` the head of exactly `dem⁻(u)` members of `P j`, every
`v ∈ LayP_{j+1}` the last vertex of exactly `dem⁺(v)` members; members pairwise edge-disjoint; the `E(P_j)`
pairwise disjoint, disjoint from all bead sets, bead sets of distinct indices disjoint. Then there is `Φ : ℕ`
with `Φ_j = Φ` and `|P_j| = Φ` for every `j`, and sets `F j ⊆ E(P_j)` with `E(P_j) \ F j ⊆ E(G[T_j])`, and a
decomposition of `⋃_i B_{K i} ∪ ⋃_j F j` into at most `Φ` objects, each a cycle of length ≥ `max 3 k` with all
edges in `E(G)`.
TeX hypotheses (D), (P), (JC-P) and conclusions (i), (ii): quoted clause by clause in `HccpData.Valid` and in
the Spec docstring. Checked: `dem⁻ = exc⁻ + pad`, `dem⁺ = exc⁺ + pad`, `Φ_j = Σ_{LayP_j} dem⁺` as in the TeX;
`exc(u)` is taken in the (by (D) unique) cluster containing `u` (`pexc`); the `k = 1` reading
(`X^out → X^in`) is the uniform reading with `succ 0 = 0`, `pad = 0` (a head `u` needs `dem⁻(u) = exc⁻(u) ≥ 1`,
so `u ∈ X^out`; likewise for last vertices), proved equivalent in Lib (`jcp_iff_jcpOne`); (D) for distinct
*indices* is the reading over families with multiplicity (an injective indexing represents every TeX
instance, so nothing is lost); `E(G[T_j])` is `(G.induce (T j)).edges` (edges of `G` with both ends in `T j`);
"length ≥ max(3,k)" is kept (`c.length` = number of edges of the cycle). `beads_G` is the `B ⊆ E(G)` part of
"`B_𝒦 ⊆ E(G[A ∪ U])`" of [s6:defCluster], the rest being the cluster axioms. Faithful.

### `HccUnionStatement` [s6:lemHCCglob] ¶1
Back-translation. For every `q`, pairwise disjoint `E i ⊆ E(G)` (`i : Fin q`) and decompositions `D i` of
`E i`: there is a decomposition `D'` of `⋃ E i` with `|D'| = Σ |D i|`.
TeX: "Let `E_1, …, E_q ⊆ E(G)` be pairwise disjoint, and suppose each `E_i` decomposes into `a_i` objects. Then
`E_1 ∪ ⋯ ∪ E_q` decomposes into `Σ_i a_i` objects." Exact count, as the TeX. `E i ⊆ E(G)` is kept although
unused. Faithful.

### `HccGlobStatement` [s6:lemHCCglob] ¶2 (T0-glob-input)
Back-translation. For every family of `q` systems, each valid for `G`, with `beads ∪ allPathEdges` of distinct
systems pairwise disjoint: there are `Φ s` with `(S s).Phi j = Φ s` for all `s, j`, sets `F s j ⊆ E(P_j(s))`
with `E(P_j(s)) \ F s j ⊆ E(G[T_j(s)])`, and a decomposition of `⋃_s (B(S s) ∪ ⋃_j F s j)` into at most
`Σ_s Φ s` objects, all cycles with edges in `E(G)`.
TeX: "suppose several systems satisfy the hypotheses of Lemma HCC-P separately …, and the edge sets they
decompose (their beads together with their sets `F_j`) are pairwise disjoint. Then the union of these edge
sets decomposes into at most the sum of their values `Φ`. No vertex-disjointness across systems is needed."
The literal hypothesis names the outputs `F_j`. The Spec assumes input-level disjointness (beads and all path
edges), which implies the literal one (`F_j ⊆ E(P_j)`) and is exactly what JS-LC Step 7 verifies; recorded
in CONVENTIONS (T0 row `T0-glob-input`). No cross-system vertex condition is assumed (GLOB-NO-VERTEX-DISJ
respected). `Φ s` is determined by `∀ j, Phi j = Φ s` since `k ≥ 1`. Faithful in the consumer's form.

### `ConcIStatement`, `ConcIIStatement`, `ConcIIIStatement` [s6:thmCONC] (i)–(iii)
Back-translation. (i) For every graph `G`, real `D_*`, run valid for `(G, D_*)`, every round `r`, every
`a ∈ Std_r`, every `l ≥ r + 1` and every vertex `h`: `#{u ∈ Z⁰_r(a) \ Dup*_r : s(h,u) ∈ E(G_l)} ≤ τ_r − 1`
(ℕ-subtraction). (ii) Additionally for every designation `δ` (`IsDesignation`: `δ l u ∈ anc_l(u)` for every
classed port `u` of a standalone pre-part of round `l ≥ 3`), every `r`, `a ∈ Std_r`, every `l`:
`m_{(r,a),l} ≤ τ_r − 1 + d*_{(r,a),l}`. (iii) Under `Gamma1core D_*`, valid run, designation:
`Σ_{l=1}^{R} Σ_{Y ∈ stdParts} m_{Y,l} ≤ 2^{σ+14} n log* D_*/log₂ D_* + 100 ε n log* D_*/(C' log₂ log₂ D_*)`
with `n = |V(G)|`, `σ = 100`, `ε = 2^{-5}`, `C' = 103`.
TeX: (i) "for every `Y ∈ Std_r`, every `l ≥ r+1` and every vertex `h`: `#{u ∈ Y⁰ \ Dup*_r : hu ∈ E(G_l)} ≤
τ_r − 1`"; (ii) "`m_{Y,l} ≤ τ_r − 1 + d*_{Y,l}` for every `Y ∈ Std_r` and every `l`"; (iii)
"`Σ_{(Y,l): Y standalone} m_{Y,l} ≤ 2^{σ+14} n log* D_*/log D_* + 100 ε n log* D_*/(C' log log D_*)`".
Checked: `τ_r − 1` in ℕ is exact because `1 ≤ tauOf d` for every real `d` (`EG/Proof/HB/Origin.lean`
`one_le_tauOf`; indeed `MOf d ≥ 2^40` so `log₂ M ≥ 40`, `sOf ≥ 1`, `τ ≥ 1`), so the ℕ statement is the TeX
statement. (i) ranges over all `l ≥ r+1` (`G_l` stationary for `l ≥ R+1`) and needs no `δ` (the TeX
quantifies `δ` but (i) does not read it: stronger). Rounds `r` outside `[1,R]` have `Std_r = ∅`. (iii): the
index set `l ∈ [1,R]`, `Y ∈ stdParts` (all standalone parts of all rounds) loses no pair with `m ≠ 0`
(`Std_l = ∅` for `l ∉ [1,R]`, so `classDeg = 0` there). `log = logb 2` (TeX "All logarithms are to base 2");
`2^{σ+14}` with `σ : ℕ`; the denominators are positive under `Gamma1core` (`D_* > 2`, `log log D_* ≥ 2^8`).
Hypotheses: (i), (ii) carry no Γ and no `n ≥ N_0` (stronger than the TeX standing assumptions); (iii)
carries `Gamma1core` only, per TRIAGE §2.6 (CONC-IMPLICIT-HYPS), no `d_1 ≥ D_*` (implied by `Valid` when
`R ≥ 1`; sums empty when `R = 0`). No Γ2(b),(c). (iv) is meta and automatic (∀ δ). Faithful.

### `ConcTauSumStatement`, `ConcDStarSumStatement` (proof of (iii); consumer s6:thmCONCL (iv))
Back-translation. Under `Gamma1core`, valid run: `Σ_{Y ancestor} Σ_{l = r(Y)+2}^{R} (τ_{r(Y)} − 1) ≤
2^{σ+14} n log* D_*/log D_*`; and for every designation `Σ_{l=1}^{R} Σ_{Y ancestor} d*_{Y,l} ≤
80 ε n log* D_*/(C' log log D_*)`.
TeX (proof of (iii)): "`Σ_{(Y,l), Y ∈ Std}(τ_r − 1) ≤ … ≤ 2^{σ+14} n log* D_*/log D_*`" and
"`Σ_{(Y,l)} d*_{Y,l} ≤ … ≤ 80 ε n log* D_*/(C' log log D_*)`"; [s6:thmCONCL] (iv): "The number of ancestors of
round `r` (light and standalone) is at most `1.37 n/P_r` ((K1)). The computation in the proof of Theorem
CONC(iii) applies verbatim" / "it applies to all ancestors together and gives at most `80 ε n …`".
These are stated over all ancestors (the CONC-L form; the standalone sums are sub-sums of nonnegative terms).
The τ-sum's inner range `[r+2, R]` has `R − r − 1` terms, exactly the TeX count "at most `R − r − 1` values of
`l`". Constant 80 as in the TeX proof (the theorem's 100 is deliberately looser). Consistent with the TeX;
the derivation is in the Lean proof (0 sorry).

### `LogStarFactsStatement`, `KStarStatement`, `TowerHalfStatement`, `TowerEndStatement`
Back-translation. (log*) for `x ≥ 1`, `k : ℕ`: `log* x ≤ k ↔ x ≤ T_k`; for `x > 1`: `log* x = 1 + log*(log₂ x)`;
for `x ≥ 1`: `log* x ≤ 1 + log₂ x`. (k*) `Gamma1core D_*` ⇒ `2^8 ≤ log log D_*`, `16 < log log D_*`,
`T_5 < D_*`, `6 ≤ log* D_*`. (TowerHalf) `Gamma1core`, valid run, `1 ≤ r < R` ⇒ `𝖺(d_r) ≤ 𝖺(d_{r+1})/2`,
same for `𝖻`, `𝖼`. (TowerEnd) `Gamma1core`, `d ≥ D_*` ⇒ `𝖺(d) ≤ (2k_*+4)/log D_*`,
`𝖻(d) ≤ (2k_*+3)/log log D_*`, `𝖼(d) ≤ (2k_*+3)/(log D_*)^{1/2}` with `𝖺(d) = (2 log* d + 2)/log d`,
`𝖻(d) = (2 log* d + 1)/log log d`, `𝖼(d) = (2 log* d + 1)/(log d)^{1/2}` (`towA/B/C`, `rpow` exponent `1/2`).
TeX: quoted in full in the module docstring of `ConcTower.lean` and `TowerFns.lean`; compared word by word:
constants `2k_*+4`, `2k_*+3`, `2k_*+3`; exponents `1/2`; `T_0 = 1`, `T_{i+1} = 2^{T_i}` is `EG.tower`
(`tower 5 = 2^{65536}`); "every `r < R`" with 1-indexed rounds is `r ∈ Ico 1 R`; the standing assumption
enters as `Gamma1core` (items (a), (b) are what the TeX proof uses). The TeX cites s2:lemTower(a)
("`λ_r ≥ d_{r+1}^{1/A}`", s2.tex 1147) for "`x ≥ 2^{y/A}`": consistent with that lemma's statement. Faithful.
Parse check: `Real.logb 2 Dstar ^ ((1 : ℝ) / 2)` is `(logb 2 Dstar) ^ (1/2)` (application binds tighter).

## 2. Vacuity
- No Spec has contradictory hypotheses: `EGTest/Spec_s6a.lean` (re-elaborated by me: rc=0, 0 errors,
  0 sorry) exhibits instances satisfying the hypotheses of GATE (oriented triangle, `W` one arc), MED (`K5`
  parity-clean with injective rank; `O5` admissible), EQ-LPT (`m=3`, `k=2`, greedy `σ3`), PAR (one edge,
  disjoint sides, `J' = E`), HCC-P (`S1` with `k=1`, `S2` with `k=2`, the empty system for every `k ≥ 1`),
  the union (¶1 on `E_0 = ∅`; ¶2 on two systems), CONC (a valid run with a designation; `Gamma1core D`
  with the round-free run; `Gamma1core D ∧ D ≤ d`).
- No conclusion is trivially true: all are proved by non-trivial proofs in `EG/Proof/Chain/` (0 sorry), and
  every conclusion has content on the test instances (e.g. GATE forces a decomposition of the triangle into
  one cycle; CONC (i) at `l ≥ r+1` bounds a real count by `τ_r − 1 ≥ 0`).
- Junk-value audit: `τ_r − 1` exact (`one_le_tauOf`); `Real.logb` denominators positive under `Gamma1core`;
  `IsPathIn` one-vertex paths are excluded in HCC-P by the head/last counts (a trivial path `[u]` would need
  `dem⁻(u) ≥ 1` and `dem⁺(u) ≥ 1`, impossible for `k ≥ 2` by (D) and for `k = 1` since `exc⁻, exc⁺` are not
  both positive); `medOrient` is total but claimed only under the lemma's hypotheses.
- Not constructible at toy size (as the status says): a valid run with `Std_r ≠ ∅`, or with `R ≥ 1` under Γ1.
  This is a limitation of the test, not a vacuity of the Specs (the manuscript's runs exist for large `n`).

## 3. Consistency
- Reuse: every label of the chunk has exactly one Spec file (`grep -rln "\[label\]" EG/Spec`): Gate, MED,
  EqLpt, PAR, HCCP (HCC-P and both paragraphs of the union lemma), CONC, ConcTower. `EG/Spec/Chain/EngineMult.lean`
  mentions `[s6:lemMED]`/`[s6:lemHCCP]` only in prose; its statements are labelled
  `[s6:lemJSLC:proof-claim-c]` (chunk s6b). No duplicate statement.
- Defs: the Specs read only locked Defs plus the two probe Defs files (`P2E/Par.lean`, `P3B/TowerFns.lean`),
  both recorded in the status. `Gamma1core` from `EG/Defs/Gamma/Core.lean`; no `Gamma2a`, no Γ2(b),(c), no
  `N0Cond`, no `n ≥ N_0` in this chunk (TRIAGE §2.6). `IsBalanced` is used only in GATE (global balance is
  right there); cluster admissibility is pointwise at hubs (CONVENTIONS "Orientations").
- Consumer forms: `HccGlobStatement` records "cycles of `G`" (JS-LC Step 7); `EqLptExistsStatement` for
  "layer them by that lemma"; the two CONC sums in the all-ancestors form for CONC-L (iv);
  `MedStatement` (a) gives consumers an admissible orientation (the status corrects the blueprint's name
  `Cluster.exists_admissible`, which does not exist).
- Hidden hypotheses: none found. Hypotheses beyond the TeX wording are only (a) `Disjoint V_a V_b` (implicit
  in "sides", needed, T0), (b) `beads_G` (the `E(G)` part of the cluster definition), (c) the input-level
  disjointness of the union lemma (T0-glob-input, implies the literal one). Hypotheses dropped relative to the
  TeX standing assumptions (n ≥ N_0, Γ2–Γ4, `d_1 ≥ D_*`, `δ` in (i)) only strengthen the statements.

## 4. Hygiene
`python3 -I scripts/lint.py`: 0 findings. Spec files have the module header (`module`, `public import`,
`@[expose] public section`), docstrings starting with the manuscript label and quoting the TeX. No file edited.

## 5. Minor remarks (cosmetic; no action required on any Spec)
- C1. `HccGlobStatement` restates `(S s).Phi j = Φ s` but not `((S s).P j).length = Φ s`; the latter is
  available from `HccpStatement` for each system, and `Φ s` is already determined. Nothing to change.
- C2. `LogStarFactsStatement` and `KStarStatement` carry the docstring label `[s6:thmCONC]` for text that
  precedes the theorem (the docstrings say so). Acceptable; a grep for the label finds them together with the
  theorem, which is where the facts are used.
- C3. `HccUnionStatement` keeps the unused hypothesis `E i ⊆ G.edges` (faithful to the TeX wording; harmless).
- C4. Status file: the (iv) entry says "(iv) is meta (automatic …)"; correct, matches CONC-IV-META.

## 6. Math findings (manuscript)
No finding of class T1–T3 from this review. I re-derived, against the TeX proofs: GATE (2-cycle exclusion via
simplicity; count `p ≤ |𝒲|`); MED (a) (`pot(h) ∈ (0,1)` uses `1 ≤ rk(u_d) ≤ |U| − 1`, fine since `2d ≥ 2`),
(b) (`Σ_u d⁺(u) = #{port→hub} + e(B[U]) = Σ_h d⁻(h) + e(B[U])`, uses "no hub–hub bead"); EQ-LPT; PAR (the
parity sum needs that every edge has exactly one end in `V_a`, i.e. disjoint sides); HCC-P Steps 0–4
(including `k = 2` where `LayP_{j+1} = LayP_{j−1} ≠ LayP_j`, the `k = 1` case, `|𝒲| = |𝒫_{k−1}|`, and the
block-crossing length bound, whose maximal non-𝒲 subpath is non-empty because the head of a 𝒲-arc lies in
`LayP_0` and its tail in `T_{k−1} ∪ LayP_{k−1}`); CONC (i)–(iii) arithmetic (`2k+4 ≤ 8k/3`, `2k+3 ≤ 2.5k` for
`k ≥ 6`; `1.37 · 16/3 < 8`; `32 · 2.5 = 80 ≤ 100`). All correct as written. T0 records (already in
CONVENTIONS / blueprint): T0-glob-input (union lemma hypothesis names outputs), PAR-SIDES-DISJOINT
(disjoint sides implicit in "bipartite with sides"), HCCP-INDEXED-CLUSTERS ((D) over families with
multiplicity).
