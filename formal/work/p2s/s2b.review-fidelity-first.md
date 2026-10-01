# Clean-room review of the s2b Specs (lens: fidelity-first, model A)

Reviewed: `work/p2s/s2b.md`; the 7 Spec modules of the unit `EG/Spec/HB/{Structure,OVRun,DegRec,
Exists,Lacunary,Tower,Parentless}.lean` (22 `…Statement` defs); the reused Specs they cite
(`StructureHY`, `StructureLight`, `CapPrePart`, `OVRunK`, `LacunaryGeom`, `TowerA`, `TowerB`,
`TowerBM`, `TowerBLate`, `TowerC`); test `EGTest/Spec_s2b.lean`; against `proofs/manuscript/s2.tex`
lines 20–29 (standing assumption) and 722–1533 (s2:propStructure … s2:remTauConstants). Defs read:
`EG/Defs/HB/{Round,Run,SplitTree,Witness}.lean`, `EG/Defs/Log.lean`, `EG/Defs/Gamma/Core.lean`,
`EG/Defs/Constants.lean`, `EG/Defs/Graph.lean` (`card`, `deg`, `induce`, `deleteVerts`). No Lean
file edited. Scratch checks in the session scratchpad (`s2bcheck.lean`, compiled with
`lake env lean`: parsing of `Real.logb 2 n ^ 2`, `WithTop ℕ` offsets, `HypH` with `F = 0`,
elaborated form of `TowerDStatement`): all as expected.

**Verdict: approve.** Every new statement back-translates to the TeX clause it cites, with the
TeX quantifier order, strictness, constants (`1.12, 1.21, 1.37, 5.46, 6.61, 7.6, 15.2, 30.4, 16,
4, 4.5, 9, 6, 1.2, 7, 2.1, 31, 103, 105, 2^{-5}, 2^{-6}`), `log = log₂`, and ℕ/ℝ choices. No
vacuity found. Only `Gamma2a` or `Gamma1core` are assumed: no Γ2(b),(c) anywhere (grep empty).
Lint: `python3 -I scripts/lint.py` → 0 findings. The remarks below are cosmetic, plus two T0 notes.

## 1. Fidelity (back-translation vs TeX)

### `StructureExpStatement` [s2:propStructure] (i)
TeX: "each `X^0_Z` is a `(2^{-5},s_l)`-expander on `Z^0`; each light `X_Z` is a
`(2^{-6},s_l/2)`-expander on the light part `Z`; every `H_Y` has minimum degree greater than
`s_Y`; and `s_r ≥ λ_r^{100}` for every `r ≤ R`."
Back-translation: for every V, G, D_*, run with D_* ≥ 2^{117} and a valid run: (1) for every round
l ∈ [1,R] and pre-part a, V(X^0_a) = Z^0_a and X^0_a is a (2^{-5}, s_l)-expander; (2) for every light
pre-part, V(X_a) = Z^0_a \ S_a and X_a is a (2^{-6}, s_l/2)-expander (real s_l/2); (3) every ancestor
Y has V(H_Y) ≠ ∅ and deg_{H_Y}(v) > s_Y (strict, real) for all v ∈ V(H_Y); (4) λ_r ≤ Λ_r and
λ_r^{100} ≤ s_r (natural power) for r ∈ [1,R].
Match. "`δ(H_Y) > s_Y`" stated pointwise with nonemptiness (CONVENTIONS: `minDeg` is 0 on the empty
graph). The extra `λ_r ≤ Λ_r` is proved in the TeX proof and cited by lemTower(b) ("in (the proof
of) Proposition s2:propStructure(i)"): a strengthening. Truth in the model: pre-parts are leaves of
`twoLevel` with ≥ P_l vertices, hence τ-run leaves of big pieces (small pieces are leaves with
< P_l vertices), and `IsTauRun` contains "leaf iff (ε,s_l)-expander"; `X^0_Z ⊆ G'_l[Z^0]` (node
graphs are `induce`/`deleteEdges` of the root), so (L2) transfers for s2:lemHS; `P_l ≥ 117^{103}
≥ 11`. Hypotheses: TeX `n ≥ N_0`, `d_1 ≥ D_*` dropped (vacuous at R = 0; strengthening); Γ only
through Γ2(a). OK.

### `StructurePartitionStatement` [s2:propStructure] (iii), clauses not in `StructureHYStatement`
TeX: "`E(G_{l+1}) ⊆ E(G'_l) ⊆ E(G_l)` for every `l ≤ R`, so `d_{l+1} ≤ d_l`; and
`E(G) = ⨆ E(Cyc_l) ⊔ E_0 ⊔ ⨆_{Y light} E_{r(Y)}(Y) ⊔ ⨆_l ⨆_{Z∈Std_l} E_l(Z)` (disjoint unions); … the
graphs `X^0_Z` of the pre-parts of one round are pairwise edge-disjoint; `Σ_{l≤R}|Cyc_l| ≤ n`; and
`|E_0| < D_* n/2`."
Back-translation: with Γ2(a), n ≥ 1, valid run: for l ∈ [1,R] the two inclusions and
d_{l+1} ≤ d_l; E(G) = (⋃_l E(Cyc_l) ∪ E_0) ∪ ⋃_{Y ∈ light ∪ std} E_{r(Y)}(Y); disjointness of every
pair of distinct members (cycles/cycles of distinct rounds, cycles/E_0, cycles/parts, parts/E_0,
parts/parts); X^0_a, X^0_b edge-disjoint for a ≠ b in one round; Σ_l (number of cycles of Cyc_l) ≤ n;
|E_0| < D_* n/2 (ℝ).
Match. The displayed ⊔ is fully encoded (union + all pairwise disjointness). `|Cyc_l|` = number of
cycles (list length; `CyclesValid` makes the flattened edge list `Nodup`, so no repeated cycle).
`0 < G.card` replaces `n ≥ N_0`: needed, since for n = 0 the last clause is `0 < 0` (with
D_* ≥ 2^{117}, d_1 = 0 < D_* and R = 0 is valid). `E_0 = E(G_{R+1})` and `G_1 = G` (`graph G 1 =
graph G 0 = G` because `IsRound 0` fails). The cycle-count proof works for any maximal family
(encoding HB-R1-ENCODING), since it only uses edge-disjointness and length ≥ `d_l log² d_l`. OK.

### `StructureVertexStatement` [s2:propStructure] (iv)
Back-translation: for every valid run (no Γ) and round l: light parts of distinct light pre-parts
are disjoint; for light a, |Z^0_a|/2 ≤ |Z^0_a \ S_a| and P_l/2 ≤ |Z^0_a|/2 (ℝ); v ∉ D_l lies in at most
one Z^0_a; ports of distinct a, b ∈ Std_l disjoint; v in the light part of light a ⇒ home_l(v) = a;
at most one light pre-part has v in its light part.
Match, all five TeX clauses ("namely in the light part of `home_l(v)`" = the `home` clause). True
without Γ: uses only (L1), the definition of D_l as μ ≥ 2 and `homeOrder.toFinset =
prePartAddrs` from `Round.Valid`. OK.

### `OVRoundStatement` / `OVRunStatement` [s2:propOV], (s2:eqDupComposite)
Back-translation (round level; run level identical per round r ∈ [1,R], with `dup`, `hubs`, `mult`,
ancestors of round r): leaf mass of `tree0` ≤ 1.12n; leaf mass S of `twoLevel` ≤ 1.21n; for every
real M ≥ 2, Δ_{≥M} ≤ 5.46εS/log M ≤ 6.61εn/log M; Σ|Z^0| ≤ 1.37n; |Std| ≤ 1.37n/P; #pre-parts ≤ 1.37n/P;
|D| ≤ Σ_w(μ(w)−1)^+ ≤ 7.6εn/log P; Σ_{Std}|Z^0∩D| ≤ Σ_all|Z^0∩D| ≤ 2dup ≤ 15.2εn/log P; mass of
pre-parts failing (L1) ≤ 30.4εn/log P; Σ|Z^0∩Dup*| ≤ 16εn/log P; Σ_w mult(w) = Σ|V(part)| ≤ 1.37n;
mult(w) ≤ μ(w).
Match with every link of every TeX chain. `Δ_{≥M}` = `STree.DeltaGe` (sum of |N''| over non-leaf
nodes of size ≥ M), as in s2:lemOVgeneric. The first link of eqDupComposite holds for all real
M ≥ 2 (lemOVgeneric (a) with c = 1.6: 1.6(1+1/c_OV) = 5.455 ≤ 5.46); second link 5.46·1.21 =
6.6066 ≤ 6.61. `(μ − 1)` in ℕ is `(μ−1)^+`. Round-level (K1) "number of ancestors" = number of
pre-parts (one part per pre-part). Γ2(a) is implicit in the TeX (lemCap(ii) feeds lem14tau(b));
correct and minimal. OK.

### `DegRecRoundStatement` / `DegRecStatement` [s2:propDegRec], bounds
Back-translation: under Γ1 (a)–(e), one valid round with D_* ≤ d(H) (resp. every round of a valid
run): M ≤ d² (ℝ), Λ ≤ 2λ, s ≤ P (ℕ), d(next) ≤ 1.21P + 9 s log M ≤ 6P + 9 s log M + 1.2 s ≤ 7λ^{103}
≤ λ^{105} < d.
Match: every link of the TeX chain, same constants, `x = λ_l`, `A = 105` (natural power). `d(next)`
uses the same n (`next` keeps `H.verts`). Γ1 is really needed (the counterexample of §4 shows
d_{l+1} = d_l under Γ2(a) alone). OK.

### `DegRecKindsRoundStatement` / `DegRecKindsStatement` [s2:propDegRec], kinds
Back-translation: under Γ2(a): every edge of G_{l+1} is (a) in the deleted set of the τ-run of a
big piece, or (b) an edge of a leaf of `twoLevel` with < P vertices, or (c) an edge of X^0_a with an
end in S_a, a light; each big piece has ≤ 4 s |𝒫| log|𝒫| deleted edges; the union over big pieces
has ≤ 4.5 n s log M edges; every leaf with q < P vertices has 2|E| < qP; each light a has
≤ |Z^0_a| s/2 guest edges; E(X^0_a) ∩ E(G_{l+1}) = ∅ for a ∈ Std.
Match. "in total" = size of the union (the TeX count is of edges). (b)'s "a leaf with q vertices
has fewer than `qP_l/2` edges" restricted to q < P: see T0 note 4.2. The `q ≥ 1` needed by (b) holds
in the model: witnesses have `1 ≤ |U|` and `|U| ≤ 2m/3` (`IsWitness`), so both children of an
`s = 0` split are nonempty, and the τ-children have ≥ |U'| ≥ 1 and m − |U'| ≥ m/3 vertices; the root
has n ≥ 1 vertices since d(H) ≥ D_* > 0. The counterfactual GC sentence is not formalized (not a
proposition about a run; its factual content is the standalone clause). OK.

### `RoundStepsStatement` [s2:propExists] "(R1) and the first level of (R3) terminate"
Back-translation: for every V: (1) every graph has a list of cycles satisfying `CyclesValid`
(maximal edge-disjoint family of well-formed cycles of length ≥ T in H); (2) for every K and every
rule W giving a parameter-0 witness at every non-(ε,0)-expander, there is a finite split tree which
is an s = 0 recursion on K, stops exactly at (ε,0)-expanders, and uses W's witnesses at every
internal node.
Faithful reading of "terminates with any admissible choices" in a model with finite trees. True:
greedy deletion; for s = 0, F = ∅ and |U| + |N| < (2/3)(33/32)m < m, m − |U| < m. W exists (a
non-expander has a witness, by the definition of `IsWitness`). OK.

### `RoundTauTermStatement` [s2:propExists] "τ-runs terminate with any witnesses"
Back-translation: under Γ2(a), D_* ≤ d(H), (R1) valid and the first level of (R3) valid and stopped
at (ε,0)-expanders: for every big piece 𝒫: s ≥ 1; 128 s log²|𝒫| ≤ τ; for every graph K with
2 ≤ |K| ≤ |𝒫| and every witness (U,F) at K with parameter s: U' ≠ ∅, |K[U'∪N'']| < |K|,
|splitSnd| < |K|; for every witness rule W there is a τ-run of 𝒫 using W.
Match; the split clause is over arbitrary K (not only node graphs), a strengthening that I checked
is true: F_0 ⊆ F (an edge from U to V∖(U∪N) not in F would put its end in N), F_1 ⊆ F_0, so
|H_out|, |H_in| ≤ s|U|/τ ≤ |U|/128; hence U' ≠ ∅ and |U' ∪ N''| ≤ (2/3)m(1 + 1/32 + 1/128) < m. Not
assuming `Round.Valid` (which already contains the τ-runs) is the right shape. OK.

### `RoundExistsStatement`, `RunTerminatesStatement`, `ExistsRunStatement` [s2:propExists]
Back-translations: (a) Γ2(a), D_* ≤ d(H) ⇒ ∃ c, `Round.Valid H c`; (b) Γ1: for every list of choices
whose every listed round l has d_l ≥ D_* and is a valid round on G_l: d_{l+1} < d_l for all listed
l, and the list length ≤ |E(G)|; (c) Γ1: ∀ G ∃ run, `run.Valid G D_*`.
Match ("`d_{l+1} < d_l` while `d_l ≥ D_*`, so R is finite"; "for every graph G a valid run
exists"). (a) is true with Γ2(a) (home order chosen last; `prePartAddrs` does not depend on it).
(b): the edge count drops by ≥ 1 per round, so length ≤ |E(G)|. See §4.1 for Γ. OK.

### `LacunaryMonoStatement`, `LacunaryIIStatement` [s2:lemLacunary] (ii)
Back-translation (Mono): Γ1 ⇒ x ≤ 2^{x/105} for x ≥ x_0 = log D_*; and every F antitone on
[x_0,∞) with F(2^{x/105}) ≤ F(x)/2 (x ≥ x_0) satisfies (H). (II): Γ1, valid run, R ≥ 1 ⇒
2^{λ_{r+1}/105} ≤ λ_r (1 ≤ r < R); for F ≥ 0, antitone, halving on [x_0,∞): Σ_{r=1}^R F(λ_r) ≤ 2F(λ_R)
≤ 2F(x_0); Σ(R−r+1)F(λ_r) ≤ 4F(x_0); if R ≥ 3: Σ_{l=3}^R F(λ_{l−2}) ≤ 2F(λ_{R−2}) ≤ 2F(x_0) and
Σ(R−l+1)F(λ_{l−2}) ≤ 4F(λ_{R−2}) ≤ 4F(x_0).
Match, including "≤ 4F(x_0)" (not 4F(λ_R)) for the unshifted weighted sum as in the TeX, and the
shifted weights (R−l+1 = (R−2)−(l−2)+1). ℕ subtractions exact on the ranges. OK.

### `LacunarySeqStatement`, `LacunaryRunStatement` [s2:lemLacunary] (iii)
Match: (H) = `HypH x_0 F`; (Seq) any x_0, λ_r ≥ x_0 on [1,R], 2^{λ_{r+1}/A} ≤ λ_r on [1,R) ⇒ both
bounds with F(λ_R); (Run) same for runs, shifted sums written out ("likewise for F(λ_{l−2})"). The
Defs' `HypH` adds `x_0 ≤ y` (F's domain); as a hypothesis this is weaker than the TeX (H), so the
Specs are (slightly) stronger, and equivalent under Γ1 since 2^{x/A} ≥ x ≥ x_0. OK.

### `LacunaryExamplesStatement` [s2:lemLacunary] (iv)
Back-translation: Γ1 ⇒ for a ≥ 1/100: x^{−a} satisfies (H), antitone and ≥ 0 on [x_0,∞); same for
1/log x; same for (95 log x + 8)x^{−b}, b ≥ 1; for x > 1: 2 log*(2^x) + 2 = 2 log* x + 4; for η ∈ {x,
x^{1/2}, log x}: F = (2 log*(2^x) + 2)/η satisfies (H), F ≥ 0 on [x_0,∞), F(x) ≤ 2F(x_0) for x ≥ x_0.
Match (the three log*-functions are not claimed monotone; nonnegativity added, as the TeX
codomain `[0,∞)` of (iii) requires). The identity: `logIter (k+1) (2^x) = logIter k x`, so
log*(2^x) = log* x + 1 for x > 1. I rechecked the TeX proofs of (H) and of F(x) ≤ 2F(x_0) (cases
k = 0, 1, ≥ 2): correct. OK.

### `TowerBRestStatement`, `TowerDStatement`, `TowerEStatement`, `TowerStatement` [s2:lemTower]
Back-translations: (BRest) Γ1, valid, d_1 ≥ D_*: M_l log⁴M_l ≤ P_{l−2}/2 (3 ≤ l ≤ R, ℝ);
2M_l ≤ M_{l−1} (2 ≤ l ≤ R, ℕ); 2P_{r+1} ≤ P_r (1 ≤ r, r+1 ≤ R, ℕ); Σ_{l=1}^R ψ(M_l) ≤ 2.1ψ(D_*).
(D) for 1 ≤ r ≤ l ≤ R: 2^{2log* d_r + 2} ≤ λ_r, 2^{R−r} ≤ 2^{2log* d_r+2}, 2^{l−r} ≤ 2^{R−r} (natural
exponents). (E) Σ_l 15.2ε/log P_l ≤ ε_A; Σ_l |D_l| ≤ ε_A n; Σ_l Σ_{a∈Std_l} |Z^0_a ∩ D_l| ≤ ε_A n.
Match, exact constants, `ψ = psiPool`, `ε_A = epsA` (= 31ε/(103 log log D_*)). `TowerStatement` is
the conjunction of the eight parts (a)–(e); together they cover every clause of the TeX lemma
(checked clause by clause against the existing `TowerA/B/BM/BLate/C`). OK.

### `FreshStatement` [s2:propParentless] (i), (K4)
Back-translation: every valid run (no Γ): x in a round-r pre-part ⇒ home_r(x) = some a, a a pre-part,
(r,a) an ancestor, x ∈ V((r,a)), x ∈ Z^0_a \ S_a if light, x ∈ Z^0_a otherwise; for a ∈ Std_l,
x ∈ U_a: x ∈ F_a ⇔ l ≤ j_0(x) + 1; at most one a ∈ Std_l has x ∈ U_a; x ∈ F_a ⇒ j_0(x) ∈ {l, l−1}
(as `j0 = l ∨ j0 + 1 = l`); Σ_l Σ_{Std_l} |F_a| ≤ 2n.
Match ("j_0(x) ≥ l−1" ⇔ l ≤ j_0(x)+1 in `WithTop ℕ`, checked by `decide` on examples; j_0(x) is
finite as x ∈ U_a ⊆ Z^0_a). OK.

### `AdmissibleParentStatement` [s2:propParentless] (ii)
Back-translation: Γ1, valid run, light parts Y, Z with r(Y) + 2 ≤ r(Z): P_{r(Y)}/2 ≤ |V(Y)|;
P_{r(Z)−2}/2 ≤ P_{r(Y)}/2; M log⁴M ≤ P_{r(Z)−2}/2 (M = M_{r(Z)}); |V(Z)| L_Z⁴ ≤ M log⁴M.
Match, all four links; `r(Z) ≤ R` from `lightParts`. `d_1 ≥ D_*` implied by `Valid` whenever the
statement is non-vacuous. OK.

### `ParentlessCountStatement` [s2:propParentless] (iii)
Back-translation: every valid run, every finite `Bad ⊆ PartId`: Σ_{Z light} #{v ∈ V(Z) : no light
Y ∉ Bad with r(Y)+2 ≤ r(Z) and v ∈ V(Y)} ≤ 2n + Σ_{Y∈Bad} |V(Y)|(R − r(Y)); and each parentless
(v,Z) has r(Z) = j_1(v), or r(Z) = j_1(v)+1, or (j_1(v)+2 ≤ r(Z) and some Y ∈ Bad, light, of round
j_1(v) contains v).
Match. `Bad` wider than "a set of light parts": the parentless predicate only looks at light Y, and
extra members only add nonnegative terms, so the TeX statement is the special case. "The number of
such pairs" = sum over Z of the per-Z counts (each pair once). Consumer s5:eqPl (`EG/Spec/Light/
Stages.lean`) sums over non-demoted Z only, which is ≤ this sum. OK.

## 2. Vacuity
* Hypotheses are satisfiable: `Gamma1core` (`exists_gamma1core`), `Gamma2a (2^117)`, `Run.Valid`
  with R = 1 and a light part (K₃, `EGTest/Spec_s2b.lean`), the choice-list hypothesis of
  `RunTerminatesStatement`, the F/sequence hypotheses of the Lacunary Specs, the η-disjunction.
  Joint satisfiability of Γ with a run having R ≥ 1 is the content of `ExistsRunStatement` (R ≥ 1
  needs d(G) ≥ D_*, e.g. K_m with m − 1 ≥ D_*); not checkable cheaply, as the status says.
* No conclusion is trivially true: every inequality has the TeX constant; no `IsExpander` with
  ε ≤ 0 (the constants are 2^{-5}, 2^{-6}); `IsPathConnected`/ball conventions not involved;
  `minDeg` avoided (pointwise degree with nonemptiness); the `P_l = 0` junk (d ≤ 1) is unreachable
  in the Γ-Specs and harmless in the Γ-free ones (Vertex, Fresh, ParentlessCount: purely
  combinatorial, true for every P).

## 3. Consistency and hygiene
* Reuse: s2:lemCap(ii), propStructure(iii) (HY part), propStructure(iv) first clause, propOV
  (K1)/(K3), lemLacunary(i), lemTower (a), (b) parts, (c) are cited, not restated. Overlaps, all
  harmless and documented: `StructurePartitionStatement` repeats the pairwise disjointness of the
  part sets `E_{r(Y)}(Y)` already in `StructureHYStatement` (needed to state the ⊔ in one place);
  `StructureVertexStatement` implies the declared input `StructureLightStatement` (P4B).
* Hypotheses: only `Gamma2a` or `Gamma1core`; never Γ2(b),(c), never `N0Cond`. Each Spec's choice
  is minimal for its proof (Γ2(a) where only lemCap(ii)/HS are used, Γ1 where propDegRec is used).
* Lint: `python3 -I scripts/lint.py` → `lint (development): 0 findings`. No `sorry` in the Spec
  files.

## 4. T0 notes and remarks

4.1 **EX-GAMMA (T0, agreed).** Without Γ1 the literal "for every graph G a valid run exists" is
false: D_* = 2^{117}, G = K_m with m = 2^{117}+1. Then d_1 = 2^{117}, λ = 117, T = 2^{117}·117² > m
(no long cycle), K_m is an (ε,0)-expander (single piece of size m), P = ⌈117^{103}⌉ ≈ 2^{708} > m (no
big piece, no pre-part), so every edge passes down and d_2 = d_1 forever. The Specs carry
`Gamma1core`. **Correction to s2b.md:** the "manuscript action (optional): add a standing-assumption
sentence to s2" is already done in v6.1: `s2.tex` lines 24–29 ("Standing assumption. Throughout
this section … `D_*` … satisfies Γ1–Γ4 …; for instance the termination part of Proposition
s2:propExists uses Proposition s2:propDegRec, and hence Γ1"). So the T0 is purely the encoding of
that standing assumption; no manuscript action is needed (cosmetic fix to the status file).

4.2 **propDegRec (b) wording (T0).** "a leaf with `q` vertices has fewer than `qP_l/2` edges" read
for *every* leaf is false (a pre-part is a leaf with P_l ≤ q ≤ M_l, and an expander leaf can have
~q²/2 > qP_l/2 edges). In context (item (b), and the proof "(b) A leaf with `q < P_l` vertices …")
it is about the small leaves; the Spec states it for q < P_l. Correct reading; optional wording fix
"a leaf with `q < P_l` vertices".

4.3 Cosmetic (other units' files, not edited): the module docstrings of `EG/Spec/HB/TowerA.lean`,
`TowerC.lean`, `OVRunK.lean` and `EG/Proof/HB/OVRunK.lean` still say the s2b Specs
(`TowerEStatement`, `OVRunStatement`) are "not written yet"; they now exist.

4.4 Cosmetic: `HypH` (Defs) quantifies `y ≥ x_0` as well; as a hypothesis this makes
`LacunarySeqStatement`/`LacunaryRunStatement` slightly stronger than the TeX (iii); equivalent
under Γ1. No action.
