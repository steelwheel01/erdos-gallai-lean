# P2-D [hb] definition review, round 2 (clean room)

Reviewer: clean-room Defs reviewer, round 2, 2026-09-26.
Scope: `EG/Defs/HB/Witness.lean`, `EG/Defs/HB/SplitTree.lean`, `EG/Defs/HB/Round.lean`,
`EG/Defs/HB/Run.lean` (the state after fix round 1), and, for usability, `EG/Lib/HB/SplitTree.lean`,
`EG/Lib/HB/Run.lean`, `EGTest/HB.lean`.
Checked against:
- manuscript v6.1 `proofs/manuscript/s2.tex`: defWitness (41–59), defTauRules (71–108), lemSEP
  (135–172), lemThinCut (220–235), lemOVgeneric (278–319), lem14tau (376–409), defHBtp (503–598),
  defAncestors (600–631), lemCap (635–651), propStructure (722–760), lemEL (821–826), propOV
  (829–862), propDegRec (916–941), propExists, lemLacunary (H), lemTower (b),(e), lemGC,
  propOrigin, propParentless (1414–1443);
- TRIAGE §1a (M-INTEGER), §2.1, §2.2, §2.12, §3 items 7–10;
- the `defs_needed` tables and Lean sketches of blueprints s2a, s2b, s3b, s5, s6a, s6b, s7a, s7b
  (every `run.*` / `EG.HB.*` name they use was tallied, 90 distinct names);
- the design note `work/p2d/hb.md` including its "Fix round 1" section, and `hb.review1.md`.

I did not edit any Lean file. Build state re-checked: the `.olean` files of the four Defs and both
Lib modules are newer than their sources; `python3 scripts/lint.py` reports 0 findings; my scratch
test (below) compiles with `lake env lean` (0 errors, no `sorry`).

## Verdict: APPROVE (no major issue)

- Every definition back-translates to the quoted manuscript text; I re-did the back-translation
  independently of round 1 (tables below) and found no deviation of meaning.
- The M-INTEGER repair (v6.1 (R2)) is implemented exactly: `MOf : ℕ` is the ceiling of the real
  maximum, and `Λ_l = log₂ (M_l : ℝ)` is the log of the integer.
- The two design constraints TRIAGE asks the Defs reviewer to check hold: (a) `prePartAddrs`,
  `mu`, `D`, `home`, `guests`, `DupStar` do not mention `isLight`/`isGC`/`isL1`/`isL2` (checked by
  reading `Round.lean`: their bodies use only `twoLevel`, `X0`, `Z0`, `POf`, `homeOrder`); (b)
  `Round.Valid` has both directions of both stopping rules (`StopsAt` is an `↔`, and `IsTauRun`
  contains `StopsAt`), edge-disjointness (`Nodup` of the flattened cycle edges), "length ≥ T_l"
  and maximality of the cycles, and a complete duplicate-free home order.
- All round-1 issues are fixed as described in `hb.md`; I re-verified each (`bigPieceAddrs` exists
  at both levels, `Run.thetaGC` is in address form with `thetaGC_eq`, the Lib lemmas of issue 1
  exist, the docstrings are corrected, the scratch tests were added to `EGTest/HB.lean`).
- Every downstream use in the blueprints is statable with the given objects and index types; the
  remaining differences are argument-shape renames (issue 1 below), not gaps.
- The issues below are name-map documentation, one guard asymmetry, Lib lemmas that later proof
  tasks need, and test depth. None changes the meaning of a Def.

## Back-translation

### Witness.lean (s2:defWitness, s2:defTauRules)

| Lean | Manuscript text | Match |
|---|---|---|
| `IsWitness H ε s U F` = `U ⊆ V(H) ∧ F ⊆ E(H) ∧ 1 ≤ |U| ∧ |U| ≤ 2m/3 ∧ |F| ≤ s|U| ∧ |Nbr_{H−F}(U)| < ε|U|/log²m` | "a pair (U,F) with U⊆V(H) and F⊆E(H) such that 1≤|U|≤(2/3)m, |F|≤s|U|, |Nbr_{H−F}(U)|<ε|U|/log²m" | yes; `nbrSet` is taken in `V(H)∖U` (s1:convGraphs(c)); the conjuncts are the literal negation of `IsExpander`, so `not_isExpander_iff_exists_isWitness` is `rfl` after `push_neg` |
| `witN H U F = Nbr_{H−F}(U)`, `witF0 H U N = E_H(U, V(H)∖(U∪N))` | "N := Nbr_{H−F}(U), F_0 := E_H(U, V(H)∖(U∪N))" | yes; `witF0` takes `N`, which makes Fact (c) definitional |
| `tauHout = {v ∈ U : τ ≤ deg_{F_0}(v)}`, `tauU1 = U∖H_out`, `tauN1 = N∪H_out` | rule (1) | yes (real comparison, `τ ≤ (degE F₀ v : ℝ)`) |
| `tauF1 = E_H(U', V∖(U'∪N'))`, `tauHin = {x ∈ V∖(U'∪N') : τ ≤ deg_{F_1}(x)}`, `tauN2 = N'∪H_in`, `tauF2 = E_H(U', V∖(U'∪N''))` | rule (2) | yes (`tauF2` is `splitDel H U' N''` by definition) |
| `tauG1 = H[U'∪N''] − F''`, `tauG2 = (H − U' − E(G_1)) − F''` | "G_1 := H[U'∪N'']−F'' and G_2 := H−U'−E(G_1)−F''" | yes; (eqSplit) is left as a statement |
| `splitFst`, `splitSnd`, `splitDel` | lemSEP: "H_{ν_1}=H_ν[U'∪N''], H_{ν_2}=H_ν[V∖U']−E(H_ν[N'']), F''_ν := E_{H_ν}(U', V∖(U'∪N''))" | yes |

Edge cases: at `m = 1`, `logb 2 1 = 0` and Lean's `x/0 = 0`, so the last conjunct reads
`card < 0`: no witness exists, matching the manuscript ("Then m ≥ 2") and the fact that a
one-vertex graph is an expander (`IsExpander` is trivially true there, so the `rfl` equivalence
stays consistent). `τ > s` and `U ⊆ V(H)` are not assumed by the τ-rule functions; the
manuscript's "let τ > s be real" is a hypothesis of the lemmas.

### SplitTree.lean (lemSEP, lemThinCut, lemOVgeneric, lem14tau, (R3) graft)

| Lean | Manuscript | Match |
|---|---|---|
| `STree` (choices `(U'_ν, N''_ν)` at non-leaf nodes), `Addr = List Bool`, `nodeAddrs`/`leafAddrs`/`internalAddrs` | "a finite rooted binary tree whose nodes carry graphs … at every non-leaf node there are disjoint sets U'_ν, N''_ν"; "distinct leaf nodes are distinct leaves even if their vertex sets coincide" | yes; leaves are identified by address, never by vertex set |
| `graphAtD t H₀ a` (fold `splitFst`/`splitSnd` along `a`) | "H_ν = H_0 at the root", children as in lemSEP | yes; total (past a leaf: the leaf's graph; documented) |
| `WF` | "disjoint U'_ν, N''_ν ⊆ V(H_ν)" at every non-leaf | yes |
| `delAt`, `deleted = ⋃ F''_ν` | "the deleted set at ν is F''_ν"; "a deleted edge is an edge of some F''_ν" | yes |
| `leafMass = Σ_{leaves} |H_a|`, `dup = {v : v lies in ≥ 2 leaf addresses}` | "total size of the leaves"; "Dup … vertices lying in at least two leaves" | yes (filtering `V(H₀)` is exact since node graphs are subgraphs of the root) |
| `DeltaGe M = Σ_{internal a, M ≤ |H_a|} |N''_a|`, `dupGe M v = #{internal a : M ≤ |H_a|, v ∈ N''_a}` | lemOV: "Δ_{≥M} := Σ_ν |N''_ν| over non-leaf ν with |ν| ≥ M"; "dup_{≥M}(v) … number of non-leaf nodes ν with |ν|≥M and v∈N''_ν" | yes (real `M`) |
| `OVHyp ε c` = `WF ∧ ∀ internal a, 2 ≤ |H_a| ∧ |H_{a++[false]}| ≤ ¾|H_a| ∧ |N''_a| ≤ cε|U'_a|/log²|H_a|` | "m ≥ 2, |ν_1| ≤ (3/4)m, |N''_ν| ≤ cε|U'_ν|/log²m" | yes; `n_0 ≥ 1` omitted (unused, blueprint OV-N0-POS) |
| `graft t f` (replace leaf `a` by `f a`, addresses `a ++ b`), `leafPrefix` | (R3) "attaching, at every piece 𝒫 with |𝒫| ≥ P_l, the tree of its τ-run" | yes (checked the recursion by hand: `graft nil f = f []`, `graft (node p l r) f = node p (graft l (f ∘ cons false)) (graft r (f ∘ cons true))`) |
| `StopsAt t H P = ∀ a ∈ nodeAddrs, (a ∈ leafAddrs ↔ P H_a)` | "a node is a leaf iff its graph is an (ε,0)-expander"; 14^τ "stops if H is an (ε,s)-expander (the node is then a leaf), and otherwise …" | yes, both directions |
| `IsS0Rec ε` = `WF ∧ ∀ internal a, ∃ U F, IsWitness H_a ε 0 U F ∧ label = (U, Nbr_{H_a}(U))` | "at every non-leaf node ν there is a witness (U_ν,F_ν) at H_ν with parameter s=0 and U'_ν=U_ν, N''_ν=Nbr_{H_ν}(U_ν)" | yes |
| `IsTauSplitTree ε τ` | lemThinCut hypothesis "there are s_ν<τ and a witness at H_ν (with parameter s_ν) whose τ-rules give U'_ν and N''_ν" | yes |
| `IsTauRun ε (s:ℕ) τ` = `WF ∧ StopsAt (IsExpander ε s) ∧ ∀ internal a, ∃ witness (U,F) with parameter s, label = (tauU1 …, tauN2 …)` at `N = witN` | lem14tau definition of the τ-run | yes; `WF` is redundant given Fact (a) but harmless; hypotheses `s ≥ 1`, `τ ≥ 128 s log² n_0` are not in the predicate (correct: they are lemma hypotheses) |
| `cOV = log₂(4/3)` | "put c_OV := log₂(4/3)" | yes |

### Round.lean (defHBtp (R0)–(R5), (GC))

Parameters (functions of the real `d`), all checked symbol by symbol against v6.1:
`lamOf = log₂ d`; `tHBOf = log₂² d`; `TOf = tHBOf d * d` (= t^HB_l d_l);
`MOf = ⌈max(2^40, 2^16 · T · log₂⁴ T)⌉₊ : ℕ`; `LamOf = log₂ (MOf d : ℝ)`; `sOf = ⌈Λ^σ⌉₊`;
`POf = ⌈λ^{C'}⌉₊`; `tauOf = ⌈128 s log₂² M⌉₊`; `thetaGC d z = ⌈z · λ^{−1/2}⌉₊` (`Real.rpow`).
`σ = EG.sigmaC = 100`, `C' = EG.Cp = 103` (locked constants). Types are those of TRIAGE §2.1.
Remark: `MOf d ≥ 2^40` for *every* real `d` (the `max`), hence `Λ ≥ 40`, `s ≥ 40^100`,
`τ ≥ 128·s·1600 > s` unconditionally; so the τ-rules are used with `τ > s` even off Γ.

| Lean | Manuscript | Match |
|---|---|---|
| `RoundChoice` = `cycles`, `tree0`, `tauRun : Addr → STree`, `homeOrder` | "any witnesses in both levels of (R3), any vertex order in (R1), and any home orders in (R4)" | yes: exactly the choices; everything else is derived (PLAN §3 decision 5) |
| `d H = 2|E(H)|/|V(H)|` | (R0) "d_l := 2|E(G_l)|/n", "All graphs G_l, G'_l below have vertex set V(G)" | yes (`Run.graph_verts`) |
| `cycEdges`, `graph' = H − E(Cyc_l)` | (R1) "The deleted cycles form Cyc_l; the remaining graph is G'_l" | yes |
| `CyclesValid`: each listed cycle WF (Nodup, ≥3), edges in E(G_l), `T_l ≤ length`; flattened edge list `Nodup`; no WF cycle of length ≥ T_l in G'_l | (R1) greedy deletion of long cycles; "Thus G'_l has no cycle of length at least t^HB_l d_l" | yes as TRIAGE §2.12 "(R1) as any maximal family": the greedy outcomes for all vertex orders are maximal edge-disjoint families, and the Lean set of valid runs is a superset (strengthening every ∀-run statement); cycle length = number of vertices = number of edges |
| `pieceAddrs = tree0.leafAddrs`, `piece a = tree0.graphAtD G'_l a` | (R3) "Its leaves are the s=0 pieces" | yes |
| `bigPieceAddrs = {a ∈ pieceAddrs : P_l ≤ |piece a|}` | "every piece with |𝒫| ≥ P_l" | yes (new in fix round 1) |
| `twoLevel = tree0.graft (a ↦ if P_l ≤ |piece a| then tauRun a else nil)` | "the split recursion obtained from the s=0 recursion by attaching, at every piece with |𝒫|≥P_l, the tree of its τ-run" | yes; small pieces stay leaves |
| `X0 a = twoLevel.graphAtD G'_l a`, `Z0 = V(X0)` | "Z^0 denotes its vertex set and X^0_Z its leaf graph" | yes |
| `prePartAddrs = {a ∈ twoLevel.leafAddrs : P_l ≤ |X0 a|}` | "equivalently, the leaves of the two-level recursion with at least P_l vertices" | yes; the first form is now a Lib lemma (`exists_tauRun_leaf_of_mem_prePartAddrs`, `append_mem_prePartAddrs`) |
| `DupStar = twoLevel.dup G'_l` | "Dup*_l := vertices lying in at least two leaves (of any size, singletons included) of the two-level recursion" | yes |
| `mu w = #{pre-parts a : w ∈ Z0 a}`, `D = (⋃ Z0).filter (2 ≤ mu)` | defAncestors "μ_r(w) is the number of round-r pre-parts containing w"; (R4) "D_l := vertices lying in at least two round-l pre-parts" | yes; `mem_D : v ∈ D ↔ 2 ≤ μ v` |
| `home v = homeOrder.find? (a ∈ prePartAddrs ∧ v ∈ Z0 a)` | "the first pre-part containing v" | yes; `none` if none (junk, never read) |
| `guests a = (Z0 a ∩ D).filter (home · ≠ some a)` | "S_Z := {v ∈ Z^0 ∩ D_l : home(v) ≠ Z}" | yes |
| `isL1 = 2|S_Z| ≤ |Z^0|` | "(L1) |S_Z| ≤ |Z^0|/2" | yes (equivalent in ℕ/ℝ) |
| `isL2 = ∀ u ∈ Z^0, |N_{G'_l[Z^0]}(u) ∩ S_Z| ≤ s_l/2` (real) | "(L2) every u ∈ Z^0 has at most s_l/2 neighbours in S_Z in the graph G'_l[Z^0]" | yes (graph is G'_l[Z^0], not X^0_Z: HB-L2-GRAPH) |
| `isGC = ∀ x ∈ S_Z, |N_{X^0_Z}(x) ∩ (Z^0∖S_Z)| < θ^GC_l(|Z^0|)` | "(GC) no x ∈ S_Z has at least θ^GC_l(Z^0) neighbours in Z^0∖S_Z in the graph X^0_Z" | yes |
| `isLight = L1 ∧ L2 ∧ GC`, `isGCPart = L1 ∧ L2 ∧ ¬GC`, `Std = prePartAddrs.filter ¬isLight` | "light iff (L1), (L2), (GC). Otherwise standalone. … GC-part … Std_l is the set of round-l standalone pre-parts" | yes |
| `partVerts = if light then Z^0∖S_Z else Z^0`, `X = X^0_Z − S_Z`, `partGraph = if light then X else X0` | "light part with vertex set Z^0∖S_Z and graph X_Z := X^0_Z − S_Z"; Naming | yes |
| `assign e` = step (1) `find?` over home order of `a ∈ pre-parts ∧ e ∈ E(partGraph a)`; else (2) light `a` with both ends in `partVerts a`; else (3) standalone `a` with both ends in `Z0 a`; `none` = passes down | (R5)(1)–(4) | yes; step (1)'s "first in home order" is a harmless total fallback (the `X^0_Z` are edge-disjoint by SEP(i), a lemma); step (3)'s order = home order (TRIAGE §2.12) |
| `E a = E(G'_l).filter (assign = some a)`, `passed`, `next` (verts `V(H)`, edges `passed`) | "E_l(Z) … edges assigned at round l to Z"; "(4) … E(G_{l+1}) is the set of these edges" | yes |
| `pieceOf a = tree0.leafPrefix a` | propOrigin "the piece 𝒫 containing Y" | yes |
| `Valid = CyclesValid ∧ tree0.IsS0Rec ε G' ∧ tree0.StopsAt G' (IsExpander ε 0) ∧ (∀ big piece a, (tauRun a).IsTauRun ε s_l τ_l (piece a)) ∧ homeOrder.Nodup ∧ homeOrder.toFinset = prePartAddrs` | (R1), (R3) "stops exactly at (ε,0)-expanders … any witness with parameter 0", "run the τ-run of 𝒫 with s=s_l and τ=τ_l, with any witnesses", (R4) "Fix an order of the round-l pre-parts" | yes; `ε = EG.epsC`; Lemma 14^τ's hypotheses are not required (they follow from lemCap(ii) under Γ2(a)) |

### Run.lean (defHBtp loop, defAncestors, ν_l, ε_A, ψ, (H))

| Lean | Manuscript | Match |
|---|---|---|
| `Run` = list of `RoundChoice`; `R = length`; `choice l = rounds[l−1]`; `IsRound l = 1 ≤ l ≤ R` | "For l = 1, 2, …"; "R := l − 1" at the stop | yes, 1-indexed (TRIAGE §2.1) |
| `graph G 0 = G`, `graph G (l+1) = if IsRound l then next (graph l) (choice l) else graph l` | "Put G_1 := G", (R5)(4) | yes: `G_1 = G`, `G_{l+1} = next` for `1 ≤ l ≤ R`, stationary for `l ≥ R+1` |
| `Valid G Dstar = (∀ l ∈ [1,R], Dstar ≤ d_l ∧ Round.Valid G_l c_l) ∧ d_{R+1} < Dstar` | (R0) "If d_l < D_*, stop … R := l−1"; "valid run" | yes (TRIAGE §2.2); Γ is never in `Valid` |
| `E0 = E(G_{R+1})` | "put E_0 := E(G_l)" at the stop `l = R+1` | yes |
| `parts = {(l,a) : l ∈ [1,R], a ∈ prePartAddrs l}`, `ancestors = parts`, `lightParts`, `stdParts`, `ancestorsUpTo k` | Naming "A round-l part is a light part or a standalone pre-part"; defAncestors; "Every ancestor corresponds to a distinct pre-part" | yes; `PartId = ℕ × Addr` (TRIAGE §2.1) |
| `ancVerts`, `ancGraph`, `ancEps` (`2^{−6}` / `2^{−5}`), `ancS` (`s_r/2` real / `s_r`), `ancRound`, `LY = log₂|V(Y)|` | defAncestors bullets, "r(Y)", "L_Y := log|V(Y)|" | yes |
| `anc l x = {Y ∈ ancestors : r(Y)+2 ≤ l ∧ x ∈ V(Y)}` | "anc_l(x) := {Y : ancestor of a round r ≤ l−2 with x ∈ V(Y)}, and ∅ for l ≤ 2" | yes (`anc_eq_empty_of_le_two`) |
| `hubs = Z^0 ∩ D_l`, `ports = Z^0∖D_l`, `fresh = {x ∈ U_Z : anc_l(x) = ∅}`, `classed = U_Z∖F_Z` | defAncestors "For Z ∈ Std_l" bullets | yes (total in `a`; statements take `a ∈ Std_l`) |
| `dup r = Σ_{w ∈ V(G)} (μ_r(w) − 1)` (ℕ) | "dup_r := Σ_w (μ_r(w)−1)^+" | yes (truncated subtraction is `(·)^+`) |
| `mult r w = #{pre-parts a of round r : w ∈ partVerts a}` | "mult_r(w) is the number of ancestors Y of round r with w ∈ V(Y)" | yes |
| `nuAnc l = #{Y ∈ ancestors : r(Y)+2 ≤ l}` | propOV (K1) "the number ν_l of ancestors of rounds at most l−2" | yes |
| `j0 x = min {r ∈ [1,R] : ∃ pre-part a of round r, x ∈ Z0 a}`, `j1` with light parts and `partVerts` (`WithTop ℕ`, `⊤` if none) | "j_0(x) is the first round in which x lies in a pre-part, and j_1(x) the first round in which x lies in a light part (∞ if there is none)" | yes |
| `epsA D = 31ε/(C' · log₂log₂ D)`, `psiPool x = (6 log₂ x + 12)/x` | lemTower (e), (b) | yes |
| `HypH x0 F = ∀ x y, x0 ≤ x → x0 ≤ y → 2^{x/A} ≤ y → F y ≤ F x/2` | lemLacunary (iii) "(H) F(y) ≤ F(x)/2 whenever x ≥ x_0 and y ≥ 2^{x/A}" for F : [x_0,∞) → [0,∞) | yes; the domain restriction `x0 ≤ y` is the literal reading (F is only defined there). Safe for the proofs: (iii) applies (H) at `y = λ_r ≥ x_0`; (ii) and (iv) prove the weaker predicate. I concur with round 1 |

Guards (`IsRound`) on `cycles`, `pieceAddrs`, `bigPieceAddrs` (via `pieceAddrs`), `prePartAddrs`,
`DupStar`, `mu`, `D`, `assign`, `E`; hence `Std`, `parts`, `mult`, `anc`, `hubs`, `dup`, `nuAnc`
vanish outside `[1,R]` (TRIAGE §2.1 stationarity), and `graph` is stationary from `R+1`. Per-address
wrappers (`Z0`, `X0`, `guests`, `isLight`, `partVerts`, `home`, `tree0`, `tauRun`, `piece`,
`twoLevel`, `pieceOf`) are unguarded and documented as meaningful only at listed addresses.

## Edge cases and Lean conventions (all junk regions checked to be unreachable in statements)

- `Round.d` with `|V(H)| = 0` is `0` (documented).
- `MOf d ≥ 2^40` for all `d` (so `LamOf`, `sOf`, `tauOf` are never degenerate); `POf d = 0` for
  `d ≤ 1` (`λ ≤ 0`), and `thetaGC` is junk for `λ ≤ 0`. In a valid run under Γ, `d_l ≥ D_* ≥ 2^117`.
  (`POf`'s `d ≤ 1` behaviour is not mentioned in its docstring; see issue 4.)
- `graphAtD` past a leaf, `leafPrefix` at a non-leaf end, `labelU/labelN = ∅` at leaves,
  `home = none`, `j0 = ⊤`, `choice 0 = choice 1`, `graph G 0 = G`, `tauRun` off big pieces:
  all documented in the docstrings.
- `IsTauRun ε (s : ℕ)` casts `s` to `ℝ` inside `IsWitness` and `IsExpander`
  (`isWitness_natCast_iff` bridges literals).
- `Finset.filter` over the `Prop`-valued `isLight`/`isL1` uses `open Classical in` at the
  definition; consumers need `classical` (documented in `hb.md`).
- Rounds are `ℕ`, 1-indexed; offsets are written `Y.1 + 2 ≤ l` (no ℕ-subtraction in Defs).

## Downstream coverage

All 90 distinct `run.*` / `EG.HB.*` names used in the blueprint sketches (s2a, s2b, s3b, s5, s6a,
s6b, s7a, s7b) resolve to a Def, up to the renames below. Objects checked one by one against the
`defs_needed` rows citing s2 in s3b:304–305, 474–475, 600; s5:116–117, 248, 386–387, 433, 503,
585, 636; s6a:528–532, 596; s7a:137, 217, 221, 284, 422, 603, 707; s7b:123.

| Blueprint form | Def to use | Kind |
|---|---|---|
| `run.LY G Y.1 Y.2`, `run.ancEps G Y.1 Y.2`, `run.ancS G Y.1 Y.2` (s3b), `run.ancVerts G r a`, `run.ancGraph G r a`, `run.LY G r a` (s2b) | `run.LY G Y`, `run.ancEps G Y`, `run.ancS G Y`, `run.ancVerts G (r, a)`, `run.ancGraph G (r, a)` — these take `Y : PartId` | rename (argument shape) |
| `run.pieceAddrs G l`, `run.pieceOf G r Y`, `run.R G` | `run.pieceAddrs l`, `run.pieceOf r Y`, `run.R` (no `G`; also `run.tree0 l`, `run.tauRun l q`, `run.cycles l`) | rename |
| `run.Mr G l`, `run.H Y`, `run.allAncestors G`, `run.ancestorSet G`, `run.isStd Y`, `EG.HB.psi` | `run.M G l`, `run.ancGraph G Y`, `run.ancestors G`, `Y ∈ run.stdParts G`, `psiPool` | rename |
| `run.thetaGC G r a` (s6b), `run.bigPieceAddrs G l` (s2b) | exist (fix round 1) | — |
| `run.srcs`/`srcEdges` (EdgeSrc), `run.TypeAlpha/TypeBeta`, `run.lightIncidences`, `run.Parentless`, `run.IsClassedPort`, `KJS/KHUB/tJS` | Spec-local one-liners of the provided objects (D-HB-25), or s3/s7 Defs | by design |
| `(X0 a).eBetween {x} W` (s2a/s2b lemGC sketches) vs `Round.isGC`'s `|nbrs x ∩ W|` | equal for loopless graphs; a bridging Lib lemma is useful (issue 3) | API |

Statability spot-checks (each written out in my head against the Def types): lemCap(ii) (`degE
(run.E G l a) v ≤ M_l − 1`, `128 s_l log²|piece| ≤ τ_l`); propStructure(i)–(iv) (`ancGraph`,
`ancEps`, `ancS`, pointwise `deg`, `graph_edges_subset_of_le`, `Disjoint (X0 a).edges (X0 b).edges`,
`(run.cycles l).length`, `E0`); lemEL; propOV (K1)–(K3), (F11) (`leafMass`, `DeltaGe`, `dup`,
`hubs`, `isL1`, `DupStar`, `mult`, `mu`); propDegRec kinds (a)–(c) (`(run.tauRun l q).deleted
(run.piece G l q)` at `q ∈ bigPieceAddrs`, small leaves via `twoLevel.leafAddrs`, guest edges via
`X0`/`guests`); lemGC; propOrigin (`pieceOf`, `DupStar`, `(tauRun q).dup (piece q)`); propParentless
(`home`, `ports`, `fresh`, `j0 + 1` in `WithTop ℕ`, `j1`, `partVerts`, `run.R − Y.1`); lemTower
(`LY`, `nuAnc`, `psiPool`, `epsA`, `hubs`); lemLacunary (`HypH`, `lam`); s3 (`KJS = M^2`, JS sites
`Icc (Y.1+2) run.R`, `LY`, `ancEps`, `ancS`); s5 (`lightParts`, `X`, `E`, `partVerts`); s6
(designation `ℕ → V → PartId`, `anc`, `classed`, `ancestorsUpTo`, `thetaGC G r a`, `DupStar`); s7
(`M`, `lam`, `mult`, `ancRound`, `fresh`, `Std`, `classed`). All statable.

## Non-vacuity (scratch test, not added to the repo)

`EGTest/HB.lean` already contains: a valid one-round run on `K₃` (both directions of both stopping
rules exercised), a genuine three-split τ-run with two deleted edges, and the round-1 overlap test
(a guest, a light part losing a guest edge, `assign` step (1) and pass-down). What was still
untested: steps (2) and (3) of (R5), a standalone pre-part, `Std ≠ ∅`, `Dup*`, a τ-run deletion
inside a round, `next`.

`HBScratch3.lean` (session scratchpad; compiles with `lake env lean`, 0 errors, no `sorry`):
`G5` on `Fin 5` with edges `01, 03, 14, 02, 12` (`d = 2`, so `λ = 1`, `P = 1`, `θ^GC(z) = z`,
`s = 40^100`). First level: root split `({3,4}, {0,1})`; pieces `[false] = G5[{0,1,3,4}]` and
`[true] = G5[{0,1,2}] − E(G5[{0,1}])`. Second level: the τ-run at `[false]` splits `({0,3}, ∅)`.
Proved: `twoLevel` is the expected grafted tree; the τ-run deletes exactly `{01}`, and `01` lies in
no leaf of the two-level tree; pre-parts `{[ff],[ft],[t]}` with `Z⁰ = {0,3}, {1,4}, {0,1,2}`;
`Dup* = {0,1} = D`; `μ(0) = 2`.
- Order A `[ff, ft, t]`: `home 0 = ff`, `home 1 = ft`, `S_t = {0,1}`, `2·2 > 3` so `t` fails (L1)
  and `Std = {[true]}`; `ff`, `ft` light; **`assign 01 = some [true]` by step (3)** (the edge is in
  no part graph and in no light part, but inside `Z⁰_t`); `passed = ∅`; hubs/ports of `t` are
  `{0,1}` / `{2}`.
- Order B `[t, ff, ft]`: `S_t = ∅` (light, `V(t) = {0,1,2}`), `S_ff = {0}`, `S_ft = {1}`; `ff`
  and `ft` are light with (GC) evaluated through `θ = 2`; `X_ff`, `X_ft` have no edges;
  **`assign 01 = some [true]` by step (2)**; the guest–core edge `03` (type (α) of propOrigin)
  **passes down**; `E(G_{next}) = {03, 14}`.
This matches a hand reading of (R4)/(R5), and shows that steps (2)/(3) are not vacuous in the Lean
model (they apply exactly to edges deleted by a τ-run or to guest edges whose ends are duplicated).

## Issues

| # | Severity | Location | Issue | Suggested fix |
|---|---|---|---|---|
| 1 | minor | `hb.md` name map / CONVENTIONS | The PartId-indexed Defs (`LY`, `ancVerts`, `ancGraph`, `ancEps`, `ancS`) take `Y : PartId`, while blueprints s2b/s3b write them with two arguments `G r a` / `G Y.1 Y.2`; `pieceAddrs`, `pieceOf`, `tree0`, `tauRun`, `cycles`, `R` take no `G` although s2a/s2b/s7a pass one. Statable as is (`run.LY G (r, a)`), but every Spec author will hit it. | Add these rows to the name map in `hb.md` (and CONVENTIONS): "ancestor data takes `Y : PartId`; choice-only objects take no `G`". No Def change. |
| 2 | minor | `Run.lean` (guards) | There is no run-level `E(Cyc_l)` as a `Finset`: propStructure(iii)'s partition and lemCap need `Round.cycEdges (run.choice l)`, which is *unguarded* (for `l > R` it is `cycEdges default = ∅` anyway, and for `l = 0` it is round 1's edges), while `run.cycles l` is guarded. | Either add `run.cycEdges l := ((run.cycles l).flatMap cycleEdges).toFinset` (a Def, before the lock) or record in CONVENTIONS that Specs write `((run.cycles l).flatMap cycleEdges).toFinset`. |
| 3 | minor | `EG/Lib/HB/*` | Graft lemmas that the s2b proof route lists and that are true for these Defs are not yet in Lib: `WF` of `graft` from `WF` of the pieces; `internalAddrs`/`labelAt` of the graft; `deleted (twoLevel) = ⋃_{q big} (tauRun q).deleted (piece q)` when the first level deletes nothing (needs `IsS0Rec → delAt = ∅`); `(tauRun q).dup (piece q) ⊆ DupStar`; `u ∉ DupStar → u` in exactly one piece; `OVHyp` transport. Also the bridge `((X.nbrs x) ∩ W).card = X.eBetween {x} W` for `x ∉ W` (lemGC sketches use `eBetween`, `Round.isGC` uses `nbrs`). | Lib work for the s2b proof tasks; no Def change. |
| 4 | cosmetic | `Round.lean` `POf` docstring | `POf d = 0` for `d ≤ 1` (then every two-level leaf, even an empty leaf graph, is a "pre-part"); junk, unreachable (`d_l ≥ D_* ≥ 2^117`). | One clause in the docstring, as for `thetaGC`. |
| 5 | cosmetic | `EGTest/HB.lean` | Steps (2) and (3) of (R5), a standalone pre-part, `Dup*`, and a τ-run deletion inside a round are untested in the repo. | Add `HBScratch3.lean` (above) as a `namespace StandaloneTest`. |

Design deviations re-checked and accepted (as in round 1): D-HB-1 (`Round.Valid H c` without `n`
and `Dstar`: `n = |V(H)|` and `D_*` enters only through `Run.Valid`; round-level Specs add
`Dstar ≤ Round.d H`), D-HB-2 (own inductive `STree`), D-HB-8 ((R1) as any maximal family, a
strengthening), D-HB-9 (pre-parts by the "equivalently" form, first form now a Lib lemma), D-HB-12
((R5) as one `Option` assignment, step (3) in the home order), D-HB-14 (`Run` structure), D-HB-16
(guards), D-HB-20 (`HypH` domain), D-HB-21 (no `irreducible_def`).

## Summary for the orchestrator

Approve. The four Defs files are faithful to v6.1 (M_l is the integer ceiling), total with
documented junk values, and usable: every quantity that s2–s7 read is present with the TRIAGE
index types (`Addr`, `PartId`, ℕ rounds, ℕ/ℝ parameters), and the (R4)/(R5) semantics were checked
on two non-trivial hand examples (round-1 tests plus the new scratch test) including the two
previously unexercised assignment steps. Issues 1, 3, 4, 5 need no Def change; issue 2 is a
one-line optional Def (`run.cycEdges`) that can equally be a documented Spec idiom. The files can be
locked.
