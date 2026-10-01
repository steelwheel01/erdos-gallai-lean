# P3A: clean-room review, round 2 (Specs of probe P-3, part 1; re-run 2026-09-30)

Reviewer: clean-room Spec reviewer, round 2 (re-run of 2026-09-30, after the proof stage and its
two fix rounds and the re-dispatch of the same day). This file replaces the round-2 review of
2026-09-29 (in git history, commit ed552cf and earlier). I back-translated every Spec from the
Lean and compared it with the TeX *before* reading `P3A.review1.md`, the previous `P3A.review2.md`
and `P3A.audit.md`; where I agree with them I say so briefly, and I mark what I add. No Lean file
of the repository was edited. My scratch checks are in the session scratchpad
(`P3ARev2c.lean`, outside the repo; `lake env lean`: rc=0, 0 errors). The manuscript is a
CANDIDATE proof (AI-reviewed only); nothing here calls the conjecture solved.

Read in full: the eight Specs `EG/Spec/HB/{TauRules, SEP, ThinCut, Overlap, Lemma14Tau, GC, EL,
TowerC}.lean`; `EG/Proof/HB/{EL, TowerC}.lean` and the theorem headers of the other six Proof
files; the locked Defs `EG/Defs/HB/{Witness, SplitTree, Round, Run}.lean`, `EG/Defs/Graph.lean`,
`EG/Defs/Expander.lean`, `EG/Defs/Constants.lean`, `EG/Defs/Gamma/Core.lean`;
`EGTest/ProbeP3A.lean`; `work/p2b/P3A.md` (all rounds); `AGENTS.md`, `CONVENTIONS.md`;
`proofs/manuscript/s2.tex` v6.1 l.1–135 (conventions, defWitness, defTauRules, eqSplit, Facts
with proofs), 135–277 (lemSEP, lemThinCut with proofs), 278–501 (lemOVgeneric, lem14tau with
proofs), 503–640 (defHBtp, defAncestors), 821–837 (lemEL), 1144–1172 and 1249–1257 (lemTower,
proof of (c)), 1282–1318 (lemGC).

## Verdict: APPROVE

- All 25 statements are faithful to the TeX (§1). The only deviation with mathematical content
  is the T1 repair `0 < τ` on the two bounds of lem14tau (c) (`L14ThinStatement`), which I
  re-derived independently and re-checked in Lean (§6); it is minimal. Every other deviation is
  a strengthening or an explicit implicit conjunct (§1.3).
- No contradictory hypotheses; no conclusion is trivially true where the TeX has content (§2).
- Declared inputs (§3): the only remaining declared input is `TowerCStatement`
  ([s2:lemTower] (c)), exactly what lemGC (iv) cites ("(iv) is Lemma lemTower (c)"), stated as
  in the TeX except that the standing assumption Γ1–Γ4 is replaced by `Gamma1core`, which makes
  the *input* stronger than the TeX; I re-derived that it stays true. `ELStatement` is proved.
  Nothing the probe should prove is hidden among the inputs.
- Hygiene (§4): lint 0 findings; `sorry` only in `EG.towerC`; every probe theorem has exactly
  its Spec's type; axioms `[propext, Classical.choice, Quot.sound]` (only `gcTheta` adds
  `sorryAx`, through `towerC`); Spec/Defs/Proof files of the unit are byte-identical to HEAD;
  the test file type-checks (rc=0, 0 sorry).
- Issues (§5): 1 minor (process), 4 cosmetic; none blocks.

## 1. Fidelity (back-translation, compared with the TeX)

Notation: `ε = epsC = 2^{-5}`, `log = Real.logb 2`, `m = |H| = H.card`, `n_0 = |H_0|`,
`H_a = t.graphAtD H a`, children `a0 = a ++ [false]` (`ν_1`), `a1 = a ++ [true]` (`ν_2`),
`U'_a = t.labelU a`, `N''_a = t.labelN a`, `F''_a = t.delAt H a`, `Dup = t.dup H`,
`S = t.leafMass H`, `Δ_{≥M} = t.DeltaGe H M`, `dup_{≥M}(v) = t.dupGe H M v`.

### 1.1 Defs facts the reading depends on (re-checked in the locked files)

- `IsWitness H ε s U F` = `U ⊆ V(H) ∧ F ⊆ E(H) ∧ 1 ≤ |U| ∧ |U| ≤ 2m/3 ∧ |F| ≤ s|U| ∧
  |Nbr_{H−F}(U)| < ε|U|/log²m` (reals, `log²m = (logb 2 m)^2`): the TeX witness conjunct by
  conjunct; it is the negated body of `IsExpander` with the same casts. A witness forces `m ≥ 2`
  (`1 ≤ |U| ≤ 2m/3`) and `0 ≤ s` (`0 ≤ |F| ≤ s|U|`, `|U| ≥ 1`; checked in Lean, scratch (iii)).
- `nbrSet U = (V(H) \ U).filter (has a neighbour in U)` = `Nbr_H(U)`; `witN H U F =
  Nbr_{H−F}(U)`; `witF0 H U N = E_H(U, V \ (U ∪ N))`, a function of `(U,N)` (TeX Fact (c):
  "defined from `F_0 = E_H(U, V∖(U∪N))`").
- `tauHout = {v ∈ U : τ ≤ deg_{F_0}(v)}` (TeX "`deg_{F_0}(v) ≥ τ`", non-strict, real
  comparison), `tauU1 = U \ H_out`, `tauN1 = N ∪ H_out`, `tauF1 = E_H(U', V \ (U' ∪ N'))`,
  `tauHin = {x ∈ V \ (U' ∪ N') : τ ≤ deg_{F_1}(x)}`, `tauN2 = N' ∪ H_in`,
  `tauF2 = splitDel H U' N'' = E_H(U', V \ (U' ∪ N''))`; `tauG1 = H[U'∪N''] − F''`,
  `tauG2 = ((H − U') − E(G_1)) − F''`: the literal (1), (2) and the literal children.
- `induce U` has vertex set `V(H) ∩ U` and the edges inside `U`; `deleteVerts U = induce (V \ U)`;
  `deleteEdges F` keeps the vertices; `edgesBetween A B = {e ∈ E(H) : ∃ a ∈ A, b ∈ B, s(a,b) = e}`,
  `eBetween = |edgesBetween|`; `FGraph` is loopless and `@[ext]`, so equalities of graphs are
  equalities of both finsets; `H ≤ H'` is inclusion of both finsets.
- `STree`: `nil` a leaf, `node (U',N'') l r`; `graphAtD` computes `H_a` by `splitFst`/`splitSnd`
  along the address (total; below a leaf it repeats the leaf graph, but every Spec reads it only
  at `nodeAddrs`/`leafAddrs`/`internalAddrs` or prefixes of them); leaves, internal nodes and
  `Dup`, `S`, `Δ`, `dup` are counted by *address* ("distinct leaf nodes are distinct leaves even
  if their vertex sets coincide"); `deleted = ⋃_{a internal} F''_a`.
- `WF` = "at every internal `a`, `U'_a, N''_a ⊆ V(H_a)` disjoint" (the split-recursion side
  condition); `OVHyp ε c` = `WF` + the three node conditions `m ≥ 2`, `|a0| ≤ 3m/4`,
  `|N''_a| ≤ cε|U'_a|/log²m` (literal); `IsS0Rec ε` = `WF` + at every internal node a witness
  `(U,F)` with parameter `0` and label `(U, Nbr_{H_a}(U))` (literal); `IsTauSplitTree ε τ` = `WF`
  + at every internal node some `s_a < τ` and a witness with parameter `s_a` whose `τ`-rules give
  the label (literal); `IsTauRun ε s τ` = `WF` + `StopsAt` ("leaf ⇔ `(ε,s)`-expander", both
  directions) + label from the `τ`-rules of some witness with parameter `s` (`s : ℕ`).
  `IsTauRun` has no `s < τ` clause, but an internal node has `m ≥ 2`, so under the lemma's
  hypothesis `τ ≥ 128 s log² n_0 ≥ 128 s > s`, as the TeX remarks.
- Round/run layer: `Z0 = V(X^0)`; `D = {v ∈ ⋃ Z^0 : μ(v) ≥ 2}`; `home v` = first address of the
  home order that is a pre-part containing `v`; `guests = {v ∈ Z^0 ∩ D : home v ≠ Z}`;
  `isL1`: `2|S_Z| ≤ |Z^0|`; `isL2` in `G'_l[Z^0]` with real `s_l/2`; `isGC`: every guest `x` has
  `|N_{X^0}(x) ∩ (Z^0 \ S_Z)| < θ^GC`; `isLight = L1 ∧ L2 ∧ GC`; `isGCPart = L1 ∧ L2 ∧ ¬GC`;
  `Std = prePartAddrs.filter ¬isLight`; `partVerts = Z^0 \ S_Z` if light else `Z^0`; `assign` =
  (R5) steps (1)–(3) in the home order, `none` = passes down; `next.edges = passed = {e ∈ E(G'_l)
  : assign e = none}`; `thetaGC d z = ⌈z λ^{-1/2}⌉₊` (`rpow`); `tauOf = ⌈128 s log² M⌉₊`;
  `POf = ⌈λ^{103}⌉₊`; `sOf = ⌈Λ^{100}⌉₊`; `Run.Valid` = `∀ l ∈ [1,R], D_* ≤ d_l ∧ Round.Valid`,
  and `d_{R+1} < D_*`; `run.graph` is stationary for `l ≥ R+1`; `ancestors = parts = {(l,a) :
  l ∈ [1,R], a ∈ prePartAddrs l}`; `ancVerts (l,a) = partVerts l a`. I confirmed that
  `prePartAddrs`, `X0`, `Z0`, `DupStar`, `mu`, `D`, `home`, `guests` never mention `isGC`/`isLight`
  (lemGC (i), first clause).

### 1.2 Statement by statement

| Statement | plain mathematics (what the Lean says) | TeX (quoted) | result |
|---|---|---|---|
| `WitnessExistsStatement` | `s ≥ 0`, `H` not an `(ε,s)`-expander ⇒ `m ≥ 2` and `∃ (U,F)` witness | "Then `m ≥ 2` … Since `H` is not an `(ε,s)`-expander, a witness exists" | faithful |
| `WitnessFactStatement` | `s ≥ 0`, witness `(U,F)`, `N = Nbr_{H−F}(U)` ⇒ `F_0 ⊆ F`, `Nbr_{H−F_0}(U) = N`, `(U,F_0)` witness | "*Fact.* `F_0 ⊆ F` and `Nbr_{H−F_0}(U) = N`. In particular `(U,F_0)` is again a witness" | faithful |
| `TauEqSplitStatement` | context `s ≥ 0`, witness, `s < τ` ("let `τ > s` be real"), `N`; ∀ `e ∈ F''`: `e = xy` with `x ∈ U'`, `y ∈ V \ (U'∪N'')`, `e ∉ (U'∪N'')^{(2)}`, `e` meets `U'`; `G_1 = H[U'∪N'']`, `G_2 = H[V\U'] − E(H[N''])` as graphs | "Every edge of `F''` has one end in `U'` and the other outside `U'∪N''`, so no edge of `F''` lies inside `U'∪N''`, and every edge of `F''` meets `U'`. Hence (eqSplit)" | faithful (the premise conjunct is true by the definition of `splitDel`) |
| `TauFactAStatement` | `U' ∩ N'' = ∅`; `U' ∪ N' = U ∪ N`; `F'' ⊆ F_1 ⊆ F_0 ⊆ F`; `U', N'' ⊆ V(H)` | Fact (a) | faithful; the two added conjuncts are implicit (`U' ⊆ U ⊆ V`; `N, H_out, H_in ⊆ V`) and true |
| `TauFactBStatement` | `E(G_1)`, `E(G_2)`, `F''` pairwise disjoint with union `E(H)`; `V(G_1) = U'∪N''`; `V(G_2) = V \ U'`; `U'` only in `G_1`, `N''` in both, `V \ (U'∪N'')` only in `G_2` | Fact (b) | faithful (`G_i` are the literal `tauG1`/`tauG2`) |
| `TauFactCStatement` | `(U,F_0)` witness; `N_0 := Nbr_{H−F_0}(U) = N`; the nine objects at `(U,N_0)` equal those at `(U,N)` | Fact (c) | faithful; the first sentence of (c) is definitional (the Defs take `(H,U,N,τ)` and no `F`); the content is `N_0 = N` |
| `SEP0Statement` | `WF` ⇒ at every internal `a`: three disjointnesses, `E(a0) ∪ E(a1) ∪ F''_a = E(H_a)`, `U'_a` only in `a0`, `N''_a` in both, other vertices of `H_a` only in `a1`, `|a0| + |a1| = |a| + |N''_a|`; every vertex of a node lies in a leaf extending it; `S = n_0 + Σ_{internal} |N''_a|` | (0) | faithful |
| `SEPMonoStatement` | `b` a node, `a <+: b` ⇒ `H_b ≤ H_a` | (0′), implicit ("Every edge of a child is an edge of its parent", "vertex sets shrink downwards") | faithful; without `WF` (stronger; true since `induce`/`deleteEdges` give subgraphs) |
| `SEPiStatement` | `WF`, `e ∈ E(H_0)` ⇒ `#{leaves ∋ e} + #{internal a : e ∈ F''_a} = 1`; a leaf containing `e` contains its ends; if `e ∈ F''_a`: `e ∈ E(H_b)` for every prefix `b` of `a` (`a` included), `e ∉ E(a0) ∪ E(a1)`, `e = xy` with `x ∈ U'_a`, `y ∈ V(H_a) \ (U'_a ∪ N''_a)`, `x` only in `a0`, `y` only in `a1` | (i) | faithful; "the first node … at which this happens" ⇔ "edge of every ancestor, of neither child": at a strict ancestor the edge (not deleted there, count = 1) lies in exactly one child by (0), which contains both ends |
| `SEPiiStatement` | `WF`, `u ∈ V(H_0) \ Dup` ⇒ ∃ leaf `L ∋ u`, unique among leaves, `{nodes ∋ u} = {prefixes of L}`, `u ∉ N''_a` for internal prefixes `a` | (ii) | faithful |
| `SEPiiiStatement` | `WF`, `u ∈ V(H_0) \ Dup`, `u ∈ V(L)`, `L` leaf, `h ∈ V(H_0) \ V(L)`, `ν* <+: L`, `h ∈ V(H_{ν*})`, every prefix of `L` containing `h` is no longer than `ν*` ⇒ every deleted `hu'` with `u' ∈ V(L) \ Dup` lies in `F''_{ν*}` | (iii) | faithful ("deepest" = longest prefix; prefixes of `L` are totally ordered, so `ν*` is unique; `u` only names `Leaf_u`) |
| `ThinCutStatement` | `τ > 0`, `IsTauSplitTree ε τ` ⇒ ∀ leaf `L`, ∀ `h : V`: `#{e ∈ deleted : ∃ u ∈ V(L) \ Dup, e = hu} ≤ ⌈τ⌉ − 1` (ℤ); `≤ k − 1` (ℕ) if `τ = k`; `= 0` if `h ∈ V(L)` | the display, "which is `τ−1` when `τ` is an integer", "this number is `0` if `h ∈ V(Leaf)`" | faithful (edge count = vertex count, `u ↦ hu` injective and `hh` is never an edge; `τ = k > 0` gives `k ≥ 1`, so `k − 1` is exact) |
| `ThinCutEdgeStatement` | same hypotheses; `u ∉ Dup`, `u ∈ e ∈ E(H_0)` ⇒ `e` deleted, or `e ∈ E(L)` for the unique leaf `L ∋ u` | "Moreover, if `u ∉ Dup` then every edge at `u` is either deleted or an edge of the unique leaf containing `u`" | faithful (`u ∈ V(H_0)` follows from `u ∈ e ∈ E(H_0)`) |
| `OVStatement` | `c > 0`, `3.42cε < 1`, `n_0 ≥ 1`, `OVHyp ε c` ⇒ ∀ real `M ≥ 2`: (a) `Δ_{≥M} ≤ cε(1/log²M + 1/(c_OV log M)) S` and that `≤ 3.42cεS/log M`; `Σ_{v∈V(H_0)} dup_{≥M}(v) = Δ_{≥M}`; (b) `#{L : |L| ≥ M, v ∈ L} ≤ 1 + dup_{≥M}(v)`; `Σ_{|L|≥M} |L| ≤ |⋃_{|L|≥M} V(L)| + Δ_{≥M}`; (c) `S ≤ n_0/(1 − 3.42cε)` | (a)–(c), "(so `Σ_v dup_{≥M}(v) = Δ_{≥M}`)", `c_OV := log₂(4/3)` (= `cOV`) | faithful; (a) in the sharp form (needed by lem14tau (b)); (b)'s consequence additive (no ℕ-subtraction); `M` real; the sum over `V(H_0)` loses nothing since `N''_a ⊆ V(H_0)` under `WF` |
| `OVInstanceStatement` | `IsS0Rec ε` ⇒ at every internal `a`, for every witness `(U,F)` of parameter `0` with label `(U, Nbr_{H_a}(U))`: `F = ∅`, `Nbr_{H_a−F}(U) = N`, `H_{a0} = H_a[U∪N]`, `H_{a1} = (H_a \ U) − E(H_a[U∪N]) = H_a[V\U] − E(H_a[N])`, `F''_a = ∅`, ∀ `τ > 0`: `F_0 = H_out = H_in = ∅`, `U' = U`, `N'' = N`; globally `IsTauSplitTree ε τ` ∀ `τ > 0`, `OVHyp ε 1`, `S ≤ n_0/(1−3.42ε) ≤ 1.12 n_0` | "*Instance `c = 1`*" paragraph | faithful; the "[BM] recursion" sentence is commentary; `τ > 0` is needed for `H_out = ∅` (at `τ ≤ 0`, `H_out = U`), as the TeX says "for any `τ > 0`" |
| `L14SplitStatement` | `s ≥ 1` (ℕ), `128 s log² n_0 ≤ τ`, `IsTauRun ε s τ`; at every internal `a` (`K = H_a`, `m = |K|`), for every witness `(U,F)` of parameter `s` whose `τ`-rules give the label: `|H_out|+|H_in| ≤ |F_0|/τ ≤ s|U|/τ ≤ |U|/(128 log²m)`; `|N''| < 1.25ε|U|/log²m < 1.5ε|U|/log²m`; `(127/128)|U| ≤ |U'|`, `0 < |U'|`; `U ⊆ U'∪N''`; `|U'∪N''| ≤ 0.698m < 3m/4`; `m − |U'| < m` (ℕ) | (a), first display and sentence | faithful; each link of the TeX chains is a conjunct, strict/non-strict as in the TeX; "every witness giving the label" is a true strengthening (the counting uses only `(U,F)` and `m ≤ n_0`); at an internal node `m ≥ 2`, so `τ ≥ 128 > 0` and the divisions are real |
| `L14TermStatement` | (T1) every `τ`-rule split of a `K` with `2 ≤ |K| ≤ n_0` by a witness of parameter `s` has children `splitFst`/`splitSnd` of sizes in `[1, |K|)`; (T2) for every address-dependent witness rule `W` (a witness at every non-expander) there is a `τ`-run of `H_0` whose labels are the `τ`-rule sets of `W`'s witnesses | "The recursion terminates", "for every choice of witnesses" ("Both children of every split have fewer vertices than their parent, so … the binary tree is finite") | faithful formalization of termination: the recursion driven by `W` is a finite `STree` satisfying `IsTauRun` |
| `L14GlobalStatement` | `|deleted| ≤ 4 s n_0 log n_0`; every edge in exactly one leaf or deleted at exactly one node; every leaf graph an `(ε,s)`-expander; `S ≤ 2n_0 − 2n_0/(2 + log n_0)` | rest of (a) | faithful; "it is a split recursion" is `WF`, part of `IsTauRun` (and implied by the label clause, checked in `EGTest`) |
| `L14OVStatement` | at every internal `a`: `|N''_a| ≤ 1.6ε|U'_a|/log²m`, `U'_a` only in `a0`, `|a0| ≤ 3m/4`, `m ≥ 2`; `OVHyp ε 1.6`; `S ≤ n_0/(1−5.5ε)`; `n_0/(1−5.5ε) ≤ 1.21 n_0`; `Δ_{≥M} ≤ 5.46εS/log M` ∀ `M ≥ 2` | (b) | faithful (`m ≥ 2` is the proof's "every non-leaf node has `m ≥ 2`") |
| `L14ThinStatement` | (c) ∀ leaf `L`, ∀ `h`: [`τ > 0` ⇒] `# ≤ ⌈τ⌉ − 1` and [`τ > 0` ⇒] `# ≤ k − 1` for `τ = k`; `# = 0` if `h ∈ V(L)` (unconditional); (d) as `ThinCutEdgeStatement` (unconditional) | (c), (d) | faithful up to the T1 repair (§6) |
| `GCDefStatement` | valid run, `r ∈ [1,R]`, pre-part `a`: (L1) ∧ (L2) ⇒ (light ⇔ (GC)); ¬((L1) ∧ (L2)) ⇒ not light | (i), second clause | faithful; the first clause is definitional (§1.1, last bullet) |
| `GCStatement` | (ii) light `a`, guest `x` ⇒ `e_{X^0_a}({x}, Z^0_a \ S_a) < θ^GC_r(Z^0_a)`; (iii) GC-part `a` ⇒ `a ∈ Std_r`, `V(Y) = Z^0_a`, every edge of `G'_r` inside `Z^0_a` has `assign ≠ none`, `E(X^0_a) ⊆ E_r(a)`, no edge of `G_{r+1}` inside `Z^0_a`, `S_a ⊆ D_r ⊆ Dup*_r` | (ii), (iii) with the parenthetical "(the edges of `X^0_Y` … by (R5)(1))" | faithful; `eBetween {x} B = |N_{X^0}(x) ∩ B|` since `B = Z^0 \ S ⊆ V(X^0)`, `x ∉ B` and `X^0` is loopless, so (ii) is the quantity of `isGC`; "assigned at round `r`" = to some part |
| `GCThetaStatement` | `Gamma1core D_*`, valid run, `r ∈ [1,R]`, pre-part `a` ⇒ `τ_r < θ^GC_r(Z^0_a)` (ℕ) | (iv) "`θ^GC_r(Z^0) > τ_r` for every round-`r` pre-part `Z`" | faithful; the standing assumption Γ1–Γ4 is replaced by `Gamma1core`, so the Spec is stronger; true (§3) |
| `ELStatement` | valid run, `Y ∈ ancestors` (`Y = (r,a)`), every `l > r` ⇒ no edge of `G_l` inside `V(Y)` | lemEL | faithful; `l > R+1` harmless (`graph` stationary). Proved (`EG.edgeLaminarity`, 0 `sorry`) |
| `TowerCStatement` | `Gamma1core D_*`, valid run, `D_* ≤ d_1`, `r ∈ [1,R]` ⇒ `τ_r ≤ 257Λ_r^{102} ≤ 2^{111}λ_r^{102}`; `τ_r/P_r ≤ 2^{111}/λ_r`; ∀ pre-part: `P_r λ_r^{−1/2} ≤ θ^GC_r`, `τ_r < P_r λ_r^{−1/2}` | lemTower (c) | faithful (`σ+2 = 102`, `σ+11 = 111`, `rpow −1/2`, ℕ ceilings cast to ℝ; "(so `R ≥ 1`)" follows from `Valid`) |

Checks made in this round (my own; where the earlier reviews list the same item I agree):
- **Quantifier order.** In `L14SplitStatement` and `OVInstanceStatement` the witness is
  universally quantified after the address and before the label hypothesis (every witness
  consistent with the label; a true strengthening). In `L14TermStatement` (T2) `W` is quantified
  outside `∃ t`, as "for every choice of witnesses" requires. In `SEPiiiStatement` `ν*` is
  universally quantified with its two defining properties, which pin it down uniquely. In the
  `τ`-rule statements `N` is a bound variable fixed by `N = witN H U F` (a definitional
  abbreviation, not an extra hypothesis).
- **Strict vs non-strict.** `tauHout`/`tauHin`: `τ ≤ deg` (TeX `≥`); `IsWitness`: `<` (TeX `<`);
  lem14tau (a): `≤, ≤, ≤` for the `τ`-chain, `<, <` for `|N''|`, `≤` for `127/128`, `≤ 0.698m`,
  `< 3m/4`, `n_2 < m`; (b): `≤ 1.6ε…`, `≤ 3m/4`, `≤ 1.21`, `≤ 5.46…`; OV: `≤` throughout; thin
  cut: `≤ ⌈τ⌉ − 1`, `= 0`; GC (ii) `<`, (iv) `<`; Tower (c): `≤, ≤, ≤, ≤, <`. All as in the TeX.
- **Constants and log base.** Every logarithm is `Real.logb 2` (s2: "`log = log₂`"). Literals
  `1.25`, `1.5`, `127/128`, `0.698`, `3/4`, `4 s n_0 log n_0`, `2n_0 − 2n_0/(2 + log n_0)`,
  `1.6`, `5.5`, `1.21`, `5.46`, `3.42`, `1.12`, `257`, `2^{111}`, `102`, `128`, `2^{40}` are the
  TeX's. `Real.logb 2 M ^ 2` parses as `(logb 2 M)^2`; `x / logb 2 K.card ^ 2` as
  `x / (log m)²`; `U.card / (128 * Real.logb 2 K.card ^ 2)` as `|U|/(128 log²m)`. Numeric
  relations re-checked by `norm_num` (scratch (iv)): `3.42·1.6 ≤ 5.5`, `1/(1−5.5ε) ≤ 1.21`,
  `1/(1−3.42ε) ≤ 1.12`, `257·2^{102} ≤ 2^{111}`, `(1 + 1.25/32)(2/3) ≤ 0.698`, `1/128 = ε/4`,
  `1.6(1 + 41/17) ≤ 5.46` and `1 + 41/17 ≤ 3.42` with `3^{41} ≤ 2^{65}` (so `c_OV ≥ 17/41`
  suffices for both constants).
- **Integer vs real.** `s : ℕ` cast to ℝ (TeX "`s ≥ 1` an integer"); `τ`, `c`, `M` real;
  `m − |U'| < m` in ℕ is exact (`1 ≤ |U'| ≤ m`); `⌈τ⌉ − 1` in ℤ and `k − 1` in ℕ under
  `τ = k > 0`; `θ^GC`, `τ_r`, `P_r`, `s_r`, `M_r` are ℕ ceilings as in v6.1 (R2), (GC);
  `λ_r^{−1/2}` is `rpow`.
- **Edge cases.** `n_0 ∈ {0,1}` in the lem14tau statements: `StopsAt` forces `t = nil` (a graph
  with `≤ 1` vertex is an expander), so `deleted = ∅`, `S = n_0`, and the bounds of
  `L14GlobalStatement` read `0 ≤ 0` and `n_0 ≤ 2n_0 − 2n_0/2 = n_0`; only (c) fails at `τ = 0`
  (§6). `τ = 0` is allowed by the hypothesis only at `n_0 ≤ 1`, where no internal node exists,
  so `L14SplitStatement`'s `x/τ` (Lean `x/0 = 0`) is never reached. `IsTauSplitTree` does not ask
  `s_ν ≥ 0`, but a witness forces it. The junk regimes `POf d = 0`, `thetaGC = 0` (`λ ≤ 0`) are
  unreachable in `GCThetaStatement`/`TowerCStatement`: `Gamma1core D → 2^{2^{256}} ≤ D`
  (scratch (v)) and `Valid` gives `D ≤ d_r` for `r ∈ [1,R]`. `OVStatement` at `S = 0` or
  `Δ = 0` is consistent. `ThinCutStatement` with `h ∉ V(H_0)`: the count is `0`.

### 1.3 Every deviation from the literal TeX, classified

| # | Deviation | Direction | Verdict |
|---|---|---|---|
| 1 | `L14ThinStatement`: `0 < τ` on the two bounds of (c) | weaker than the literal TeX | the literal TeX is false at `τ = 0` (§6); minimal repair; T1 |
| 2 | `L14SplitStatement`, `OVInstanceStatement`: every witness consistent with the label | stronger | true |
| 3 | `TauEqSplitStatement`: the premise "one end in `U'`, other in `V \ (U'∪N'')`" as a conjunct | stronger | true by definition of `splitDel` |
| 4 | `TauFactAStatement`: `U', N'' ⊆ V(H)` | stronger (implicit) | true |
| 5 | `L14OVStatement`: `2 ≤ |H_a|`; `OVStatement`: `Σ dup = Δ`; `GCStatement`: `V(Y) = Z^0`, `E(X^0) ⊆ E_r(Y)` | stronger (explicit implicit conjuncts) | true |
| 6 | `GCThetaStatement`, `TowerCStatement`: `Gamma1core` instead of Γ1–Γ4 | stronger (as an *input*, riskier) | true: (c) needs only `Λ_r ≤ 2λ_r` (from `M_r ≤ d_r²`, which holds for `d_r ≥ D_* ≥ 2^{2^{256}}`), `s_r ≤ 2Λ_r^{σ}` (`Λ_r ≥ 40`), `P_r ≥ λ_r^{103}`, `|Z^0| ≥ P_r` (definition of a pre-part) and `λ_r^{1/2} > 2^{111}` (Γ1(a) at `μ = log λ_r ≥ log log D_*`: `λ_r ≥ 2^{256}`); this is the TeX proof of (c), l.1249–1257, and it uses Γ1(a) only |
| 7 | `IsTauRun` without `s < τ`; `IsTauSplitTree` without `s_ν ≥ 0` | more trees ⇒ stronger statements | fine (edge cases above) |
| 8 | `SEPMonoStatement` without `WF`; `ThinCutEdgeStatement` without `u ∈ V(H_0)`; `ELStatement` for all `l > r`; `L14TermStatement` (T1) for all `K` with `2 ≤ |K| ≤ n_0` | stronger | true (all proved) |
| 9 | `ε` fixed to `epsC` | as the TeX ("Throughout, `ε = 2^{-5}`") | fine |
| 10 | `n_0 ≥ 1` in `OVStatement`, `0 ≤ s` in the `τ`-rule statements, `D_* ≤ d_1` in `TowerCStatement` | kept although unused (`Valid` gives `D_* ≤ d_1` when `R ≥ 1`, and `Icc 1 0 = ∅`) | literal to the TeX; harmless |

## 2. Vacuity

- **Consistency of the hypotheses.** `EGTest/ProbeP3A.lean` (re-run by me: `LEAN_NUM_THREADS=2
  scripts/check.sh EGTest/ProbeP3A.lean 1200` → rc=0, 0 errors, 0 sorry-warnings) exhibits: the
  `τ`-rule context (`H2`, witness `({0,1}, ∅)`, `s = 1 < τ = 512`); a `τ`-run at the smallest
  allowed `τ = 512 = 128·1·log²4` with three splits and two deleted edges (`L14*` hypotheses);
  `IsTauSplitTree`; `OVHyp ε 1` on a two-split `s = 0` recursion with `0 < c`, `3.42cε < 1`,
  `n_0 ≥ 1`; a valid run on `K3` with three light pre-parts (`GC*`, `EL`); `Gamma1core ∧ Valid`
  jointly (the run without rounds); a non-idle `τ`-split (`H_out = {0}`, deleted edge `14`,
  `Dup = {0}`) on which the thin-cut bound is attained (`1 = ⌈2⌉ − 1`); a round-local GC-part
  with every (iii) conclusion checked at the round level.
- **Trivial conclusions.** None where the TeX has content. The near-definitional items are
  exactly what the TeX calls definitional or arithmetic: `GCDefStatement` is a tautology of
  `isLight = L1 ∧ L2 ∧ GC` (I re-proved it in three lines, scratch (ii); the TeX's (i) is "the
  order of definitions"); `GCStatement` (ii) is `isGC` unfolded; the nine equalities of
  `TauFactCStatement` follow from `N_0 = N`; the second conjunct of `SEPiStatement` ("which
  contains `x` and `y`") follows from `edge_verts`; the second inequality of OV (a) is the TeX's
  numeric relaxation `1 + 1/c_OV ≤ 3.42`. The literal lem14tau (c) is refutable at `τ = 0`
  (§6), so the hypotheses do constrain the conclusion.
- **Quantitative content.** No toy instance has `N''_a ≠ ∅` under `OVHyp`/`IsTauRun` (it needs
  `|U'| ≳ 32 log²m`), so OV (a)/(b) and 14^τ (b) are verified by proof alone (`EG.ov`,
  `EG.l14OV`, kernel-checked, 0 `sorry`). Not a defect (carried audit note).
- **Independent scratch checks** (`P3ARev2c.lean`, rc=0): (i) `example : XStatement := EG.x`
  for all 25 statements; (ii) `#print axioms`: `[propext, Classical.choice, Quot.sound]` for
  `l14Thin`, `gc`, `ov`, `edgeLaminarity`; `sorryAx` only in `towerC` and `gcTheta`; (iii) a
  witness forces `0 ≤ s`; (iv) the numeric relations of §1.2; (v) `Gamma1core D → 2^{2^{256}} ≤
  D`; (vi) my own re-derivation of the L14-C-TAU0 witness (§6).

## 3. Declared inputs

| Input | Used by the manuscript proof? | Stated as in the TeX? | Probe node in disguise? | Status |
|---|---|---|---|---|
| `TowerCStatement` ([s2:lemTower] (c)) | yes: lemGC (iv) "is Lemma lemTower (c)" (s2.tex l.1317) | yes (full (c); `Gamma1core` for the standing assumption, stronger and true, §1.3 item 6; `D_* ≤ d_1` kept) | no: lemTower is a tower-unit node; its proof needs (b) (`Λ_r ≤ 2λ_r`, `s_r ≤ 2Λ_r^σ` via propDegRec) and Γ1(a), none of which is in P3A's probe list | stub `EG.towerC`, the only `sorry`; used only by `EG.gcTheta` |
| `ELStatement` ([s2:lemEL]) | cited by lemGC (iii) | yes | no | **proved** (`EG.edgeLaminarity`, 0 `sorry`); `GCStatement` (iii)'s `G_{r+1}` clause is proved directly from (R5)(3) |

- Nothing hidden: the probe list (defTauRules facts, SEP, thin cut, OV (sharp), lem14tau,
  lemGC) contains no part of lemTower, and lemGC (iv) has no content beyond (c). That the
  probe's (iv) is therefore a one-line corollary is a consequence of the manuscript's own
  structure, not of the Spec design.
- Correctly not used: B-M Lemma 25 (`EG.bmLemma25`), Cap (`EG/Proof/HB/Cap.lean`) and Lemma 15:
  lem14tau takes `τ ≥ 128 s log² n_0` as a hypothesis and `Round.Valid` does not require it
  (lemCap (ii) enters only through propExists, outside P3A). s1:citDef11 is the Def
  `IsExpander`; s1:citLem14 is attribution (s2 re-proves the argument).
- The stub has the prescribed form (`/-- [DECLARED INPUT] [s2:lemTower] (c) … -/ theorem towerC :
  EG.Spec.TowerCStatement := by sorry`). The sibling input `TowerBRoundStatement`
  (`EG/Spec/HB/TowerB.lean`, unit P4A) uses the same `Gamma1core` convention and refers to
  `TowerCStatement` instead of restating (c), as required.

## 4. Hygiene

- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- `sorry` in the unit's Spec/Proof/Lib files: only `EG/Proof/HB/TowerC.lean:24` (the stub); the
  other occurrences of the word are in docstrings.
- Module headers: Specs `module` + `public import` + `@[expose] public section`, namespace
  `EG.Spec`, every statement `∀ (V : Type u) [DecidableEq V]`, docstrings starting with the
  manuscript label and quoting the TeX; Proof files `public section`, namespace `EG`.
- CONVENTIONS: rounds bounded by `Finset.Icc 1 run.R`; per-address wrappers read only at
  `a ∈ run.prePartAddrs G r`; `run.tauRun` never read by a Spec; `Gamma1core`, `epsC`, `sigmaC`
  named as prescribed; no new Defs (nothing under `EG/Defs/Probe/` for P3A).
- Freeze: `git diff HEAD -- EG/Spec/HB EG/Defs/HB EG/Proof/HB` is empty (the unit's files are
  byte-identical to HEAD `ed552cf`). The only working-tree change under `EG/` is
  `EG/Defs/Gamma/Full.lean` (another unit; not P3A). The 25 P3A statements are not yet in
  `LOCK.json` (0 matches), so the freeze is enforced by the edit-deny rule only (integrator
  note, carried from the audit).
- Build state: oleans of the 8 Spec and 8 Proof modules exist and are newer than their sources;
  the scratch file importing all eight Proof modules elaborates (so the modules are consistent
  with each other); the test file type-checks (above).
- Root files `EG.lean`/`EGTest.lean` untouched by the unit; the imports to add are listed in
  `P3A.md`.

## 5. Issues

- **m1 (minor, process).** `TowerCStatement` is the unit's only `sorry`. It is legitimate as an
  input (lemGC (iv) is by the TeX "Lemma lemTower (c)"), but the orchestrator should confirm
  that the s2 tower unit owns `EG.towerC`, and the future Tower Spec must import
  `EG/Spec/HB/TowerC.lean` rather than restate (c) (the docstrings of `TowerC.lean`,
  `TowerA.lean`, `TowerB.lean`, `TowerBLate.lean` already say so). Not a Spec defect.
- **c1 (cosmetic, stale documentation in a locked file).** The module docstring of
  `EG/Spec/HB/EL.lean` still calls `ELStatement` "a DECLARED INPUT of the probe … the stub is
  `EG.edgeLaminarity`". It is proved. For the integrator's next documentation pass on locked
  files (`EG/Proof/HB/EL.lean` already records the change).
- **c2 (cosmetic).** `GCDefStatement` is a tautology of the definition of `isLight` (three-line
  proof). This is faithful to the TeX, whose (i) is definitional, and the design note says so;
  I record it so that nobody counts it as content when tallying "proved nodes".
- **c3 (cosmetic, test coverage; carried).** No instance exercises `N''_a ≠ ∅` under
  `OVHyp`/`IsTauRun`; the quantitative content of OV (a)/(b) and 14^τ (b) is checked by proof
  alone (§2). Acceptable.
- **c4 (cosmetic, lock).** The P3A statements are `PENDING` (not in `LOCK.json`). Once the
  orchestrator locks them, `scripts/lock.py check` will also guard the Defs they depend on.

## 6. Math findings (manuscript)

**L14-C-TAU0 — class T1, confirmed independently (my own Lean witness, scratch (vi)).**
s2:lem14tau assumes `s ≥ 1` and `τ ≥ 128 s log² n_0`, which at `n_0 = 1` is `τ ≥ 0`, so `τ = 0`
is in scope. Take `H_0` = one vertex, `s = 1`, `τ = 0`. The one-vertex graph is an
`(ε,1)`-expander (no `U` with `1 ≤ |U| ≤ 2/3`), so the `τ`-run is the single leaf; nothing is
deleted; (c) claims `0 ≤ ⌈0⌉ − 1 = −1` (and "`= τ − 1` for integer `τ`" claims `0 ≤ −1`). The
proof's "If `n_0 = 1` the root is an `(ε,s)`-expander and everything is trivial" is right for
(a), (b), (d) and wrong for (c). In Lean the same happens at `n_0 = 0` (`logb 2 0 = 0`). The
statement is true for every `τ > 0` (at `n_0 ≤ 1` the count is `0 ≤ ⌈τ⌉ − 1`), Lemma lemThinCut
itself assumes `τ > 0`, and every application has `τ = τ_l = ⌈128 s_l Λ_l²⌉ ≥ 128`. Repair
adopted in `L14ThinStatement`: `0 < τ` on the two bounds; minimal. Manuscript action: write
"(c) for `τ > 0`" or "Let `n_0 ≥ 2`" in the lemma. No downstream impact.

**No other finding.** Re-derived in this round from the TeX: the witness Fact; Facts (a)–(c)
and (eqSplit); SEP (0)–(iii) (in (iii), the deletion node of `hu'` is an ancestor of `Leaf_u`
containing `h` whose path child does not contain `h`, hence it is the deepest one, `ν*`); thin
cut cases A/B and `deg < τ ⇒ deg ≤ ⌈τ⌉ − 1`; OV (a) (charge `cε/log²|ν|` per `(ν,u)`, `u ∈ U'_ν`,
mapped to a leaf copy below `ν_1`; consecutive charging ancestors satisfy `|ν^{(i)}| ≤
|ν^{(i+1)}_1| ≤ (3/4)|ν^{(i+1)}|`; sum ≤ `1/log²M + 1/(c_OV log M)`), (b) (leaves of the subtree
`𝒞_v`), (c) (`Δ_{≥2} = Σ_ν|N''_ν|` since all internal nodes have `m ≥ 2`), the instance
(`|U∪N| < (33/32)(2/3)m ≤ 3m/4`); lem14tau's counting at one split (`Σ_{v∈U} deg_{F_0}(v) =
|F_0|`, `|F_1| = |F_0| − a` because every `F_0` edge has exactly one end in `U`, hence at most
one in `H_out`; `τ(|H_out| + |H_in|) ≤ |F_0|`; `|N''| = |N| + |H_out| + |H_in|` disjointly;
`(1 + 1.25/32)(2/3) ≈ 0.693 ≤ 0.698`), termination, the induction inequalities (8)
(`6ε/log m ≤ 3/16 < 3/5`) and (9) (`7L² − 3.6L − 3.2 ≥ 0` for `L ≥ 1`, `3ε < 1/10`), (b)'s
constants; lemGC (ii)–(iv) and lemEL; lemTower (c) under Γ1(a) only. Two observations, not
findings: lem14tau (a)'s `|F_0|/τ` is meaningless at `τ = 0`, but no split exists then; lemGC
(iii)'s citation of Lemma EL is correct but unnecessary (the clause follows from (R5)(3)
directly, as the Lean proof does).

## 7. Answers to the author's open questions

1. L14-C-TAU0: accept the repair `0 < τ` on the two bounds of (c) and send the T1 note to the
   manuscript.
2. Declared inputs: EL is settled (proved). TowerC stays an input owned by the tower unit; the
   future Tower Spec imports `EG/Spec/HB/TowerC.lean` (m1).
3. Recording lemGC (i)'s first clause as a Defs design constraint is acceptable (re-verified in
   `Round.lean`).
4. No galactic GC-part construction is needed; the round-local `GCPartTest` suffices.
