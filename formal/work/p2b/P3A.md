# P2b probe unit P3A (probe P-3, part 1), stage 1: statements

Chain: τ-rules → SEP → thin cut → OV (sharp) → Lemma 14^τ → rule GC (TRIAGE §4 row P-3, first half).
Manuscript: `proofs/manuscript/s2.tex` v6.1 (a CANDIDATE proof, AI-reviewed only).
Blueprints: `work/p2/blueprint_s2a.md` (defWitness, defTauRules, lemSEP, lemThinCut, lemOVgeneric, lem14tau) and `work/p2/blueprint_s2b.md` (lemGC, lemEL, lemTower). Data model: `work/p2d/hb.md`.

## Current status (2026-09-30, after the Spec fix round 2 re-dispatch; unchanged since the proof-stage fix round 2)

- Every probe node of P3A is proved (0 `sorry`), and so is Lemma EL (`EG.edgeLaminarity`). The only `sorry` of the unit is the declared-input stub `EG.towerC` ([s2:lemTower] (c), owner: s2 tower unit), used only by `EG.gcTheta`.
- The "Status (stage 1)" bullets below are historical; see "Summary of proof round 1" and the proof-stage fix rounds at the end.

## Status (stage 1)

- Every file compiles (`scripts/check.sh`; `lake build` of all the modules below).
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`scripts/Axioms.lean --prefix EG` on `EG.Proof.HB.{GC,TauRules,EL,TowerC}`): 736 constants, 0 violations. `sorryAx` appears only in the two declared-input stubs `EG.edgeLaminarity` and `EG.towerC`.
- Proved already (trivial): `EG.witnessExists : WitnessExistsStatement` and `EG.gcDef : GCDefStatement`.
- Everything else is stage 2. No proof file of a probe node contains `sorry`.
- One T1 finding: **L14-C-TAU0** (see "Math findings"). `L14ThinStatement` carries the minimal repair, and `EGTest.ProbeP3A.lem14tau_c_literal_false` is a Lean witness that the literal bound is false.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Spec/HB/TauRules.lean` | `EG.Spec.HB.TauRules` | `WitnessExistsStatement`, `WitnessFactStatement`, `TauEqSplitStatement`, `TauFactAStatement`, `TauFactBStatement`, `TauFactCStatement` |
| `EG/Spec/HB/SEP.lean` | `EG.Spec.HB.SEP` | `SEP0Statement`, `SEPMonoStatement`, `SEPiStatement`, `SEPiiStatement`, `SEPiiiStatement` |
| `EG/Spec/HB/ThinCut.lean` | `EG.Spec.HB.ThinCut` | `ThinCutStatement`, `ThinCutEdgeStatement` |
| `EG/Spec/HB/Overlap.lean` | `EG.Spec.HB.Overlap` | `OVStatement` (sharp (a), (b), (c)), `OVInstanceStatement` |
| `EG/Spec/HB/Lemma14Tau.lean` | `EG.Spec.HB.Lemma14Tau` | `L14SplitStatement`, `L14TermStatement`, `L14GlobalStatement`, `L14OVStatement`, `L14ThinStatement` |
| `EG/Spec/HB/GC.lean` | `EG.Spec.HB.GC` | `GCDefStatement`, `GCStatement`, `GCThetaStatement` |
| `EG/Spec/HB/EL.lean` | `EG.Spec.HB.EL` | `ELStatement` (declared input) |
| `EG/Spec/HB/TowerC.lean` | `EG.Spec.HB.TowerC` | `TowerCStatement` (declared input) |
| `EG/Proof/HB/EL.lean` | `EG.Proof.HB.EL` | stub `EG.edgeLaminarity` (`sorry`, DECLARED INPUT) |
| `EG/Proof/HB/TowerC.lean` | `EG.Proof.HB.TowerC` | stub `EG.towerC` (`sorry`, DECLARED INPUT) |
| `EG/Proof/HB/TauRules.lean` | `EG.Proof.HB.TauRules` | `EG.witnessExists` (proved) |
| `EG/Proof/HB/GC.lean` | `EG.Proof.HB.GC` | `EG.gcDef` (proved) |
| `EGTest/ProbeP3A.lean` | `EGTest.ProbeP3A` | non-vacuity checks; Lean witness of L14-C-TAU0 |

Statements are in namespace `EG.Spec` and proofs in namespace `EG`. Every statement quantifies `∀ (V : Type u) [DecidableEq V]`.

Root imports for the orchestrator to add (I did not edit `EG.lean` or `EGTest.lean`):
- to `EG`: the eight Spec modules and the four Proof modules above;
- to `EGTest`: `EGTest.ProbeP3A`.

No new Defs file (nothing under `EG/Defs/Probe/`).

## Nodes: label → Lean names

| Label | Role | Statement(s) | Planned proof name(s) (stage 2) |
|---|---|---|---|
| s2:defWitness (Fact, first sentences) | probe (added: defTauRules (a) uses `F_0 ⊆ F`) | `WitnessExistsStatement`, `WitnessFactStatement` | `EG.witnessExists` (**done**), `EG.witnessFact` |
| s2:defTauRules, s2:eqSplit | probe | `TauEqSplitStatement`, `TauFactAStatement`, `TauFactBStatement`, `TauFactCStatement` | `EG.tauEqSplit`, `EG.tauFactA/B/C` |
| s2:lemSEP | probe | `SEP0Statement`, `SEPMonoStatement` ((0′), implicit), `SEPiStatement`, `SEPiiStatement`, `SEPiiiStatement` | `EG.sep0`, `EG.sepMono`, `EG.sepI`, `EG.sepII`, `EG.sepIII` |
| s2:lemThinCut | probe | `ThinCutStatement`, `ThinCutEdgeStatement` | `EG.thinCut`, `EG.thinCutEdge` |
| s2:lemOVgeneric | probe (sharp form) | `OVStatement`, `OVInstanceStatement` | `EG.ov`, `EG.ovInstance` |
| s2:lem14tau | probe | `L14SplitStatement`, `L14TermStatement`, `L14GlobalStatement`, `L14OVStatement`, `L14ThinStatement` | `EG.l14Split`, `EG.l14Term`, `EG.l14Global`, `EG.l14OV`, `EG.l14Thin` |
| s2:lemGC | probe | `GCDefStatement` (tautological in Lean: (i) is definitional in the TeX, see below), `GCStatement`, `GCThetaStatement` | `EG.gcDef` (**done**; not counted as content), `EG.gc`, `EG.gcTheta` |
| s2:lemEL | declared input in stage 1; **proved** since the proof-stage fix round 1 | `ELStatement` | `EG.edgeLaminarity` (0 `sorry`) |
| s2:lemTower (c) | **declared input** | `TowerCStatement` | stub `EG.towerC` |

Planned stage-2 Lib files:
- `EG/Lib/HB/Split.lean`: the generic split partition, which is the content of Fact (b) for any disjoint `U', N'' ⊆ V(H)`. SEP (0) and defTauRules (b) both reduce to it.
- `EG/Lib/HB/Address.lean`: the child laws `graphAtD (a ++ [b])` at internal nodes, prefix induction and `subtreeAt`.
- `EG/Lib/HB/OVPotential.lean`: the OV potential lemma.
- `EG/Lib/HB/Numeric.lean`: `cOV ≥ 17/41` via `2^65 ≥ 3^41`, and the small constants of 14^τ.

## Declared inputs, with justification

1. **[s2:lemEL] `ELStatement`**, stub `EG.edgeLaminarity`.
   - Cited by [s2:lemGC] (iii): "By Lemma EL … no edge of `G_{r+1}` has both ends in `Y^0`".
   - It is not a node of probe P-3. It is a short (R5) argument (blueprint s2b, about 80 lines) that belongs to the s2 structure unit, together with propStructure.
   - It could be discharged cheaply in stage 2 if the orchestrator wants P3A to own it.
   - Statement: for every valid run, every ancestor `Y` and every `l > r(Y)`, `E(G_l) ∩ V(Y)^{(2)} = ∅`.
2. **[s2:lemTower] (c) `TowerCStatement`**, stub `EG.towerC`.
   - [s2:lemGC] (iv) is literally "is Lemma [s2:lemTower](c)".
   - Its proof needs the Γ1 transfer lemmas, `Λ_r ≥ λ_r`, `s_r ≤ P_r` and the (R2) parameter algebra (blueprint s2b, "(c) ~80 lines" on top of the (b) infrastructure). These belong to the tower unit, not to the split-tree chain.
   - The full (c) is stated, not only the `θ > τ` clause, so that the future `Tower` Spec imports this file instead of restating (c).

Nothing is cited from s1 that needs a statement:
- s1:citDef11 is the Def `IsExpander`.
- s1:citLem14 is attribution only (blueprint deps_notes).
- B-M Lemma 25, Cap and Lemma 15 are not used by this chain. lemCap (ii) enters only through propExists, which is not in P3A.

## Definitions used (all locked; no new Defs)

- `EG/Defs/HB/Witness.lean`:
  - `IsWitness`, `witN`, `witF0`;
  - the generic split `splitFst`, `splitSnd`, `splitDel`;
  - the τ-rules `tauHout`, `tauU1`, `tauN1`, `tauF1`, `tauHin`, `tauN2`, `tauF2`, and the literal children `tauG1`, `tauG2`.
- `EG/Defs/HB/SplitTree.lean`:
  - `Addr`, `STree`, `labelAt`, `labelU`, `labelN`, `nodeAddrs`, `leafAddrs`, `internalAddrs`, `graphAtD`, `delAt`;
  - `WF`, `leafMass`, `dup`, `deleted`, `DeltaGe`, `dupGe`, `OVHyp`;
  - `IsS0Rec`, `IsTauSplitTree`, `IsTauRun`, `cOV`.
- `EG/Defs/HB/Round.lean` and `Run.lean`:
  - `Run.Valid`, `R`, `graph`, `graph'`, `d`, `lam`, `Lam`, `P`, `tau`, `thetaGC`;
  - `prePartAddrs`, `X0`, `Z0`, `guests`, `D`, `DupStar`, `isL1`, `isL2`, `isGC`, `isLight`, `isGCPart`, `Std`, `assign`, `E`;
  - `ancestors`, `ancVerts`.
- `EG/Defs/Constants.lean`: `epsC`, `sigmaC`.
- `EG/Defs/Gamma/Core.lean`: `Gamma1core`.
- `EG/Defs/Log.lean` is **not** needed by this half of P-3. The log* API is needed for the tower facts and CONC-L (part 2 of P-3).

No existing definition looks wrong for this chain.

Checked specifically:
- `OVHyp` matches the three node conditions literally.
- `IsTauSplitTree` matches the thin-cut hypothesis literally.
- `IsTauRun` has the stop rule in both directions.
- `thetaGC` is a natural-number ceiling.
- `Round.assign` step (1) is well defined without the edge-disjointness.

## Back-translation of every statement (plain mathematics next to the TeX)

Notation: `H` is a finite simple graph, `m = |V(H)|` and `ε = 2^{-5}`. A tree `t` with `t.WF H` is a split recursion on `H` whose nodes are addresses. `H_a` is the graph at `a`, `a0`/`a1` are its children, `U'_a`/`N''_a` are its labels, and `F''_a = delAt`.

### defWitness

**`WitnessExistsStatement`**
- Lean: for `s ≥ 0`, if `H` is not an `(ε,s)`-expander then `m ≥ 2` and some `(U,F)` is a witness with parameter `s`.
- TeX: "Then `m ≥ 2` … Since `H` is not an `(ε,s)`-expander, a witness exists."

**`WitnessFactStatement`**
- Lean: for `s ≥ 0`, a witness `(U,F)` and `N = Nbr_{H−F}(U)`:
  - `F_0 := E_H(U, V∖(U∪N)) ⊆ F`;
  - `Nbr_{H−F_0}(U) = N`;
  - `(U, F_0)` is a witness.
- TeX: "*Fact.* `F_0 ⊆ F` and `Nbr_{H−F_0}(U) = N`. In particular `(U,F_0)` is again a witness at `H`, with the same set `N`."

### defTauRules and eqSplit

All five statements share one context: `s ≥ 0`, a witness `(U,F)`, `s < τ`, `N = Nbr_{H−F}(U)`.

**`TauEqSplitStatement`**
- Lean:
  - every edge of `F''` is `xy` with `x ∈ U'` and `y ∈ V(H)∖(U'∪N'')` (the premise; added in fix round 1, c1), avoids `(U'∪N'')^{(2)}` and meets `U'`;
  - the literal children `G_1 = H[U'∪N''] − F''` and `G_2 = H − U' − E(G_1) − F''` equal `H[U'∪N'']` and `H[V∖U'] − E(H[N''])` (as graphs).
- TeX: the (eqSplit) paragraph.

**`TauFactAStatement`**
- Lean: `U' ∩ N'' = ∅`; `U' ∪ N' = U ∪ N`; `F'' ⊆ F_1 ⊆ F_0 ⊆ F`; plus `U' ⊆ V(H)` and `N'' ⊆ V(H)`.
- TeX: Fact (a). The last two facts are implicit in the TeX (blueprint TAU-IMPLICIT-SUBSETS).

**`TauFactBStatement`**
- Lean:
  - `E(G_1)`, `E(G_2)` and `F''` are pairwise disjoint with union `E(H)`;
  - `V(G_1) = U' ∪ N''` and `V(G_2) = V ∖ U'`;
  - vertices of `U'` lie in `G_1` only, vertices of `N''` lie in both, and vertices of `V∖(U'∪N'')` lie in `G_2` only.
- TeX: Fact (b).

**`TauFactCStatement`**
- Lean: with `N₀ = Nbr_{H−F_0}(U)`:
  - `(U,F_0)` is a witness and `N₀ = N`;
  - all nine objects (`H_out`, `U'`, `N'`, `F_1`, `H_in`, `N''`, `F''`, `G_1`, `G_2`) computed from `(U,N₀)` equal those computed from `(U,N)`.
- TeX: Fact (c) "every witness `(U,F)` yields the same split as its minimal part `(U,F_0)`". The first sentence of (c) is definitional.

### lemSEP

**`SEP0Statement`**
- Lean: at every internal `a`:
  - `E(H_a) = E(H_{a0}) ⊔ E(H_{a1}) ⊔ F''_a` (pairwise disjoint);
  - vertices of `U'_a` go only to `a0`, vertices of `N''_a` go to both, and other vertices of `H_a` go only to `a1`;
  - `|H_{a0}| + |H_{a1}| = |H_a| + |N''_a|`.

  Moreover:
  - every vertex of a node lies in a leaf below it;
  - `Σ_{leaves} |H_L| = |H| + Σ_{internal} |N''_a|`.
- TeX: SEP (0).

**`SEPMonoStatement`**
- Lean: if `a` is a prefix of a node address `b`, then `H_b ≤ H_a` (a subgraph).
- TeX: (0′). This is implicit: "Every edge of a child is an edge of its parent", "vertex sets shrink downwards".

**`SEPiStatement`**
- Lean: for `e ∈ E(H)`:
  - `#{leaves L : e ∈ E(H_L)} + #{internal a : e ∈ F''_a} = 1`;
  - a leaf containing `e` contains both ends;
  - if `e ∈ F''_a`, then:
    - `e` is an edge of every prefix of `a`;
    - `e` is an edge of neither child;
    - `e = xy` with `x ∈ U'_a` and `y ∈ V(H_a)∖(U'_a∪N''_a)`;
    - `x` lies only in `a0` and `y` lies only in `a1`.
- TeX: SEP (i).

**`SEPiiStatement`**
- Lean: for `u ∈ V(H)∖Dup` there is a leaf `L ∋ u`, unique among leaves, such that:
  - the nodes containing `u` are exactly the prefixes of `L`;
  - `u ∉ N''_a` for every internal prefix `a` of `L`.
- TeX: SEP (ii).

**`SEPiiiStatement`**
- Lean: take `u ∈ V(H)∖Dup` in leaf `L`, and `h ∈ V(H)∖V(H_L)`. Let `ν*` be a longest prefix of `L` with `h ∈ V(H_{ν*})`. Then every deleted edge `hu'` with `u' ∈ V(H_L)∖Dup` lies in `F''_{ν*}`.
- TeX: SEP (iii).

### lemThinCut

Both statements share one context: `τ > 0` and `t.IsTauSplitTree ε τ H`, meaning every split comes from the τ-rules of some witness with parameter `s_a < τ`.

**`ThinCutStatement`**
- Lean: for every leaf `L` and vertex `h`, let `#` be the number of deleted edges of the form `hu` with `u ∈ V(H_L)∖Dup`. Then:
  - `# ≤ ⌈τ⌉ − 1` (in ℤ);
  - if `τ = k ∈ ℕ` then `# ≤ k − 1`;
  - `# = 0` if `h ∈ V(H_L)`.
- TeX: the main display, "which is `τ−1` when `τ` is an integer", "this number is `0` if `h ∈ V(Leaf)`".

**`ThinCutEdgeStatement`**
- Lean: if `u ∉ Dup` and `e ∈ E(H)` meets `u`, then either `e` is deleted, or `e ∈ E(H_L)` for a leaf `L ∋ u` that is the only leaf containing `u`.
- TeX: "Moreover, if `u ∉ Dup` then every edge at `u` is either deleted or an edge of the unique leaf containing `u`".

### lemOVgeneric

**`OVStatement`**
- Hypotheses: `c > 0`, `3.42cε < 1`, `n_0 ≥ 1`, and `OVHyp ε c` (split recursion; at every internal node `m ≥ 2`, `|ν_1| ≤ 3m/4` and `|N''| ≤ cε|U'|/log²m`).
- Conclusions: for every real `M ≥ 2`:
  - (a) `Δ_{≥M} ≤ cε(1/log²M + 1/(c_OV log M))S` and `cε(1/log²M + 1/(c_OV log M))S ≤ 3.42cεS/log M`;
  - `Σ_{v∈V(H)} dup_{≥M}(v) = Δ_{≥M}`;
  - (b) `#{leaves L : |L| ≥ M, v ∈ L} ≤ 1 + dup_{≥M}(v)` for every `v`;
  - `Σ_{|L|≥M} |L| ≤ |⋃_{|L|≥M} V(L)| + Δ_{≥M}`.

  Also (c) `S ≤ n_0/(1 − 3.42cε)`.
- TeX: (a), the parenthetical identity, (b) with its consequence (written additively), and (c).

**`OVInstanceStatement`**
- Hypothesis: `t` is an `s = 0` recursion.
- At every internal `a`, with a witness `(U,F)` of parameter 0 whose label is `(U, N = Nbr_{H_a}(U))`:
  - `F = ∅` and `Nbr_{H_a−F}(U) = N`;
  - `H_{a0} = H_a[U∪N]`;
  - `H_{a1} = H_a∖U − E(H_a[U∪N])`, which equals `H_a[V∖U] − E(H_a[N])`;
  - `F''_a = ∅`;
  - for every `τ > 0`: `F_0 = ∅`, `H_out = H_in = ∅`, `U' = U` and `N'' = N`.
- Globally:
  - `t` is a τ-rule split tree for every `τ > 0`;
  - `OVHyp ε 1` holds;
  - `S ≤ n_0/(1 − 3.42ε) ≤ 1.12 n_0`.
- TeX: the instance paragraph.

### lem14tau

All five statements share one context: `s ∈ ℕ` with `s ≥ 1`, `τ ≥ 128 s log² n_0`, and `t.IsTauRun ε s τ H`.

**`L14SplitStatement`**
- Lean: at every internal `a` with `K = H_a` and `m = |K|`, and for every witness `(U,F)` with parameter `s` whose τ-rules give the label of `a`:
  - `|H_out| + |H_in| ≤ |F_0|/τ ≤ s|U|/τ ≤ |U|/(128 log² m)`;
  - `|N''| < 1.25ε|U|/log²m < 1.5ε|U|/log²m`;
  - `|U'| ≥ (127/128)|U|` and `|U'| > 0`;
  - `U ⊆ U' ∪ N''`;
  - `|U'∪N''| ≤ 0.698m < 3m/4`;
  - `m − |U'| < m`.
- TeX: (a), first display and sentence.

**`L14TermStatement`**
- (T1): every τ-rule split (parameter `s`) of a graph `K` with `2 ≤ |K| ≤ n_0` has children of sizes in `[1, |K|)`.
- (T2): for every rule `W` that picks a witness with parameter `s` at each non-expander (possibly depending on the address), there is a τ-run whose labels are the τ-rule sets of `W`'s witnesses.
- TeX: "The recursion terminates", for every choice of witnesses. The proof's "Both children of every split have fewer vertices than their parent, so every root-to-node path has at most `n_0` nodes, and the binary tree is finite" is the same claim.

**`L14GlobalStatement`**
- Lean:
  - `|⋃F''| ≤ 4 s n_0 log n_0`;
  - every edge is in exactly one leaf or deleted at exactly one node;
  - every leaf graph is an `(ε,s)`-expander;
  - `S ≤ 2n_0 − 2n_0/(2 + log n_0)`.
- TeX: the rest of (a). "It is a split recursion" is `WF`, which is part of `IsTauRun`.

**`L14OVStatement`**
- Lean: at every internal `a`:
  - `|N''_a| ≤ 1.6ε|U'_a|/log²|H_a|`;
  - `U'_a` goes only to `a0`;
  - `|H_{a0}| ≤ 3|H_a|/4`;
  - `|H_a| ≥ 2`.

  Also:
  - `OVHyp ε 1.6` holds;
  - `S ≤ n_0/(1 − 5.5ε) ≤ 1.21 n_0`;
  - `Δ_{≥M} ≤ 5.46εS/log M` for every `M ≥ 2`.
- TeX: (b).

**`L14ThinStatement`**
- Lean:
  - (c) for every leaf `L` and vertex `h`:
    - if `τ > 0` then `# ≤ ⌈τ⌉ − 1`, and `# ≤ k − 1` when `τ = k ∈ ℕ`;
    - `# = 0` if `h ∈ V(H_L)`.
  - (d) for `u ∉ Dup`, every edge at `u` is deleted or lies in the unique leaf containing `u`.
- TeX: (c), (d). **The hypothesis `τ > 0` on the two bounds is the T1 repair L14-C-TAU0.**

### lemGC

**`GCDefStatement`**
- Lean: for a valid run, `r ∈ [1,R]` and a pre-part `a`:
  - if (L1) and (L2) hold, then `a` is light iff (GC) holds;
  - if (L1) or (L2) fails, then `a` is not light.
- Tautological in Lean (fix round 2 re-dispatch, review c2): `isLight = L1 ∧ L2 ∧ GC` by definition, so the proof is three lines; this is faithful, since the TeX's (i) is definitional ("the order of definitions"). Do not count `EG.gcDef` as content when tallying proved nodes.
- TeX: (i) "(GC) only decides whether a pre-part satisfying (L1) and (L2) is light or standalone". The first clause of (i) (pre-parts, `X^0`, `Dup*`, `D`, `home` and `S_Z` are defined independently of (GC)) is definitional: the Defs `Round.prePartAddrs`, `X0`, `DupStar`, `D`, `home` and `guests` do not mention `isGC`/`isLight` (checked by reading `EG/Defs/HB/Round.lean`).

**`GCStatement`**
- Context: a valid run and `r ∈ [1,R]`.
- (ii): for a light pre-part `a` and a guest `x ∈ S_a`, `e_{X^0_a}({x}, Z^0_a∖S_a) < θ^GC_r(Z^0_a)`.
- (iii): for a GC-part `a`:
  - `a ∈ Std_r` and `V(Y) = Z^0_a`;
  - every edge of `G'_r` inside `Z^0_a` is assigned (`assign ≠ none`);
  - `E(X^0_a) ⊆ E_r(a)`;
  - no edge of `G_{r+1}` lies inside `Z^0_a`;
  - `S_a ⊆ D_r ⊆ Dup*_r`.
- TeX: (ii), (iii), including the parenthetical "(the edges of `X^0_Y` … by (R5)(1))".

**`GCThetaStatement`**
- Lean: under `Gamma1core D_*`, for a valid run, `τ_r < θ^GC_r(Z^0_a)` for every round-`r` pre-part `a`.
- TeX: (iv).

### Declared inputs

**`ELStatement`**
- Lean: for a valid run, an ancestor `Y` and any `l > r(Y)`, no edge of `G_l` has both ends in `V(Y)`.
- TeX: Lemma EL.

**`TowerCStatement`**
- Lean: under `Gamma1core D_*`, for a valid run with `d_1 ≥ D_*` and `r ∈ [1,R]`:
  - `τ_r ≤ 257Λ_r^{102} ≤ 2^{111}λ_r^{102}`;
  - `τ_r/P_r ≤ 2^{111}/λ_r`;
  - `P_r λ_r^{−1/2} ≤ θ^GC_r(Z^0)` and `τ_r < P_r λ_r^{−1/2}` for every round-`r` pre-part.
- TeX: lemTower (c) (`σ + 2 = 102`, `σ + 11 = 111`).

## Deviations from the literal TeX (all to be checked by the statement reviewer)

1. **Repair (T1): `0 < τ` on the two bounds of `L14ThinStatement`.** See L14-C-TAU0.
2. **Stronger than the TeX (true, harmless):**
   - `SEPMonoStatement` has no `WF` hypothesis.
   - `ThinCutEdgeStatement` does not assume `u ∈ V(H_0)` (it follows from `u ∈ e ∈ E(H_0)`).
   - `ELStatement` quantifies over all `l > r`, including `l > R+1`, where `G_l` is stationary.
   - `L14TermStatement` (T2) quantifies over every address-dependent witness rule.
3. **Added implicit conjuncts:**
   - `U' ⊆ V(H)` and `N'' ⊆ V(H)` in Fact (a);
   - `2 ≤ |H_a|` in `L14OVStatement` ("every non-leaf node has `m ≥ 2`", from the proof);
   - the "(so `Σ_v dup_{≥M}(v) = Δ_{≥M}`)" identity in `OVStatement`;
   - `V(Y) = Y^0` and `E(X^0_Y) ⊆ E_r(Y)` in `GCStatement`.
4. **Kept although unused:**
   - `n_0 ≥ 1` in `OVStatement` (blueprint OV-N0-POS);
   - `0 ≤ s` in the τ-rule statements;
   - the τ-rule context in `TauEqSplitStatement` (the equalities hold for all `U`, `N`, `τ`; the stage-2 proofs go through general Lib lemmas).
5. **`ε` is fixed to `epsC = 2^{-5}`** in every statement ("Throughout, `ε = 2^{-5}`"). The stage-2 Lib lemmas will be ε-generic where that costs nothing.
6. **Γ.**
   - The chain up to lem14tau uses no Γ.
   - `GCStatement` and `ELStatement` take no hypothesis on `D_*`.
   - `GCThetaStatement` and `TowerCStatement` take `Gamma1core Dstar`, which is the part of the standing assumption that lemTower uses (blueprint GC-IV-GAMMA, TOW-GAMMA-ITEMS).

## Non-vacuity (`EGTest/ProbeP3A.lean`, compiles)

- **τ-rule context:** the root of `H2` (two disjoint edges) with witness `({0,1}, ∅)`, `s = 1 < τ = 512`.
- **Lemma 14^τ:** `TauRunTest.t` is a τ-run of `H2` at `s = 1`, `τ = 512 = 128·1·log₂²4`, the smallest allowed τ (`t_isTauRun_512`, `l14_hyps`).
  - It has three splits and deletes `01` and `23`.
  - The hypothesis of `L14SplitStatement` at the root is checked explicitly.
- **SEP and thin cut:** `t.WF H2`, and `t.IsTauSplitTree ε 512 H2` (`t_isTauSplitTree`).
- **OV:**
  - `OVHyp ε 1` for `tree0` on `E3` (two splits), with `0 < 1`, `3.42ε < 1` and `n_0 = 3 ≥ 1` (`ov_hyps`);
  - `tree0` is an `s = 0` recursion (instance statement).
- **GC and EL:** `run1` is a valid run on `K3` with one round and three pre-parts.
  - All its pre-parts are light (`d = 2` gives `λ = 1`, so `θ^GC(z) = z`, which is larger than any possible guest degree).
  - So **the GC-part clause of (iii) is not exercised by a valid run.** A valid run with a GC-part needs `λ_r^{1/2}` below a guest's core degree, so no toy instance exists.
  - Fix round 1 (m2): `GCPartTest` checks the round-level forms of the GC-part clause on a hand-built, not valid, round with a GC-part (see "Fix round 1").
- **GCTheta / TowerC:** `Gamma1core D` and a valid run are jointly satisfiable (the run without rounds on `E2`). A run with a round under Γ1 needs `d_1 ≥ 2^{2^{256}}` and is not built.
- **L14-C-TAU0:** `lem14tau_c_literal_false`. `H1` (one vertex), `s = 1`, `τ = 0` and the one-leaf τ-run satisfy all hypotheses, but the literal bound reads `0 ≤ ⌈0⌉ − 1 = −1`.

## Math findings

**L14-C-TAU0 (T1, minor edge case; the statement is true after adding `τ > 0` or `n_0 ≥ 2`).**
- What the TeX allows: s2:lem14tau assumes `τ ≥ 128 s log² n_0`. For `n_0 = 1` this is `τ ≥ 0`, so `τ = 0` is allowed.
- Why (c) fails there:
  - the τ-run of a one-vertex graph is a single leaf (it is an `(ε,s)`-expander);
  - it deletes no edge, so the count in (c) is 0;
  - but (c) claims `0 ≤ ⌈0⌉ − 1 = −1`, and "(`= τ − 1` for integer `τ`)" claims `0 ≤ −1`.
- The proof says "If `n_0 = 1` the root is an `(ε,s)`-expander and everything is trivial", which is not true for this item.
- Lemma [s2:lemThinCut] itself assumes `τ > 0`, so the gap is only in 14^τ's restatement.
- No downstream impact: every application has `τ = τ_l ≥ 128`.
- Suggested manuscript fix: in lem14tau (c), write "if `τ > 0`" or "(for `n_0 ≥ 2`)", or assume `n_0 ≥ 2` in the lemma.
- Lean: `EGTest.ProbeP3A.lem14tau_c_literal_false`.

No other statement of the chain looked false. Every statement was re-derived while writing the Specs:
- the per-split counting of 14^τ and the 0.698 / 127/128 margins;
- the deletion bound (8) and the B-M bound (9);
- OV (a)–(c) via the chain/potential argument;
- the instance bound `|U∪N| < (33/32)(2/3)m ≤ 3m/4`;
- lemGC (iii) `E(X^0_Y) ⊆ E_r(Y)`: SEP (i) on the two-level recursion plus completeness of the home order.

## Hazards for stage 2

- **H1 (OV-CONST-546):** L14OV's `5.46` needs the sharp OV (a) with `c_OV ≥ 0.414508`. Use `17/41` (`2^65 ≥ 3^41`); `12/29` is not enough.
- **H2 (OV proof route):** use the potential `Φ_M(x) = [x ≥ M](1/log²M + 1/(c_OV log M) − 1/(c_OV log x))` by structural induction (blueprint OV-A-PROOF-ROUTE), not the chain/integral argument.
- **H3 (tree infrastructure):** everything rests on address lemmas that do not exist yet:
  - `graphAtD (a ++ [b])` at internal `a`;
  - prefix-closure of `nodeAddrs`;
  - `subtreeAt` and the induction principle "P holds for the subtree at every node".
  - Estimate: about 300 lines before SEP.
- **H4 (L14Term T2):** building the tree needs well-founded recursion on `|K|`, with the address as an accumulating parameter.
- **H5 (B-M bound):** `L14GlobalStatement`'s leaf bound `2n_0 − 2n_0/(2+log n_0)` is unused downstream (blueprint LEM14-BM-BOUND-UNUSED) but is part of the Spec: about 150 lines of real inequalities (`7L² − 3.6L − 3.2 ≥ 0`).
- **H6 (ℤ ceilings):** the thin-cut bound mixes `ℤ` (`⌈τ⌉ − 1`), `ℕ` (`k − 1`) and a real threshold. Prove the real form `# < τ` first, then derive the other two.
- **H7 (GC (iii)):** needs SEP (i) on `twoLevel` (via `Valid.wf_twoLevel`), `homeOrder.toFinset = prePartAddrs`, and `EG.edgeLaminarity` for the `G_{r+1}` clause.

## Open questions for the orchestrator / reviewers

1. **L14-C-TAU0 repair:** accept `0 < τ` on the bounds of `L14ThinStatement` and send the T1 note to the manuscript? Alternative: add `2 ≤ H.card` to the whole lemma.
2. **Declared-input ownership:** should P3A prove `ELStatement` in stage 2 (cheap), and who owns `TowerCStatement`? The future full `Tower` Spec should import `EG/Spec/HB/TowerC.lean`.
3. **(i) of lemGC:** is recording the first clause as a Defs design constraint (no statement) acceptable?
4. **GC-part non-vacuity:** is a valid run with a GC-part worth constructing (a galactic `d`)? Or is the round-local `OverlapTest`-style check of (ii) on a non-valid round enough?

## Fix round 1 (review `work/p2b/P3A.review1.md`, verdict APPROVE)

Every issue was re-checked against the TeX and the locked Defs.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor, process): EL (s2:lemEL) is declared as an input although it is a cheap s2 node | valid as a process point, no Spec defect | No Spec change: `ELStatement` is faithful (reviewer agrees) and stays a declared input with stub `EG.edgeLaminarity`, as the generic rule "used but not proved" allows. **Deferred to the orchestrator** (open question 2): P3A can prove it in stage 2 (an (R5) case analysis on `Round.assign`, ~80 lines) if assigned. `TowerCStatement` stays an input (tower unit). |
| **m2** (minor, test gap): the GC-part clause of `GCStatement` (iii) is not exercised | **fixed** | New section `GCPartTest` in `EGTest/ProbeP3A.lean`. Round `c` on `H4` (`Fin 4`, edges `01, 23`, `d = 1`): root split `({0},{1})`, pre-parts `[false] = {0,1}` (light) and `[true] = {1,2,3}` with guest `1`. (L1), (L2) hold and (GC) fails, so `[true]` is a GC-part (`gcPart_T`). One `example` checks the round-level forms of every (iii) conclusion: `[true] ∈ Std`; every edge of `G'` inside `Z^0` is assigned; `E(X^0) = {23} ⊆ E([true])`; `next` has no edge inside `Z^0`; `S = D = Dup* = {1}`. It also checks that the guest set and `E(X^0)` are nonempty. `V(Y) = Z^0` is run-level and not checked. Caveat: the round is not valid and sits in the junk parameter regime (`λ = log₂ 1 = 0`, so `P = 0` and `θ^GC ≡ 0`, via Lean's `0^{-1/2} = 0`); the reviewer's argument shows no toy valid run can have a GC-part. |
| **c1** (cosmetic): `TauEqSplitStatement` omits the premise "one end in `U'`, the other outside `U'∪N''`" | **fixed** | Added as the first part of the first conjunct: `∃ x ∈ U', ∃ y ∈ V(H) ∖ (U'∪N''), e = s(x,y)`. It is true by the definition `F'' = E_H(U', V∖(U'∪N''))` (`splitDel`, `edgesBetween`). Docstring updated. This strengthens the statement, which is not yet proved. |
| **c2** (cosmetic): SEP (i) "first node" encoded as "in every prefix, in neither child" | not an issue | The encoding is equivalent (the reviewer agrees) and the module docstring already says so. No change. |
| **c3** (cosmetic): the repair note in `Lemma14Tau.lean` says `τ = τ_l ≥ 1` | **fixed** | The note now says `τ = τ_l = ⌈128 s_l Λ_l²⌉ ≥ 128`, matching the lemma's own remark "`τ ≥ 128 s > s` whenever `n_0 ≥ 2`". It also records the reviewer's second instance of L14-C-TAU0: `n_0 = 0` in Lean, where `logb 2 0 = 0`. |

Files changed:
- `EG/Spec/HB/TauRules.lean` (c1);
- `EG/Spec/HB/Lemma14Tau.lean` (c3, docstring only);
- `EGTest/ProbeP3A.lean` (m2, plus the module docstring).

Checks:
- `lake build` of `EG.Spec.HB.{TauRules, Lemma14Tau}`, `EG.Proof.HB.{TauRules, GC, EL, TowerC}` and `EGTest.HB` succeeded.
- `scripts/check.sh EGTest/ProbeP3A.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan on `EG.Proof.HB.{TauRules, GC}`: 730 constants, 0 sorryAx, 0 violations.
- `sorry` still appears only in the two declared-input stubs.

## Fix round 2 (review `work/p2b/P3A.review2.md`, verdict APPROVE)

Every issue was re-checked against the TeX and the locked Defs. No Spec or Proof file changed in this round.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor, process; carried from round 1): EL (s2:lemEL) is declared as an input although it is a cheap s2 node | valid as a process point; not a Spec defect | No Spec change. `ELStatement` is faithful: both reviewers agree, and I re-checked it against s2.tex lemEL. It keeps the prescribed stub `EG.edgeLaminarity`. **Still deferred to the orchestrator:** either assign `ELStatement` to P3A stage 2 or confirm the declaration. The stage-2 proof is an (R5) case analysis on `Round.assign`, about 80 lines: for an edge inside `partVerts Y`, step (2) or step (3) of `assign` returns `some _`, so the edge is not in `passed`; then `E(G_l) ⊆ E(G_{r+1})` by antitonicity. `TowerCStatement` stays an input. The future full Tower Spec must import `EG/Spec/HB/TowerC.lean` and must not restate (c). |
| **c1** (cosmetic, test coverage): every `τ`-rule instance in `EGTest` is idle, and the thin-cut bound is only checked with count 0 | valid | **fixed.** New section `NonIdleTau` in `EGTest/ProbeP3A.lean`, adapted from the reviewer's scratch check. It builds `H6` on `Fin 6` with edges `02, 03, 14`, witness `U = {0,1,5}`, `F = {02,03,14}`, `s = 1 < τ = 2`, and proves `H_out = {0}`, `U' = {1,5}`, `N' = N'' = {0}`, `F_1 = F'' = {14}`, `H_in = ∅`. The one-split tree `tr` with label `({1,5},{0})` satisfies `IsTauSplitTree epsC 2 H6` (`tst`), with `deleted = {14}` and `Dup = {0}`. One `example` bundles the hypotheses of `ThinCutStatement` with `H_out ≠ ∅`, a deleted edge, and the count at leaf `[false]`, `h = 4` being `1 = ⌈2⌉ − 1` (ℤ form) and `2 − 1` (ℕ form). So the bound is attained. Two further examples check count `1` at leaf `[true]` with `h = 1`, and count `0` for `h = 0 ∈ V([false])`. The helper lemmas `tauHout_two` and `tauHin_two` turn `2 ≤ (deg : ℝ)` into `2 ≤ deg`. |
| **c2** (cosmetic): `TowerCStatement` keeps the redundant hypothesis `D_* ≤ d_1` | not an issue | It is the TeX's "with `d_1 ≥ D_*`", so the statement stays literal. `Valid` gives the hypothesis for `r ∈ [1,R]`, so keeping it costs nothing. Kept, as the reviewer suggests. |
| **c3** (cosmetic): in `SEPiiiStatement` the vertex `u` only names the leaf `L` | not an issue | This is faithful to the TeX's `Leaf_u` and equivalent to quantifying over leaves directly. Kept, as the reviewer suggests. |

Files changed: `EGTest/ProbeP3A.lean` (c1, plus a module-docstring bullet).

Checks:
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP3A.lean 1200`: rc=0, 0 errors, 0 sorry-warnings.
- `python3 -I scripts/lint.py`: 0 findings.
- `sorry` appears only in the two declared-input stubs `EG/Proof/HB/{EL,TowerC}.lean`.
- The Spec/Proof modules of the unit are unchanged since fix round 1 and were already built.

## Proof round 1 (stage 3)

Progress log (updated as the round proceeds; final summary at the end of this section).

- New Lib files: `EG/Lib/HB/Split.lean` (generic split, witness Fact, τ-rule facts valid for all
  `(U,N,τ)`), `EG/Lib/HB/Address.lean` (addresses, children = generic split, prefixes, node
  decomposition), `EG/Lib/HB/SEP.lean` (SEP (i) count, (ii), (iii), thin cut core).
- Proved (0 sorry): `EG.witnessFact`, `EG.tauEqSplit`, `EG.tauFactA/B/C`
  (`EG/Proof/HB/TauRules.lean`); `EG.sep0`, `EG.sepMono`, `EG.sepI`, `EG.sepII`, `EG.sepIII`
  (`EG/Proof/HB/SEP.lean`); `EG.thinCut`, `EG.thinCutEdge` (`EG/Proof/HB/ThinCut.lean`).
- Observation: the thin cut (and SEP (iii)) need neither `WF` nor `s_ν < τ` nor the witness
  property; only that the labels are `τ`-rule sets of some pair `(U,N)` (`STree.TauLabels`),
  as the manuscript's proof remarks.
- `EG/Lib/HB/OVPotential.lean` (per-vertex potential `Φ(x) = [x ≥ M](C - 1/(c_OV log x))`,
  induction on the tree; `c_OV ≥ 17/41`; (b) by induction; identity; consequence; (c)).
  Proved (0 sorry): `EG.ov`, `EG.ovInstance` (`EG/Proof/HB/Overlap.lean`).
- `EG/Lib/HB/Lemma14.lean` (counting at one split `τ(|H_out|+|H_in|) ≤ |F_0|`, all inequalities
  of (a) at one split, children sizes, `IsTauRun` node decomposition) and
  `EG/Lib/HB/Lemma14Ind.lean` (the induction [BM (8), (9)], `7L²-3.6L-3.2 ≥ 0`, construction
  `tauBuild` of a `τ`-run for any witness rule by fuel `|H_0|`).
  Proved (0 sorry): `EG.l14Split`, `EG.l14Term`, `EG.l14Global`, `EG.l14OV`, `EG.l14Thin`
  (`EG/Proof/HB/Lemma14Tau.lean`).
- `EG/Lib/HB/GC.lean` (round level: an edge of `G'_l` inside `Z^0` of a standalone pre-part is
  assigned; an edge of `X^0_Z` is assigned to `Z` by (R5)(1), using SEP (i) on the two-level
  recursion; `D_l ⊆ Dup*_l`; `S_Z ⊆ D_l`).
  Proved: `EG.gc` (0 sorry, no declared input), `EG.gcTheta` (from the declared input
  `EG.towerC`) (`EG/Proof/HB/GC.lean`).

### Summary of proof round 1

**Every probe node of P3A is proved.** Statements (all frozen Specs, unchanged) and proofs:

| Spec | Proof | File |
|---|---|---|
| `WitnessExistsStatement` | `EG.witnessExists` (stage 1) | `EG/Proof/HB/TauRules.lean` |
| `WitnessFactStatement` | `EG.witnessFact` | same |
| `TauEqSplitStatement` | `EG.tauEqSplit` | same |
| `TauFactA/B/CStatement` | `EG.tauFactA`, `EG.tauFactB`, `EG.tauFactC` | same |
| `SEP0Statement`, `SEPMonoStatement` | `EG.sep0`, `EG.sepMono` | `EG/Proof/HB/SEP.lean` |
| `SEPiStatement`, `SEPiiStatement`, `SEPiiiStatement` | `EG.sepI`, `EG.sepII`, `EG.sepIII` | same |
| `ThinCutStatement`, `ThinCutEdgeStatement` | `EG.thinCut`, `EG.thinCutEdge` | `EG/Proof/HB/ThinCut.lean` |
| `OVStatement` (sharp) | `EG.ov` | `EG/Proof/HB/Overlap.lean` |
| `OVInstanceStatement` | `EG.ovInstance` | same |
| `L14SplitStatement`, `L14TermStatement` | `EG.l14Split`, `EG.l14Term` | `EG/Proof/HB/Lemma14Tau.lean` |
| `L14GlobalStatement`, `L14OVStatement`, `L14ThinStatement` | `EG.l14Global`, `EG.l14OV`, `EG.l14Thin` | same |
| `GCDefStatement` | `EG.gcDef` (stage 1) | `EG/Proof/HB/GC.lean` |
| `GCStatement` | `EG.gc` | same |
| `GCThetaStatement` | `EG.gcTheta` (uses the declared input `EG.towerC`) | same |

New Lib files (module, `public section`, namespace `EG.HB`): `EG/Lib/HB/Split.lean`,
`Address.lean`, `SEP.lean`, `OVPotential.lean`, `Lemma14.lean`, `Lemma14Ind.lean`, `GC.lean`
(about 2980 lines of Lean in the round, Lib + Proof). No new Defs file; no Spec file changed.

**Declared inputs actually used.** Only `EG.towerC` ([s2:lemTower] (c)), by `EG.gcTheta`.
`EG.edgeLaminarity` ([s2:lemEL]) is **no longer used**: `GCStatement` (iii) "no edge of `G_{r+1}`
has both ends in `Z^0`" is proved directly from (R5) (`E(G_{r+1})` is the set of unassigned edges
of `G'_r`, and (R5)(3) assigns every edge inside `Z^0` of a standalone pre-part). The manuscript's
proof cites Lemma EL for this step; the direct argument is the "equivalently" clause of that proof
read in the other direction. The EL stub can stay (for the structure unit) but P3A does not
depend on it.

**Checks** (2026-09-29):
- `lake build EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC}`: success; 0 warnings in
  the new files.
- `python3 -I scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG` on the six Proof modules: 1211 constants,
  2 use `sorryAx`: `EG.towerC` (declared-input stub) and `EG.gcTheta` (only through `EG.towerC`);
  0 violations. `#print axioms` of `EG.l14OV`, `EG.gc`: `[propext, Classical.choice, Quot.sound]`.
- A scratch file importing all six Proof modules together with `EG.Proof.HB.{EL,Cap}` and
  `EG.Lib.HB.Run` compiles (no name clashes).

**Root imports for the orchestrator** (I did not edit `EG.lean`):
`EG.Lib.HB.{Split,Address,SEP,OVPotential,Lemma14,Lemma14Ind,GC}` and
`EG.Proof.HB.{SEP,ThinCut,Overlap,Lemma14Tau}` (new), plus the stage-1 modules listed above
(`EG.Proof.HB.{TauRules,GC,EL,TowerC}` and the Spec modules) if not yet imported.

**Proof notes (no math finding).**
- The thin cut and SEP (iii) need neither `WF` nor `s_ν < τ` nor the witness property, only that
  the labels are `τ`-rule sets of some `(U,N)` (`STree.TauLabels`), as the manuscript remarks.
- OV (a) is proved per vertex with the potential `Φ(x) = [x ≥ M](C - 1/(c_OV log x))` by
  induction on the tree (hazard H2); the step `w(x) + Φ(x₁) ≤ Φ(x)` for `M ≤ x₁ ≤ 3x/4` reduces
  to `1/log² x ≤ 1/(log x · log x₁)`. `c_OV ≥ 17/41` from `2^65 ≥ 3^41` (hazard H1) gives both
  `3.42` and `5.46`. OV (c) and the instance do not need `n_0 ≥ 1`.
- Lemma 14^τ (a): the per-split count `τ(|H_out|+|H_in|) ≤ |F_0|` is a disjoint-union argument on
  `F_0`; the induction uses `log₂ 0.698 ≤ -2/5` (`0.698^5 ≤ 1/4`) and `7L²-3.6L-3.2 ≥ 0`. The
  bound `|U' ∪ N''| ≤ (1 + 1.25/32)(2/3) m ≈ 0.693 m` is slightly better than the manuscript's.
  The induction is stated for every `τ`-run on `K` with `128 s log²|K| ≤ τ` and needs no case
  `n_0 = 1`.
- (T2) of termination: `STree.tauBuild` builds the `τ`-run of any witness rule by fuel `|H_0|`
  (a graph without vertices is an expander).
- No statement looked false; the T1 finding L14-C-TAU0 of stage 1 stands (the repaired
  `L14ThinStatement` is proved).

**Remaining:** nothing in P3A's probe list. Open for the orchestrator: whether the EL stub stays a
declared input of another unit (P3A no longer needs it).

## Fix round 1 (proof stage; review `work/p2b/P3A.review1.md`, re-run of 2026-09-29, verdict APPROVE)

Every issue was re-checked against `s2.tex` v6.1 and the locked Defs/Specs. No Spec or Defs file
changed (they are locked); documentation-only suggestions for locked files are recorded here.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor): `ELStatement` is a declared input with a `sorry` stub that P3A no longer uses | valid | **fixed: Lemma EL is now proved** (`EG.edgeLaminarity`, `EG/Proof/HB/EL.lean`, 0 `sorry`; the Spec is unchanged). New round-level lemma `EG.HB.Round.assign_ne_none_of_mem_partVerts` (`EG/Lib/HB/GC.lean`): for a valid round, an edge with both ends in `V(Z)` of any pre-part `Z` is assigned, by (R5) step (2) if `Z` is light (`V(Z) = Z^0 \ S_Z`) and by step (3) if standalone (`V(Z) = Z^0`), or by an earlier step. Proof of EL: for `Y = (r,a)` and `l > r`, `E(G_l) ⊆ E(G_{r+1}) = passed_r` (antitonicity `Run.graph_edges_subset_of_le`), and passed edges are unassigned. This also removes a `sorry` from the dependencies of `EG.Proof.Chain.JSLCTypes` (unit P2J), which uses `EG.edgeLaminarity`. Remaining caveat: the locked module docstring of `EG/Spec/HB/EL.lean` still calls the statement a declared input of P3A (stale documentation only, for the integrator). |
| **c1** (cosmetic): `GCThetaStatement` omits `d_1 ≥ D_*` and assumes only `Gamma1core` | not an issue (Spec stronger than the TeX, and true) | Re-checked: lemGC (iv) in the TeX is just "`θ^GC_r(Z^0) > τ_r` for every round-`r` pre-part"; `d_1 ≥ D_*` is a hypothesis of lemTower (c), and `Run.Valid` gives it for `R ≥ 1` (used in `EG.gcTheta` via `Run.Valid.dstar_le`). The TeX's standing assumption Γ1–Γ4 is stronger than `Gamma1core`, which is all that lemTower (c) needs. So the Spec is stronger than the TeX and true. No change: the Spec file is locked; this paragraph is the requested record. |
| **c2** (cosmetic): the `WF` conjunct of `IsTauRun` is implied by the label clause | valid (documentation) | The Spec docstring is locked, so the sentence is recorded here and **machine-checked**: new `example` at the end of `EGTest/ProbeP3A.lean` proves `StopsAt ∧ (label clause) → IsTauRun`, i.e. `WF` follows from the label clause via `EG.HB.tau_split_wf` (the `τ`-rule sets of a witness are disjoint subsets of `V(H_a)`, Fact (a)). Hence `IsTauRun` does not restrict the class of runs, and "it is a split recursion" (TeX) is a consequence, not a silent assumption. |
| **c3** (cosmetic): `L14TermStatement` (T1) quantifies over all `K` with `2 ≤ |K| ≤ n_0` | not an issue | Stronger than the TeX and true (proved as `EG.l14Term`); already recorded in "Deviations" 2. No change. |
| **c4** (cosmetic, test coverage): no test instance has `N''_ν ≠ ∅` under `OVHyp`/`IsTauRun` | valid as an audit note; no fix possible by `decide` | `|N''| ≤ cε|U'|/log²m < 1` unless `|U'| ≳ 32 log²m`, so a test instance needs graphs with hundreds of vertices. The hypotheses do not force `N'' = ∅`, and OV (a)/(b), 14^τ (b) are proved (`EG.ov`, `EG.l14OV`, 0 `sorry`). **Audit note:** the quantitative content of OV (a)/(b) and 14^τ (b) is checked by proof only, not by a test instance. |

Files changed:
- `EG/Lib/HB/GC.lean`: new lemma `Round.assign_ne_none_of_mem_partVerts` (+ docstring bullet);
- `EG/Proof/HB/EL.lean`: the stub is replaced by a proof (now imports `EG.Lib.HB.GC`);
- `EG/Proof/HB/TowerC.lean`: docstring only (it is now the only `sorry` of P3A);
- `EGTest/ProbeP3A.lean`: the c2 check (imports `EG.Lib.HB.Split`).

Checks (2026-09-29):
- `lake build EG.Lib.HB.GC EG.Proof.HB.EL EG.Proof.HB.GC EG.Proof.Chain.JSLCTypes`: success.
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP3A.lean 1200`: rc=0, 0 errors, 0 sorry.
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP2J.lean 1200` (the only other transitive importer of `EG.Proof.HB.EL`): rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan on `EG.Proof.HB.{EL,GC}`: 1054 constants, 2 use `sorryAx`: `EG.towerC` (declared-input stub) and `EG.gcTheta` (through it); `EG.edgeLaminarity` is sorry-free.

**Declared inputs of P3A now:** only `EG.towerC` ([s2:lemTower] (c)), used by `EG.gcTheta`.

## Fix round 2 (proof stage; review `work/p2b/P3A.review2.md`, verdict APPROVE)

Every issue was re-checked against `s2.tex` v6.1 and the files. No Spec, Defs or proof changed.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor, process): `EG.towerC` is the unit's only `sorry`; ownership by the tower unit to be confirmed; the full Tower Spec must import `EG/Spec/HB/TowerC.lean` | valid (process; no Spec defect) | Nothing to fix in P3A. Re-checked: lemGC (iv) is literally "Lemma lemTower (c)" (s2.tex l.1317), so the input is legitimate. **For the orchestrator:** confirm that the s2 tower unit owns the stub `EG.towerC` and that its Tower Spec imports `EG/Spec/HB/TowerC.lean` without restating (c). The existing `EG/Spec/HB/TowerB.lean` already says "import this file, do not restate it" and refers to `TowerCStatement`. The ownership note and the import requirement are now also in the docstring of `EG/Proof/HB/TowerC.lean`. |
| **c1** (cosmetic): the locked module docstring of `EG/Spec/HB/EL.lean` still calls `ELStatement` a declared input | valid (stale documentation) | The file is locked, so I did not edit it. **For the integrator's documentation pass:** replace the "DECLARED INPUT … the stub is `EG.edgeLaminarity`" paragraph by "proved in `EG/Proof/HB/EL.lean` (`EG.edgeLaminarity`, 0 `sorry`)". |
| **c2** (cosmetic): the docstring of `EG/Proof/HB/TowerC.lean` says the proof of (c) needs lemCap (ii) | valid | **fixed.** Re-checked s2.tex (proof of lemTower (c), l.1249–1257). It uses `s_r ≤ 2Λ_r^σ` and `Λ_r ≤ 2λ_r` from (b) (propDegRec), `P_r ≥ λ_r^{σ+3}` (`C_P = σ+3`) and Γ1(a). lemCap (ii) enters (b) only for `L_Y ≤ log M_r`, which (c) does not use. The docstring now says so and no longer mentions lemCap. |
| **c3** (cosmetic, test coverage; review 1 c4): no test instance has `N''_ν ≠ ∅` under `OVHyp`/`IsTauRun` | valid as an audit note; no fix needed | Already recorded in the proof-stage fix round 1 (c4). **Audit note:** the quantitative content of OV (a)/(b) and 14^τ (b) is verified by proof alone (`EG.ov`, `EG.l14OV`, kernel-checked, 0 `sorry`). |
| **c4** (cosmetic): the opening "Status (stage 1)" bullets of this file are superseded | valid | **fixed.** New "Current status" section at the top of this file. |

Files changed: `EG/Proof/HB/TowerC.lean` (docstring only); `work/p2b/P3A.md`.

Checks (2026-09-29):
- `lake build EG.Proof.HB.TowerC EG.Proof.HB.GC`: success (the only warning is the declared-input `sorry` in `EG.towerC`).
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP3A.lean 1200`: rc=0, 0 errors, 0 sorry-warnings.
- `python3 -I scripts/lint.py`: 0 findings.

## Re-verification (proof round 1 re-dispatch, 2026-09-29)

Task re-issued as "Proof round 1"; everything was already done, so nothing was re-proved. Re-checked:
- `lake build EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}`: success; the
  only warning is the declared-input `sorry` of `EG.towerC`.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`, the seven Proof modules above without TowerC as root): 1214 constants,
  2 use `sorryAx`: `EG.towerC` (declared-input stub) and `EG.gcTheta` (through it); 0 violations.
- `scripts/lock.py check`: no locked HB Spec/Defs constant changed. The only violation is the
  locked file `CONVENTIONS.md` (not touched by P3A; for the integrator).

## Fix round 1 (re-dispatch, 2026-09-30; review `work/p2b/P3A.review1.md`, re-run of 2026-09-29)

The task was re-issued with the same five issues. The proof-stage "Fix round 1" above had already
handled all of them. I re-checked each one against the current files. No file other than this one
changed.

| Issue | Verdict | Current state |
|---|---|---|
| **m1** (minor): `ELStatement` is a declared input with an unused `sorry` stub | valid | **fixed** (proof-stage fix round 1). `EG.edgeLaminarity` in `EG/Proof/HB/EL.lean` is proved with 0 `sorry`, via `EG.HB.Round.assign_ne_none_of_mem_partVerts` (`EG/Lib/HB/GC.lean`). The Spec is unchanged. The axiom scan shows that `EG.edgeLaminarity` is sorry-free. |
| **c1** (cosmetic): `GCThetaStatement` omits `d_1 ≥ D_*` and assumes only `Gamma1core` | not an issue | The Spec is stronger than the TeX and is still true. `Run.Valid` gives `D_* ≤ d_1` (`Run.Valid.dstar_le`), and lemTower (c) needs only Γ1(a),(b). The Spec file is locked, so the requested sentence is recorded here instead of in its docstring. |
| **c2** (cosmetic): the `WF` conjunct of `IsTauRun` is redundant | valid (documentation) | **fixed** (proof-stage fix round 1). The locked Spec docstring cannot be edited. The fact is recorded here and machine-checked: the last `example` in `EGTest/ProbeP3A.lean` derives `WF` from the label clause via `EG.HB.tau_split_wf`. So "it is a split recursion" is a consequence, not an assumption. |
| **c3** (cosmetic): (T1) of `L14TermStatement` quantifies over all `K` | not an issue | This is stronger than the TeX and still true: it is proved as `EG.l14Term`. It is already recorded in "Deviations" 2. |
| **c4** (cosmetic): no test instance has `N''_ν ≠ ∅` | valid as an audit note | Not fixable by `decide`, because it needs `|U'| ≳ 32 log² m`. **Audit note:** OV (a)/(b) and 14^τ (b) are checked by proof only (`EG.ov`, `EG.l14OV`, 0 `sorry`). |

Checks (2026-09-30):
- `lake build EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}`: success. The only warning is the declared-input `sorry` of `EG.towerC`.
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP3A.lean 1200`: rc=0, 0 errors, 0 sorry-warnings.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan on `EG.Proof.HB.{EL,GC}`: 1054 constants, 0 violations. 2 constants use `sorryAx`: `EG.towerC` (the declared-input stub) and `EG.gcTheta` (through `EG.towerC`).

The only declared input of P3A is now `EG.towerC` ([s2:lemTower] (c)).

## Fix round 2 (Specs; re-dispatch 2026-09-30; review `work/p2b/P3A.review2.md`, re-run of 2026-09-30, verdict APPROVE)

Every issue was re-checked against `s2.tex` v6.1 and the current files. All five are documentation or
process points; none is a Spec defect. No Lean file changed (Spec, Defs and `LOCK.json` are locked or
integrator-owned); only this file changed.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor, process): `TowerCStatement` is the unit's only `sorry`; tower-unit ownership of `EG.towerC` to be confirmed; the full Tower Spec must import `EG/Spec/HB/TowerC.lean` | valid (process only; the input is legitimate) | Nothing to fix in P3A. Re-checked: lemGC (iv) is literally "Lemma lemTower (c)" (s2.tex l.1317). The docstrings already say it: `EG/Proof/HB/TowerC.lean` l.12-13 and l.23 ("Owner: the s2 tower unit; the full Tower Spec must import `EG/Spec/HB/TowerC.lean` and must not restate (c)"), `EG/Spec/HB/TowerC.lean` l.14-15, and TowerA/TowerB say the same. **For the orchestrator:** record that the s2 tower unit owns `EG.towerC`, and require its Tower Spec to import `EG/Spec/HB/TowerC.lean`. |
| **c1** (cosmetic): the locked module docstring of `EG/Spec/HB/EL.lean` (l.6-11) still calls `ELStatement` a declared input of P3A | valid (stale documentation) | Confirmed by reading l.6-11. The file is locked, so it is not edited here. **For the integrator's documentation pass:** replace the paragraph with "proved in `EG/Proof/HB/EL.lean` (`EG.edgeLaminarity`, 0 `sorry`)". The node table of this file was updated: the lemEL row now says "proved". |
| **c2** (cosmetic): `GCDefStatement` is a tautology of `isLight = L1 ∧ L2 ∧ GC` | valid (faithful; bookkeeping note) | Re-checked: `Round.isLight := isL1 ∧ isL2 ∧ isGC` (`EG/Defs/HB/Round.lean` l.227-228), and `EG.gcDef` is a one-line term proof. **fixed (documentation):** the node table and the lemGC back-translation of this file now say "tautological in Lean; not counted as content". |
| **c3** (cosmetic, test coverage): no test instance has `N''_a ≠ ∅` under `OVHyp`/`IsTauRun` | valid as an audit note; no fix feasible | As recorded in the earlier rounds: an instance needs `|U'| ≳ 32 log² m`, which is out of reach of `decide`. **Audit note:** the quantitative content of OV (a)/(b) and 14^τ (b) is verified by proof alone (`EG.ov`, `EG.l14OV`, kernel-checked, 0 `sorry`). |
| **c4** (cosmetic): the 25 P3A statements are not in `LOCK.json` | valid | Confirmed: `LOCK.json` has 0 entries for the P3A Spec constants (it locks only the HB Defs, e.g. `EG.HB.IsWitness`, `EG.HB.Addr`). `LOCK.json` is integrator-owned, so it is not edited here. **For the orchestrator/integrator:** add the constants of `EG.Spec.HB.{TauRules, SEP, ThinCut, Overlap, Lemma14Tau, GC, EL, TowerC}` at the next lock update. |

Files changed: `work/p2b/P3A.md` only (status header, node table, lemGC note, this section).


## Re-verification (proof round 1 re-dispatch, 2026-09-30)

The task was re-issued as "Proof round 1". Every probe node was already proved, so nothing was
re-proved and no Lean file changed. Re-checked:
- `lake build EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL,TowerC}`: success. The
  only warning is the declared-input `sorry` of `EG.towerC`.
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP3A.lean 1200`: rc=0, 0 errors, 0 sorry-warnings.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`--prefix EG`, `EG.Proof.HB.{TauRules,SEP,ThinCut,Overlap,Lemma14Tau,GC,EL}`): 1214
  constants, 0 violations. 2 use `sorryAx`: `EG.towerC` (the declared-input stub) and `EG.gcTheta`
  (through it).
- No proof of `TowerCStatement` exists elsewhere yet (grep), so `EG.towerC` is still a stub.

**Remaining:** nothing in P3A's probe list. The only declared input is `EG.towerC` ([s2:lemTower] (c)).
