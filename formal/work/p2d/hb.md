# P2-D [hb]: the s2 hierarchy model (s2:defWitness, s2:defTauRules, s2:lemSEP, s2:lem14tau, s2:defHBtp, s2:defAncestors): design note

Status: all seven files compile with 0 errors and 0 `sorry`. The lint (`python3 scripts/lint.py` on the seven files) reports 0 findings. The axiom scan `lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.HB.Run` inspects 780 constants and finds 0 violations and 0 `sorryAx`.
Manuscript: `proofs/manuscript/s2.tex` v6.1 (M_l is the integer ceiling in (R2)).
Inputs: TRIAGE §2.1–§2.3, §2.12, §3 items 7–10; `blueprint_s2a.md` (defWitness, defTauRules, lemSEP, lemOVgeneric, lem14tau, defHBtp, defAncestors); `blueprint_s2b.md` (DR-ROUND-LOCAL, graft API, the new Defs `epsA`, `psiPool`, `nuAnc`, `HypH`); the `defs_needed` lists of s3b, s5, s6a, s6b, s7a and s7b.

These are TRIAGE §3 items 7–10. Item 9 (`Round.lean`) is behind the M-INTEGER lock gate. It uses the v6.1 text of (R2), with the ceiling.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/HB/Witness.lean` | `EG.Defs.HB.Witness` | `IsWitness`, `witN`, `witF0`; generic split `splitFst`, `splitSnd`, `splitDel`; τ-rules `tauHout`, `tauU1`, `tauN1`, `tauF1`, `tauHin`, `tauN2`, `tauF2`, and the literal children `tauG1`, `tauG2` |
| `EG/Defs/HB/SplitTree.lean` | `EG.Defs.HB.SplitTree` | `Addr`, `STree` (inductive), `labelAt`, `subtreeAt`, `nodeAddrs`, `leafAddrs`, `internalAddrs`, `labelU`, `labelN`, `graphAtD`, `delAt`, `WF`, `leafMass`, `dup`, `deleted`, `DeltaGe`, `dupGe`, `OVHyp`, `graft`, `leafPrefix`, `StopsAt`, `IsS0Rec`, `IsTauSplitTree`, `IsTauRun`, `cOV` |
| `EG/Defs/HB/Round.lean` | `EG.Defs.HB.Round` | parameters `lamOf`, `tHBOf`, `TOf`, `MOf`, `LamOf`, `sOf`, `POf`, `tauOf`, `thetaGC`; `RoundChoice`; round objects `Round.d`, `cycEdges`, `graph'`, `CyclesValid`, `pieceAddrs`, `piece`, `twoLevel`, `X0`, `Z0`, `prePartAddrs`, `DupStar`, `mu`, `D`, `home`, `guests`, `isL1`, `isL2`, `isGC`, `isLight`, `isGCPart`, `Std`, `partVerts`, `X`, `partGraph`, `assign`, `E`, `passed`, `next`, `pieceOf`, `Round.Valid` |
| `EG/Defs/HB/Run.lean` | `EG.Defs.HB.Run` | `Run`, `PartId`; `R`, `choice`, `IsRound`, `graph`, `d`, `lam`, `tHB`, `T`, `M`, `Lam`, `s`, `P`, `tau`, `thetaGC`; run-level wrappers of all round objects; `E0`, `pieceOf`, `Run.Valid`; `parts`, `ancestors`, `lightParts`, `stdParts`, `ancestorsUpTo`, `ancVerts`, `ancGraph`, `ancEps`, `ancS`, `ancRound`, `LY`, `anc`, `hubs`, `ports`, `fresh`, `classed`, `dup`, `mult`, `nuAnc`, `j0`, `j1`; `epsA`, `psiPool`, `HypH` |
| `EG/Lib/HB/SplitTree.lean` | `EG.Lib.HB.SplitTree` | witness iff non-expander; split vertex sets; tree structure lemmas; node graphs are subgraphs of the root; the one-leaf tree; the graft API |
| `EG/Lib/HB/Run.lean` | `EG.Lib.HB.Run` | round level: (R5) partition lemmas, `D = {μ ≥ 2}`, `S_Z, V(Z) ⊆ Z^0`; run level: recursion, `V(G_l) = V(G)`, antitone edges, stationarity, guards, parts and ancestors, `anc = ∅` for `l ≤ 2`, `mult ≤ μ`, `Valid` accessors, `valid_nil_iff` |
| `EGTest/HB.lean` | `EGTest.HB` | parameter values at `d = 2`; the run without rounds; **a hand-built valid run with one round on `K_3`**; objects of that run; negative tests |

All names are in the namespace `EG.HB` (sub-namespaces `STree`, `Round`, `Run`).

Root imports for the orchestrator to add (I did not edit `EG.lean` or `EGTest.lean`):
- to `EG`: `EG.Defs.HB.Witness`, `EG.Defs.HB.SplitTree`, `EG.Defs.HB.Round`, `EG.Defs.HB.Run`, `EG.Lib.HB.SplitTree`, `EG.Lib.HB.Run`;
- to `EGTest`: `EGTest.HB`.

Size: Defs 1059 lines (Witness 129, SplitTree 245, Round 321, Run 364), Lib 760 lines, tests 359 lines.

## Definitions, with the manuscript text

### `EG/Defs/HB/Witness.lean` (s2:defWitness, s2:defTauRules; s2.tex:41–133)

**`IsWitness H ε s U F`** = `U ⊆ V(H) ∧ F ⊆ E(H) ∧ 1 ≤ |U| ∧ |U| ≤ 2|H|/3 ∧ |F| ≤ s|U| ∧ |Nbr_{H−F}(U)| < ε|U|/log₂²|H|`.

> "A *witness* at H is a pair (U,F) with U⊆V(H) and F⊆E(H) such that 1≤|U|≤(2/3)m, |F|≤s|U|, |Nbr_{H−F}(U)|<ε|U|/log²m."

- The six conjuncts use the same casts and forms as `FGraph.IsExpander` (blueprint WIT-HYP-ORDER).
- `EG.HB.not_isExpander_iff_exists_isWitness` (Lib) is proved by `push Not; rfl`, which checks that the definition is literally the negated body of `IsExpander`.
- `ε` is a parameter (blueprint WIT-EPS-PARAM). Statements use `EG.epsC`.
- The definition does not assume that H is not an expander. "Since H is not an (ε,s)-expander, a witness exists" is the lemma above.

**`witN H U F := (H.deleteEdges F).nbrSet U`** ("N := Nbr_{H−F}(U)").

**`witF0 H U N := H.edgesBetween U (V(H) \ (U ∪ N))`** ("F_0 := E_H(U, V(H)∖(U∪N))").
- It takes N, not F. This makes Fact (c) of defTauRules ("depend only on (U,N)") definitional (blueprint TAU-SIGNATURE-UN).

**`splitFst H U' N'' := H[U' ∪ N'']`, `splitSnd H U' N'' := H[V(H)∖U'] − E(H[N''])`, `splitDel H U' N'' := E_H(U', V(H)∖(U'∪N''))`.**

> lemSEP: "H_{ν_1}=H_ν[U'_ν∪N''_ν], H_{ν_2}=H_ν[V(H_ν)∖U'_ν]−E(H_ν[N''_ν]), and the *deleted set* at ν is F''_ν := E_{H_ν}(U'_ν, V(H_ν)∖(U'_ν∪N''_ν))"; (eqSplit): "G_1=H[U'∪N''], G_2=H[V∖U']−E(H[N''])".

- These are the forms of Lemma SEP, and both levels of the two-level recursion use them (blueprint TAU-DEFINE-BY-EQSPLIT).

**τ-rules** (rules (1), (2)), all functions of `(H, U, N, τ)`:
- `tauHout := {v ∈ U : τ ≤ deg_{F_0}(v)}` ("H_out := {v∈U : deg_{F_0}(v) ≥ τ}");
- `tauU1 := U ∖ H_out` ("U' := U∖H_out");
- `tauN1 := N ∪ H_out` ("N' := N∪H_out");
- `tauF1 := E_H(U', V∖(U'∪N'))` ("F_1 := E_H(U', V∖(U'∪N'))");
- `tauHin := {x ∈ V∖(U'∪N') : τ ≤ deg_{F_1}(x)}` ("H_in := {x∈V∖(U'∪N') : deg_{F_1}(x) ≥ τ}");
- `tauN2 := N' ∪ H_in` ("N'' := N'∪H_in");
- `tauF2 := splitDel H U' N''` ("F'' := E_H(U', V∖(U'∪N''))"; this is the deleted set).

The comparison "deg ≥ τ" is the real inequality `τ ≤ (degE F v : ℝ)` (blueprint TAU-REALCOMPARE). The definitions are total for every real τ; the manuscript's "τ > s" is a hypothesis of the statements, not of the definitions (blueprint TAU-TAU-GT-S-UNUSED).

**`tauG1 := H[U'∪N''] − F''`, `tauG2 := H − U' − E(G_1) − F''`.**

> "The *split of H by the τ-rules* has the two children G_1 := H[U'∪N'']−F'' and G_2 := H−U'−E(G_1)−F''".

- These are the literal children. The Spec layer can state (eqSplit) as `tauG1 = splitFst`, `tauG2 = splitSnd` (TauEqSplitStatement in blueprint_s2a). The trees use `splitFst`/`splitSnd`.

### `EG/Defs/HB/SplitTree.lean` (s2:lemSEP, s2:lemThinCut, s2:lemOVgeneric, s2:lem14tau)

**`Addr := List Bool`** is a node address: `false` means the first child and `true` the second (TRIAGE §2.1).

**`inductive STree V | nil | node (p : Finset V × Finset V) (l r : STree V)`.**

> "A *split recursion* on a graph H_0 is a finite rooted binary tree whose nodes ν carry graphs H_ν, with H_ν=H_0 at the root, such that at every non-leaf node ν there are disjoint sets U'_ν, N''_ν ⊆ V(H_ν) for which the two children ν_1, ν_2 of ν carry …"

- The tree stores the choices only. The graphs are computed (PLAN §3 decision 5).
- Decision D-HB-2 below: this is a separate inductive type, not the TRIAGE `BinaryTree` abbreviation.

**Addresses and labels.**
- `nodeAddrs`, `leafAddrs` ("call the leaf nodes *leaves*"), `internalAddrs`.
- `labelAt t a : Option (Finset V × Finset V)` gives `(U'_a, N''_a)` at a non-leaf node.
- `labelU`, `labelN` give ∅ elsewhere.
- `subtreeAt` is provided.

**`graphAtD t H₀ a`** is H_a, computed by folding `splitFst`/`splitSnd` along a.
- It is total: an address that runs past a leaf returns that leaf's graph (D-HB-3).

**`delAt t H a := splitDel H_a U'_a N''_a`** ("the deleted set at ν is F''_ν").

**`WF t H`**: for every internal a, `U'_a, N''_a ⊆ V(H_a)` and they are disjoint ("there are disjoint sets U'_ν, N''_ν ⊆ V(H_ν)"). This is needed because `induce` intersects with the vertex set (blueprint SEP-INCLUSION-HYP).

**`leafMass t H := Σ_{a ∈ leafAddrs} |H_a|`** ("the total size of the leaves"). Leaves are counted by address.

**`dup t H := {v ∈ V(H) : #{a ∈ leafAddrs : v ∈ V(H_a)} ≥ 2}`** ("Let Dup be the set of vertices lying in at least two leaves").
- Leaves are counted by address, so "distinct leaf nodes are distinct leaves even if their vertex sets coincide".
- Filtering V(H₀) loses nothing, because node graphs are subgraphs of the root (`STree.graphAtD_le`).

**`deleted t H := ⋃_{a internal} F''_a`** ("A *deleted edge* is an edge of some F''_ν").

**`DeltaGe t H M := Σ_{a internal, M ≤ |H_a|} |N''_a|`** ("Δ_{≥M} := Σ_ν |N''_ν|, the sum over the non-leaf nodes ν with |ν| ≥ M").
**`dupGe t H M v := #{a internal : M ≤ |H_a|, v ∈ N''_a}`** ("dup_{≥M}(v) be the number of non-leaf nodes ν with |ν|≥M and v∈N''_ν").
In both, M is real.

**`OVHyp ε c t H`**: `WF` and, at every internal a, `2 ≤ |H_a|`, `|H_{a++[false]}| ≤ (3/4)|H_a|` and `|N''_a| ≤ cε|U'_a|/log²|H_a|`.

> "such that at every non-leaf node ν, with m:=|ν|, m≥2, |ν_1|≤(3/4)m, |N''_ν|≤cε|U'_ν|/log²m"

- "n_0 ≥ 1" is omitted (blueprint OV-N0-POS).

**`graft t f`**: at every leaf a of t, attach f a; a node b of f a gets the address a ++ b.

> (R3) "The *two-level recursion* of round l is the split recursion obtained from the s=0 recursion by attaching, at every piece 𝒫 with |𝒫|≥P_l, the tree of its τ-run."

**`leafPrefix t x`** is the leaf of t on the path x, that is, the piece above a node of the two-level tree. `leafPrefix_append` in Lib: `t.leafPrefix (a ++ b) = a` for a leaf a.

**`StopsAt t H P`**: for every a ∈ nodeAddrs, `a ∈ leafAddrs ↔ P H_a`.
- It quotes (R3) "a node is a leaf iff its graph is an (ε,0)-expander" and 14^τ "stops if H is an (ε,s)-expander (the node is then a leaf)".
- It has both directions (blueprint HB-STOPRULE).

**`IsS0Rec ε t H`**: `WF`, and at every internal a there is a witness (U,F) with parameter 0 such that `labelAt a = some (U, Nbr_{H_a}(U))`.

> "Call a split recursion an *s=0 recursion* if at every non-leaf node ν there is a witness (U_ν,F_ν) at H_ν with parameter s=0 and U'_ν=U_ν, N''_ν=Nbr_{H_ν}(U_ν)."

**`IsTauSplitTree ε τ t H`**: `WF`, and at every internal a there are s < τ and a witness with parameter s whose τ-rule sets `(tauU1, tauN2)` at `N = witN` are the label. This is the hypothesis of lemThinCut:

> "at each non-leaf node ν there are s_ν<τ and a witness at H_ν (with parameter s_ν) whose τ-rules give U'_ν and N''_ν".

**`IsTauRun ε (s : ℕ) τ t H`** is `WF ∧ StopsAt (IsExpander ε s) ∧` (at every internal a there is a witness with parameter s whose τ-rule sets are the label).

> "The *τ-run* of H_0 (with parameters s,τ) is the recursion that, at a node H, stops if H is an (ε,s)-expander (the node is then a leaf), and otherwise picks any witness (U,F) at H with parameter s and splits H by the τ-rules at threshold τ."

- "For every choice of witnesses" means every tree that satisfies the predicate.
- The lemma's hypotheses (s ≥ 1, τ ≥ 128 s log² n_0) are not part of it.

**`cOV := log₂(4/3)`** ("put c_OV := log₂(4/3)").

### `EG/Defs/HB/Round.lean` (s2:defHBtp (R0)–(R5), (GC); s2.tex:503–598)

**Parameters** (functions of the real d = d_l):

| Lean | Manuscript |
|---|---|
| `lamOf d := log₂ d` | "(R0) Otherwise put λ_l := log d_l" |
| `tHBOf d := log₂² d` | "(R1) t^HB_l := log² d_l" |
| `TOf d := tHBOf d * d` | "a cycle of length at least t^HB_l d_l" |
| `MOf d : ℕ := ⌈max(2^40, 2^16 · TOf d · log₂⁴(TOf d))⌉₊` | "(R2) M_l := ⌈max(2^40, 2^16 t^HB_l d_l log⁴(t^HB_l d_l))⌉ ∈ ℕ" |
| `LamOf d := log₂ (MOf d : ℝ)` | "Λ_l := log M_l" (the logarithm of the integer) |
| `sOf d : ℕ := ⌈LamOf d ^ sigmaC⌉₊` | "s_l := ⌈Λ_l^σ⌉" |
| `POf d : ℕ := ⌈lamOf d ^ Cp⌉₊` | "P_l := ⌈λ_l^{C'}⌉" |
| `tauOf d : ℕ := ⌈128 · sOf d · log₂²(MOf d)⌉₊` | "τ_l := ⌈128 s_l log² M_l⌉" |
| `thetaGC d z : ℕ := ⌈z · lamOf d ^ (−1/2 : ℝ)⌉₊` | "(GC) θ^GC_l(Z^0) := ⌈|Z^0| λ_l^{−1/2}⌉" |

Types follow TRIAGE §2.1: M, s, P, τ and θ^GC are in ℕ; λ, t^HB, T and Λ are in ℝ. σ = `EG.sigmaC` and C' = `EG.Cp` are the locked constants. `thetaGC` is junk for λ ≤ 0; statements have λ > 1 under Γ.

**`structure RoundChoice V`** has four fields:
- `cycles : List (List V)`, the cycles Cyc_l;
- `tree0 : STree V`, the s=0 recursion;
- `tauRun : Addr → STree V`, the τ-run trees indexed by piece address;
- `homeOrder : List Addr`.

> "A *valid HB*^{τ+} run* is an execution of this procedure with any witnesses in both levels of (R3), any vertex order in (R1), and any home orders in (R4)."

**Round objects** (H = G_l, c the choices):
- **`Round.d H := 2|E(H)|/|H|`.** Quote: "(R0) d_l := 2|E(G_l)|/n". Here n = |V(G)| = |V(G_l)|, since "All graphs G_l, G'_l below have vertex set V(G)" (`Run.graph_verts`).
- **`cycEdges c`, `graph' H c := H − E(Cyc_l)`.** Quote: "The deleted cycles form Cyc_l; the remaining graph is G'_l".
- **`CyclesValid H c`** has three conditions:
  - every listed cycle is a WF cycle object with its edges in E(G_l) and length ≥ T_l;
  - the flattened edge list is `Nodup`, so the cycles are pairwise edge-disjoint;
  - `G'_l` has no WF cycle of length ≥ T_l.

  Quote: "(R1) … As long as the current graph contains a cycle of length at least t^HB_l d_l, delete one (the lexicographically first, for a fixed order of V(G)). The deleted cycles form Cyc_l; the remaining graph is G'_l. Thus G'_l has no cycle of length at least t^HB_l d_l." This is the TRIAGE §2.12 decision "(R1) as any maximal family".
- **`pieceAddrs c := c.tree0.leafAddrs`, `piece H c a := c.tree0.graphAtD (graph' H c) a`.** Quote: "Its leaves are the *s=0 pieces* 𝒫 of round l".
- **`twoLevel H c := c.tree0.graft (fun a => if P_l ≤ |piece a| then c.tauRun a else nil)`.** Quote: "(R3) … attaching, at every piece 𝒫 with |𝒫|≥P_l, the tree of its τ-run".
- **`X0 H c a := (twoLevel H c).graphAtD (graph' H c) a`, `Z0 := (X0 …).verts`.** Quote: "For a pre-part named Z, Z^0 denotes its vertex set and X^0_Z its leaf graph".
- **`prePartAddrs H c := (twoLevel H c).leafAddrs.filter (P_l ≤ |X0 a|)`.** Quote: "The *round-l pre-parts* are the leaves of the τ-runs with at least P_l vertices; equivalently, the leaves of the two-level recursion with at least P_l vertices". The definition uses the second form; the first form is a lemma (D-HB-9).
- **`DupStar H c := (twoLevel H c).dup (graph' H c)`.** Quote: "Dup*_l := the set of vertices lying in at least two leaves (of any size, singletons included) of the two-level recursion".
- **`mu H c w := #{a ∈ prePartAddrs : w ∈ Z0 a}`.** Quote (defAncestors): "μ_r(w) is the number of round-r pre-parts containing w".
- **`D H c := (⋃_a Z0 a).filter (2 ≤ mu ·)`.** Quote: "(R4) D_l := the set of vertices lying in at least two round-l pre-parts". `Round.mem_D`: `v ∈ D ↔ 2 ≤ μ(v)` ("so D_r = {w : μ_r(w) ≥ 2}").
- **`home H c v := c.homeOrder.find? (a ∈ prePartAddrs ∧ v ∈ Z0 a)`.** Quote: "Fix an order of the round-l pre-parts (the *home order*). For a vertex v lying in some pre-part, home(v)=home_l(v) := the first pre-part containing v". The value is `none` if v lies in no listed pre-part.
- **`guests H c a := (Z0 a ∩ D).filter (home · ≠ some a)`.** Quote: "The *guests* of a pre-part Z are S_Z := {v∈Z^0∩D_l : home(v)≠Z}".
- **`isL1 := 2|S_Z| ≤ |Z^0|`.** Quote: "(L1) |S_Z| ≤ |Z^0|/2".
- **`isL2 := ∀ u ∈ Z^0, |N_{G'_l[Z^0]}(u) ∩ S_Z| ≤ s_l/2`** (a real comparison). Quote: "(L2) every u∈Z^0 has at most s_l/2 neighbours in S_Z in the graph G'_l[Z^0]". The graph is G'_l[Z^0], not X^0_Z (blueprint HB-L2-GRAPH).
- **`isGC := ∀ x ∈ S_Z, |N_{X^0_Z}(x) ∩ (Z^0∖S_Z)| < θ^GC_l(|Z^0|)`.** Quote: "(GC) no x∈S_Z has at least θ^GC_l(Z^0) neighbours in Z^0∖S_Z in the graph X^0_Z".
- **`isLight := isL1 ∧ isL2 ∧ isGC`; `isGCPart := isL1 ∧ isL2 ∧ ¬isGC`.** Quote: "The pre-part Z is *light* iff (L1), (L2), (GC). Otherwise Z is *standalone*. A pre-part satisfying (L1) and (L2) but failing (GC) is a *GC-part*".
- **`Std H c := prePartAddrs.filter (¬ isLight)`.** Quote: "Std_l is the set of round-l standalone pre-parts".
- **`partVerts := if light then Z^0∖S_Z else Z^0`; `X := X^0_Z − S_Z`; `partGraph := if light then X else X0`.** Quote: "A light pre-part Z gives the *light part* with vertex set Z^0∖S_Z and graph X_Z := X^0_Z−S_Z"; Naming: "A *round-l part* is a light part or a standalone pre-part".
- **`assign H c e : Option Addr`** chains three steps with `Option.or`:
  1. the first a in the home order with `a ∈ prePartAddrs` and `e ∈ E(partGraph a)`;
  2. otherwise, the first light a with `e ∈ (partVerts a).sym2`;
  3. otherwise, the first standalone a with `e ∈ (Z0 a).sym2`.

  The value `none` means that e passes down. Quote: "(R5) (1) For every light pre-part Z the edges of X_Z are assigned to the light part Z; for every standalone pre-part Z the edges of X^0_Z are assigned to Z. … (2) Every edge not yet assigned whose ends both lie in some light part is assigned to the first such light part (in the home order). (3) Every edge not yet assigned whose ends both lie in Z^0 for some standalone pre-part Z is assigned to the first such pre-part. (4) Every other edge of G'_l passes down". See D-HB-12.
- **`E H c a := E(G'_l).filter (assign · = some a)`.** Quote: "E_l(Z) denotes the set of edges assigned at round l to Z".
- **`passed`, `next H c`** (vertex set V(H), edge set `passed`). Quote: "(4) … E(G_{l+1}) is the set of these edges".
- **`pieceOf c a := c.tree0.leafPrefix a`.** This is the piece above a node of the two-level recursion (propOrigin, s6 CONC).
- **`Round.Valid H c`** has these conjuncts:
  - `CyclesValid`;
  - `c.tree0.IsS0Rec ε (G'_l)`;
  - `c.tree0.StopsAt (G'_l) (IsExpander ε 0)`;
  - `∀ a ∈ c.tree0.leafAddrs, P_l ≤ |piece a| → (c.tauRun a).IsTauRun ε s_l τ_l (piece a)`;
  - `homeOrder.Nodup ∧ homeOrder.toFinset = prePartAddrs`.

  In all of them ε = `EG.epsC`. Quote: "(R3) Run an s=0 recursion on G'_l that stops exactly at (ε,0)-expanders: a node is a leaf iff its graph is an (ε,0)-expander, and otherwise any witness with parameter 0 is used. … Inside every piece with |𝒫|≥P_l, run the τ-run of 𝒫 with s=s_l and τ=τ_l, with any witnesses"; (R4) "Fix an order of the round-l pre-parts".

### `EG/Defs/HB/Run.lean` (s2:defHBtp loop, s2:defAncestors, s2:propOV ν_l, s2:lemTower ε_A and ψ, s2:lemLacunary (H))

**`structure Run V where rounds : List (RoundChoice V)`**, with `R := rounds.length` and `choice l := rounds.getD (l−1) default`.
- Rounds are 1-indexed (TRIAGE §2.1).
- `IsRound l := 1 ≤ l ∧ l ≤ R` is decidable.

**`graph G : ℕ → FGraph V`** is defined by `graph 0 = G` (junk) and `graph (l+1) = if IsRound l then Round.next (graph l) (choice l) else graph l`. So G_1 = G, G_{l+1} is `next` for l ∈ [1,R], and G_l is stationary for l ≥ R+1 (`graph_of_R_lt`). Quote: "Put G_1 := G. All graphs G_l, G'_l below have vertex set V(G)."

**Parameters:** `d G l := Round.d (graph G l)`, and `lam`, `tHB`, `T`, `M`, `Lam`, `s`, `P`, `tau`, `thetaGC` as `…Of (d G l)`.

**Round objects at the run level:**
- **Guarded** (`if IsRound l then Round.… else ∅ / 0 / none / []`): `cycles`, `cycEdges` (via `cycles`; fix round 2), `pieceAddrs`, `prePartAddrs`, `DupStar`, `mu`, `D`, `assign`, `E`.
- **Derived from guarded sets:** `Std := prePartAddrs.filter (¬ isLight)`.
- **Plain wrappers:** `graph'`, `tree0`, `tauRun`, `piece`, `twoLevel`, `X0`, `Z0`, `home`, `guests`, `isL1`, `isL2`, `isGC`, `isLight`, `isGCPart`, `partVerts`, `X`, `partGraph`, `pieceOf`.

See D-HB-16.

**`E0 G := E(G_{R+1})`.** Quote: "(R0) If d_l < D_*, stop, and put E_0 := E(G_l) and R := l−1".

**`Run.Valid run G Dstar := (∀ l ∈ Icc 1 R, Dstar ≤ d G l ∧ Round.Valid (graph G l) (choice l)) ∧ d G (R+1) < Dstar`.** This is TRIAGE §2.2, and `Valid` never contains Γ.

**`PartId := ℕ × Addr`.**
- `parts G := ⋃_{l∈[1,R]} {(l,a) : a ∈ prePartAddrs l}`. Quote (Naming): "A *round-l part* is a light part or a standalone pre-part of round l".
- `ancestors G := parts G`. Quote (defAncestors): "An *ancestor of round r* is either a light part Y of round r … or a standalone pre-part Y∈Std_r, GC-parts included". "Every ancestor corresponds to a distinct pre-part" is definitional.
- `lightParts`, `stdParts`, and `ancestorsUpTo G k` (rounds ≤ k, for s6 c^agg).

**Ancestor data:**
- `ancVerts G Y := partVerts G Y.1 Y.2`. Quote: "V(Y) := Y (the vertex set Y^0∖S_Y)" / "V(Y) := Y^0".
- `ancGraph`. Quote: "H_Y := X_Y" / "H_Y := X^0_Y".
- `ancEps`. Quote: "ε_Y := 2^{−6}" / "ε_Y := 2^{−5}".
- `ancS : ℝ`. Quote: "s_Y := s_r/2" / "s_Y := s_r".
- `ancRound Y := Y.1` ("r(Y)").
- `LY := log₂|V(Y)|` ("L_Y := log|V(Y)|").

**`anc G l x := ancestors.filter (Y.1 + 2 ≤ l ∧ x ∈ V(Y))`.**

> "For l≥3 and a vertex x, anc_l(x) := {Y : Y an ancestor of a round r≤l−2 with x∈V(Y)}, and anc_l(x) := ∅ for l≤2."

The condition is written as r + 2 ≤ l (TRIAGE §2.1). `anc_eq_empty_of_le_two` is the TRIAGE test.

**Ports:**
- `hubs := Z^0 ∩ D_l`. Quote: "A_Z := Z^0∩D_l".
- `ports := Z^0 ∖ D_l`. Quote: "U_Z := Z^0∖D_l".
- `fresh := ports.filter (anc_l · = ∅)`. Quote: "F_Z := {x∈U_Z : anc_l(x)=∅}".
- `classed := ports ∖ fresh`. Quote: "Q_Z := U_Z∖F_Z".

These are total over addresses; statements take a ∈ Std_l.

**Counts:**
- `dup G r := Σ_{w∈V(G)} (μ_r(w) − 1)` in ℕ. Quote: "dup_r := Σ_w(μ_r(w)−1)^+". Truncated subtraction is (·)^+.
- `mult G r w := #{a ∈ prePartAddrs r : w ∈ partVerts r a}`. Quote: "mult_r(w) is the number of ancestors Y of round r with w∈V(Y)".
- `nuAnc G l := #{Y ∈ ancestors : Y.1 + 2 ≤ l}`. Quote (propOV (K1)): "the number ν_l of ancestors of rounds at most l−2".
- `j0 G x := (Icc 1 R).filter (∃ a ∈ prePartAddrs r, x ∈ Z0 r a) |>.min : WithTop ℕ` and `j1` (light part, x ∈ V(Y)). Quote: "j_0(x) is the first round in which x lies in a pre-part, and j_1(x) the first round in which x lies in a light part (∞ if there is none)". The value is ⊤ when none exists (blueprint ANC-J0-INFTY).

**Functions of D_* and of reals:**
- `epsA D := 31 · epsC / (Cp · log₂ log₂ D)`. Quote (lemTower (e)): "ε_A := 31ε/(C' log log D_*), a function of D_* alone".
- `psiPool x := (6 log₂ x + 12)/x`. Quote (lemTower (b)): "ψ(x) := (6 log x + 12)/x".
- `HypH x0 F := ∀ x y, x0 ≤ x → x0 ≤ y → 2^{x/A} ≤ y → F y ≤ F x / 2`. Quote (lemLacunary (iii)): "if F:[x_0,∞)→[0,∞) satisfies (H) F(y)≤F(x)/2 whenever x≥x_0 and y≥2^{x/A}". See D-HB-20.

## Decisions (with reasons)

- **D-HB-1 (round-local API; signatures).** DR-ROUND-LOCAL is adopted: every round object is a function of `(H = G_l, c)`, and run objects are these applied to `(run.graph G l, run.choice l)`.
  - `Round.*` takes no `n` argument, because n = |V(G_l)| = |V(G)| (`Run.graph_verts`, `Run.d_eq`).
  - `Round.Valid H c` takes no `Dstar`, because D_* enters only through the stopping test of (R0), which is in `Run.Valid`.
  - This is a simplification of the TRIAGE signature `Round.Valid n H Dstar c`, with the same content. Round-level Specs (lemCap(ii), propOV, propDegRec) add `Dstar ≤ Round.d H`, and propExists quantifies over choice lists.
- **D-HB-2 (`STree` is its own inductive).** TRIAGE says `BinaryTree (Finset V × Finset V)`.
  - With an `abbrev`, terms built with `BinaryTree.node`/`nil` have type `BinaryTree …`, and generalized field notation (`t.IsTauRun`, `(…).graphAtD`) fails on them. This was observed during the build.
  - The inductive has the same shape and constructor names `nil`/`node p l r`.
- **D-HB-3 (`graphAtD` is total).** An address that continues below a leaf returns the leaf's graph, and `[]` returns the root. Only node addresses are meaningful, and statements quantify over `nodeAddrs`/`leafAddrs`/`internalAddrs`.
- **D-HB-4 (children).** Trees always use `splitFst`/`splitSnd`, the SEP forms. The literal τ-split children `tauG1`/`tauG2` are Defs, so that (eqSplit) can be a Spec.
- **D-HB-5 (`witF0` takes N).** This makes defTauRules Fact (c) definitional.
- **D-HB-6 (`IsWitness`).** The conjuncts are the literal negated body of `IsExpander`. `not_isExpander_iff_exists_isWitness` is proved by `push Not; rfl`.
- **D-HB-7 (types).** τ is real in the τ-rules; s is `ℕ` in `IsTauRun` ("s≥1 an integer"; s_l ∈ ℕ). The witness parameter is real.
- **D-HB-8 ((R1) as any maximal family).** This is TRIAGE §2.12. It enlarges the set of valid runs, which strengthens every ∀-run statement.
  - The length of a cycle is its number of vertices, which equals its number of edges.
  - Pairwise edge-disjointness is expressed as `Nodup` of the flattened cycle edges.
- **D-HB-9 (pre-parts).** Pre-parts are defined as the leaves of the two-level recursion with at least P_l vertices (the "equivalently" form). The τ-run-leaf form is a later lemma, provable from `mem_leafAddrs_graft` and `graphAtD_graft_append`.
- **D-HB-10 (D_l).** D_l is the union of the pre-part vertex sets, filtered by μ ≥ 2. This is literally "vertices lying in at least two pre-parts", and `mem_D` gives D = {μ ≥ 2}.
- **D-HB-11 (home order).** `home` is `find?` on `homeOrder`, restricted to pre-part addresses. `Round.Valid` requires `homeOrder` to be duplicate-free with entry set = pre-parts. This is what lemEL needs (blueprint EL-HOMEORDER-COMPLETE).
- **D-HB-12 ((R5) as one assignment function).** `assign` is a single `Option Addr`. `E` and `passed` are filters of it, so the per-round partition is definitional (blueprint STR-PARTITION-ENCODING). The step priority is implemented by `Option.or`.
  - Step (1) takes the first pre-part in the home order whose part graph contains e. Its uniqueness (SEP(i)) is a lemma, not an assumption (HB-EMBEDDED-CLAIMS).
  - Step (3)'s "first such pre-part" is taken in the home order (TRIAGE §2.12, HB-R5-ORDER).
- **D-HB-13 (GC does not feed back).** `prePartAddrs`, `mu`, `D`, `home` and `guests` do not mention `isLight`/`isGC`. This is the design constraint of TRIAGE §2.2, lemGC(i) and EX-GC-DEFINITIONAL, and the Defs reviewer can check it by reading `Round.lean`.
- **D-HB-14 (`Run` is a one-field structure).** TRIAGE writes `Run V := List (RoundChoice V)`. A structure keeps `run.R`, `run.graph`, … unambiguous and prevents `List` API from leaking in. Construct runs with `⟨[c₁, …, c_R]⟩`.
- **D-HB-15 (1-indexing and stationarity).**
  - `choice l = rounds[l−1]`.
  - `graph G 0 = G` is a junk value; no statement should use round 0.
  - `graph` is stationary for l ≥ R+1, and `graph_edges_subset_of_le` gives antitonicity for all l (lemEL, propOrigin, s5/s6).
- **D-HB-16 (guards).** The index sets and counts vanish outside [1,R]: `pieceAddrs`, `prePartAddrs`, `Std`, `D`, `DupStar`, `mu`, `E`, `assign` (none), `cycles` ([]), and hence `parts`, `mult`, `anc`, `hubs`.
  - Without the guards, a round l > R would use the default choice, and its single two-level leaf could be a "pre-part" (TRIAGE §2.1 requires Std_l = ∅ and E_l = ∅ for l > R).
  - Per-address wrappers (`Z0`, `guests`, `isLight`, `partVerts`, `X0`, …) are not guarded and are meaningful only for addresses in `prePartAddrs G l`. **Spec authors must bound addresses by `a ∈ run.prePartAddrs G l` (or `run.Std G l`, `run.lightParts G`)**, as the manuscript does.
- **D-HB-17 (parts = ancestors).** Both are the same `Finset PartId`. Ancestors are exactly the parts, since every pre-part gives one part. Both names exist because the manuscript uses both words.
- **D-HB-18 (anc offset).** The offset is written `Y.1 + 2 ≤ l` with rounds ≥ 1 (ANC-ROUND-OFFSET). The TRIAGE test `anc G l x = ∅` for l ≤ 2 is `Run.anc_eq_empty_of_le_two`, and it is instantiated in `EGTest/HB.lean`.
- **D-HB-19 (j0, j1).** Both are `WithTop ℕ` via `Finset.min` (⊤ if there is none), so the definitions contain no proof terms.
- **D-HB-20 (`HypH` domain).** F : [x_0,∞) → [0,∞) becomes a total `ℝ → ℝ`, and its domain is kept as the hypotheses `x0 ≤ x` and `x0 ≤ y`.
  - This is the literal reading: (H) is only meaningful for arguments in the domain.
  - The proof of (iii) needs it only at y = λ_r ≥ x_0.
  - It is weaker than the unrestricted form, so (iv) is easier to prove and (iii) is still provable.
  - Nonnegativity is a separate hypothesis.
- **D-HB-21 (no `irreducible_def`).** Mathlib's `irreducible_def` expands to an `opaque` declaration (checked in `Mathlib/Tactic/IrreducibleDef.lean`), and the lint forbids `opaque`. The derived objects are plain `@[expose]` defs with characterization lemmas. They reduce by `decide`/`rfl` in tests, as needed for the K_3 run.
- **D-HB-22 (parameter forms).**
  - `TOf d := tHBOf d * d` follows the manuscript's order t^HB_l d_l. TRIAGE writes `d * log² d`; the two are equal by commutativity.
  - M_l uses the v6.1 ceiling. Λ_l is the log of the cast integer.
  - s_l and P_l use the locked `sigmaC` and `Cp`.
- **D-HB-23 (`dup` of a split tree).** It filters V(H₀). All leaf vertex sets lie in V(H₀) (`graphAtD_le`), so this is exact.
- **D-HB-24 (`OVHyp` is a Def).** It is the hypothesis list of Lemma OV, used by the OV Spec and by lem14tau(b). `n_0 ≥ 1` is omitted because it is unused.
- **D-HB-25 (not defined here; left Spec-local, as proposed by the blueprints).** These are left out: `EdgeSrc`/`srcEdges` (propStructure), `TypeBeta`/`TypeAlpha` (propOrigin), `lightIncidences`/`Parentless` (propParentless), `IsClassedPort` (s7a), and `KJS`/`KHUB`/`tJS` (s3/s7 Defs).
  - Each is a one-line function of the objects above.
  - `pieceOf`, `DupStar`, `tauRun`, `piece`, `run.tau` and `run.mult` are provided for them.

## API (`EG/Lib/HB/*`)

- **SplitTree:**
  - `not_isExpander_iff_exists_isWitness`, `witN_subset_verts`, `disjoint_witN`, `witF0_subset`;
  - `splitFst_verts`, `splitSnd_verts`, `splitFst_le`, `splitSnd_le`, `splitDel_subset`, `tauU1_subset`, `tauHout_subset`;
  - structural simp lemmas for `labelAt`/`nodeAddrs`/`leafAddrs`/`internalAddrs`/`graphAtD`/`graft`/`leafPrefix`;
  - `nodeAddrs_eq_union`, `disjoint_leafAddrs_internalAddrs`, `labelAt_isSome_of_mem_internalAddrs`;
  - `graphAtD_le` (SEP (0'): node graphs are subgraphs of the root), `graphAtD_verts_subset`, `graphAtD_edges_subset`, `dup_subset`, `mem_dup`, `deleted_subset`;
  - the one-leaf tree: `leafMass_nil`, `dup_nil`, `deleted_nil`, `wf_nil`, `stopsAt_nil_iff`, `isS0Rec_nil`, `isTauRun_nil_iff`;
  - graft: `graft_nil_fun`, `leafPrefix_append`, `graphAtD_graft_append`, `labelAt_graft_append`, `labelAt_graft_of_mem_internalAddrs`, `graphAtD_graft_of_mem_nodeAddrs`, `mem_leafAddrs_graft`, `leafPrefix_mem_of_mem_leafAddrs_graft`.
- **Run (round level):**
  - `graph'_verts`, `graph'_le`, `next_verts`, `next_edges`, `next_le_graph'`, `next_le`;
  - `mem_E`, `mem_passed`, `passed_subset`, `E_subset`, `disjoint_E`, `mem_passed_or_mem_E`, `disjoint_passed_E`;
  - `assign_mem` (only listed pre-parts), `mem_prePartAddrs_of_mem_E`;
  - `mem_D`, `guests_subset`, `partVerts_subset`, `mem_Std`.
- **Run (run level):**
  - recursion: `graph_zero`, `graph_one`, `graph_succ_of_isRound`, `graph_succ_of_not_isRound`, `graph_verts`, `card_graph`, `graph'_verts`, `d_eq`, `graph_succ_le`, `graph_le_of_le`, `graph_edges_subset_of_le`, `graph_of_R_lt`;
  - guards: `isRound_of_mem_prePartAddrs`, `prePartAddrs_of_isRound`, and the `*_of_not_isRound` lemmas;
  - parts and ancestors: `mem_D_iff`, `mem_Std_iff`, `mem_parts`, `mem_ancestors`, `isRound_of_mem_parts`, `mem_lightParts`, `mem_stdParts`, `mem_anc`, `anc_eq_empty_of_le_two`, `fresh_eq_ports_of_le_two`, `nuAnc_eq_zero_of_le_two`, `partVerts_subset_Z0`, `mult_le_mu`;
  - validity: `Valid.dstar_le`, `Valid.round`, `Valid.stop`, `valid_nil_iff`.

## Tests (`EGTest/HB.lean`)

- **Parameters at d = 2:** t^HB = 1, T = 2, M = 2^40, Λ = 40, s = 40^100, P = 1.
- **The run without rounds:** it is valid on the edgeless `Fin 2` graph with D_* = 1, and not valid with D_* = 0.
- **Non-vacuity of `Run.Valid` with one round** (`run1_valid`).
  - The setup: G = K_3 on `Fin 3`, D_* = 1. Then d_1 = 2, T_1 = 2 and P_1 = 1.
  - (R1): the cycle `[0,1,2]` has length 3 ≥ 2 and must be removed, leaving G'_1 edgeless.
  - (R3) first level: the s=0 tree splits off `{0}` and then `{1}` with the witnesses ({v}, ∅), giving three one-vertex pieces. Each piece is an expander (|·| ≤ 1). The internal nodes are not expanders, which is shown via the witness.
  - (R3) second level: the τ-runs are single leaves.
  - The pre-parts are the three leaves. The home order lists them.
  - d_2 = 0 < 1, so R = 1.
  - Every component of `Round.Valid` is checked, including both directions of the stopping rule.
  - On this run: `D_1 = ∅`, there are no guests, all three pre-parts are light, `Std_1 = ∅`, `lightParts = {(1,[false]),(1,[true,false]),(1,[true,true])}`, `prePartAddrs 2 = ∅`, `anc_2 = ∅` and `E_0 = ∅`.
  - This D_* violates Γ. A valid run under Γ is s2:propExists, a later proof task.
- **Negative tests:**
  - dropping the long cycle violates (R1) maximality;
  - stopping the s=0 recursion at the non-expander root violates the stopping rule;
  - a single-leaf τ-run at a non-expander is not a τ-run.

## Notes for Spec authors and reviewers

- Specs over runs read `∀ Dstar (Γ-items), ∀ G run, run.Valid G Dstar → …` (HB-DSTAR-PARAM). `Run.Valid` contains no Γ.
- Bound addresses by `run.prePartAddrs G l` / `run.Std G l` / `run.lightParts G` / `run.ancestors G` (D-HB-16). Bound tree addresses by `nodeAddrs`/`leafAddrs`/`internalAddrs`.
- Round offsets are written `r + 2 ≤ l`. `run.lam G (l-2)` etc. need `3 ≤ l`, as in the manuscript.
- Four different "dup" objects exist (ANC-DUP-POSPART / OV-DUP-NAMES):
  - `STree.dup` (the vertex set Dup of one split recursion);
  - `run.DupStar` (Dup*_l);
  - `run.dup` (the number dup_r);
  - `STree.dupGe` (dup_{≥M}(v)).
- **Argument shapes (name map; fix round 2, review 2 issue 1).**
  - Ancestor data takes `Y : PartId`: `run.LY G Y`, `run.ancVerts G Y`, `run.ancGraph G Y`, `run.ancEps G Y`, `run.ancS G Y` (write `run.LY G (r, a)`, not `run.LY G r a` or `run.LY G Y.1 Y.2`).
  - Choice-only objects take no `G`: `run.R`, `run.choice l`, `run.cycles l`, `run.cycEdges l`, `run.tree0 l`, `run.tauRun l q`, `run.pieceAddrs l`, `run.pieceOf l a` (blueprints s2a/s2b/s7a write `run.R G`, `run.pieceAddrs G l`, `run.pieceOf G r Y`).
  - Everything that depends on the graphs takes `G` first: `run.piece G l q`, `run.bigPieceAddrs G l`, `run.prePartAddrs G l`, `run.X0 G l a`, …
  - Renames: `run.Mr G l` → `run.M G l`; `run.H Y` → `run.ancGraph G Y`; `run.allAncestors G` / `run.ancestorSet G` → `run.ancestors G`; `run.isStd Y` → `Y ∈ run.stdParts G`; `EG.HB.psi` → `EG.HB.psiPool`.
- `E(Cyc_l)` is `run.cycEdges l` (guarded; `graph'_eq_deleteEdges` at a round). Do not use the unguarded `Round.cycEdges (run.choice l)` in run-level statements (at `l = 0` it is round 1's set).
- (GC) counts `|N_{X^0_Z}(x) ∩ (Z^0 \ S_Z)|`; the lemGC sketches' `eBetween {x} W` form is `Run.isGC_iff_eBetween` / `FGraph.card_nbrs_inter_eq_eBetween`.
- `run.isLight` and the other per-address wrappers are `Prop`s. Filters over them use classical decidability (`open Classical in`). In proofs, use `classical` and `simp only [..., Finset.mem_filter]` rather than `rw [Finset.mem_filter]`.

## Manuscript issues

None new. The known T0 items handled here are:
- (R1) as any maximal family;
- (R5)(3) in the home order;
- j_0 = ∞ convention;
- the stopping rule in both directions;
- Lemma 14^τ hypotheses not in `Valid`;
- the round offset r + 2 ≤ l.

The (H) domain reading (D-HB-20) is a Lean-side reading, not a manuscript defect.

## Fix round 1 (review `work/p2d/hb.review1.md`, verdict APPROVE; all 9 issues checked)

All nine issues are valid. Every one is fixed. None changes the meaning of an existing Def. Two Defs were added or changed in form; both are documented below.

| # | Sev. | Verified | Fix |
|---|---|---|---|
| 1 | minor | yes: the lemmas were missing | Added to `EG/Lib/HB/Run.lean`, at round level (`Round.*`) and run level (`Run.*`). See the list below. |
| 2 | minor | yes: `tauRun` is unconstrained off the big pieces | **New Defs.** `Round.bigPieceAddrs H c := (pieceAddrs c).filter (P_l ≤ \|piece\|)` and `Run.bigPieceAddrs G l := (run.pieceAddrs l).filter (run.P G l ≤ \|run.piece G l ·\|)`. The latter is `∅` outside [1,R] via `pieceAddrs`. The docstrings of `Run.tauRun`, `RoundChoice.tauRun` and the Lib header now say: "read `tauRun` only at `q ∈ bigPieceAddrs`". `Run.Valid.isTauRun` gives the τ-run property there. |
| 3 | minor | yes | **Def form changed.** `Run.thetaGC` now takes the address: `run.thetaGC G l a := EG.HB.thetaGC (run.d G l) (run.Z0 G l a).card`, which is blueprint s6b's `run.thetaGC G r a` and the manuscript's θ^GC_l(Z^0). The numeric form `EG.HB.thetaGC d z` is unchanged; it is used by `Round.isGC` and by blueprints s2b/s3b. `Run.thetaGC_eq` (rfl) bridges the two. Nothing used the old `Run.thetaGC G l z`. |
| 4 | minor | yes | Both scratch tests are added to `EGTest/HB.lean`, in the namespaces `TauRunTest` and `OverlapTest`. They reuse the file's `K3`, `d_K3`, `POf_two` and `LamOf_two`. Also added: `12 ∈ passed`, `01 ∈ E [false]`, `E [true] = ∅` (via `E_subset_sym2`), and the pieces of `run1` (`bigPieceAddrs = all three leaves`, `pieceOf`, `pieceOf_mem_bigPieceAddrs`, `thetaGC` address form). |
| 5 | cosmetic | yes: `choice 0 = rounds[0]` | Docstring of `Run.choice` now states it and says why it is harmless. The Def is unchanged; `if l = 0` would only move the junk value. |
| 6 | cosmetic | yes | The Witness module doc now cites `EG.Lib.HB.SplitTree`. |
| 7 | cosmetic | yes | The Run module doc now reads "stationary for `l ≥ R + 1`". |
| 8 | cosmetic | yes | The Def keeps the manuscript's literals 2^{-6}/2^{-5}, which are the most faithful form. Added Lib lemmas `Run.ancEps_of_isLight : ancEps = epsC / 2` and `Run.ancEps_of_not_isLight : ancEps = epsC`. |
| 9 | cosmetic | yes | Added a note in the `EG.Lib.HB.SplitTree` header, and the lemma `isWitness_natCast_iff`. The τ-run test uses `rw [Nat.cast_one]` as documented. |

New Lib lemmas for issue 1. Each exists at round level (`EG.HB.Round`, arguments `H c`) and at run level (`EG.HB.Run`, arguments `run G l`) unless noted.
- **Leaf and part graphs:**
  - `X0_le_graph'` (X^0_Z ≤ G'_l);
  - `X0_le` / `X0_le_graph` (≤ G_l);
  - `X0_verts` (simp);
  - `Z0_subset_verts` (Z^0 ⊆ V(G_l), and at run level ⊆ V(G));
  - `X_le_X0`, `X_verts` (round level only);
  - `partGraph_verts` (V(partGraph) = V(Z));
  - `partGraph_le_X0`, `partGraph_le_graph'`;
  - `Run.ancGraph_verts` (V(H_Y) = V(Y)).
- **E_l(Z):**
  - `E_subset_sym2 : E_l(Z) ⊆ (partVerts Z).sym2`, proved through the three `Option.or` steps of `assign`;
  - `mem_partVerts_of_mem_E`;
  - `Run.E_subset_graph'_edges`.
- **Pieces:**
  - `mem_bigPieceAddrs`, `bigPieceAddrs_subset`;
  - `Run.bigPieceAddrs_of_isRound`, `Run.bigPieceAddrs_of_not_isRound`, `Run.pieceAddrs_of_isRound`;
  - `Round.prePartAddrs_subset_leafAddrs`;
  - `Round.X0_append` (graft);
  - `X0_append_of_mem_bigPieceAddrs`;
  - `pieceOf_mem_pieceAddrs`, `pieceOf_mem_bigPieceAddrs`.
- **First form of the pre-parts** (closes the "later lemma" of D-HB-9):
  - `exists_tauRun_leaf_of_mem_prePartAddrs`: a pre-part `a` is `q ++ b` with `q = pieceOf a` a big piece and `b` a leaf of `tauRun q`, and `X0 a = (tauRun q).graphAtD (piece q) b`;
  - the converse, `append_mem_prePartAddrs`.
- **Validity:** `Run.Valid.isTauRun` (on a valid run, the tree at a big piece is a τ-run with (ε, s_l, τ_l)).

Name map for Spec authors, in addition to the review's rename table:
- `run.bigPieceAddrs G l` now exists, as in blueprint s2b.
- `run.thetaGC G r a` is the address form, as in blueprint s6b.

Build state:
- `lake build EG.Lib.HB.Run` succeeds, and it rebuilds the Defs.
- `scripts/check.sh EGTest/HB.lean` reports 0 errors and no `sorry`.
- `python3 scripts/lint.py` reports 0 findings.
- `Axioms.lean --prefix EG EG.Lib.HB.Run` reports 0 violations.

## Fix round 2 (review `work/p2d/hb.review2.md`, verdict APPROVE; all 5 issues checked)

All five issues are valid; all are fixed. One Def was added (`Run.cycEdges`); no existing Def changed meaning (the only other Defs edit is the `POf` docstring).

| # | Sev. | Verified | Fix |
|---|---|---|---|
| 1 | minor | yes: the PartId-indexed Defs take `Y : PartId`, the choice-only Defs take no `G` | Name-map rows added under "Notes for Spec authors and reviewers" above and in `CONVENTIONS.md` (new section "The s2 hierarchy (EG.Defs.HB)"). No Def change. |
| 2 | minor | yes: `Round.cycEdges (run.choice l)` is unguarded (`run.choice 0 = run.choice 1`) | **New Def** `Run.cycEdges l := ((run.cycles l).flatMap cycleEdges).toFinset` (guarded through `run.cycles`, so `∅` outside `[1,R]`). Lib: `cycEdges_of_isRound` (`= Round.cycEdges (run.choice l)`), `cycEdges_of_not_isRound` (simp), `graph'_eq_deleteEdges` (`G'_l = G_l − E(Cyc_l)` at a round), `cycEdges_subset_graph_edges` (valid run). Tests: `run1.cycEdges 1 = E(K₃)`, `= ∅` at `l = 0, 2`. |
| 3 | minor | yes: the lemmas were missing (all are true for these Defs) | Added (no `sorry`). `EG/Lib/HB/SplitTree.lean`: `mem_internalAddrs_graft`, `append_mem_nodeAddrs_of_mem_internalAddrs`, `labelU/labelN_graft_of_mem_internalAddrs`, `labelU/labelN_graft_append`, `wf_graft`, `ovHyp_graft` (OVHyp transport: OV hypotheses of `t` and of every `f a` at its leaf graph give those of the graft), `delAt_graft_of_mem_internalAddrs`, `delAt_graft_append`, `deleted_graft`, `delAt_eq_empty_of_isS0Rec`, `deleted_eq_empty_of_isS0Rec`, `exists_mem_leafAddrs_mem_verts` (leaves cover the root), `mem_dup_iff_exists`, `dup_subset_dup_graft`, `dup_subset_dup_graft_of_mem_leafAddrs`, and `EG.FGraph.card_nbrs_inter_eq_eBetween` (`|N_X(x) ∩ W| = e_X({x}, W)`, no `x ∉ W` needed since graphs are loopless). `EG/Lib/HB/Run.lean`, round level: `wf_twoLevel`, `deleted_twoLevel` (`deleted(twoLevel) = ⋃_{q big} (tauRun q).deleted (piece q)` given `IsS0Rec`), `tree0_dup_subset_DupStar`, `tauRun_dup_subset_DupStar`, `existsUnique_piece_of_notMem_DupStar`, `isGC_iff_eBetween`; run level: `Valid.wf_twoLevel`, `Valid.deleted_twoLevel`, `tauRun_dup_subset_DupStar`, `tree0_dup_subset_DupStar`, `existsUnique_piece_of_notMem_DupStar`, `isGC_iff_eBetween` (with `run.thetaGC G l a`). |
| 4 | cosmetic | yes: `lamOf d ≤ 0` for `d ≤ 1` and `C' = 103` is odd, so `⌈λ^{C'}⌉₊ = 0` | `POf` docstring now states the junk value and why it is unreachable (`d_l ≥ D_* ≥ 2^{117}` under Γ). |
| 5 | cosmetic | yes | The reviewer's scratch test is added to `EGTest/HB.lean` as `namespace StandaloneTest` (duplicated parameter lemmas removed in favour of the file's `logb_two_two`, `POf_two`, `OverlapTest.sOf_two'`; `tree0`/`tauRun` renamed `t0`/`tauS`). It covers a standalone pre-part (`Std = {[true]}`), `Dup* = D = {0,1}`, `μ(0) = 2`, a `τ`-run deletion inside a round, (R5) steps (2) and (3), a passed-down guest–core edge and `E(next) = {03, 14}`. Added: `deleted(twoLevel) = {01}` and one `eBetween` evaluation. |

Build state:
- `lake build EG.Lib.HB.Run` succeeds (rebuilds `EG.Defs.HB.Round`, `EG.Defs.HB.Run`, `EG.Lib.HB.SplitTree`).
- `scripts/check.sh` on `EG/Lib/HB/SplitTree.lean`, `EG/Lib/HB/Run.lean`, `EGTest/HB.lean`: 0 errors, no `sorry`, no warnings.
- `python3 scripts/lint.py`: 0 findings.
