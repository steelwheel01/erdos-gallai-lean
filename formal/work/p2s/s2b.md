# P2 Specs, chunk s2b (s2: structure of a valid run, EL, overlap constants, degree recursion, existence, lacunary sums, tower facts, rule GC, ORIGIN^τ, parentless mass): status

Manuscript v6.1 `proofs/manuscript/s2.tex` lines 722–1533 (a CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s2b.md`, `nodes_s2b.json`; data model TRIAGE §2.1–§2.4, §2.12;
Defs `EG/Defs/HB/{Witness,SplitTree,Round,Run}.lean`, `EG/Defs/Log.lean`,
`EG/Defs/Gamma/Core.lean` (locked, not edited).

Result: 7 new Spec modules of this unit (22 `…Statement` defs), 1 test file, no new Defs, no
proofs, no stubs. Three of the modules (`Structure.lean`, `OVRun.lean`, `DegRec.lean`) were
written by the first (interrupted) run of this unit and committed by the orchestrator; this run
re-checked them against the TeX, built them, and added `Exists.lean`, `Lacunary.lean`,
`Tower.lean`, `Parentless.lean`. Many s2b nodes already had (partial) Specs from probes P3A, P3B,
P2J, P4A, P4B; these are reused, not restated.

Build: `lake build EG.Spec.HB.Structure EG.Spec.HB.OVRun EG.Spec.HB.DegRec EG.Spec.HB.Exists
EG.Spec.HB.Lacunary EG.Spec.HB.Tower EG.Spec.HB.Parentless`: success.
`scripts/check.sh EGTest/Spec_s2b.lean`: 0 errors, 0 sorry. `python3 -I scripts/lint.py`:
0 findings. No existing file of another unit edited. Root imports to add (I did not edit root
files): `EG.Spec.HB.Structure`, `EG.Spec.HB.OVRun`, `EG.Spec.HB.DegRec`, `EG.Spec.HB.Exists`,
`EG.Spec.HB.Lacunary`, `EG.Spec.HB.Tower`, `EG.Spec.HB.Parentless` to `EG`;
`EGTest.Spec_s2b` to `EGTest`.

## Table: label → Lean name → file → status

All names in namespace `EG.Spec`. "new" = written by this unit (s2b).

| label | Lean name(s) | file | status |
|---|---|---|---|
| s2:propStructure (i) | `StructureExpStatement` | `EG/Spec/HB/Structure.lean` | **new** (first run of s2b) |
| s2:propStructure (ii) | not restated: `CapPrePartStatement`, `CapRunTauStatement`, `CapRoundStatement` (s2:lemCap (ii)) | `EG/Spec/HB/CapPrePart.lean`, `CapRound.lean` | existing (P2J, s2a) |
| s2:propStructure (iii), clauses used by JS-LC/J⁺ | `StructureHYStatement` | `EG/Spec/HB/StructureHY.lean` | existing (P2J) |
| s2:propStructure (iii), the rest | `StructurePartitionStatement` | `EG/Spec/HB/Structure.lean` | **new** (first run) |
| s2:propStructure (iv), first clause (under `RunHyp`) | `StructureLightStatement` | `EG/Spec/HB/StructureLight.lean` | existing (P4B) |
| s2:propStructure (iv), all clauses | `StructureVertexStatement` | `EG/Spec/HB/Structure.lean` | **new** (first run) |
| s2:lemEL | `ELStatement` | `EG/Spec/HB/EL.lean` | existing (P3A) |
| s2:propOV (K1) incl. `ν_l`, run level | `OVK1Statement` | `EG/Spec/HB/OVRunK.lean` | existing (P3B) |
| s2:propOV (K3), run level | `OVK3Statement` | `EG/Spec/HB/OVRunK.lean` | existing (P3B) |
| s2:propOV leaf masses, (eqDupComposite), (K2), (F11), run level | `OVRunStatement` | `EG/Spec/HB/OVRun.lean` | **new** (first run) |
| s2:propOV all clauses except `ν_l`, round level | `OVRoundStatement` | `EG/Spec/HB/OVRun.lean` | **new** (first run) |
| s2:propDegRec bounds, round / run level | `DegRecRoundStatement`, `DegRecStatement` | `EG/Spec/HB/DegRec.lean` | **new** (first run) |
| s2:propDegRec kinds (a)–(c), counts, standalone clause, round / run level | `DegRecKindsRoundStatement`, `DegRecKindsStatement` | `EG/Spec/HB/DegRec.lean` | **new** (first run) |
| s2:propExists, (R1) and first level of (R3) terminate | `RoundStepsStatement` | `EG/Spec/HB/Exists.lean` | **new** |
| s2:propExists, τ-runs terminate with any witnesses | `RoundTauTermStatement` | `EG/Spec/HB/Exists.lean` | **new** |
| s2:propExists (proof), a valid round exists | `RoundExistsStatement` | `EG/Spec/HB/Exists.lean` | **new** |
| s2:propExists, `d_{l+1} < d_l`, R finite, every choice sequence terminates | `RunTerminatesStatement` | `EG/Spec/HB/Exists.lean` | **new** |
| s2:propExists, a valid run exists | `ExistsRunStatement` | `EG/Spec/HB/Exists.lean` | **new** |
| s2:propExists, "(GC) feeds back into nothing" | none (property of the Defs; checked: `Round.D/home/guests/prePartAddrs/Z0/X0` do not mention `isL1/isL2/isGC/isLight`) | — | design constraint, no Spec |
| s2:lemLacunary (i) | `LacunaryGeomStatement` | `EG/Spec/HB/LacunaryGeom.lean` | existing (P3B) |
| s2:lemLacunary (ii) | `LacunaryMonoStatement`, `LacunaryIIStatement` | `EG/Spec/HB/Lacunary.lean` | **new** |
| s2:lemLacunary (iii) | `LacunarySeqStatement`, `LacunaryRunStatement` | `EG/Spec/HB/Lacunary.lean` | **new** |
| s2:lemLacunary (iv) | `LacunaryExamplesStatement` | `EG/Spec/HB/Lacunary.lean` | **new** |
| s2:lemLacunary, all parts | `LacunaryStatement` (conjunction) | `EG/Spec/HB/Lacunary.lean` | **new** |
| s2:lemTower (a) | `TowerAStatement` | `EG/Spec/HB/TowerA.lean` | existing (P3B) |
| s2:lemTower (b), first sentence | `TowerBRoundStatement` | `EG/Spec/HB/TowerB.lean` | existing (P4A) |
| s2:lemTower (b), `M_l ≤ (A log λ_{l-2})^{2A} ≤ λ_{l-2}^{1.6}`, `Σ 1/M_l ≤ 2/D_*` | `TowerBMStatement` | `EG/Spec/HB/TowerBM.lean` | existing (P4B) |
| s2:lemTower (b), `P_{l-2} ≥ M_l^{13}`, `ν_l ≤ 2.74n/P_{l-2}` | `TowerBLateStatement` | `EG/Spec/HB/TowerBLate.lean` | existing (P2J) |
| s2:lemTower (b), `P_{l-2}/2 ≥ M_l log⁴M_l`, `M_{l-1} ≥ 2M_l`, `P_r ≥ 2P_{r+1}`, ψ-sum | `TowerBRestStatement` | `EG/Spec/HB/Tower.lean` | **new** |
| s2:lemTower (c) | `TowerCStatement` | `EG/Spec/HB/TowerC.lean` | existing (P3A) |
| s2:lemTower (d) | `TowerDStatement` | `EG/Spec/HB/Tower.lean` | **new** |
| s2:lemTower (e) | `TowerEStatement` | `EG/Spec/HB/Tower.lean` | **new** |
| s2:lemTower, all parts | `TowerStatement` (conjunction of the eight) | `EG/Spec/HB/Tower.lean` | **new** |
| s2:lemGC (i), second clause | `GCDefStatement` | `EG/Spec/HB/GC.lean` | existing (P3A) |
| s2:lemGC (i), first clause | none (order of definitions; Defs design constraint) | — | no Spec |
| s2:lemGC (ii), (iii) | `GCStatement` | `EG/Spec/HB/GC.lean` | existing (P3A) |
| s2:lemGC (iv) | `GCThetaStatement` | `EG/Spec/HB/GC.lean` | existing (P3A) |
| s2:propOrigin (a) | `OriginTypesStatement` | `EG/Spec/HB/Origin.lean` | existing (P3B) |
| s2:propOrigin (b) | `OriginThinStatement` | `EG/Spec/HB/Origin.lean` | existing (P3B) |
| s2:propOrigin (c) | = (K3): `OVK3Statement` | `EG/Spec/HB/OVRunK.lean` | existing (P3B) |
| s2:propOrigin (final paragraph) | `OriginGuestCapStatement` | `EG/Spec/HB/Origin.lean` | existing (P3B) |
| s2:propParentless (i) incl. (K4) | `FreshStatement` | `EG/Spec/HB/Parentless.lean` | **new** |
| s2:propParentless (ii) | `AdmissibleParentStatement` | `EG/Spec/HB/Parentless.lean` | **new** |
| s2:propParentless (iii) incl. "more precisely" | `ParentlessCountStatement` | `EG/Spec/HB/Parentless.lean` | **new** |
| s2:remTauConstants (+ Table s2:tabTauConstants) | none (no mathematical content used; right column proved in propOV, lem14tau(b), lemTower(b); left column neither used nor proved) | — | no Spec |

Coverage: every clause of every node has a statement (or is a Defs design constraint / remark,
listed). The existing Specs were checked for coverage and skimmed for faithfulness; they have
their own review records (`work/p2b/{P3A,P3B,P2J,P4A,P4B}.review*.md`). No problem found in them.

## New Specs: TeX next to a back-translation of the Lean

Common reading: `V : Type u` with decidable equality, `G : FGraph V` a finite simple graph,
`n = |V(G)|`, `run.Valid G D_*` (every round `l ∈ [1,R]` has `d_l ≥ D_*` and valid choices, and
`d_{R+1} < D_*`), rounds 1-indexed, `log = log₂`, `ε = 2^{-5}`, `A = 105`. "Round level" means:
an input graph `H` (= `G_l`) and round choices `c` with `Round.Valid H c` and `D_* ≤ d(H)`.

### `StructureExpStatement` (s2:propStructure (i))
TeX: "each `X^0_Z` is a `(2^{-5},s_l)`-expander on `Z^0`; each light `X_Z` is a
`(2^{-6},s_l/2)`-expander on the light part `Z`; every `H_Y` has minimum degree greater than
`s_Y`; and `s_r ≥ λ_r^{100}` for every `r ≤ R`."
Lean, read back: for every valid run with `D_* ≥ 2^{117}`: (1) for every round `l` and pre-part
`a`, `V(X^0_a) = Z^0_a` and `X^0_a` is a `(2^{-5}, s_l)`-expander; (2) for every light pre-part,
`V(X_a) = Z^0_a \ S_a` and `X_a` is a `(2^{-6}, s_l/2)`-expander (real `s_l/2`); (3) for every
ancestor `Y`, `V(H_Y)` is nonempty and every vertex of `H_Y` has degree `> s_Y`; (4) for every
round `r`, `λ_r ≤ Λ_r` and `λ_r^{100} ≤ s_r`.

### `StructurePartitionStatement` (s2:propStructure (iii), the clauses not in `StructureHYStatement`)
TeX: "`E(G_{l+1}) ⊆ E(G'_l) ⊆ E(G_l)` for every `l ≤ R`, so `d_{l+1} ≤ d_l`; and
`E(G) = ⨆_{l≤R} E(Cyc_l) ⊔ E_0 ⊔ ⨆_{Y light} E_{r(Y)}(Y) ⊔ ⨆_{l≤R} ⨆_{Z∈Std_l} E_l(Z)` (disjoint
unions); … the graphs `X^0_Z` of the pre-parts of one round are pairwise edge-disjoint;
`Σ_{l≤R}|Cyc_l| ≤ n`; and `|E_0| < D_* n/2`."
Lean, read back: for every valid run on `G` with `n ≥ 1` and `D_* ≥ 2^{117}`: for every round
`l`, `E(G_{l+1}) ⊆ E(G'_l) ⊆ E(G_l)` and `d_{l+1} ≤ d_l`; `E(G)` equals the union of the
`E(Cyc_l)` (`l ∈ [1,R]`), `E_0` and the `E_l(a)` over all light parts and all standalone
pre-parts `(l,a)`; the members are pairwise disjoint (cycle sets of distinct rounds; cycle sets
and `E_0`; cycle sets and part sets; part sets and `E_0`; distinct part sets); `X^0_a`, `X^0_b`
are edge-disjoint for distinct pre-parts `a ≠ b` of one round; the total number of listed cycles
over all rounds is at most `n`; `|E_0| < D_* n/2`.

### `StructureVertexStatement` (s2:propStructure (iv))
TeX: "light parts of one round are pairwise vertex-disjoint, and `|Y| ≥ |Y^0|/2 ≥ P_r/2` for every
light part `Y` of round `r`; every vertex outside `D_l` lies in at most one round-`l` pre-part;
the port sets `U_Z` of distinct `Z ∈ Std_l` are pairwise disjoint; and each vertex lies in at most
one light part per round, namely in the light part of `home_l(v)` if that pre-part is light."
Lean, read back: for every valid run (no condition on `D_*`) and round `l`: light parts of
distinct light pre-parts are disjoint; for a light pre-part, `|Z^0|/2 ≤ |Z^0 \ S|` and
`P_l/2 ≤ |Z^0|/2`; every `v ∉ D_l` lies in at most one pre-part `Z^0`; the port sets of distinct
standalone pre-parts are disjoint; every vertex of the light part of a light pre-part `a` has
`home_l(v) = a`; and at most one light pre-part of round `l` has `v` in its light part.

### `OVRoundStatement` (s2:propOV, round level) and `OVRunStatement` (run level, clauses not in `OVK1Statement`/`OVK3Statement`)
TeX: "Let `S_r` be the total size of the leaves of the two-level recursion of round `r`, and
`S^𝒫_r` the total size of the `s = 0` pieces. Then `S^𝒫_r ≤ 1.12 n` and `S_r ≤ 1.21 n`, and:
(K1) `Σ|Z^0| ≤ 1.37 n` …; `|Std_r| ≤ 1.37 n/P_r`; the number of ancestors of round `r` is at most
`1.37 n/P_r` …; (K2) `|D_r| ≤ dup_r ≤ 7.6 ε n/log P_r`, and
`Σ_{Z∈Std_r}|A_Z| ≤ Σ|Z^0 ∩ D_r| ≤ 2dup_r ≤ 15.2 ε n/log P_r` …; (K3) the total size `Σ|Z^0|` of the
round-`r` pre-parts failing (L1) is at most `30.4 ε n/log P_r`, and
`Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n/log P_r` …; (F11) `Σ_w mult_r(w) = Σ_Y |V(Y)| ≤ 1.37 n` …, and
`mult_r(w) ≤ μ_r(w)` for every vertex `w`"; proof, (s2:eqDupComposite): "for `M ≥ 2`,
`Δ_{≥M} ≤ 5.46 ε S_r/log M ≤ 6.61 ε n/log M`".
Lean, read back (round level): for `H`, `c` with `Round.Valid H c`, `D_* ≤ d(H)`,
`D_* ≥ 2^{117}`, `n = |V(H)|`: leaf mass of the `s = 0` tree `≤ 1.12 n`; leaf mass `S` of the
two-level tree `≤ 1.21 n`; for every real `M ≥ 2`, `Δ_{≥M} ≤ 5.46 ε S/log M ≤ 6.61 ε n/log M`;
`Σ_a |Z^0_a| ≤ 1.37 n`; `|Std| ≤ 1.37 n/P`; number of pre-parts `≤ 1.37 n/P`;
`|D| ≤ Σ_w (μ(w) − 1)^+ ≤ 7.6 ε n/log P`; `Σ_{a∈Std} |Z^0_a ∩ D| ≤ Σ_a |Z^0_a ∩ D| ≤
2Σ_w(μ(w)−1)^+ ≤ 15.2 ε n/log P`; `Σ` of `|Z^0_a|` over pre-parts failing (L1) `≤ 30.4 ε n/log P`;
`Σ_a |Z^0_a ∩ Dup*| ≤ 16 ε n/log P`; `Σ_w #{a : w ∈ V(part a)} = Σ_a |V(part a)| ≤ 1.37 n`; and
`#{a : w ∈ V(part a)} ≤ μ(w)` for every `w`. Run level: the same for every round `r ∈ [1,R]` of a
valid run with `D_* ≥ 2^{117}`, except (K1) and (K3) (in `OVK1Statement`, `OVK3Statement`), with
`dup_r`, `A_a = hubs`, `mult_r`, and the (F11) sum over the ancestors `Y` of round `r`.

### `DegRecRoundStatement` / `DegRecStatement` (s2:propDegRec, bounds)
TeX: "Let `l` be a round of a valid `HB^tp` run with `d_l ≥ D_*` (that is, `l ≤ R`), and put
`x := λ_l`. Then `M_l ≤ d_l^2`, `Λ_l ≤ 2x`, `s_l ≤ P_l`, and
`d_{l+1} ≤ 1.21 P_l + 9 s_l log M_l ≤ 6P_l + 9 s_l log M_l + 1.2 s_l ≤ 7x^{103} ≤ x^A < d_l`."
Lean, read back: under Γ1 (a)–(e), for one valid round with `D_* ≤ d(H)` (resp. every round
`l ∈ [1,R]` of a valid run): `M ≤ d^2`, `Λ ≤ 2λ`, `s ≤ P`, `d(next) ≤ 1.21P + 9 s log M ≤
6P + 9 s log M + 1.2 s ≤ 7λ^{103} ≤ λ^{105} < d` (all in `ℝ`, `M`, `s`, `P` cast).

### `DegRecKindsRoundStatement` / `DegRecKindsStatement` (s2:propDegRec, kinds)
TeX: "every edge of `G_{l+1}` is of one of the following kinds: (a) an edge deleted by the
`τ`-run of a piece `𝒫` with `|𝒫| ≥ P_l`; there are at most `4 s_l |𝒫| log|𝒫|` of them for each
piece and at most `4.5 n s_l log M_l` in total; (b) an edge of a leaf of the two-level recursion
with fewer than `P_l` vertices …; a leaf with `q` vertices has fewer than `qP_l/2` edges; (c) a
guest edge: an edge of `X^0_Z` with an end in `S_Z`, for a light pre-part `Z`; there are at most
`|Z^0| s_l/2` of them for each light `Z`. Standalone pre-parts, GC-parts included, pass none of the
edges of their leaf graphs down …"
Lean, read back: under `D_* ≥ 2^{117}`, for one valid round with `D_* ≤ d(H)` (resp. every round
of a valid run): every edge of `G_{l+1}` is (a) in the deleted set of the `τ`-run of a big piece,
or (b) an edge of a leaf of the two-level tree with fewer than `P` vertices, or (c) an edge of
`X^0_a` with an end in `S_a` for a light pre-part `a`; each big piece's deleted set has at most
`4 s |𝒫| log|𝒫|` edges; their union at most `4.5 n s log M`; every leaf with `q < P` vertices has
`2|E| < qP`; each light `a` has at most `|Z^0_a| s/2` guest edges; `E(X^0_a) ∩ E(G_{l+1}) = ∅` for
`a ∈ Std`.

### `RoundStepsStatement` (s2:propExists, "(R1) and the first level of (R3) terminate")
TeX: "within a round, (R1) and the first level of (R3) terminate"; proof: "(R1) deletes at least
one edge per step, so it terminates. In the first level of (R3), a node that is not an
`(ε,0)`-expander has a witness …, and its children have `|U| + |N| < (3/4)m` and `m − |U| < m`
vertices …; so every root-to-node path has at most `n` nodes and this level terminates."
Lean, read back: for every `V`: (1) for every graph `H` there is a list of vertex lists that is a
valid (R1) family (`CyclesValid`: well-formed cycles of length `≥ T(d(H))` in `H`, pairwise
edge-disjoint, and after deleting them no well-formed cycle of length `≥ T` remains); (2) for every
graph `K` and every rule `W` that returns a witness with parameter `0` at every graph that is not an
`(ε,0)`-expander, there is a split tree `t` that is an `s = 0` recursion on `K`, stops exactly at
`(ε,0)`-expanders, and at every non-leaf address `a` carries `(W a K_a).1` and its neighbourhood
in `K_a`.

### `RoundTauTermStatement` (s2:propExists, "the τ-runs terminate with any witnesses")
TeX: "the `τ`-runs terminate with any witnesses (`U' ≠ ∅` and `n_1, n_2 < m` at every split)";
proof: "By Lemma s2:lemCap(ii), `τ_l ≥ 128 s_l log²|𝒫|` for every piece, so Lemma s2:lem14tau(a)
applies to every `τ`-run with every choice of witnesses: `U' ≠ ∅`, `n_1, n_2 < m`, and the `τ`-run
terminates."
Lean, read back: for `H`, `c`, `D_*` with `D_* ≥ 2^{117}`, `D_* ≤ d(H)`, a valid cycle family
and a valid `s = 0` recursion on `G'` stopping exactly at `(ε,0)`-expanders (the `τ`-runs and the
home order are not assumed), for every big piece `𝒫` (`|𝒫| ≥ P`): `s ≥ 1`;
`128 s log²|𝒫| ≤ τ`; for every graph `K` with `2 ≤ |K| ≤ |𝒫|` and witness `(U,F)` at `K` with
parameter `s`, the `τ`-rules give `U' ≠ ∅` and both children `splitFst`, `splitSnd` have fewer
than `|K|` vertices; and for every rule `W` returning a witness with parameter `s` at every graph
that is not an `(ε,s)`-expander, there is a `τ`-run of `𝒫` (parameters `s`, `τ`) whose label at
every non-leaf address is the pair of the `τ`-rules for the witness `W a K_a`.

### `RoundExistsStatement` (s2:propExists, proof: "All required choices … exist")
TeX: "All required choices (witnesses, vertex orders, home orders) exist. So each round is a
finite procedure."
Lean, read back: for every graph `H` and real `D_*` with `D_* ≥ 2^{117}` and `D_* ≤ d(H)`, there
are round choices `c` with `Round.Valid H c`.

### `RunTerminatesStatement` (s2:propExists, "every sequence of admissible choices terminates … `d_{l+1} < d_l` while `d_l ≥ D_*`, so `R` is finite")
Lean, read back: under Γ1 (a)–(e), for every graph `G` and every list `cs` of round choices such
that for every `l ∈ [1, |cs|]`, `d_l ≥ D_*` and `cs[l-1]` is a valid round on `G_l` (the graph
produced by the earlier choices): `d_{l+1} < d_l` for every `l ∈ [1,|cs|]`, and `|cs| ≤ |E(G)|`.

### `ExistsRunStatement` (s2:propExists, "For every graph `G` a valid `HB*^{τ+}` run exists")
Lean, read back: under Γ1 (a)–(e), for every graph `G` there is a run with `run.Valid G D_*`.

### `LacunaryMonoStatement` (s2:lemLacunary (ii), function-level step of the proof)
TeX (proof of (ii)): "Hence `2^{x/A} ≥ x ≥ x_0` for `x ≥ x_0`. If `F` is non-increasing and
`F(2^{x/A}) ≤ F(x)/2`, then for `y ≥ 2^{x/A}` we get `F(y) ≤ F(2^{x/A}) ≤ F(x)/2`, which is (H)."
Lean, read back: under Γ1, with `x_0 = log D_*`: `x ≤ 2^{x/105}` for every `x ≥ x_0`; and every
`F : ℝ → ℝ` antitone on `[x_0,∞)` with `F(2^{x/105}) ≤ F(x)/2` for all `x ≥ x_0` satisfies (H)
(`HypH x_0 F`: `F(y) ≤ F(x)/2` whenever `x, y ≥ x_0` and `y ≥ 2^{x/105}`).

### `LacunaryIIStatement` (s2:lemLacunary (ii))
TeX: quoted in the module docstring ("For a valid run with `R ≥ 1`, the degree recursion gives
`λ_r ≥ 2^{λ_{r+1}/A}` for all `r < R`. Hence, if `F` … then `Σ F(λ_r) ≤ 2F(λ_R) ≤ 2F(x_0)` and
`Σ (R−r+1)F(λ_r) ≤ 4F(x_0)`; for the shifted sums (when `R ≥ 3`) … `≤ 2F(λ_{R−2}) ≤ 2F(x_0)` and
… `≤ 4F(λ_{R−2}) ≤ 4F(x_0)`").
Lean, read back: under Γ1, for every valid run with `R ≥ 1`: `2^{λ_{r+1}/105} ≤ λ_r` for
`1 ≤ r < R`; and for every `F` nonnegative and antitone on `[x_0,∞)` with
`F(2^{x/105}) ≤ F(x)/2` for `x ≥ x_0`: `Σ_{r=1}^R F(λ_r) ≤ 2F(λ_R) ≤ 2F(x_0)`,
`Σ_{r=1}^R (R−r+1)F(λ_r) ≤ 4F(x_0)`, and if `R ≥ 3`: `Σ_{l=3}^R F(λ_{l−2}) ≤ 2F(λ_{R−2}) ≤
2F(x_0)` and `Σ_{l=3}^R (R−l+1)F(λ_{l−2}) ≤ 4F(λ_{R−2}) ≤ 4F(x_0)`.

### `LacunarySeqStatement` (s2:lemLacunary (iii), sequence form)
TeX: "(iii) More generally, if `F : [x_0,∞) → [0,∞)` satisfies (H) …, then `Σ_{r≤R} F(λ_r) ≤
2F(λ_R)` and `Σ_{r≤R} (R−r+1)F(λ_r) ≤ 4F(λ_R)`"; proof: "By (H) with `x = λ_{r+1}` and
`y = λ_r`, `F(λ_r) ≤ F(λ_{r+1})/2`, and (i) applies".
Lean, read back: for every real `x_0`, `F`, sequence `λ` and `R ≥ 1`: if `F ≥ 0` on `[x_0,∞)`,
`F` satisfies (H) at `x_0`, `λ_r ≥ x_0` for `r ∈ [1,R]`, and `2^{λ_{r+1}/105} ≤ λ_r` for
`r ∈ [1,R)`, then `Σ_{r=1}^R F(λ_r) ≤ 2F(λ_R)` and `Σ_{r=1}^R (R−r+1)F(λ_r) ≤ 4F(λ_R)`.

### `LacunaryRunStatement` (s2:lemLacunary (iii), run form)
Lean, read back: under Γ1, for every valid run with `R ≥ 1` and every `F ≥ 0` on `[x_0,∞)`
(`x_0 = log D_*`) satisfying (H): `Σ F(λ_r) ≤ 2F(λ_R)`, `Σ (R−r+1)F(λ_r) ≤ 4F(λ_R)`, and if
`R ≥ 3`: `Σ_{l=3}^R F(λ_{l−2}) ≤ 2F(λ_{R−2})` and `Σ_{l=3}^R (R−l+1)F(λ_{l−2}) ≤ 4F(λ_{R−2})`.

### `LacunaryExamplesStatement` (s2:lemLacunary (iv))
TeX: quoted in the module docstring.
Lean, read back: under Γ1, with `x_0 = log D_*`: for every `a ≥ 1/100`, `x ↦ x^{-a}` satisfies
(H), is antitone on `[x_0,∞)` and nonnegative there; the same for `x ↦ 1/log x`, and for
`x ↦ (95 log x + 8) x^{-b}` for every `b ≥ 1`; `2 log*(2^x) + 2 = 2 log* x + 4` for every `x > 1`;
and for each `η ∈ {x ↦ x, x ↦ x^{1/2}, x ↦ log x}`, `F(x) = (2 log*(2^x) + 2)/η(x)` satisfies
(H), is nonnegative on `[x_0,∞)`, and `F(x) ≤ 2F(x_0)` for all `x ≥ x_0`.

### `TowerBRestStatement` (s2:lemTower (b), remaining clauses)
TeX: "For `3 ≤ l ≤ R`: … `P_{l−2}/2 ≥ M_l log⁴ M_l`. For `2 ≤ l ≤ R`: `M_{l−1} ≥ 2M_l`. For
`r < R`: `P_r ≥ 2P_{r+1}`. Moreover … `Σ_{l≤R} ψ(M_l) ≤ 2.1 ψ(D_*)` with `ψ(x) := (6 log x + 12)/x`."
Lean, read back: under Γ1, for every valid run with `d_1 ≥ D_*`: `M_l log⁴ M_l ≤ P_{l−2}/2` for
`3 ≤ l ≤ R` (reals); `2M_l ≤ M_{l−1}` for `2 ≤ l ≤ R` (ℕ); `2P_{r+1} ≤ P_r` for `1 ≤ r`,
`r + 1 ≤ R` (ℕ); `Σ_{l=1}^R ψ(M_l) ≤ 2.1 ψ(D_*)` (`ψ = psiPool`).

### `TowerDStatement` (s2:lemTower (d))
TeX: "For `r ≤ l ≤ R`: `λ_r ≥ 2^{2 log* d_r + 2} ≥ 2^{R−r} ≥ 2^{l−r}`."
Lean, read back: under Γ1, for every valid run with `d_1 ≥ D_*` and `1 ≤ r ≤ l ≤ R`:
`2^{2 log* d_r + 2} ≤ λ_r`, `2^{R−r} ≤ 2^{2 log* d_r + 2}`, `2^{l−r} ≤ 2^{R−r}` (natural
exponents, exact subtraction).

### `TowerEStatement` (s2:lemTower (e))
TeX: "Put `ε_A := 31 ε/(C' log log D_*)` … Then `Σ_{l≤R} 15.2 ε/log P_l ≤ ε_A`. Consequently
`Σ_{l≤R} |D_l| ≤ ε_A n` and `Σ_{l≤R} Σ_{Z∈Std_l} |A_Z| ≤ ε_A n`."
Lean, read back: under Γ1, for every valid run with `d_1 ≥ D_*`: `Σ_{l=1}^R 15.2 ε/log P_l ≤
epsA D_*`; `Σ_l |D_l| ≤ epsA D_* · n`; `Σ_l Σ_{a∈Std_l} |Z^0_a ∩ D_l| ≤ epsA D_* · n`
(`epsA D = 31 ε/(103 log log D)`, Defs).

### `TowerStatement`, `LacunaryStatement`
Conjunctions of all the Specs of the lemma (existing ones included), so that a consumer can cite
the whole lemma.

### `FreshStatement` (s2:propParentless (i))
TeX: "If `x` lies in a round-`r` pre-part, then `H := home_r(x)` is an ancestor of round `r`
containing `x`: `x ∈ H^0 \ S_H = V(H)` if `H` is light, and `x ∈ H^0 = V(H)` otherwise. Hence, for
`Z ∈ Std_l` and `x ∈ U_Z`, `x ∈ F_Z` iff `j_0(x) ≥ l−1`. A vertex is a port of at most one part per
round, so it is a fresh port only at rounds `j_0(x)` and `j_0(x)+1`, and (K4)
`Σ_{l≤R} Σ_{Z∈Std_l} |F_Z| ≤ 2n`."
Lean, read back: for every valid run (no condition on `D_*`): for every round `r` and vertex `x`
lying in some round-`r` pre-part there is `a` with `home_r(x) = some a`, `a` a round-`r`
pre-part, `(r,a)` an ancestor, `x ∈ V((r,a))`, `x ∈ Z^0_a \ S_a` if `a` is light and `x ∈ Z^0_a`
otherwise; for every round `l`, `a ∈ Std_l` and port `x ∈ U_a`: `x ∈ F_a ↔ l ≤ j_0(x) + 1`; at
most one `a ∈ Std_l` has `x ∈ U_a`; `x ∈ F_a` implies `j_0(x) = l` or `j_0(x) + 1 = l`; and
`Σ_{l=1}^R Σ_{a∈Std_l} |F_a| ≤ 2n`.

### `AdmissibleParentStatement` (s2:propParentless (ii))
TeX: "If `Y` is a light part of round `r ≤ l−2` and `Z` is a light part of round `l ≤ R`, then
`|Y| ≥ P_r/2 ≥ P_{l−2}/2 ≥ M_l log⁴ M_l ≥ |Z| L_Z^4`."
Lean, read back: under Γ1, for every valid run and light parts `Y`, `Z` with `r(Y) + 2 ≤ r(Z)`:
`P_{r(Y)}/2 ≤ |V(Y)|`, `P_{r(Z)−2}/2 ≤ P_{r(Y)}/2`, `M_{r(Z)} log⁴ M_{r(Z)} ≤ P_{r(Z)−2}/2`,
`|V(Z)| L_Z^4 ≤ M_{r(Z)} log⁴ M_{r(Z)}` (reals).

### `ParentlessCountStatement` (s2:propParentless (iii))
TeX: quoted in the module docstring.
Lean, read back: for every valid run (no condition on `D_*`) and every finite set `Bad` of part
identities: `Σ_{Z light} #{v ∈ V(Z) : no light part Y ∉ Bad with r(Y) + 2 ≤ r(Z) has v ∈ V(Y)}
≤ 2n + Σ_{Y∈Bad} |V(Y)|(R − r(Y))`; and for every light part `Z` and `v ∈ V(Z)` with `(v,Z)`
parentless: `r(Z) = j_1(v)`, or `r(Z) = j_1(v) + 1`, or (`j_1(v) + 2 ≤ r(Z)` and some light part
`Y ∈ Bad` of round `j_1(v)` contains `v`).

## Hazards and choices (T0 decisions)

* **T0-exists-gamma (propExists, EX-GAMMA-NEEDED; TRIAGE §1b).** The TeX statement has no
  hypothesis on `D_*`; it is false for `D_* = 2^{117}`, `G = K_{2^{117}+1}` (every round passes
  all edges down). `D_*` is by definition a constant satisfying Γ1–Γ4, so the Specs carry
  `Gamma1core Dstar` where Γ1 is used (`RunTerminatesStatement`, `ExistsRunStatement`) and only
  `Gamma2a Dstar` where only lemCap(ii) is used (`RoundTauTermStatement`, `RoundExistsStatement`;
  weaker hypothesis = stronger statement). Manuscript action (optional): add a standing-assumption
  sentence to s2 ("`D_*` satisfies Γ1–Γ4 throughout"), as in s5.tex:9 and s7.tex:10.
* **T0-exists-shape.** "Every sequence of admissible choices terminates" is formalized as (a)
  existence of the finite object for every admissible choice rule (R1 family; `s = 0` recursion for
  every witness rule; `τ`-run for every witness rule) and (b) a bound `|cs| ≤ |E(G)|` on every list
  of valid rounds with `d_l ≥ D_*` (such a list is not required to be a finished run). The
  termination of the `τ`-runs is stated for rounds whose first level is done (not under
  `Round.Valid`, which already contains the `τ`-runs); this is the round-local reading of the
  proof's first paragraph (TRIAGE §2.2 DR-ROUND-LOCAL).
* **T0-lac-seq.** lemLacunary (iii) is stated both for an abstract sequence (no condition on `D_*`)
  and for runs (Γ1); (ii) is split into the function-level step (`LacunaryMonoStatement`, with
  `2^{x/A} ≥ x` from the proof, which makes the hypothesis `F(2^{x/A}) ≤ F(x)/2` evaluate `F` inside
  its domain) and the run form. `R ≥ 1` is a hypothesis of all run forms (implicit in "`F(λ_R)`").
  The shifted weighted sum of (iii) ("likewise for `F(λ_{l−2})`") is written out as in (ii).
* **T0-lac-examples.** (iv) adds nonnegativity on `[x_0,∞)` for all six functions (implicit in
  "`F : [x_0,∞) → [0,∞)`"); the three `log*` functions are not claimed antitone (they are not).
* **T0-tower-nat.** (b) `M_{l−1} ≥ 2M_l` and `P_r ≥ 2P_{r+1}` in `ℕ`; (d) natural exponents with
  exact subtraction (`r ≤ l ≤ R`); (e) sums over `[1,R]`. The probe Specs of (a), (b), (c) were
  written with `d_1 ≥ D_*` and `Gamma1core`; the new ones use the same hypotheses.
* **T0-parentless-hyps.** propParentless (i), (iii) are stated without `d_1 ≥ D_*` and without any
  condition on `D_*` (unused; strengthening); (ii) carries `Gamma1core` and drops `d_1 ≥ D_*`
  (implied whenever the statement is not vacuous).
* **T0-parentless-bad.** `Bad` is any `Finset PartId` (not required to consist of light parts;
  extra members only enlarge the bound). The pair count is written as a sum over light parts of
  the number of parentless vertices (each pair once). "`j_0(x) ≥ l−1`" is `l ≤ j_0(x) + 1` in
  `WithTop ℕ`. The "more precisely" clause is an implication with three disjuncts; "the light part
  of round `j_1(v)` containing `v`" is written with `∃` (it is unique by propStructure (iv)).
* **Prior-run modules (Structure, OVRun, DegRec)**: T0 choices as in their module docstrings:
  propStructure drops `n ≥ N_0` and `d_1 ≥ D_*` and carries `0 < n` for (iii) (TRIAGE §2.12);
  (i) and (iii) carry `Gamma2a`, (iv) nothing; the minimum degree of `H_Y` is stated pointwise
  with nonemptiness; `λ_r ≤ Λ_r` added to (i) (lemTower (b) cites it from the proof); propOV
  carries `Gamma2a` (implicit in the TeX, OV-IMPLICIT-DSTAR); propDegRec bounds carry
  `Gamma1core`, kinds `Gamma2a`; the counterfactual "declaring a pre-part a GC-part … can only
  decrease the set of passed-down edges" is not formalized (not a proposition about a run;
  its factual content is the standalone clause); "a leaf with `q` vertices has fewer than
  `qP_l/2` edges" is stated for the small leaves without `q ≥ 1` (leaves of valid rounds are
  nonempty; a proof must show it).
* **Not formalized (no mathematical content used downstream):** s2:remTauConstants and its table;
  the closing commentary of lemLacunary; lemGC (i) first clause and propExists "(GC) feeds back
  into nothing" (Defs design constraints, verified by reading `EG/Defs/HB/Round.lean`).

## Consumers in other chunks

* s5:defStages (eqPl) uses `ParentlessCountStatement` with `Bad` = demoted or parent-bad parts:
  arbitrary `Bad`, parentless = "no light part outside `Bad` of round `≤ l−2` contains `v`", as
  requested by blueprint s5 STAGES-PL-PARENTLESS.
* s5:lemExpect / lemParent use lemLacunary (ii)/(iv) for `F(x) = x^{-205}`: `LacunaryIIStatement`
  with `LacunaryExamplesStatement` (a = 205 ≥ 1/100) and `LacunaryMonoStatement` (to pass from (H)
  to halving, `x ≤ 2^{x/A}` is provided).
* s7:thmJVps / thmMainProof use `ExistsRunStatement` (under `Gamma1core`, which `GammaCond`
  implies).
* s7 (`epsA`) and s6/s7 (`D_l`, `A_Z` sums) use `TowerEStatement`; s5 eqLY uses `TowerDStatement`
  and `TowerAStatement`.

## Non-vacuity (EGTest/Spec_s2b.lean)

`Gamma1core`, `Gamma2a` satisfiable; `Run.Valid` satisfiable with `R = 1` and a light part (the
`K₃` run of `EGTest.HB`); the choice-list hypothesis of `RunTerminatesStatement` satisfiable by a
list of length 1; the hypotheses on `F` and on the sequence of the Lacunary Specs satisfiable
(`F = 0`, `λ_r = 2`, `R = 2`); the `η`-disjunction satisfiable. Not checked (not feasible
cheaply): joint satisfiability of Γ with a valid run/round with `d ≥ D_*`; this is exactly
`ExistsRunStatement` / `RoundExistsStatement`.
