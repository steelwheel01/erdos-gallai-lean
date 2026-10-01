# P2 Specs, chunk s6a (routing engine GATE/MED/EQ-LPT/PAR/HCC-P/union; designations; CONC): status

Manuscript v6.1 `proofs/manuscript/s6.tex` lines 1–333 (CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s6a.md`, `nodes_s6a.json` (9 nodes); TRIAGE §2.6 (CONC takes only
the Γ items it uses), §2.9 (s6 interfaces); Defs design notes `work/p2d/chain.md`,
`work/p2d/design.md`; probe notes `work/p2b/P2E.md`, `work/p2b/P3B.md` (and P1b GATE).

**Result: every node of the chunk already has a Spec. No new Spec, no new Defs file, no Spec or
Defs edited.** I checked each existing Spec against the TeX (quantifiers and their order, strict vs
non-strict, constants, log base, edge cases, ℕ vs ℝ) and found no fidelity problem and no
mathematical finding of class T1–T3. The existing Specs were approved by two statement reviews each
(P1b GATE; P2E: MED, EQ-LPT, PAR, HCC-P, union; P3B: CONC, tower facts), and each has a proof in
`EG/Proof/Chain/` (not re-audited here; `grep sorry` finds none in those proof files).

New file: `EGTest/Spec_s6a.lean` (non-vacuity checks). `scripts/check.sh EGTest/Spec_s6a.lean`:
0 errors, 0 warnings, 0 sorry. `python3 -I scripts/lint.py`: 0 findings. For the orchestrator: the
root import to add to `EGTest` is `EGTest.Spec_s6a` (I did not edit the root files). No new EG
module, so nothing to add to `EG`.

## Table: label → Lean name → file → status

All Lean names are in namespace `EG.Spec`.

| label (kind) | Lean name(s) | file | status |
|---|---|---|---|
| s6:lemGATE (lemma) | `GateStatement` (first conclusion), `GatePreciseStatement` ("More precisely") | `EG/Spec/Chain/Gate.lean` | existing (P1b, locked); proved `EG.gate`, `EG.gate_precise` |
| s6:defCluster (definition) | Defs `EG.Chain.Cluster`, `exc`, `excPos`, `excNeg`, `Cluster.{verts, portBeads, beadCount, ParityClean, IsAdmissible, load, medOrient}`; embedded claim "every bead is oriented exactly once" is a proved Lib lemma (`EG/Lib/Chain/MedOrient.lean`, [s6:defCluster] docstring at l. 197) | `EG/Defs/Chain/Cluster.lean` | existing Defs (locked); no Spec needed |
| s6:lemMED (lemma) | `MedStatement` ((a), for `medOrient rk`), `MedExcStatement` ((b), every admissible `O`) | `EG/Spec/Chain/MED.lean` | existing (P2E); proved `EG.med`, `EG.medExc` |
| s6:lemEQLPT (lemma) | `EqLptStatement` (every greedy placement), `EqLptExistsStatement` ("so the rule is consistent") | `EG/Spec/Chain/EqLpt.lean` | existing (P2E); proved `EG.eqLpt`, `EG.eqLptExists` |
| s6:lemPAR (lemma) | `ParStatement` (for every choice), `ParExistsStatement` ("such an edge exists") | `EG/Spec/Chain/PAR.lean` (+ probe Defs `EG/Defs/Probe/P2E/Par.lean`: `oddComps`, `IsParChoice`) | existing (P2E); proved `EG.par`, `EG.parExists` |
| s6:lemHCCP (lemma) | `HccpStatement` (data/hypotheses `HccpData`, `HccpData.Valid` in `EG/Defs/Chain/HCCP.lean`) | `EG/Spec/Chain/HCCP.lean` | existing (P2E); proved `EG.hccp` |
| s6:lemHCCglob (lemma) | `HccUnionStatement` (first paragraph), `HccGlobStatement` (second paragraph, input-level disjointness, T0 row `T0-glob-input`) | `EG/Spec/Chain/HCCP.lean` | existing (P2E); proved `EG.hccUnion`, `EG.hccGlob` |
| s6:defDesign (definition) | Defs `EG.Chain.{Designation, IsDesignation, classedPorts, classDeg, mY, dStar, alphaY, Bead, gammaL, IsGiant, cAgg, cFresh, cPP}`; embedded claims (unique `Z_u`, `u ∈ V(Y(u))`, `r(Y(u)) ≤ l−2`, vanishing for `l ≤ 2`, a designation exists) are proved Lib lemmas in `EG/Lib/Chain/Design.lean` (`eq_of_mem_classed`, `IsDesignation.mem_ancVerts`, `IsDesignation.round_add_two_le`, `classedPorts_eq_empty_of_le_two`, `mY_eq_zero_of_le_two`, `dStar_eq_zero_of_le_two`, `cAgg_eq_zero_of_le_two`, `Bead_eq_empty_of_le_two`, `exists_isDesignation`) | `EG/Defs/Chain/Design.lean` | existing Defs (locked); no Spec needed |
| s6:thmCONC (theorem) | `ConcIStatement`, `ConcIIStatement`, `ConcIIIStatement`; proof-level shared sums `ConcTauSumStatement`, `ConcDStarSumStatement` (consumer: s6:thmCONCL (iv), chunk s6b); (iv) is meta (automatic: (ii), (iii) quantify over every designation) | `EG/Spec/Chain/CONC.lean` | existing (P3B); proved `EG.concI`, `EG.concII`, `EG.concIII`, `EG.concTauSum`, `EG.concDStarSum` |
| (unlabelled log* facts before s6:thmCONC; `k_* ≥ 6`) | `LogStarFactsStatement`, `KStarStatement` (docstring label `[s6:thmCONC]`) | `EG/Spec/Chain/ConcTower.lean` (+ probe Defs `EG/Defs/Probe/P3B/TowerFns.lean`: `towA`, `towB`, `towC`) | existing (P3B); proved `EG.logStarFacts`, `EG.kStar` |
| s6:eqTowerHalf (equation, proved before s6:thmCONC) | `TowerHalfStatement` | `EG/Spec/Chain/ConcTower.lean` | existing (P3B); proved `EG.towerHalf` |
| s6:eqTowerEnd (equation) | `TowerEndStatement` | `EG/Spec/Chain/ConcTower.lean` | existing (P3B); proved `EG.towerEnd` |

## Check of the existing Specs against the TeX (summary)

No new Spec, so no new back-translation; the existing Specs' docstrings quote the TeX. Points
checked, with the plain reading of the Lean statement:

- **GATE.** `F ⊆ G.edges`, `IsOrientation F A`, `IsBalanced A` (every vertex, as in the TeX "at
  every vertex"), `W ⊆ A`, `IsAcyclic (A \ W)` ⟹ a decomposition of `F` into at most `|W|` objects,
  all cycles with edges in `E(G)`; precise form: a list of directed cycles of `A`, each of length
  ≥ 3, well-formed cycles of `G`, each containing a `W`-arc, arc lists concatenating without
  duplicates to exactly `A`, at most `|W|` of them. Faithful.
- **MED.** (a) for `K.ParityClean` and `rk` injective on `U_𝒦` (a linear order on a finite set):
  `medOrient rk` admissible and a real `pot` with values in `(0,1)` on `V(𝒦)`, strictly increasing
  along arcs. (b) for every admissible `O` (hypothesis parity-clean kept, implied anyway):
  `|exc(u)| ≤ deg`, `exc(u) − deg` even (in ℤ), `Σ_{U_𝒦} exc = 0`, `Φ(𝒦) ≤ b(𝒦)` in ℝ (b is a
  half-integer in general). Faithful.
- **EQ-LPT.** Real loads, `Antitone Φ`, `Φ ≥ 0`, `1 ≤ k ≤ m`; the nondeterministic rule is the
  relation `IsGreedyLPT` ((G1) minimum load, (G2) empty layer whenever one exists); for every
  greedy `σ`: `σ` onto, and `L_j − L_{j'} ≤ Φ_1` for all `j, j'` (= max − min ≤ Φ_1 since k ≥ 1).
  Existence is a separate Spec (the proof's "the rule is consistent"). Faithful (not stated over ℕ).
- **PAR.** `Disjoint V_a V_b` and every edge `s(a,b)` with `a ∈ V_a`, `b ∈ V_b` (bipartite with
  sides; disjointness is needed, counterexample in blueprint PAR-SIDES-DISJOINT: T0). For every
  `J'` with `IsParChoice` (exactly one edge in each odd component, none elsewhere, each a
  non-bridge or pendant edge): `|J'| ≤ #odd`, `#odd ≤ |V(E)|/2` (in ℝ), and disjoint `S_a, S_b`
  with `S_a ∪ S_b = E \ J'`, even `S_a`-degrees on `V_b`, even `S_b`-degrees on `V_a`. Faithful.
- **HCC-P.** Data and all hypotheses in the locked `HccpData.Valid` (uniform in `k` with
  `succ j = (j+1) mod k`; indexed clusters; `(D)` for distinct indices; the `k = 1` reading proved
  equivalent, `jcp_iff_jcpOne`). Conclusion: `∃ Φ, ∀ j, Φ_j = Φ ∧ |𝒫_j| = Φ`, sets
  `F_j ⊆ E(𝒫_j)` with `E(𝒫_j) \ F_j ⊆ E(G[T_j])`, and a decomposition of `⋃ B_𝒦 ∪ ⋃ F_j` into at
  most `Φ` objects, each a cycle of `G` of length ≥ `max 3 k`. Faithful (length bound kept).
- **Union.** First paragraph: pairwise disjoint `E_i ⊆ E(G)` with decompositions of lengths
  `a_i` ⟹ a decomposition of the union of length exactly `Σ a_i`. Second paragraph: valid systems,
  beads and path edges of distinct systems pairwise disjoint (input level, T0 `T0-glob-input`,
  implies the literal output-level hypothesis since `F_j ⊆ E(𝒫_j)`), no cross-system vertex
  condition ⟹ common values `Φ s`, sets `F s j` as in HCC-P (ii), and a decomposition of the union
  of `B(𝒮_s) ∪ ⋃_j F s j` into at most `Σ_s Φ s` cycles of `G`. Faithful for its consumer (JS-LC
  Step 7).
- **CONC.** (i) valid run, `a ∈ Std_r`, every `l ≥ r+1` (all naturals; `G_l` is stationary after
  `R+1`), every `h`: `#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1` (ℕ subtraction, exact since
  `τ_r ≥ 1`). (ii) every designation, every `l`: `m_{Y,l} ≤ τ_r − 1 + d*_{Y,l}`. (iii) under
  `Gamma1core D_*` only (TRIAGE §2.6): `Σ_{l ∈ [1,R]} Σ_{Y standalone} m_{Y,l} ≤
  2^{σ+14} n log* D_*/log D_* + 100 ε n log* D_*/(C' log log D_*)`, `log = logb 2`; the index
  range loses nothing (`m_{Y,l} = 0` outside `[1,R]`, Lib `mY_eq_zero_of_not_isRound`). No
  `n ≥ N_0`, no Γ2(b),(c). Faithful.
- **Tower facts.** `log*` facts for `x ≥ 1` / `x > 1`; `k_* ≥ 6` chain from `Gamma1core`;
  (eqTowerHalf) for `r ∈ [1,R)` of a valid run under `Gamma1core`; (eqTowerEnd) for `d ≥ D_*`.
  Constants `2k_*+4`, `2k_*+3`, exponent `1/2` as `rpow`. Faithful.

## Hazards and choices (T0 decisions, all pre-existing)

| ID | node | decision |
|---|---|---|
| T0-glob-input | s6:lemHCCglob | input-level cross-system disjointness (CONVENTIONS T0 record) |
| PAR-SIDES-DISJOINT | s6:lemPAR | `Disjoint V_a V_b` made explicit ("bipartite graph with sides") |
| EQ-GREEDY-RELATION | s6:lemEQLPT | the rule is a relation; ∀ greedy placements + separate existence Spec |
| HCCP-K1-UNIFORM, HCCP-INDEXED-CLUSTERS, HCCP-PATH-FAMILY-LIST, HCCP-PAD-DOMAIN | s6:lemHCCP | locked Defs `HccpData.Valid` (design note `work/p2d/chain.md`) |
| CL-G-FREE, CL-ADMISSIBLE-LOCAL, CL-BEADCOUNT-HALF (real `beadCount`) | s6:defCluster | locked Defs |
| CONC-IMPLICIT-HYPS | s6:thmCONC | (i), (ii) need no Γ; (iii), the sums and the tower facts take `Gamma1core` only |
| CONC-SUM-INDEX, CONC-ROUND-RANGE | s6:thmCONC | sums over `l ∈ [1,R]`, `Y ∈ stdParts`; (i) for all `l ≥ r+1` |
| CONC-IV-META | s6:thmCONC | (iv) not stated (automatic) |

Consumer forms (TRIAGE §2): the shared sums `ConcTauSumStatement` / `ConcDStarSumStatement` are
stated over all ancestors, the form read by s6:thmCONCL (iv) (chunk s6b); `HccGlobStatement`
records "cycles of `G`" read by JS-LC Step 7; EQ-LPT consumers read existence
(`EqLptExistsStatement`); MED consumers get an admissible orientation from `MedStatement` (a)
(the blueprint's Lib corollary `Cluster.exists_admissible` does not exist under that name).

## Non-vacuity (`EGTest/Spec_s6a.lean`)

- GATE: the cyclically oriented triangle with `W` one arc (instances of `EGTest.Gate`).
- MED: cluster `K5` parity-clean, rank injective; `O5` admissible.
- EQ-LPT: loads `3,2,1`, `k = 2`, antitone, nonnegative, greedy `σ3`.
- PAR: one edge `01`, sides `{0}`, `{1}` disjoint; `J' = {01}` is a PAR choice.
- HCC-P: systems `S1` (`k = 1`) and `S2` (`k = 2`) valid; new empty system valid for every
  `k ≥ 1` (so `k = 3`, `max(3,k) = k`, has satisfiable hypotheses).
- Union: first paragraph on `E_0 = ∅`; second paragraph on two systems (`S1` and the empty `k = 3`
  system) with disjoint beads/path edges.
- CONC: `run1` valid with a designation ((i), (ii) up to `a ∈ Std_r`); `Gamma1core D`, the run
  without rounds on `E2` and a designation ((iii), sums, eqTowerHalf); `Gamma1core D`, `D ≤ d`
  (eqTowerEnd, `k_*`).
- Not checked: a valid run with a standalone pre-part (`a ∈ Std_r`) or with `R ≥ 1` under Γ1 does
  not exist at toy size (same limitation as `EGTest/ProbeP3B.lean`).
