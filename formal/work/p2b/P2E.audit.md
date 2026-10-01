# P2E audit (independent auditor, 2026-09-30, HEAD `ed552cf`): probe P-2 part 1, the s6a routing engine

Auditor: independent, clean-room. I re-derived every check below myself against the TeX and the
Lean sources and re-ran every machine check on the current tree; I did not rely on the previous
audit's text (2026-09-29), which this file replaces. I edited no Lean file; the only file written
is this one.

The proof under formalization is a CANDIDATE proof of the Erdős–Gallai cycle decomposition
conjecture, reviewed only by AI. Nothing here says the conjecture is solved.

**Verdict: approve**, with one minor process issue for the integrator (§6, item 1: the unit's
fix round 1 appended a row to `CONVENTIONS.md`, a file listed in `LOCK.json`, so `scripts/lock.py
check` now reports exactly that one violation). On the five task items: (1) the sorry frontier of
the unit's modules is exactly the declared-input stub `EG.eulerTreeTJoin`, which no probe theorem
uses; (2) no `def … : Prop :=` body of any Spec and no definition of the new Defs file changed
after review round 1, every later diff is a docstring, and nothing of the unit changed after
review round 2; (3) I found no hidden weakening: every probe theorem's type is literally its
Spec, the Specs depend only on locked Defs plus the reviewed `Par.lean`, and every hypothesis and
conclusion back-translates to the TeX with the two recorded T0 deviations of HCCglob ¶2 and
nothing else; (4) the refutation target of this part (the engine's multiplicity bounds feeding
JS-LC) is covered by proved statements at the engine level, and the aggregated form handed off to
part 2 is now also a proved, sorry-free Spec in P2J; (5) every math finding of the author, the
two reviewers and the previous audit is confirmed at the class given (one T0, T1 wording points,
no T2/T3, no suspect item).

## 0. What I read and ran

Read: `AGENTS.md`, `CONVENTIONS.md` (incl. the T0 row `T0-glob-input`); `work/p2b/P2E.md` in full
(stage 1, fix rounds 1–2, proof round 1 and the three re-verifications), `P2E.review1.md`,
`P2E.review2.md`; `proofs/manuscript/s6.tex:16–237` (GATE, defCluster, MED, EQ-LPT, PAR, HCC-P,
HCCglob) and `443–615` (JS-LC Steps 1–8 and the joint-routing claim), `s1.tex:1489–1500`
(citEuler), `s2.tex:518–527` ((R2), `M_l ≥ 2^40`); `work/p2/TRIAGE.md` §4 row P-2 (line 329) and
the rows PAR-SIDES-DISJOINT, GLOB-OUTPUT-LEVEL-HYP, EQ-USE-EMPTY-S0; the s6a blueprint entries
MED-ONLY-EXISTENCE-USED, EQ-USE-EMPTY-S0, PAR-SIDES-DISJOINT, PAR-FORALL-CHOICE,
PAR-DIRECT-PROOF-OPTION, HCCP-FLAGGED-REDERIVED, HCCP-LENGTH-UNUSED, GLOB-OUTPUT-LEVEL-HYP,
GLOB-NO-VERTEX-DISJ; `work/p2d/chain.md` (the integrator flag for `IsParChoice`);
`work/p2b/P2J.md` (the hand-off).
Lean, in full: `EG/Spec/Chain/{MED,EqLpt,PAR,HCCP,EngineMult}.lean`, `EG/Spec/Found/EulerTreeTJoin.lean`,
`EG/Defs/Probe/P2E/Par.lean`, `EG/Proof/Found/EulerTreeTJoin.lean`, the locked Defs
`EG/Defs/Chain/{Cluster,EqLpt,HCCP}.lean` and `EG/Defs/Components.lean`, the proof files
`EG/Proof/Chain/{MED,EqLpt,HccpEndMult,HCCGlob,PAR}.lean` and the main theorem of
`EG/Proof/Chain/HCCP.lean`, `EGTest/ProbeP2E.lean`; the definitions `IsPathIn`, `IsThrough`,
`walkEdges` (`Walk.lean`), `Obj`, `WF`, `IsDecomp`, `cycleEdges` (`Objects.lean`), `degE`,
`induce`, `restrictEdges`, `toSimpleGraph` (`Graph.lean`), `IsOrientation`, `outDeg`, `inDeg`,
`IsDirCycle`, `IsAcyclic` (`Orient.lean`); the statements of `Valid.countP_end_le`,
`Valid.natAbs_pexc_le`, `max_demMinus_demPlus` (`Lib/Chain/HccpEnds.lean`), `exists_tJoin`,
`exists_par_partition`, `card_le_oddComps`, `two_mul_card_oddComps_le`, `exists_isParChoice`,
`exists_nonBridge_or_pendant`, `hccp_F_props`, `gate_with_cycles`, `le_length_of_blocks`,
`mem_edgeComps`, `mem_compEdges`, `mem_compEdges_of_mem`, `isNonBridge_compEdges_iff`,
`isPendant_compEdges_iff`; for the hand-off, `EG.Spec.JslcJointMultStatement`
(`EG/Spec/Chain/JSLCRouting.lean`) and `junctionOcc`, `IsPort`, `PreValid`
(`EG/Defs/Probe/P2J/PreSystem.lean`).

Ran (from `formal/`, on HEAD `ed552cf`, working tree):
- `git diff` of the eight Spec/Defs/stub files between `1e0e84a` (first commit of MED, EqLpt,
  Par.lean), `3a26761` (first commit of the other five; the tree review 1 read), `3278dd4`
  (review 1 committed, fix round 1), `41e8a4e` (fix round 2, proofs, review 2, previous audit),
  HEAD and the working tree (§2);
- olean freshness of the 17 Spec/Defs/Proof modules of the unit: every `.olean` is newer than
  its source; the Lib oleans of `EG/Lib/Chain/` are present;
- `LEAN_NUM_THREADS=2 lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Chain.{MED,EqLpt,
  HccpEndMult,HCCP,HCCGlob,PAR,EngineMult,HCCUnion,EngineMultTJS} EG.Proof.Found.EulerTreeTJoin`:
  `inspected 1744 constants under [EG]; 1 use sorryAx; 0 meta-scan hits; 0 violations`, the one
  line being `SORRY EG.eulerTreeTJoin (EG.Proof.Found.EulerTreeTJoin)`;
- the same scan on `EG.Proof.Chain.JSLCRouting` (part 2's hand-off module, for §4): `inspected
  2682 constants under [EG]; 0 use sorryAx; 0 meta-scan hits; 0 violations`;
- `python3 -I scripts/lint.py`: `lint (development): 0 findings`;
- `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/ProbeP2E.lean 900`: `rc=0 errors=0 sorry-warnings=0`;
- `grep sorry` over all unit files (Spec, Defs/Probe, Proof/Chain, Lib/Chain, the stub, the
  test): one hit, `EG/Proof/Found/EulerTreeTJoin.lean:20`;
- `grep` for `set_option`, `private`, `local instance`, `attribute [`, `@[simp]`, `universe`
  over the unit's Proof and Lib files: no hit (the only classical-logic uses are `classical` /
  `open Classical`, which are not tokens of concern);
- `python3 -I scripts/lock.py check`: `865 locked constants, 153 locked files; 1 violations, 234
  pending`; the violation is `LOCK: locked file changed or missing: CONVENTIONS.md` (§6 item 1);
  the unit's Spec files, `Par.lean` and the three constants `EulerTreeTJoinStatement`,
  `HccpEndMultStatement`, `JsMultNumStatement` are listed as PENDING (unlocked), as expected
  before the freeze; the Defs the Specs depend on (`Chain/Cluster`, `Chain/EqLpt`, `Chain/HCCP`,
  `Components`, `Graph`, `Objects`, `Orient`, `Walk`) are all locked;
- `git status`: the only modified files are `EG/Defs/Gamma/Full.lean` (another unit) and four
  `work/p2b/*.md` notes; no file of this unit differs from HEAD.

## 1. Sorry frontier (task item 1)

Exactly `EG.eulerTreeTJoin : EG.Spec.EulerTreeTJoinStatement` (`EG/Proof/Found/EulerTreeTJoin.lean:20`,
docstring `[DECLARED INPUT] [s1:citEuler] (a)`), the declared-input stub in the prescribed form.
The axiom scan of all nine proof modules plus the stub module lists this single `sorryAx`
constant, so every probe theorem (`EG.med`, `EG.medExc`, `EG.eqLptExists`, `EG.eqLpt`,
`EG.parExists`, `EG.par`, `EG.hccp`, `EG.hccUnion`, `EG.hccGlob`, `EG.hccpEndMult`,
`EG.jsMultNum`, `EG.tJS_eq_two_mul_add_two`, `EG.jsMult_lt_tJS`) is sorry-free, and no other
axiom appears. Moreover the stub is unreachable from the probe: no file under `EG/` imports
`EG.Proof.Found.EulerTreeTJoin` (the only mentions, `EG/Lib/Chain/ParTJoin.lean:22` and
`EG/Proof/Chain/PAR.lean:17`, are docstrings saying it is not used; `EGTest/ProbeP2E.lean:7`
imports the Spec only). The PAR proof builds the `T`-join directly (`EG.exists_tJoin`, induction
on `|T|` by symmetric differences of paths, blueprint PAR-DIRECT-PROOF-OPTION). **Pass.**

## 2. No Spec changed after its review (task item 2)

Statement bodies were compared across all trees. Every diff consists of docstring or comment
lines only; no `def … : Prop :=` body and no definition changed at any point after the first
commit of each file.

| file | 1e0e84a → 3a26761 | 3a26761 → 3278dd4 (fix round 1) | 3278dd4 → 41e8a4e (fix round 2 + proofs) | 41e8a4e → HEAD → working tree |
|---|---|---|---|---|
| `EG/Spec/Chain/MED.lean` | identical | identical | identical | identical |
| `EG/Spec/Chain/EqLpt.lean` | identical | identical | identical | identical |
| `EG/Spec/Chain/PAR.lean` | (created in 3a26761) | identical | identical | identical |
| `EG/Spec/Chain/HCCP.lean` | (created) | +5/−2 lines in the `HccGlobStatement` docstring (T0 row citation, Step 7 quotation) | +3 lines in the module docstring (length bound stays; count-only form must be a corollary) | identical |
| `EG/Spec/Chain/EngineMult.lean` | (created) | +19/−2 lines: module docstring (label tag, scope paragraph) and the two docstring tags `[s6:lemJSLC]` → `[s6:lemJSLC:proof-claim-c]` | +2/−1 lines in the module docstring (adds `EG.jsMult_lt_tJS`) | identical |
| `EG/Spec/Found/EulerTreeTJoin.lean` | (created) | +6 lines in the module docstring (canonical form) | +4 lines in the module docstring (round-2 confirmation) | identical |
| `EG/Defs/Probe/P2E/Par.lean` | identical | identical | +2/−1 lines in the `IsParChoice` docstring (redundancy note) | identical |
| `EG/Proof/Found/EulerTreeTJoin.lean` | (created) | identical | identical | identical |

I read every `+`/`−` line of the diffs. The bodies quoted in §3 are therefore the ones both
reviews approved (review 1 committed in `3278dd4`, review 2 in `41e8a4e`). **Pass.**

## 3. Hidden weakening (task item 3)

**Shape.** Each probe theorem has exactly its Spec as type, with no extra binder or hypothesis:
`theorem med : EG.Spec.MedStatement`, `medExc : MedExcStatement`, `eqLptExists :
EqLptExistsStatement`, `eqLpt : EqLptStatement`, `parExists : ParExistsStatement`, `par :
ParStatement`, `hccp : HccpStatement`, `hccUnion : HccUnionStatement`, `hccGlob :
HccGlobStatement`, `hccpEndMult : HccpEndMultStatement`, `jsMultNum : JsMultNumStatement`. The
Spec files import only locked Defs (`EG.Defs.Chain.{Cluster,EqLpt,HCCP}`, `EG.Defs.Objects`,
`EG.Defs.Graph`) plus Mathlib and the reviewed `EG.Defs.Probe.P2E.Par`. So a weakening could sit
only in a Spec body, in `Par.lean`, or in a locked Def; I back-translated each with the TeX open.

**`MedStatement` (a).** ∀ `V`, `K : Cluster V`, `rk : V → ℕ`, `K.ParityClean → InjOn rk ports →
K.IsAdmissible (K.medOrient rk) ∧ ∃ pot : V → ℝ, (∀ v ∈ K.verts, 0 < pot v ∧ pot v < 1) ∧ ∀ a ∈
medOrient, pot a.1 < pot a.2`. `medOrient rk` filters `verts ×ˢ verts` by "bead ∧ medRule", so
every arc has both ends in `V(𝒦)` and `pot` is constrained exactly where the TeX defines it.
`medRule` (`Cluster.lean:143–146`): port→hub iff `2·#{w ∈ N_B(h) : rk w ≤ rk u} ≤ |N_B(h)|`;
hub→port iff `|N_B(h)| < 2·#{…}`; port→port iff `rk x < rk y`. `N_B(h) = beadNbrs h` consists of
ports (`no_hub_hub`, `ends_mem`), so with `rk` injective on ports the count is the position `i`
of `u_i` and the rule is the TeX's "`u_i → h` for `i ≤ d`, `h → u_i` for `i > d`"; a port–port
bead gets exactly one direction by injectivity (its ends differ, `loopless`). Every linear order
of the finite set `U_𝒦` is induced by a rank injective on `U_𝒦`; `rk` is never read at a hub.
`IsAdmissible` = `IsOrientation beads O` ∧ `IsAcyclic O` ∧ `outDeg = inDeg` at every hub (not
`IsBalanced`), as in s6:defCluster. Faithful.

**`MedExcStatement` (b).** ∀ parity-clean `K`, ∀ admissible `O`: (∀ `u ∈ ports`, `|exc O u| ≤
degE beads u` in ℤ ∧ `Even (exc O u − degE beads u)`) ∧ `∑_{ports} exc O u = 0` ∧
`(load K O : ℝ) ≤ beadCount K`, with `exc = outDeg − inDeg`, `load = ∑_U (exc)⁺`, `beadCount =
∑_h deg_B(h)/2 + |B[U]|` real, exactly the TeX's `b(𝒦)`. "For every admissible orientation" is
a ∀; "parity-clean" is kept and is implied by admissibility, so it restricts nothing. Faithful.

**`EqLptExistsStatement`, `EqLptStatement`.** `m k : ℕ`, `Φ : Fin m → ℝ`, `1 ≤ k`, `k ≤ m`,
`Antitone Φ` (= `Φ_1 ≥ … ≥ Φ_m`), `∀ i, 0 ≤ Φ i`. Exists: `∃ σ : Fin m → Fin k, IsGreedyLPT Φ σ`.
Statement: `∀ σ, IsGreedyLPT Φ σ → Surjective σ ∧ ∀ j j', layerLoad j − layerLoad j' ≤ Φ ⟨0,_⟩`.
`IsGreedyLPT` (`EqLpt.lean:46–49`): for every item, (G1) its layer has minimum `loadBefore`
(sum over the earlier items) among all layers and (G2) if some layer is `EmptyBefore` (no earlier
item), its layer is. This is the TeX rule verbatim, non-deterministic in ties, hence a relation
and a ∀ over placements; "empty" counts items, not load, as the TeX intends (a zero-load item
still occupies a layer). `max − min ≤ Φ_1` ⇔ all pairwise differences `≤ Φ_1` since `k ≥ 1`.
The existence conjunct carries the full lemma hypotheses (more than needed, harmless; the
consumer JS-LC Step 4 has them all: it sorts by load and `k_0 ≤ #clusters`). Faithful.

**`ParExistsStatement`, `ParStatement`, `oddComps`, `IsParChoice`.** Hypotheses: `E : Finset
(Sym2 V)`, `Disjoint Va Vb`, `∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a,b)`. This is "bipartite graph
with sides `V_a, V_b`" (sides of a bipartition are disjoint; without it the lemma is false:
`Va = Vb = {x,y,z}`, `E = {xy, yz}`, one even component, `J' = ∅`, no partition makes every
`S_a`-degree on `V_b` and every `S_b`-degree on `V_a` even). `oddComps E` =
`(edgeComps E).filter (Odd |compEdges E C|)`, where `edgeComps E` = the Mathlib components of
`fromEdgeSet E` containing a vertex of `edgeVerts E = V(E)`, so isolated vertices are excluded
exactly as "(V(E), E)" requires, and `compEdges E C` = the edges of `E` with both ends in `C`.
`IsParChoice E J'` = `J' ⊆ E` ∧ (∀ `C ∈ edgeComps E`, `|J' ∩ compEdges E C| = if Odd
|compEdges E C| then 1 else 0`) ∧ (∀ `e ∈ J'`, `IsNonBridge E e ∨ IsPendant E e`). Every edge of a
loopless `E` lies in `compEdges` of the component of its ends (`mem_compEdges_of_mem`), so the
middle conjunct says exactly "one chosen edge in each odd component, none in an even one";
"of that component" equals the global predicate (`isNonBridge_compEdges_iff`,
`isPendant_compEdges_iff`, both for `e ∈ compEdges E C`); `IsNonBridge E e := e ∈ E ∧ ¬ IsBridge`
and `IsPendant E e := e ∈ E ∧ ∃ v ∈ e, degE E v = 1` (`Components.lean:91–97`). Conclusions:
`|J'| ≤ |oddComps|`, `(|oddComps| : ℝ) ≤ |V(E)|/2`, `∃ Sa Sb, Disjoint Sa Sb ∧ Sa ∪ Sb = E \ J' ∧
(∀ v ∈ Vb, Even (degE Sa v)) ∧ ∀ u ∈ Va, Even (degE Sb u)`; existence: every odd component has an
admissible edge, and some `J'` is an admissible choice. "For *every* such choice" is the ∀ over
`J'`. Faithful; the new Defs file is minimal, `module`, `@[expose] public section`, and adds
nothing a Spec could exploit.

**`HccpStatement`.** Hypothesis `S.Valid G` only. I compared `Valid` (`HCCP.lean:146–185`)
clause by clause with the TeX and found nothing beyond it: `k ≥ 1` (`k_pos`); admissible
orientations (`adm`); `B_𝒦 ⊆ E(G)` (`beads_G`, from "`B_𝒦 ⊆ E(G[A ∪ U])`" of defCluster); `T_j`
pairwise disjoint (`T_disj`); `pad ≡ 0` if `k = 1` on `⋃ LayP_j` (`pad_k1`); (D) = `D_KK` (verts
of distinct cluster indices disjoint) + `Cluster.disjoint` (hubs vs ports inside a cluster) +
`D_KT` (verts vs `T_j`) + `T_disj`; (P) `parityClean`; (JC-P): paths of `G` (`path_G`, `IsPathIn`
= non-empty Nodup list with edges in `E(G)`), ends in `LayP_j` / `LayP_{succ j}` (`path_ends`),
interiors in `T_j` (`path_T`), exact first/last counts `dem⁻`/`dem⁺` (`starts`, `ends`),
pairwise edge-disjoint (`path_edisj`), `E(𝒫_j)` pairwise disjoint (`pp_disj`), disjoint from
beads (`pb_disj`), beads pairwise disjoint (`bb_disj`, the TeX's last (JC-P) sentence). The
`k = 1` reading is uniform (`succ 0 = 0`, `pad = 0`); it is equivalent to the TeX's `X^out →
X^in` reading because with `pad = 0` a vertex of `LayP_0` with `exc ≥ 0` starts `dem⁻ = 0` paths
and one with `exc ≤ 0` ends none (`jcp_iff_jcpOne`). One-vertex paths cannot occur (for `k ≥ 2`
the two layers are disjoint by `D_KK`; for `k = 1` such a path would force `exc⁻ ≥ 1` and
`exc⁺ ≥ 1`). Conclusion: `∃ Φ : ℕ, (∀ j, Phi j = Φ ∧ |P j| = Φ) ∧ ∃ F, (∀ j, F j ⊆ pathEdges j ∧
pathEdges j \ F j ⊆ (G.induce (T j)).edges) ∧ ∃ D, IsDecomp (beads ∪ ⋃ F) D ∧ |D| ≤ Φ ∧ ∀ o ∈ D,
∃ c, o = cycle c ∧ max 3 k ≤ |c| ∧ cycleEdges c ⊆ E(G)`. `IsDecomp`'s `WF` gives `c.Nodup ∧ 3 ≤
|c|`, so each object is a cycle of `G`; `|c|` (vertices) equals the number of edges of the cycle
(`cycleEdges c` has length `|c|`). This is (i) and (ii) verbatim, including the length bound
`max(3,k)` that no consumer reads (kept, correctly). Faithful.

**`HccUnionStatement`.** Literal (`E i ⊆ E(G)`, pairwise disjoint, each with a decomposition
`D i` ⇒ `∃ D'`, `IsDecomp (⋃ E i) D' ∧ |D'| = ∑ |D i|`). Faithful.

**`HccGlobStatement`.** `q` systems, each `Valid G`; hypothesis `∀ s ≠ s', Disjoint
(beads_s ∪ allPathEdges_s) (beads_{s'} ∪ allPathEdges_{s'})`; conclusion: common `Φ s`, sets
`F s j` as in HCC-P (ii), and `D` decomposing `⋃_s (beads_s ∪ ⋃_j F s j)` with `|D| ≤ ∑ Φ s` and
every object a cycle of `G`. Two deviations from the TeX, both T0 and both recorded
(`T0-glob-input`): the hypothesis is at the input level (the TeX's names the outputs `F_j`), and
the conclusion adds "cycles of `G`". I checked both against the only consumer, JS-LC Step 7
(`s6.tex:588–594`): it establishes precisely "Their bead sets are pairwise disjoint … Their path
edges are pairwise disjoint … Path edges are disjoint from beads" (the cross-system bead/path
term is included in the Lean hypothesis) and reads the conclusion as "decomposes into at most
`∑_𝒮 Φ(𝒮)` cycles". The other sensible reading of the TeX ("for the `F_j` produced, if
`B_s ∪ ⋃ F_{s,j}` are pairwise disjoint then the union decomposes into `≤ ∑ Φ_s` objects") is
literally `hccUnion` applied to the outputs of `hccp`, both proved. No cross-system vertex
condition is assumed (the bowtie test `Sys` in `EGTest/ProbeP2E.lean` shares the port `0`).
Not a weakening.

**`HccpEndMultStatement`, `JsMultNumStatement`.** Proof-internal targets, see §4. In
`JsMultNumStatement` all subtractions are in ℕ, and with `2 ≤ M` none truncates (`M − 1 ≥ 1`,
`2M − 2 ≥ 2`), so the ℕ form is the intended arithmetic.

**Locked Defs.** `exc`, `excPos`, `excNeg`, `load`, `beadCount`, `ParityClean`, `IsAdmissible`,
`medOrient` match s6:defCluster; `pexc` sums `exc` over the clusters having `u` as a port (the
unique one under (D), `pexc_eq`); `demMinus`/`demPlus`/`Phi` match the TeX definitions;
`pathEdges j` = edges of the paths of `𝒫_j`; `beads` = all beads. Nothing here makes a Spec
easier than the TeX.

**Proof-side hygiene.** No `set_option`, `private`, `local instance`, `attribute`, `universe`
restriction or forbidden token in any unit file (lint 0 findings, greps above); all new files are
`module` with the right section headers; the axiom scan shows no axiom beyond `sorryAx` on the
unused stub. **Pass: no hidden weakening found.**

## 4. Refutation target coverage (task item 4)

TRIAGE §4 row P-2 (line 329) names for the engine part "the JS-LC Step 6/7 hypothesis checks
(joint multiplicity `≤ 2M_l − 2 ≤ t^JS`, distinct pair ends, T-avoidance, aggregated J1)"; the
named P-2 target of line 336, "two J^hub edges of one class at one hub (J1 aggregated)", belongs
to part 2 (P2J). This unit's declared target is the joint multiplicity, split into an engine part
and a numeric part.

Proved statements that cover it:
1. `EG.hccpEndMult : HccpEndMultStatement`. For every valid system, junction `j` and vertex `u`:
   `#{p ∈ 𝒫_j : head p = u ∨ last p = u} ≤ max(dem⁻ u, dem⁺ u)`, `max(dem⁻ u, dem⁺ u) = |pexc u| +
   pad u`, and `u ∈ U_{𝒦_i} → |pexc u| ≤ degE B_{𝒦_i} u`. I re-derived it from `Valid`: for `k ≥ 2`
   a vertex of `LayP_j` is a head of exactly `dem⁻` paths (`starts`) and never a last vertex
   (`path_ends` and `LayP_j ∩ LayP_{succ j} = ∅` by `D_KK`, since the clusters of the two layers
   have distinct indices, `succ j ≠ j`), symmetrically for `LayP_{succ j}`, and other vertices are
   no path end (`path_ends`); for `k = 1`, `pad = 0` (`pad_k1`) and one of `exc⁻`, `exc⁺` is `0`,
   so heads + lasts `≤ exc⁻ + exc⁺ = |exc| = max`. The identity conjunct is `max((−x)⁺, x⁺) + pad =
   |x| + pad` (`max_demMinus_demPlus`, `omega`); the third is `pexc_eq` plus `|d⁺ − d⁻| ≤ d⁺ + d⁻
   = deg_B` for an orientation. This is JS-LC Step 4's "Both are at most `|exc(u)| + pad(u)`",
   claim (c)'s "at a fixed junction a port occurs in at most `max(dem⁻, dem⁺)` pairs of each
   system containing it", and MED(b) as Step 4 uses it, reading the junction-`j` pairs of a
   system as the (first, last) pairs of `𝒫_j` (distinct vertices, as claim (a) says).
2. `EG.jsMultNum : JsMultNumStatement` and `EG.jsMult_lt_tJS`: for `M ≥ 2`, `⌈(M−1)/2⌉ ≤ ⌈M/2⌉ ≤
   M − 1`, `max(2M − 2, (M − 1) + ⌈M/2⌉) = 2M − 2 < 2M + 2 = Stage1.tJS G run l`
   (`tJS_eq_two_mul_add_two` is `rfl` against `EG/Defs/Stage1/COL.lean:97`).

The aggregation over the systems of `(Y,l)` is not in this unit and is correctly declared as a
hand-off (module docstring of `EngineMult`, P2E.md fix rounds 1–2). I verified that part 2 has
closed it: `EG.Spec.JslcJointMultStatement` (`EG/Spec/Chain/JSLCRouting.lean:131`) states, for
`M ≥ 2`, systems `Sys s` with a `cherry` flag, at most one non-cherry system, `|exc| ≤ M − 1` and
`pad ≤ ⌈M/2⌉` at its ports, `|exc| ≤ 1` and `pad ≤ 1` at cherry ports, `𝒮_0`/cherry exclusivity
and at most `M − 1` cherry systems per vertex, that `∑_s junctionOcc (Sys s) j v ≤ 2M − 2 ∧
2M − 2 < 2M + 2` for every junction `j` and vertex `v`; `EG.jslcJointMult`
(`EG/Proof/Chain/JSLCRouting.lean:68`) proves it, and my axiom scan of that module reports `0 use
sorryAx`. Since `junctionOcc` (`EG/Defs/Probe/P2J/PreSystem.lean:61`) is `0` for a vertex in
neither `LayP_j` nor `LayP_{succ j}`, the previous audit's cosmetic remark that "centres occur in
no pair" was not a conjunct of the engine Spec is now moot at the aggregated level. I re-derived
the aggregation by hand and found no error: a port of `𝒮_0` occurs at a junction in `≤ |exc| +
pad ≤ (M_l−1) + ⌈(M_l−1)/2⌉ ≤ (M_l−1) + ⌈M_l/2⌉` pairs (Cap(ii) gives `deg_{R_Y}(u) ≤ M_l − 1`,
hence `|exc| ≤ M_l − 1` by MED(b); the padding spread is feasible because `Π_j ≤ Φ^raw_j =
½∑_{LayP_j}|exc| ≤ ½(M_l−1)|LayP_j|`); a port of cherry systems in `≤ 2(M_l−1)` (at most `M_l−1`
cherry systems, demand `≤ 2` each since `|exc| = 1`, `pad ≤ 1`); centres in none; both
`≤ 2M_l − 2 < 2M_l + 2` for `M_l ≥ 2`.

**Assessment: the engine part of the target is covered by proved statements of this unit, and
the aggregated form is covered by a proved, sorry-free Spec of part 2.**

## 5. Classification of every math finding (task item 5)

| # | finding (source) | class | my evidence |
|---|---|---|---|
| F1 | HCCglob ¶2 stated with input-level disjointness (beads ∪ all path edges of distinct systems) and with "cycles of `G`" in the conclusion (author H1; review 1 R1; review 2; previous audit; CONVENTIONS `T0-glob-input`) | **T0** | The TeX hypothesis names the `F_j`, which exist only after HCC-P is applied, so it is not well formed as a hypothesis on the inputs. `F_j ⊆ E(𝒫_j)` makes the input-level condition stronger; Step 7 (`s6.tex:588–594`) proves exactly the input-level condition and reads the conclusion as "at most `∑_𝒮 Φ(𝒮)` cycles". The output-level reading is `hccUnion ∘ hccp`, also proved. Encoding decision, correct; optional wording recorded in the T0 table. |
| F2 | JS-LC claim (c) writes `max(2M_l−2, (M_l−1)+⌈M_l/2⌉) = 2M_l−2` without `M_l ≥ 2` (author §6; both reviews; previous audit) | **T1** | At `M_l = 1`: `2·1−2 = 0` but `(1−1)+⌈1/2⌉ = 1`, so the equality fails, while `1 ≤ t = 4` still holds. The claim's own proof says "For `M_l ≥ 2`", and `M_l ≥ 2^40` by (R2) (`s2.tex:518, 526`: `M_l := ⌈max(2^40, …)⌉`). Harmless wording; `JsMultNumStatement` carries `2 ≤ M`. |
| F3 | HCC-P Step 3 asserts `\|𝒲\| = \|𝒫_{k−1}\| = Φ`; the Lean proof uses only `\|𝒲\| ≤ Φ` (author, proof round 1; previous audit) | **none (T1 at most)** | GATE needs only `≤`; the Lean proof bounds `\|𝒲\| ≤ ∑_{LayP_0} d⁻_{D_{k−1}} ≤ ∑_{LayP_0} dem⁺ = Φ`. The equality is true anyway: an arc of `D'_{k−1}` with head a port is the last arc of its path (interiors lie in `T_{k−1}`, disjoint from ports), cancelled cycles lie inside `T_{k−1}` so last arcs survive, and edge-disjoint paths have distinct last arcs. No gap in the manuscript. |
| F4 | PAR's citation of s1:citEuler (a) replaced in Lean by a direct `T`-join construction (author, proof round 1; blueprint PAR-DIRECT-PROOF-OPTION) | **none** | A proof alternative; the manuscript's route through a spanning tree is also valid (`C'` is connected, `\|T\|` even). The Spec is unchanged; the declared input became unused (§6 item 2). |
| F5 | EQ-USE-EMPTY-S0: with `𝒮_0(Y,l) = ∅`, `k_0 = min(K, max(1, ⌊ΣΦ/(2Φ_max)⌋))` divides by `Φ_max = 0` and EQ-LPT needs `m ≥ 1` (blueprint; review 2; author H7) | **T1 (JS-LC, part 2; not this unit)** | Step 4's formula is literally undefined at `m = 0`; Step 6 says "`𝒮_0(Y,l)` (if non-empty)". Nothing is claimed for an empty system, so this is a case split the Lean proof of JS-LC must make (P2J.md records it). No statement of this unit is touched. |
| F6 | The second conjunct of `HccpEndMultStatement` is an identity (review 1; review 2 scratch V2) | **none (cosmetic)** | `dem⁻ = (−x).toNat + pad`, `dem⁺ = x.toNat + pad`, `max = x.natAbs + pad` for every `x : ℤ` (`max_demMinus_demPlus`, by `omega`). Kept on purpose to tie the bound to the TeX's `\|exc(u)\| + pad(u)`; documented in the module docstring. |
| F7 | `IsParChoice`'s conjunct `J' ⊆ E` is implied by the third conjunct (review 2, R2-1) | **none (cosmetic)** | `IsNonBridge E e := e ∈ E ∧ ¬ IsBridge`, `IsPendant E e := e ∈ E ∧ ∃ v ∈ e, degE E v = 1` (`EG/Defs/Components.lean:91–97`). Redundant, harmless, documented. |
| F8 | "Centres occur in no pair" is not a conjunct of `HccpEndMultStatement`; the engine bound at a non-port is the junk value `pad u` (previous audit) | **none (cosmetic; resolved in part 2)** | For a non-port `u`, `pexc u = 0` and `Valid.countP_head_eq`/`countP_last_eq` give `0` path ends, so the conjunct `0 ≤ pad u` is true but uninformative. The aggregated Spec `JslcJointMultStatement` uses `junctionOcc`, which is `0` off the layers, so the aggregation does not rely on `pad` at centres (§4). |
| F9 | The unit's fix round 1 edited `CONVENTIONS.md`, a file listed in `LOCK.json` (mine, from `scripts/lock.py check`) | **none (process, minor; not a math finding)** | See §6 item 1. The row's content is correct. |

I also re-derived, independently and with no error found: MED (a) (each bead is oriented by
exactly one rule; the `2d` port neighbours of a hub have positions `1..2d`, so `d` in- and `d`
out-arcs; `pot(h) = (rk(u_d) + ½)/(|U|+1) ∈ (0,1)`, `pot(h) = ½` for a bead-less hub); MED (b)
(`|exc| ≤ d⁺ + d⁻ = deg_B` with the same parity, since the arcs at `u` are in bijection with the
beads at `u` and no arc is a loop; the handshake plus hub balance and `ends_mem` gives `∑_U exc
= 0`; `Φ ≤ ∑_U d⁺ = #{port→hub} + e(B[U]) = ∑_h d⁻(h) + e(B[U]) = b(𝒦)` using "no hub–hub bead"
and `d⁻(h) = deg(h)/2`); EQ-LPT (existence by recursion since an empty layer has minimum load
`0` under `Φ ≥ 0`; if a layer stayed empty every item would go to a layer empty before it, so `σ`
would be injective into `k − 1` layers, contradicting `k ≤ m`; the last-item argument for the
spread, using that loads only grow); PAR (a component with an edge has a cycle, whose edges are
non-bridges, or is a tree with a leaf; `|J'| = #odd ≤ |V(E)|/2` since odd components have `≥ 2`
vertices and are vertex-disjoint; after deleting a non-bridge the component stays connected with
an even number of edges, after deleting a pendant edge at a leaf `x` the rest stays connected
because no path between two vertices `≠ x` passes through a degree-1 vertex; the prescription
`∑_{V(C')} p ≡ ∑_{V_a ∩ V(C')} deg_{C'} = |E(C')| ≡ 0` needs every edge to have exactly one end
in `V_a`, i.e. `Disjoint Va Vb`; the `T`-join and the two degree conditions); HCC-P Steps 0–4
for `k = 1`, `k = 2` (`LayP_{j+1} = LayP_{j−1} ≠ LayP_j`) and `k ≥ 3` (ports are sources or sinks
of `D_j` so cancellation touches no port arc; balance `exc + dem⁻ − dem⁺ = 0` at ports, at hubs
by admissibility, at `T_j` vertices by per-path counting; `Ψ` in blocks `[3j, 3j+3)`; length
`≥ k` from `k − 1` block crossings plus the `𝒲`-arc, `≥ 3` from GATE); HCCglob ¶1 (concatenation
of decompositions of disjoint edge sets) and ¶2 (HCC-P per system, `F_{s,j} ⊆ E(𝒫_{s,j}) ⊆
allPathEdges_s`, then ¶1).

**No T2 or T3 finding, no suspect item, no counterexample to any statement of this unit.**

## 6. Issues (none blocking)

1. **Minor (process) — `CONVENTIONS.md` is a locked file and was edited by the unit.**
   `scripts/lock.py check` reports exactly one violation, `LOCK: locked file changed or missing:
   CONVENTIONS.md`. The lock hash (`LOCK.json:5199`) equals the file's hash at `3a26761`; the
   only later change is the one-line row `T0-glob-input` appended in `3278dd4` (P2E fix round 1,
   on review 1's suggestion R1) and unchanged since. The content is right (§5 F1), but the lock is
   now red until the integrator re-hashes `CONVENTIONS.md` (or moves the row). The author's
   P2E.md does record "Edited shared file: `CONVENTIONS.md`", so this is not hidden. Not a
   correctness issue.
2. **Minor — unused declared input, still the only sorry.** `EG.eulerTreeTJoin` (s1:citEuler (a))
   is unreachable from every probe theorem (§1) but remains in the tree and in P2E.md §3's
   declared-input table (the later section "Declared input no longer used" corrects it). The
   integrator should either prove it from `EG.exists_tJoin` (a spanning tree is connected, so
   every component of `(V(H), S)` contains all of `T`, whose size is even), which would empty the
   unit's sorry frontier, or move it out of the P2E input list while keeping
   `EulerTreeTJoinStatement` as the canonical s1:citEuler (a) for s5:lemParent Step 3. Not a
   correctness issue.
3. **Cosmetic — locks and root lists.** The unit's Spec files, `EG/Defs/Probe/P2E/Par.lean` and
   the three Spec constants of `EngineMult`/`EulerTreeTJoin` are PENDING in the lock check, and
   `EG.lean` lists none of the unit's Spec/Proof modules (it lists only the locked Defs and Lib
   `Chain.EqLpt`/`Chain.HCCP`). Expected before the freeze; H5 asks for a lock on `Par.lean`
   before P2J's use of `IsParChoice` is frozen.
4. **Cosmetic** — F6, F7, F8 above; `HccUnionStatement` keeps the literal, proof-unused
   `E i ⊆ E(G)` (keep).

## 7. Summary for the orchestrator

- Sorry frontier = {`EG.eulerTreeTJoin`}, the declared-input stub, unused by every probe theorem;
  axiom scan: 1744 constants, 1 `sorryAx`, 0 violations; lint 0 findings; test file compiles
  (0 errors, 0 sorry); oleans fresh.
- Statement bodies identical in every commit since each file's creation (`1e0e84a`/`3a26761`,
  `3278dd4`, `41e8a4e`, HEAD `ed552cf`, working tree); the fix rounds changed docstrings only.
- No hidden weakening; the new Defs file `Par.lean` is faithful and minimal; `Valid` is exactly
  (D), (P), (JC-P).
- Refutation target: engine part (`hccpEndMult`) and numeric part (`jsMultNum`, `jsMult_lt_tJS`)
  proved here; the aggregated claim (c) is proved in P2J (`jslcJointMult`, 0 `sorryAx`).
- Math findings: T0 ×1 (HCCglob ¶2, correct decision), T1 ×2 (claim (c) at `M_l = 1`;
  EQ-USE-EMPTY-S0 for part 2), no T2/T3, no suspect item.
- One process item: `CONVENTIONS.md` (locked) carries the unit's appended T0 row; the lock check
  is red by exactly that file until the integrator re-hashes it.
