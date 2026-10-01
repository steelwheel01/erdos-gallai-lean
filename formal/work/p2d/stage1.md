# P2-D [stage1]: stage-1 random data (s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule stage 1)

Status: 4 Defs files, 4 Lib files and 1 test file compile with 0 errors, 0 warnings and 0 `sorry`.
`python3 -I scripts/lint.py` on the 9 files reports 0 findings. The axiom scan
(`scripts/Axioms.lean --prefix EG EG.Lib.Stage1.Law`) inspects 1836 constants and reports 0 violations and
0 `sorryAx`. `scripts/lock.py check` reports 0 violations; the new Defs are PENDING (not locked yet).

The HB Run model (`EG.HB.Run`, `PartId`, `run.ancVerts/ancGraph/ancEps/ancS/LY/lam/M/s`) is used as is. No existing
file was changed.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Stage1/COL.lean` | `EG.Defs.Stage1.COL` | `LentTag`, `lateRounds`, `KJS`, `rhoJS`, `tJS`, `Tslot`, `IU`, `IJS`, `IJV`, `lentIdx`, `klend`, `JY`, `kown` (+ `NeZero`), `pY`, `tY`, `ownIdxOf`, `ownIdx`, `EdgeLabel`, `Colouring`, `jsSites`, `JSLabels`, `COLOut`, `bitLaw`, `idxLaw`, `ownLaw`, `edgeLaw`, `jsWeight`/`jsSupport` (+3 lemmas), `jsLabelLaw`, `colouringLaw`, `jsLaw`, `colLaw`, `Own`, `Lend`, `lentClass`, `LU`, `LJS`, `LJV`, `ownClass`, `ownR`, `ownM`, `Tj`, `COLa`, `COLb`, `COLc`, `COLe`, `COLg` |
| `EG/Defs/Stage1/Zones.lean` | `EG.Defs.Stage1.Zones` | `ZIdx`, `zp`, `availParts`, `zpSum`, `zoneWeight`/`zoneSupport` (+5 lemmas), `zoneLabelLaw`, `zoneLaw`, `zoneOf`, `Zone`, `zonePhase`, `rhoY` |
| `EG/Defs/Stage1/Pool.lean` | `EG.Defs.Stage1.Pool` | `poolIdx`, `qPool`, `piPool`, `poolMass`, `plabWeight`/`plabSupport` (+5 lemmas), `poolLabelLaw`, `poolLaw`, `plabOf`, `poolSet`, `poolL`, `poolRound` |
| `EG/Defs/Stage1/Law.lean` | `EG.Defs.Stage1.Law` | `Coord`, `CoordVal`, `coordLaw`, `Outcome` (fields `col`, `zone`, `js`, `pool`), `Outcome.ofCoords/toCoords/cOut/colAt/jsAt/cOutAt/labAt`, `law` |
| `EG/Lib/Stage1/COL.lean` | `EG.Lib.Stage1.COL` | index-family membership and disjointness, `klend_eq_card_lentIdx`, `lentIdx_eq_empty_iff`, `klend_pos_iff`, `card_IU_of_isLight`, `card_IJV`, `KJS_mul_rhoJS`, `rhoJS_le_one`, `one_le_kown`, `ownIdx_none/some`, `*_eq_colourClass` (rfl), vertex sets, edge membership, partitions, `COLg_of_mem_supp`, `Tj_subset`, `disjoint_Tj`, `COLa_iff_of_isLight`, `COLa_iff_of_not_isLight`, `prob_jsLabelLaw_some/none`, `prob_idxLaw_some`, `prob_mem_LJV`, `isRSubset_Tj` |
| `EG/Lib/Stage1/Zones.lean` | `EG.Lib.Stage1.Zones` | `ancVerts_subset_verts`, `zoneLabelLaw_w_of_le`, `prob_zoneLabelLaw_none`, `prob_zoneLabelLaw_choice` (two-step marginal), `rhoY_eq_zp_div_card`, `prob_zoneLabelLaw_some`, `mem_Zone`, `Zone_subset`, `disjoint_Zone` (lemZones (iii)), `isRSubset_Zone` (lemZones (ii), law form), `zonePhase_eq_some_iff`, `zonePhase_eq_none_iff` |
| `EG/Lib/Stage1/Pool.lean` | `EG.Lib.Stage1.Pool` | `mem_poolIdx`, `poolLabelLaw_w_of_le`, `prob_poolLabelLaw_some/none`, `piPool_eq`, `sum_piPool`, `mem_poolSet`, `mem_poolL`, `disjoint_poolL`, `disjoint_poolSet`, `mem_poolSet_poolRound`, `poolRound_eq`, `two_pow_le_M`, `qPool_pos`, `qPool_le` |
| `EG/Lib/Stage1/Law.lean` | `EG.Lib.Stage1.Law` | bijection lemmas, `indepFun_of_dependsOn`, `iIndepFun_of_dependsOn`, `map_eq_pi_of_dependsOn`, `map_toCoords_apply`, marginals `map_col`, `map_js`, `map_cOut`, `map_cOutAt`, `map_zone`, `map_pool`, independence `indepFun_col_js(_apply)`, `iIndepFun_cOut`, `iIndepFun_col_edges`, `iIndepFun_zone`, `iIndepFun_pool`, `indepFun_colJS_zone`, `indepFun_cOut_zone`, `indepFun_cOutAt_zone`, `indepFun_rest_pool`, `indepFun_cOut_pool`, support `law_w`, `mem_supp_law_iff`, `col_mem_supp_colouringLaw`, `COLg_of_mem_supp_law`, `zone_mem_supp`, `Zone_eq_empty_of_not_mem_IU`, `lightParts_of_zone_eq`, `pool_mem_supp`, `zonePhase_eq_some_iff_mem_Zone`, per-edge marginal `map_col_apply`, mixed shapes `iIndepFun_edge_pool`, `iIndepFun_edge_zone`, `Outcome.mem_Tj_iff` |
| `EGTest/Stage1.lean` | — | own-label bijection, JS weights at `M = 2`, `π` values, the valid run `run1` on `K_3` (empty lent families, `k_own = 1`, no pools, no zones, marginals, COL(g) on the support), a 3-round choice list (`JV 3 ∈ lentIdx`, `k_lend ≥ 1`, `poolIdx = {(3,1)}`, `P(e ∈ LJV) = p_Y`), generic instances |

Size (after fix round 2): Defs 892 lines, Lib 1609 lines, tests 301 lines.

The root files (`EG.lean`, `EGTest.lean`) are not edited (integrator-owned; `scripts/gen_roots.py`).

## Decisions

All names live in the namespace `EG.Stage1`.

**D-S1-1 (argument order).** Every `EG.Stage1` definition takes `G run` first, then the ancestor `Y : PartId`.
This follows TRIAGE §2.7's `EG.Stage1.Outcome G run` / `EG.Stage1.law G run`. Note that the HB API is `run.foo G Y`.
`lateRounds run r`, `IJV run Y` and `poolIdx run` do not take `G`, because they do not depend on it.

**D-S1-2 (one product space).** Every stage-1 variable is a coordinate of one finite product (`Coord G run`):
- an edge label triple per edge `e ∈ E(H_Y)` of each ancestor (1a);
- a zone label per vertex (1b);
- a JS label per site `(Y,(l,y))` (1c);
- a pool label per vertex (1d).

`law G run := (pi coordLaw).map Outcome.ofCoords`. `Outcome` is a record with the four fields named in TRIAGE §2.7:
`col`, `zone`, `js`, `pool`. The `col` and `js` fields are indexed by the subtype `↥(run.ancestors G)`.

Every independence statement of the manuscript about stage 1 is an instance of one lemma, `indepFun_of_dependsOn`
(functions of disjoint coordinate sets), or of its mutual form `iIndepFun_of_dependsOn`. This covers:
- "data of distinct ancestors", "distinct edges", "labels vs colours" (s3:defCOL);
- zones vs lending data (lemZones (iv)), the joint form that s3:lemCOL (c) and s5:lemE1 (c) consume;
- pools vs the rest (s7:defPool).

Marginals: `map_cOut : law.map (·.cOut Y) = colLaw G run Y`. This is exactly the hypothesis form
"`μ.map D = colLaw Y`" of the lemCOL Specs (TRIAGE §2.7).

**D-S1-3 (per-ancestor data, total accessors).** `Outcome.colAt/jsAt/cOutAt/labAt` read an outcome at any
`Y : PartId`. Off the ancestors they return a junk value: bit `false`, index `none`, own label `0`, JS label `none`.
`cOutAt_of_mem` identifies `cOutAt` with `cOut` on ancestors. Events are then applied as `COLa G run Y (ω.cOutAt Y)`.

**D-S1-4 (edge labels on the fixed edge set; TRIAGE COL-EMPTY-INDEX, L15-RANDOM-EDGESET).** Each edge of `H_Y` carries
`(bit, idx, own) : Bool × Option LentTag × Fin (kown G run Y)`.
- `bit = false` means `Own_Y`; `bit = true` means `Lend_Y`.
- `idx` is uniform on `lentIdx`, or `dirac none` when `lentIdx = ∅`. By `lentIdx_eq_empty_iff`, that happens exactly when `R < r + 2`.
- `own` is uniform on `Fin (kown G run Y)`. `kown = 4·pvJ|V(Y)| + 1 ≥ 1` for every ancestor (instance `kown.neZero`). For standalone `Y` the own label is drawn and never read.

The manuscript's "three independent uniform random variables" is therefore read with these two conventions for the
empty and standalone cases. No law that the manuscript uses changes.

**D-S1-5 (tags).** `LentTag := U l c σ | JS l j | JV l`. `c : Fin 4`, `σ < T^sl_Y` and `j < K^JS_l` are 0-based;
rounds stay 1-based, with `Y.1 + 2 ≤ l ≤ R`. `klend` is the literal sum `|I^U| + |I^JS| + |I^JV|`.
`klend_eq_card_lentIdx` proves that it equals the size of the tagged union, on which `idx` is uniform.

**D-S1-6 (classes written out).** `Own`, `Lend`, `lentClass`, `ownClass` are written as
`H_Y.restrictEdges (selectSet E(H_Y) (fun e => decide (κ e = i)))`. By `rfl` this is `colourClass H_Y κ i` of
`EG.Lib.Found.ColourClass` (`*_eq_colourClass`). The Defs therefore import no Lib module; this is the same convention
as `EG.Spec.L15pStatement`. All classes are graphs with vertex set `V(Y)`.

`LU`, `LJS`, `LJV` are `lentClass` at the three tags. `ownR`, `ownM` are `ownClass` through
`ownIdx N : Option (Fin (pvJ N) × Fin 4) ≃ Fin (4·pvJ N + 1)`, which maps `R_{j,c} ↦ 4j + c` and `M ↦ 4J`
(TRIAGE §2.7 PV-OWNCLASS-INDEX).

**D-S1-7 (JS label law, no guard).** `jsLabelLaw G run l` has weights:
- `some j ↦ M_l^{-4}` for `j < M_l^2`;
- `none ↦ 1 - M_l^{-2}`;
- `0` otherwise.

These weights form a distribution for every `M_l ∈ ℕ`, `M_l = 0` included, so no guard is needed. The label law is
exact because `M_l ∈ ℕ` (M-INTEGER).

**D-S1-8 (zone law; TRIAGE §2.7 1b, ZONE-TWO-STEP, ZONE-LAW-WELLDEF).**
- The label is `Option ZIdx`, with `ZIdx = PartId × LentTag`. The sublabel is the U-tag, so "the sublabels available to `Y` are exactly `I^U(Y)`" holds by definition.
- One-step weights: `zp_Y / |I^U(Y)|` on `(Y, i)` and `1 - Σ_{Y ∈ A(v)} zp_Y` on `none`.
- The `dite` guard is exactly `zpSum ≤ 1`, with fallback `dirac none`.
- The sum-to-one proof uses that an available `Y` with `I^U(Y) = ∅` has `T^sl = 0`, so `L_Y = 0` and `zp_Y = 0`.
- `prob_zoneLabelLaw_choice` recovers the two-step marginal `P(choice(v) = Y) = zp_Y`.
- `prob_zoneLabelLaw_some` gives `P(label = (Y,i)) = ρ_Y`, with `ρ_Y` as in lemZones (ii). `rhoY` uses real subtraction `R - r - 1`.
- `isRSubset_Zone` is lemZones (ii) in law form. Its hypotheses are the guards at the vertices of `Y`, which (s5:eqZp) discharges.

**D-S1-9 (pool law; POOL-LAW-NEEDS-GAMMA, POOL-ROUND-OFFSET).**
- `poolIdx = {(l,r) : 3 ≤ l ≤ R, 1 ≤ r, r + 2 ≤ l}`.
- `π_{l,r} = 2^{-((l:ℤ)-1-r)}` as a `zpow`; `piPool_eq` gives the `(1/2)^{l-1-r}` form.
- The `dite` guard is exactly `poolMass ≤ 1`, with fallback `dirac none`.
- Weight names: the label weights are `plabWeight`, because `poolWeight` is reserved for s7's `ω_l(v)` in `EG.Quot` (TRIAGE §2.10).
- `poolRound` is junk `0` off the pool; `poolRound_eq` gives its uniqueness on `Pool_{l,r}`.
- No `∀ l, 0 < M l` conjunct in the guard (blueprint s7a lean_shape has one): it is unnecessary.
  `M_l ∈ ℕ` and `(0:ℝ)^(-2:ℤ) = 0`, so `q_l ≥ 0` and every weight is nonnegative regardless of
  `M_l`; the guard needs only the total mass. In fact `M_l ≥ 2^40` always (`two_pow_le_M`, R2's
  `max(2^40, …)`), so `0 < q_l ≤ 2^{-80}` (`qPool_pos`, `qPool_le`). (Fix round 2, cosmetic item.)

**D-S1-10 (events of Lemma COL).**
- `COLa` is item (a) with `ε_Y`, `s_Y`, and "every own class" read as all `k_own` labels.
  - `COLa_iff_of_isLight` unfolds it to s5:defStages' COL(a): `(2^{-6}, s_r/8)`, `(2^{-6}, s_r/(16k_lend))`, `(2^{-6}, s_r/(16k_own))`.
  - `COLa_iff_of_not_isLight` unfolds it to `(2^{-5}, s_r/4)` and `(2^{-5}, s_r/(8k_lend))`.
- `COLb` is item (b) over `l ∈ lateRounds`, `j < K^JS_l`, with `t = (t^JS_l : ℝ)`.
- `COLc ω Vs` is item (c) for a family `Vs : LentTag → Finset V`; only the indices `i ∈ I^U(Y)` are read.
- `COLe` holds the deterministic inequalities only. The "on (a)" consequences are `COLa` (blueprint COL-E-DETERMINISTIC).
- `COLg` holds the partition facts. The lent-class partition needs `idx ∈ lentIdx`, which is true on the support only, so `COLg` is an event. `COLg_of_mem_supp` / `COLg_of_mem_supp_law` prove that it holds at every outcome of positive weight.
- The consumer-exclusivity sentence of (g) is a design rule for s4–s6, not a predicate (COL-CONSUMERS-NOT-A-PROPERTY).

**D-S1-11 (derived quantities).**
- `pY = 1/(2k_lend)`, junk `0` for `k_lend = 0`. `prob_mem_LJV` gives `P(e ∈ LJV_{Y,l}) = p_Y` for `l ∈ lateRounds`.
- `tY = ⌈λ_r^{1.6}⌉₊`, using `rpow` with the literal `1.6`.
- The claim `t_Y ≥ M_l` needs Γ1 and s2:lemTower. It is not proved here; it is an s3/s5 Spec.

## For the consumers

- **lemCOL Specs.** Quantify `∀ Ω μ D, μ.map D = colLaw G run Y → …`. For (c), use `μ.IndepFun D Vs`.
  - On the stage-1 law, `map_cOutAt`/`map_cOut` supply the marginal.
  - `indepFun_cOutAt_zone` composed with `fun ζ i => Zone G run ζ Y i` supplies the joint independence of the zones of `Y`.
  - `isRSubset_Zone` supplies the ρ-random property.
- **s5 (Light/Stages).**
  - `E1` reads `ownM G run Y (ω.colAt Y)` and `zonePhase ω.zone l u`.
  - "demoted" reads `COLa G run Y (ω.cOutAt Y)`.
  - "parent-bad" reads `COLc G run Y (ω.cOutAt Y) (fun i => Zone G run ω.zone Y i)`, which is literally "some `LU_{Y,l,c,σ}` is not path connected through its zone".
- **s6 `EG.Chain.StageData` instantiation** (written after Light/Stages):
  - `colA Y := COLa G run Y (ω.cOutAt Y)`;
  - `colB Y := COLb G run Y (ω.cOutAt Y)`;
  - `lab := ω.labAt` (`Outcome.mem_Tj_iff` relates it to `Tj`);
  - `own Y := (Own G run Y (ω.colAt Y)).edges`;
  - `ljs Y l j := (LJS G run Y (ω.colAt Y) l j).edges`;
  - `ljv Y l := (LJV G run Y (ω.colAt Y) l).edges`;
  - `demoted`, `dem`, `lp` come from the Light layer.
- **s7.**
  - `Pool_{l,r} = poolSet G ω.pool l r`, `Pool_l = poolL G ω.pool l`, `r(w) = poolRound ω.pool w`.
  - The candidate count uses `indepFun_cOut_pool`, `iIndepFun_pool`, `iIndepFun_col_edges` and `prob_mem_LJV`.
- **Guards.**
  - `zpSum ≤ 1` needs (s5:eqZp).
  - `poolMass ≤ 1` needs s2:lemTower (b) and Γ.
  - Both are Spec obligations. Until they are discharged, statements about the true laws carry them as hypotheses (`zoneLabelLaw_w_of_le`, `poolLabelLaw_w_of_le`).

## Manuscript readings (no T1/T2 found)

- **s3:defCOL, the "Formally, … three independent uniform random variables" sentence.** It is ill-defined when
  `k_lend(Y) = 0` (uniform on `∅`) and, for standalone `Y`, `k_own` is defined only for light `Y`. The reading
  "a lent index if `r ≤ R-2`, an own label (for light `Y`)" is encoded by D-S1-4. This is T0; a wording suggestion is
  already in blueprint s3b COL-EMPTY-INDEX.
- **s5:defZones, the two-step choice.** It is replaced by the equal one-step law (D-S1-8). The two-step marginal is a lemma.
- **s3:lemCOL (g), the lent-class partition.** It is a property of the support, not of every assignment of labels.
  This is harmless: the Lean `COLg` is proved on the support.

## Fix round 1 (review `work/p2d/stage1.review1.md`, verdict APPROVE with 5 minor and 2 cosmetic items)

No Defs file was changed. `scripts/lock.py check`: 0 violations; `python3 -I scripts/lint.py`: 0 findings;
`scripts/check.sh` on `EG/Lib/Stage1/COL.lean` and `EGTest/Stage1.lean`: rc=0, 0 errors, 0 sorry, 0 warnings;
`lake build EG.Lib.Stage1.Law EG.Lib.Stage1.Zones EG.Lib.Stage1.Pool` succeeds.

| Item | Verdict | Action |
|---|---|---|
| M1 (COLg is an event; no T0 entry; no `colLaw`-support or `μ.map D = colLaw` lemma) | valid | `COLg_of_mem_supp_colLaw` and `COLg_of_map_eq` (`μ.map D = colLaw G run Y → 0 < μ.w ω → COLg G run Y (D ω)`) added to `EG/Lib/Stage1/COL.lean`. T0 row `T0-colg-supp` and a "Stage 1" CONVENTIONS bullet (below; to be merged by the integrator) say that the Spec is stated on the support, never `∀ ω, COLg …`. The blueprint s3b lean_shape `(∀ ω, EG.Lend.COLg run G Y ω)` is superseded by this. |
| M2 (no CONVENTIONS Stage1 block; renamed blueprint names) | valid | Proposed CONVENTIONS section "Stage 1" (below) lists the renames and the argument order `G run Y`. |
| M3 (junk values and guards) | valid | The same proposed section lists the guards: `Y ∈ run.ancestors G`, `Y.1 + 2 ≤ run.R`, light `Y` for `tY`, `w ∈ poolL`, `i ∈ IU`, and the hypotheses `zpSum G run v ≤ 1`, `poolMass G run ≤ 1` until their Specs are proved. |
| M4 (COL-RANDOM-EDGESET conditional law) | valid (proof-phase gap) | Added to `EG/Lib/Stage1/COL.lean`: `edgeBits`, `edgeLabels` (`@[expose]` Lib defs), `map_pi_restrict`, `map_edgeBits_edgeLabels`, `map_edgeBits`, `map_edgeLabels`, `indepFun_edgeBits_edgeLabels`, `map_edgeLabels_cond_edgeBits`, `map_idx_cond_edgeBits` (given the bits `β`, the indices of the edges with bit `true` are i.i.d. `idxLaw`), `map_own_cond_edgeBits` (given `β`, the own labels of the edges with bit `false` are `randColouring {e // β e = false} (kown G run Y)`), `idxLaw_eq_of_nonempty` (`idxLaw` = uniform on `lentIdx`, as `some`). Still left to the lemCOL prover: transporting the lent indices along `↥lentIdx ≃ Fin k_lend` (from `klend_eq_card_lentIdx`) to get a literal `randColouring … (klend G run Y)`. |
| M5 (non-vacuity tests) | valid | `EGTest/Stage1.lean` gains: `COLg_of_mem_supp_colLaw` and `COLg_of_map_eq` instances; the abstract positivity `0 < P(label(v) = (Y,i))` under the guard, `Y ∈ availParts v`, `i ∈ IU`, `L_Y > 0`; the conditional laws given the bits; "an Own edge is in no lent class". A concrete valid run with a light part of ≥ 2 vertices and `R ≥ r + 2` is still not built (the reviewer says it is not needed for the lock). |
| C1 (TRIAGE says Tslot is in Zones.lean) | valid | TRIAGE §3 items 15/16 updated: Tslot is in COL.lean (needed by `IU`). |
| C2 (`lateRounds`, `IJV`, `poolIdx` omit `G`) | valid, by design (D-S1-1) | Recorded in the proposed CONVENTIONS Stage 1 block ("never write `lateRounds G run r`"). No code change. |

**CONVENTIONS.md is a locked file** (`scripts/lock.py`: "locked file changed or missing: CONVENTIONS.md").
An edit was tried and reverted byte-for-byte to the locked version (lock check back to 0 violations). The
integrator should paste the block below into `CONVENTIONS.md` before the "Probability" section, and the row
below into its T0 table, then re-lock. Until then this section is the reference for Spec authors.

### Proposed CONVENTIONS block "Stage 1 (EG.Stage1; design note work/p2d/stage1.md)"
- Names (blueprints s3b/s5/s6b/s7a are superseded): namespace `EG.Stage1`, not `EG.Lend`;
  `T` → `Tj`, `tauJS` → `tJS`, `JSSite` → `jsSites`, `stage1Law`/`S3.stage1Dist` → `Stage1.law G run`,
  `ω.zlab` → `ω.zone`, `ω.lab` → `ω.labAt`, `ω.LJS Y` → `LJS G run Y (ω.colAt Y)`, `ω.Mcls` →
  `ownM G run Y (ω.colAt Y)`. Events read the per-ancestor outcome: `COLa G run Y (ω.cOutAt Y)`.
- Argument order: `G run` first, then the ancestor `Y : PartId` (`klend G run Y`, `IU G run Y`,
  `colLaw G run Y`), not the blueprint order `run G Y`. Exceptions (no `G`, they do not depend on
  it): `lateRounds run r`, `IJV run Y`, `poolIdx run`; never write `lateRounds G run r`.
- Guards against junk values (the definitions are total):
  - `ω.colAt/jsAt/cOutAt/labAt Y` are junk (bit false, index none, own 0, label ∗) off the
    ancestors: assume `Y ∈ run.ancestors G` (or `Y ∈ run.lightParts G`);
  - `pY` is `0` when `k_lend = 0` and `rhoY` is junk for `r ≥ R-1`: assume `Y.1 + 2 ≤ run.R`;
  - `tY` is defined for every `Y` but meaningful only for light `Y`;
  - `poolRound π w` is `0` off the pool: read it only under `w ∈ poolL G π l`;
  - `Zone`, `COLc` are indexed by all `LentTag`s but meaningful only for `i ∈ IU G run Y`;
  - the true zone and pool laws hold only under `zpSum G run v ≤ 1` (from s5:eqZp) and
    `poolMass G run ≤ 1` (from s7:defPool "This is a probability distribution"); until those Specs are
    proved, statements about the true laws carry these guards as hypotheses.
- COL(g) is an event (the lent-class partition needs `idx ∈ lentIdx`): state it as
  `∀ ω ∈ (colLaw G run Y).supp, COLg G run Y ω`, or `0 < μ.w ω → COLg G run Y (D ω)` in the
  `μ.map D = colLaw G run Y` form (`COLg_of_mem_supp_colLaw`, `COLg_of_map_eq`,
  `COLg_of_mem_supp_law`), never `∀ ω, COLg …` (false off the support).

### Proposed T0 row (CONVENTIONS "T0 record" table)

| T0-colg-supp | s3:lemCOL (g) | "Item (g) always holds" is stated for `ω ∈ (colLaw G run Y).supp` (or `0 < μ.w ω` with `μ.map D = colLaw`); the lent-class partition fails for label assignments of weight 0 (an edge with bit `true` and index `none` when `r ≤ R-2`) | none: every labelling the manuscript draws lies in the support |

## Fix round 2 (review `work/p2d/stage1.review2.md`, verdict APPROVE with 4 minor and 4 cosmetic items)

No Defs file was changed; only additions to `EG/Lib/Stage1/{COL,Zones,Pool,Law}.lean` and
`EGTest/Stage1.lean`. `python3 scripts/lock.py check`: 0 violations (Stage1 Defs still PENDING);
`python3 -I scripts/lint.py`: 0 findings; `lake build EG.Lib.Stage1.Law EG.Lib.Chain.StageInst`
succeeds with no warnings; `scripts/check.sh EGTest/Stage1.lean 900` and
`scripts/check.sh EGTest/StageInst.lean 900`: rc=0, 0 errors, 0 sorry.

| Item | Verdict | Action |
|---|---|---|
| m1 (no support characterisation of the joint law) | valid | Added to `EG/Lib/Stage1/Law.lean`: `law_w` (`(law G run).w ω = (pi coordLaw).w ω.toCoords`), `mem_supp_law_iff` (`ω ∈ supp ↔ ∀ c, ω.toCoords c ∈ (coordLaw G run c).supp`), `zone_mem_supp` (`ω.zone v = none ∨ ∃ Y i, ω.zone v = some (Y,i) ∧ Y ∈ availParts G run v ∧ i ∈ IU G run Y`), `pool_mem_supp` (`ω.pool v = none ∨ ∃ l r, … ∧ (l,r) ∈ poolIdx run`), and the consequences `Zone_eq_empty_of_not_mem_IU` (on the support a zone with a sublabel outside `I^U(Y)` is empty) and `lightParts_of_zone_eq` (the part of a zone label is light). `EG.Chain.js_mem_supp_jsLaw` / `lt_KJS_of_labAt` in `EG/Lib/Chain/StageInst.lean` are left where they are (not this task's file; `mem_supp_law_iff` now gives them in two lines). |
| m2 (no `zonePhase` lemma) | valid | `zonePhase_eq_some_iff` (every assignment: `zonePhase ζ l v = some c ↔ ∃ Y σ, zoneOf ζ v = some (Y, U l c σ)`) and `zonePhase_eq_none_iff` in `EG/Lib/Stage1/Zones.lean`; the support form `zonePhase_eq_some_iff_mem_Zone` (s5:defZones "Equivalently, …": `↔ ∃ Y σ, v ∈ Zone G run ω.zone Y (U l c σ)`, for `ω ∈ (law G run).supp`) in `EG/Lib/Stage1/Law.lean`. The support hypothesis is needed because `Zone ⊆ V(Y)` while an off-support label may name a part not containing `v`. |
| m3 (own-class probability; per-edge marginal) | valid | `prob_mem_ownClass` (`P(e ∈ ownClass o) = 1/(2k_own)` for every `o`) and `prob_mem_ownM` (the s5:lemE1 (a) instance `P(wu ∈ M_Y) = 1/2 · 1/k_own`) in `EG/Lib/Stage1/COL.lean`; `map_col_apply` (`(law G run).map (fun ω => ω.col Y e) = edgeLaw G run Y`) in `EG/Lib/Stage1/Law.lean`. |
| m4 (mixed per-vertex independence shapes) | valid | `iIndepFun_edge_pool` (s7:lemCand (i): (colour of `uw`, pool label of `w`) over the `H_Y`-neighbours `w` of `u`) and `iIndepFun_edge_zone` (s5:lemE1 (a): (colour of `wu`, zone label of `u`) over the `H_Y`-neighbours `u` of `w`) in `EG/Lib/Stage1/Law.lean`. |
| c1 (stale Size line) | valid | Updated (Defs 892, Lib 1609, tests 301). |
| c2 (CONVENTIONS Stage 1 block and T0 row not merged) | valid, integrator action | `CONVENTIONS.md` is locked and a root/protected file; the block and the row in "Fix round 1" above remain the reference until the integrator merges them and re-locks. No change here. |
| c3 (pool guard lacks the blueprint's `∀ l, 0 < M l`) | valid (documentation) | Recorded under D-S1-9: the conjunct is unnecessary; added `two_pow_le_M`, `qPool_pos`, `qPool_le` to `EG/Lib/Stage1/Pool.lean`. |
| c4 (no non-degenerate pool test) | valid | `EGTest/Stage1.lean`: `poolMass_run3_le`, `pool_pos_run3` (`0 < P(plab = (3,1))`), `P(plab = (3,1)) = q_3/2`, and the `prob_mem_ownM` instance on `run3`; generic instances of every fix-round-2 lemma. A non-degenerate zone law (valid run with a light part of ≥ 2 vertices and `R ≥ r+2`) is still not built (not needed for the lock). |
