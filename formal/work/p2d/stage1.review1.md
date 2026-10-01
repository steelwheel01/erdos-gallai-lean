# Clean-room definition review, round 1: P2-D [stage1] (stage-1 random data)

Reviewer: clean-room definition reviewer, round 1, 2026-09-26.

Files reviewed:
- `EG/Defs/Stage1/{COL,Zones,Pool,Law}.lean`
- `EG/Lib/Stage1/{COL,Zones,Pool,Law}.lean`
- `EGTest/Stage1.lean`
- design note `work/p2d/stage1.md`

Compared against:
- manuscript v6.1: `s3.tex` (s3:defCOL, s3:lemCOL), `s5.tex` (setting, s5:eqZp, s5:defZones, s5:lemZones, s5:defStages, s5:lemE1), `s7.tex` (s7:defPool, s7:defCand, s7:defSchedule);
- TRIAGE §2.1, §2.5, §2.7, §3 items 15–18;
- blueprints `blueprint_s3b.md` (defCOL, lemCOL), `blueprint_s5.md` (defZones, lemZones, defStages, lemE1), `blueprint_s7a.md` (defPool, defCand, lemCand), and the stage-1 uses in `blueprint_s6b.md`;
- the locked HB Run model (`EG/Defs/HB/Run.lean`) and `EG/Defs/Prob/FinDist.lean`.

No Lean file was edited.

## Verdict: APPROVE, with 5 minor items and 2 cosmetic items

- No faithfulness error was found.
- No wrong weight was found.
- No missing field or wrong index type was found for any downstream use listed in the blueprints.
- The minor items are:
  - documentation for Spec authors (CONVENTIONS);
  - one missing convenience lemma;
  - one proof-phase API gap;
  - one gap in the non-vacuity tests.

None of them requires changing a definition.

## Checks run

| Check | Result |
|---|---|
| `python3 scripts/lock.py check` | 0 violations. The 4 Stage1 Defs files are PENDING. |
| `python3 -I scripts/lint.py` | 0 findings |
| `scripts/check.sh EGTest/Stage1.lean` | rc=0, 0 errors, 0 sorry |
| `/tmp/s1rev/Scratch1.lean` (Spec-shape elaboration, see §4) | 0 errors |
| `/tmp/s1rev/Scratch2.lean` (support form of COL(g), zone non-vacuity, class sanity) | 0 errors |

## 1. Back-translation of every definition against the manuscript

### 1a. COL.lean (s3:defCOL, s3:lemCOL)

| Lean | Back-translation | Manuscript (quoted) | OK? |
|---|---|---|---|
| `LentTag` = `U l c σ \| JS l j \| JV l` | tagged lent indices; `c : Fin 4`, 0-based σ | "These families are regarded as pairwise disjoint (their indices carry the tags U, JS, JV)" | yes |
| `lateRounds run r = Icc (r+2) R` | rounds `r+2 ≤ l ≤ R` | range of `l` in (ii), (iv) | yes |
| `KJS l = M_l^2 : ℕ` | K^JS_l | "`K^JS_l := M_l^2`" (M_l ∈ ℕ per v6.1 R2) | yes |
| `rhoJS l = (M_l:ℝ)^(-4)` | ρ_l | "`ρ_l := M_l^{-4}`" | yes |
| `tJS l = 2M_l + 2` | t^JS_l | "`t^JS_l := 2M_l+2`" | yes |
| `Tslot Y = ⌈L_Y^2⌉₊` | T^sl_Y | "`T^sl_Y := ⌈L_Y^2⌉`" | yes |
| `IU Y` | `{U l c σ : l ∈ lateRounds, c, σ < T^sl}` if `isLight`, else ∅ | (ii) I^U, light / standalone cases | yes |
| `IJS Y`, `IJV Y` | `{JS l j : j < K^JS_l}`, `{JV l}` | (ii) | yes |
| `lentIdx`, `klend` | the union, and the literal sum of the three cards (`klend_eq_card_lentIdx`) | "`k_lend(Y) := \|I^U\|+\|I^JS\|+\|I^JV\|`" | yes |
| `JY = Vortex.pvJ \|V(Y)\|` | `⌊log₂(log₂\|V(Y)\|/8)⌋₊` | "`J_Y := ⌊log(L_Y/8)⌋`" (log = log₂, s1:convGraphs line 730) | yes (see T0 note) |
| `kown = 4 J_Y + 1` | k_own | "`k_own := 4J_Y+1`" | yes |
| `pY = 1/(2 k_lend)` | p_Y (junk 0 at k_lend = 0) | "For `k_lend(Y) ≥ 1` put `p_Y := 1/(2k_lend(Y))`" | yes |
| `tY = ⌈λ_r^{1.6}⌉₊` | t_Y. `(1.6:ℝ) = 8/5` exactly (scratch, `norm_num`). | "`t_Y := ⌈λ_r^{1.6}⌉`" | yes |
| `ownIdxOf J : Option (Fin J × Fin 4) ≃ Fin (4J+1)` | `R_{j,c} ↦ 4j+c`, `M ↦ 4J` (a bijection, proved) | (iii) names `R_{j,c}`, `M` | yes |
| `bitLaw` | Bernoulli(1/2); `true` = Lend | (i) "probability 1/2 each" | yes |
| `idxLaw` | uniform on `lentIdx` (as `some`), `dirac none` if empty | (ii) "index chosen uniformly from I^U ⊔ I^JS ⊔ I^JV"; "If r ≥ R−1 … no classes" | yes (T0, COL-EMPTY-INDEX) |
| `ownLaw` | uniform on `Fin k_own` | (iii) "one of k_own labels, chosen uniformly" | yes |
| `edgeLaw` | bit ⊗ idx ⊗ own | "every edge e of H_Y carries three independent uniform random variables" | yes |
| `jsWeight`/`jsLabelLaw` | `some j ↦ M^{-4}` (j < M²); `none ↦ 1 − M^{-2}`; else 0 | (iv) "P(lab = j) = ρ_l … P(lab = ∗) = 1 − M_l^{-2}" | yes (weights re-checked; sum = M²·M⁻⁴ + 1 − M⁻² = 1; M = 0 gives all mass on `none`) |
| `colouringLaw`, `jsLaw`, `colLaw` | products over `E(H_Y)` and over the sites; colouring ⊗ labels | "colours of distinct edges are independent … the labels are independent of the colours" | yes |
| `Own`, `Lend` | `H_Y` restricted to bit false / true; vertex set `V(Y)` | (i); "regarded as a graph with vertex set V(Y)" | yes |
| `lentClass i` | edges with `(bit, idx) = (true, some i)` | (ii) "the edges with index … form …" (only edges of Lend_Y carry an index) | yes |
| `LU`, `LJS`, `LJV` | `lentClass` at the three tags | (ii) | yes |
| `ownClass o`, `ownR`, `ownM` | edges with `(bit, own) = (false, o)`; named through `ownIdx` | (iii) | yes |
| `jsSites`, `Tj` | sites `lateRounds × V(Y)`; `T_j = {y : lab(l,y) = some j}` | (iv) "Put T_j(Y,l) := {y ∈ V(Y) : lab_{Y,l}(y) = j}" | yes |
| `COLa` | (ε_Y, s_Y/4) for Own and Lend; (ε_Y, s_Y/(8k)) for every `i ∈ lentIdx`; if light, (2^-6, s_r/(16k_own)) for every own label | lemCOL(a), quoted in the docstring | yes |
| `COLb` | `∀ l ∈ lateRounds, j < K^JS_l`: LJS is (2^12 L^4, t^JS_l)-path connected through T_j | lemCOL(b) | yes |
| `COLc ω Vs` | `∀ i ∈ I^U`: `lentClass i` is (2^12 L^4, t_Y)-path connected through `Vs i` | lemCOL(c) | yes |
| `COLe` | the deterministic inequalities of (e), by type | lemCOL(e) | yes (log = log₂) |
| `COLg` | Own ⊔ Lend = E(H_Y); own classes partition Own; if r ≤ R−2, lent classes are pairwise disjoint with union Lend; if r ≥ R−1, `lentIdx = ∅` | lemCOL(g) | yes, but it is an event (see minor item M1) |

`COLa_iff_of_isLight` unfolds `COLa` for a light Y to exactly the COL(a) list of s5:defStages:
- `(2^-6, s_r/8)` for Own and Lend;
- `(2^-6, s_r/(16k_lend))` for the lent classes;
- `(2^-6, s_r/(16k_own))` for the own classes.

`COLa_iff_of_not_isLight` unfolds it to `(2^-5, s_r/4)` and `(2^-5, s_r/(8k))`, which is what s6:thmMIXC uses.

I checked both statements against the TeX.

### 1b. Zones.lean (s5:defZones, s5:lemZones(ii))

| Lean | Back-translation | Manuscript | OK? |
|---|---|---|---|
| `ZIdx = PartId × LentTag` | (chosen part, sublabel as a U-tag) | "The sublabels available to Y are exactly the indices of the family I^U" | yes |
| `zp Y = L_Y^{-2}` | zp_Y (0 in Lean if L_Y = 0) | "put zp_Y := L_Y^{-2}" | yes |
| `availParts v` | light parts Y with `v ∈ V(Y)` and `r(Y)+2 ≤ R` | "Y a light part with v ∈ Y and r(Y) ≤ R−2" | yes |
| `zoneWeight v` | `some (Y,i) ↦ zp_Y/\|I^U(Y)\|` for available Y and `i ∈ I^U(Y)`; `none ↦ 1 − Σ zp`; else 0 | two-step law: P(choice = Y) = zp_Y, then a uniform sublabel | yes: the one-step form has the same joint law of (choice, sublabel); `prob_zoneLabelLaw_choice` gives the marginal zp_Y |
| `zoneLabelLaw` | `dite` on `zpSum ≤ 1`, fallback `dirac none` | well-definedness relies on (s5:eqZp) | yes: the guard is exactly the nonnegativity of the `none` weight; the sum is 1 unconditionally (`zp = 0` when `I^U = ∅` for an available Y, proved) |
| `zoneLaw` | product over `↥G.verts` | "Independently for every vertex v of G" | yes |
| `Zone ζ Y i` | `{v ∈ V(Y) : label(v) = (Y,i)}` | "Zone_{Y,l,c,σ} := {v ∈ Y : choice(v) = Y and the sublabel of v is (l,c,σ)}" | yes |
| `zonePhase ζ l v` | `some c` iff the label is `(_, U l c _)` | "carries a round-l zone … phase … c" | yes |
| `rhoY` | `zp_Y / ((R−r−1)·4·T^sl_Y)` (real subtraction) | lemZones(ii) | yes; `rhoY_eq_zp_div_card` gives `zp/\|I^U\|` for light Y with r ≤ R−2 |

### 1c. Pool.lean (s7:defPool)

| Lean | Manuscript | OK? |
|---|---|---|
| `poolIdx = {(l,r) : 3 ≤ l ≤ R, 1 ≤ r, r+2 ≤ l}` | "`{(l,r) : 3 ≤ l ≤ R, 1 ≤ r ≤ l−2}`" | yes |
| `qPool l = M_l^{-2}`, `piPool l r = 2^{-(l−1−r)}` (zpow) | "`q_l := M_l^{-2}` and `π_{l,r} := 2^{-(l−1−r)}`" | yes (`piPool_eq`, `sum_piPool`) |
| `plabWeight`/`poolLabelLaw` | "P(plab = (l,r)) = q_l π_{l,r}", "P(⊥) := 1 − Σ" | yes; the guard is exactly `poolMass ≤ 1` (nonnegativity of ⊥) |
| `poolLaw` | product over `↥G.verts` ("Every vertex v of G independently draws") | yes |
| `poolSet`, `poolL`, `poolRound` | Pool_{l,r}, Pool_l (disjoint union), r(w) (junk 0 off the pool) | yes (`poolRound_eq`, `disjoint_poolL`) |

### 1d. Law.lean (s7:defSchedule stage 1)

- `Coord` is the disjoint union of:
  - `(Y, e)` for `e ∈ E(H_Y)` (1a);
  - `v ∈ V(G)` (1b);
  - `(Y, (l,y))` JS sites (1c);
  - `v ∈ V(G)` (1d).
- Each coordinate has its own law (`coordLaw`).
- `law = (pi coordLaw).map ofCoords`. `ofCoords`/`toCoords` are mutually inverse (proved).
- `Outcome` has the four TRIAGE fields: `col`, `zone`, `js`, `pool`.
- This is literally "four mutually independent families" with independence inside each family. All the manuscript's stage-1 independence claims are instances of `indepFun_of_dependsOn` / `iIndepFun_of_dependsOn`:
  - defCOL "Consequently";
  - lemZones(iv);
  - defPool "independent of all other stage-1 data";
  - s7:defSchedule "mutually independent".
- The HB Run model is used unchanged: `ancestors`, `ancVerts`, `ancGraph`, `ancEps`, `ancS`, `LY`, `lam`, `M`, `s`, `isLight`, `lightParts`.

## 2. Edge cases checked

- **r ≥ R−1.**
  - `lateRounds = ∅`, so `lentIdx = ∅`, `k_lend = 0`, and `idxLaw = dirac none`.
  - There are no JS sites and no lent classes.
  - `COLa`'s lent quantifier is vacuous, which matches "every statement below about lent classes is vacuous".
  - `COLg`'s last conjunct holds.
  - `IU = ∅`, so zones and `COLc` are vacuous, which matches s5:defStages "never parent-bad".
- **Standalone Y.**
  - `IU = ∅`.
  - Own labels are drawn but never read by `COLa` (light-only conjunct).
  - `COLe` switches on `isLight`.
  - The exported bound `2(2 + k_lend + k_own)N^{-5}` over-counts for standalone Y (the manuscript's proof has no stage-(iii) application there). This is harmless because it is an upper bound.
- **Tiny ancestors.**
  - If `L_Y < 16`, then `J_Y = 0` and `k_own = 1` (only `M`); this is tested.
  - If `L_Y = 0`, then `T^sl = 0`, `I^U = ∅` and `zp = 0` (Lean `0⁻¹`), and `zoneWeight_sum` still holds.
- **M_l.**
  - `MOf d ≥ 2^40` for every `d` (scratch proof), so `1 − M^{-2} ∈ [0,1)` for every run.
  - `jsLabelLaw` needs no guard.
- **Off-ancestor reads.** `colAt`/`jsAt`/`labAt` return junk values (false/none/0, all ∗). Every Spec must guard with `Y ∈ run.ancestors G` (see M3).
- **Zones.**
  - `Zone` for a non-U tag or a non-light `Y` is empty on the support.
  - `disjoint_Zone` holds for every ζ (lemZones(iii), deterministic).
- **`8 * klend`** in `COLa` is the division `s_Y/(8·0) = 0` when `k_lend = 0`. It is only read under `∀ i ∈ lentIdx`, which is empty then.

## 3. Probability laws (weights and independence)

- **jsLabelLaw**: `M^2·M^{-4} + (1 − M^{-2}) = 1`. `prob_jsLabelLaw_some/none` match (iv) literally. `KJS_mul_rhoJS` is "K^JS_l ρ_l = M_l^{-2}".
- **idxLaw**: `prob_idxLaw_some` gives `1/k_lend`.
- **LJV**: `prob_mem_LJV` gives `P(e ∈ LJV_{Y,l}) = 1/2 · 1/k_lend = p_Y`, which is the defCOL "Derived quantities" claim.
- **Zones**:
  - `prob_zoneLabelLaw_some` gives P(label = (Y,i)) = ρ_Y.
  - `isRSubset_Zone` is lemZones(ii) in law form, under the per-vertex guards, which (s5:eqZp) supplies.
  - Scratch 1 transports it to the joint law via `map_zone` + `isRSubset_map_iff` in 2 lines.
- **Pools**: `prob_poolLabelLaw_some` gives `q_l π_{l,r}`, and `sum_piPool` gives `1 − 2^{-(l−2)}`.
- **T_j**: `isRSubset_Tj` gives that `T_j(Y,l)` is ρ_l-random. `disjoint_Tj` holds for every outcome.
- **Independence API**, all present:
  - `iIndepFun_cOut` (ancestors);
  - `iIndepFun_col_edges` (edges);
  - `indepFun_col_js` (labels vs colours);
  - `indepFun_colJS_zone` / `indepFun_cOutAt_zone` (lemZones(iv), and the joint form that lemCOL(c) / lemE1(c) consume);
  - `indepFun_rest_pool` / `indepFun_cOut_pool` (defPool);
  - `iIndepFun_zone`, `iIndepFun_pool`.
- Anything else, such as E1-INDEP (edge `wu` plus the zone of `u`) or CAND-INDEP-MODEL (edge `uw` plus the pool label of `w`), is one call of `iIndepFun_of_dependsOn` with singleton blocks.

## 4. Can every downstream use be stated? (Scratch1, 0 errors)

These shapes were elaborated against the built modules:

- **s3:lemCOL Spec** (blueprint s3b lean_shape, with the Stage1 names and the support form of (g)):
  - `COLe`;
  - `∀ ω ∈ (colLaw).supp, COLg`;
  - the `μ.map D = colLaw` form with the exported COL(a) bound and `COLa ∧ COLb`;
  - (c) with `Vs : Ω → LentTag → Finset V`, `μ.IndepFun D Vs`, and `ρ i ≥ 1/(12L^5)` with `IsRSubset` on `i ∈ IU`.
- **s5:defStages**:
  - `E1` via `ownM G run Y (ω.colAt Y)` and `zonePhase ω.zone l u = none`;
  - parent-bad as `¬ COLc G run Y (ω.cOutAt Y) (fun i => Zone G run ω.zone Y i)`;
  - demoted via `COLa`.
- **s5:lemE1(c)**:
  - joint independence `(law).IndepFun (·.cOutAt Y) (fun ω i => Zone G run ω.zone Y i)`, by `(indepFun_cOutAt_zone ..).comp id _`;
  - ρ_Y-randomness of each zone on `law`.
- **s6:defLending Lost**: `lendBad (δ l u) ∨ ω.labAt (δ l u) l u ≠ none`.
- **s7:defCand**: `(poolSet G ω.pool l r).filter (fun w => s(u,w) ∈ (LJV G run Y (ω.colAt Y) l).edges)`.
- **s6 StageData / s7 RoundInput** need `Own`, `LJS`, `LJV`, `labAt`, `Tj`, `poolL`, `poolRound`, `COLa`, `COLb`. All exist with the right index types:
  - `LJS … l j` with `j : ℕ`, `j < KJS`;
  - `LU … l (c : Fin 4) σ`;
  - `ownR … (j : Fin J_Y) (c : Fin 4)`, whose index type is definitionally the PV one through `Vortex.pvJ`;
  - per-vertex families on `↥G.verts` (TRIAGE §2.5).

No missing field or wrong index type was found.

## 5. Issues

### Minor

- **M1. COLg is an event, so the Spec shape must change.**
  - Manuscript: "Item (g) always holds". Blueprint s3b lean_shape: `(∀ ω, EG.Lend.COLg run G Y ω)`.
  - In Lean `COLg` is false off the support. Counterexample: r ≤ R−2 and an edge with `(bit, idx) = (true, none)`. That edge is in `Lend_Y` but in no lent class, so the biUnion is strictly smaller than `Lend_Y`.
  - The design note records this (D-S1-10) and proves `COLg_of_mem_supp(_law)`. But CONVENTIONS/T0 has no entry, and there is no lemma for the Spec's "any μ with `μ.map D = colLaw`" form.
  - **Fix:**
    - Add a T0 line: "COL(g) is stated `∀ ω ∈ (colLaw G run Y).supp` (or `0 < μ.w ω`)".
    - Add `COLg_of_mem_supp_colLaw : ω ∈ (colLaw G run Y).supp → COLg G run Y ω` to `EG/Lib/Stage1/COL.lean`. It is 4 lines; checked in Scratch2: `apply COLg_of_mem_supp; rw [mem_supp] at *; intro h; apply hω; simp [colLaw, prod_w', h]`.
- **M2. CONVENTIONS has no Stage1 section**, and the blueprint names are superseded. Spec authors need the renames from blueprints s3b/s5/s6b/s7a:
  - `EG.Lend.*` → `EG.Stage1.*`;
  - `run G Y` → `G run Y`;
  - `T` → `Tj`, `tauJS` → `tJS`, `JSSite` → `jsSites`;
  - `stage1Law`/`S3.stage1Dist` → `Stage1.law`;
  - `ω.zlab` → `ω.zone`, `ω.lab` → `ω.labAt`, `ω.LJS Y` → `LJS G run Y (ω.colAt Y)`;
  - `ω.Mcls` → `ownM`.

  **Fix:** add a "Stage 1 (EG.Stage1; design note work/p2d/stage1.md)" block to CONVENTIONS, as was done for HB.
- **M3. Junk values that Specs must guard (for the same CONVENTIONS block):**
  - `colAt`/`jsAt`/`cOutAt`/`labAt` off `run.ancestors G`: require `Y ∈ run.ancestors G` (or `Y ∈ run.lightParts G`).
  - `pY` is 0 when `k_lend = 0`: require `Y.1 + 2 ≤ run.R`.
  - `rhoY` is junk for `r ≥ R−1`.
  - `tY` is defined for every Y but meaningful only for light Y.
  - `poolRound` is 0 off the pool: read it only under `w ∈ poolL`.
  - `Zone`/`COLc` are indexed by all `LentTag`s but meaningful only on `IU`.
  - `zoneLabelLaw`/`poolLabelLaw`: true-law statements carry `zpSum ≤ 1` / `poolMass ≤ 1` until the Specs that discharge them (from s5:eqZp and s7:defPool's "This is a probability distribution") are proved.
- **M4. Proof-phase API gap (COL-RANDOM-EDGESET, blueprint s3b defCOL "API").**
  - The needed lemma: given the bit vector β (positive probability), the indices on `Lend(β)` are a uniform `k_lend`-colouring (via `↥lentIdx ≃ Fin k_lend`), and the own labels on `Own(β)` are a uniform `k_own`-colouring. lemCOL(a) and lemE1(b) need it for the conditional L15⁺.
  - It is absent. No statement needs it and the definitions support it, since idx and own are independent of the bit per edge.
  - It stays open for the lemCOL prover (~150 lines, per blueprint).
- **M5. Non-vacuity tests never exercise a non-empty zone law or a valid run with r ≤ R−2.**
  - `run1` has one-vertex light parts (L_Y = 0, T^sl = 0).
  - `run3` is not valid, and its round-1 parts are the same one-vertex parts.
  - Scratch2 proves abstractly that `0 < P(label(v) = (Y,i))` whenever the guard holds, `Y ∈ availParts v`, `i ∈ I^U(Y)` and `L_Y > 0`.
  - **Fix:** add that example (and `COLg_of_mem_supp_colLaw`) to `EGTest/Stage1.lean`. A concrete valid run with a light part of ≥ 2 vertices and R ≥ r+2 is not needed for the lock.

### Cosmetic

- **C1.** TRIAGE §3 item 16 places `Tslot` in Zones.lean; it is in COL.lean (needed by `IU`). No action, or update the TRIAGE line.
- **C2.** `lateRounds`, `IJV`, `poolIdx` omit `G` (they do not depend on it). This is recorded in D-S1-1. Mention it in the CONVENTIONS block (M2) so that Spec authors do not write `lateRounds G run r`.

## 6. T0 readings (agree with the design note; no T1/T2)

- **COL-EMPTY-INDEX / standalone own label (D-S1-4).**
  - "three independent uniform random variables" is read as: idx is `dirac none` when `lentIdx = ∅`, and an own label is drawn for every ancestor.
  - No law the manuscript uses changes: the extra coordinates are independent and never read for standalone Y.
- **ZONE-TWO-STEP (D-S1-8).** The one-step law is the same joint law. The two-step marginal is proved.
- **COL(g) on the support (D-S1-10).** Agreed. It needs the CONVENTIONS entry (M1).
- **Consumer exclusivity** is a design rule, not a predicate (COL-CONSUMERS-NOT-A-PROPERTY). Agreed.

## Scratch files

- `/tmp/s1rev/Scratch1.lean`: Spec-shape elaboration, joint-law ρ-random zones, `(1.6:ℝ) = 8/5`, `pvJ (2^64) = 3`, `MOf d ≥ 2^40`.
- `/tmp/s1rev/Scratch2.lean`: COL(g) from `colLaw.supp`, zone non-vacuity, Own edges are in no lent class.
