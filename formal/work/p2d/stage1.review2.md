# Clean-room definition review, round 2: P2-D [stage1] (stage-1 random data)

Reviewer: clean-room definition reviewer, round 2, 2026-09-26. Independent of round 1
(`stage1.review1.md`), which was read only after the back-translation below was done.

Files reviewed (no Lean file edited):
- `EG/Defs/Stage1/{COL,Zones,Pool,Law}.lean` (892 lines)
- `EG/Lib/Stage1/{COL,Zones,Pool,Law}.lean` (1342 lines, after fix round 1)
- `EGTest/Stage1.lean` (223 lines)
- design note `work/p2d/stage1.md` (with its fix-round-1 section)
- the first consumer already written against these Defs: `EG/Defs/Chain/StageInst.lean`,
  `EG/Lib/Chain/StageInst.lean` (`StageData.ofOutcome`, `Coherent`, `coherent_ofOutcome`)

Compared against:
- manuscript v6.1: `s3.tex` 1027–1185 (s3:defCOL, table), 1453–1560 (s3:lemCOL); `s5.tex` 1–160
  (setting, s5:eqZp, s5:defZones, s5:lemZones, s5:defStages, s5:lemE1); `s7.tex` 28–80
  (s7:defPool, s7:defCand), 156–260 (s7:defSchedule, "Fixed rules");
- TRIAGE §2.1, §2.5, §2.7, §2.12, §3 items 15–18;
- blueprints s3b (defCOL, lemCOL, lemCOLJV), s5 (defZones, lemZones, defStages, lemE1, lemChild,
  lemParent), s6b (defLending, lemLost, lemJSLC, lemJplus, defJconsumer, consOrder, thmMIXC), s7a
  (defPool, defCand, lemCand, defSchedule, RoundInput);
- the locked HB Run model (`EG/Defs/HB/Run.lean`), `EG/Defs/Vortex.lean` (`pvJ`),
  `EG/Defs/Prob/FinDist.lean` and `EG/Lib/Prob/*`.

## Verdict: APPROVE, with 4 minor items and 4 cosmetic items

- No faithfulness error: every definition back-translates to the quoted defining text.
- No wrong weight: all four component laws were re-derived (sum, support, guards).
- No missing field and no wrong index type for any downstream use listed in the blueprints; every
  shape that round 1 did not elaborate was elaborated here (§4, scratch A, 0 errors).
- The minor items are API lemmas whose absence I measured by proving them in scratch (they are
  15–40 lines each and need no Defs change): the support characterisation of the joint law, the
  `zonePhase` characterisation (the manuscript's "Equivalently" sentence of s5:defZones), the
  own-class edge probability, and packaged per-vertex independence shapes.
- Nothing requires changing a definition. The Defs can be locked as they are.

## Checks run

| Check | Result |
|---|---|
| `python3 scripts/lock.py check` | 0 violations; the Stage1 Defs are PENDING |
| `python3 -I scripts/lint.py` on the 9 files | 0 findings |
| `LEAN_NUM_THREADS=2 scripts/check.sh EGTest/Stage1.lean 900` | rc=0, 0 errors, 0 sorry |
| `/tmp/s1rev2/ScratchA.lean` (downstream shapes, candidate API, §4–§5) | 0 errors |
| `/tmp/s1rev2/ScratchB.lean` (non-vacuity of a non-degenerate pool law, `M_l ≥ 2^40`, zones with non-U tags, own-class probability) | 0 errors |

Scratch files are also at `/tmp/claude-0/…/scratchpad/s1rev2/`.

## 1. Back-translation of every definition

### 1a. `COL.lean` (s3:defCOL, s3:lemCOL)

| Lean | Back-translation | Manuscript (quoted) | OK |
|---|---|---|---|
| `LentTag = U l (c : Fin 4) (σ : ℕ) \| JS l j \| JV l` | tagged indices, 0-based `c`, `σ`, `j` | "These families are regarded as pairwise disjoint (their indices carry the tags U, JS, JV)" | yes |
| `lateRounds run r = Icc (r+2) R` | `{l : r+2 ≤ l ≤ R}` | the range of `l` in (ii), (iv) | yes |
| `KJS l = M_l^2 : ℕ` | `K^JS_l` | "`K^JS_l := M_l^2`" (M_l ∈ ℕ, v6.1 R2) | yes |
| `rhoJS l = (M_l:ℝ)^(-4:ℤ)` | `ρ_l` | "`ρ_l := M_l^{-4}`" | yes |
| `tJS l = 2 M_l + 2` | `t^JS_l` | "Also put `t^JS_l := 2M_l+2`" | yes |
| `Tslot Y = ⌈L_Y^2⌉₊` | `T^sl_Y` | "`T^sl_Y := ⌈L_Y^2⌉`" | yes |
| `IU Y` | `{U l c σ : l ∈ lateRounds, c ∈ Fin 4, σ < T^sl}` if light, `∅` otherwise | (ii), the two cases | yes |
| `IJS Y`, `IJV Y` | `{JS l j : l ∈ lateRounds, j < K^JS_l}`, `{JV l : l ∈ lateRounds}` | (ii) | yes |
| `lentIdx`, `klend` | the union; the literal sum of the three cardinalities | "`k_lend(Y) := \|I^U\|+\|I^JS\|+\|I^JV\|`" | yes (`klend_eq_card_lentIdx`) |
| `JY = pvJ \|V(Y)\|`, `kown = 4 J_Y + 1` | `⌊log₂(log₂\|V(Y)\|/8)⌋₊`, `4J+1` (≥ 1 always) | "`J_Y := ⌊log(L_Y/8)⌋` and `k_own := 4J_Y+1`" | yes (T0: `Nat.floor` junk for tiny `Y`; TRIAGE §2.7) |
| `pY = 1/(2 k_lend)` | `p_Y` (junk 0 at `k_lend = 0`) | "For `k_lend(Y) ≥ 1` put `p_Y := 1/(2k_lend(Y))`" | yes |
| `tY = ⌈λ_r^{(1.6:ℝ)}⌉₊` | `t_Y`; `(1.6:ℝ) = 8/5` (scratch A, `norm_num`) | "`t_Y := ⌈λ_r^{1.6}⌉`" | yes |
| `ownIdxOf J : Option (Fin J × Fin 4) ≃ Fin (4J+1)`, `ownIdx N = ownIdxOf (pvJ N)` | `R_{j,c} ↦ 4j+c`, `M ↦ 4J` | (iii) the names `R_{j,c}`, `M` | yes (bijection proved) |
| `bitLaw = bernoulli 1/2` (`true` = Lend) | (i) | "with probability 1/2 each" | yes |
| `idxLaw` | uniform on `lentIdx` (as `some`); `dirac none` if empty | (ii) "chosen uniformly from `I^U ⊔ I^JS ⊔ I^JV`"; "If `r ≥ R-1` … `Lend_Y` has no classes" | yes (T0 COL-EMPTY-INDEX) |
| `ownLaw = uniform (Fin k_own)` | (iii) | "one of `k_own` labels, chosen uniformly" | yes |
| `edgeLaw = bit ⊗ (idx ⊗ own)` on `Bool × Option LentTag × Fin k_own` | the triple | "three independent uniform random variables (a fair bit, a lent index and an own label)" | yes |
| `jsWeight M`: `some j ↦ M^{-4}` (`j < M^2`), `none ↦ 1 - M^{-2}`, else 0; `jsLabelLaw l = ofFinset (jsSupport M_l) (jsWeight M_l) …` | (iv) | "`P(lab = j) = ρ_l := M_l^{-4}` for each `j`, so that `P(lab = ∗) = 1 - M_l^{-2}`" | yes; sum `= M^2·M^{-4} + 1 - M^{-2} = 1` for every `M ∈ ℕ` (`M = 0`: all mass on `none`), so no guard |
| `colouringLaw = pi edgeLaw` over `E(H_Y)`; `jsLaw = pi (jsLabelLaw l)` over the sites; `colLaw = colouringLaw.prod jsLaw` | (1a)×(1c) of one ancestor | "colours of distinct edges are independent"; "the labels of (iv) are independent of all edge variables" | yes |
| `Own`, `Lend` | `H_Y` restricted to bit `false` / `true`; vertex set `V(Y)` (`restrictEdges` keeps `verts`) | (i); "regarded as a graph with vertex set `V(Y)`" | yes |
| `lentClass i` | edges with `(bit, idx) = (true, some i)` | (ii) "The edges with index … form the … class" | yes |
| `LU`, `LJS`, `LJV` | `lentClass` at the three tags | (ii) | yes |
| `ownClass o`, `ownR j c`, `ownM` | edges with `(bit, own) = (false, o)`; names through `ownIdx` | (iii) | yes |
| `jsSites = lateRounds ×ˢ V(Y)`, `Tj lab l j` | sites; `{y ∈ V(Y) : lab(l,y) = some j}` | (iv) "Put `T_j(Y,l) := {y ∈ V(Y) : lab_{Y,l}(y) = j}`" | yes |
| `COLa` | `Own`, `Lend` `(ε_Y, s_Y/4)`; `∀ i ∈ lentIdx`, `(ε_Y, s_Y/(8k))`; light → `∀ o : Fin k_own`, `(2^{-6}, s_r/(16k_own))` | lemCOL (a), quoted in the docstring | yes; `COLa_iff_of_isLight` = the s5:defStages list, `COLa_iff_of_not_isLight` = `(2^{-5}, s_r/4)`, `(2^{-5}, s_r/(8k))` (s6:thmMIXC) |
| `COLb` | `∀ l ∈ lateRounds, ∀ j < K^JS_l`, `LJS` is `(2^{12}L^4, t^JS_l)`-path connected through `T_j` | lemCOL (b) | yes |
| `COLc ω Vs` | `∀ i ∈ I^U`, `lentClass i` is `(2^{12}L^4, t_Y)`-path connected through `Vs i` | lemCOL (c) | yes (`Vs : LentTag → Finset V`, read on `I^U` only) |
| `COLe` | the row-8 inequalities by type, `log = logb 2` | lemCOL (e) first sentences | yes (COL-E-DETERMINISTIC) |
| `COLg` | `Own ⊔ Lend = E(H_Y)`; own classes partition `Own`; `r ≤ R-2` → lent classes over `lentIdx` pairwise disjoint with union `Lend`; `r ≥ R-1` → `lentIdx = ∅` | lemCOL (g) partition facts | yes; an event (true on the support: `COLg_of_mem_supp_colLaw`, `COLg_of_map_eq`, `COLg_of_mem_supp_law`) |

### 1b. `Zones.lean` (s5:defZones, s5:lemZones (ii))

| Lean | Manuscript | OK |
|---|---|---|
| `ZIdx = PartId × LentTag`; label `Option ZIdx` | choice `∈ {none} ∪ {Y}`, sublabel `(l,c,σ)` = the U-index | yes ("The sublabels available to `Y` are exactly the indices of the family `I^U`" is definitional) |
| `zp Y = L_Y^(-2:ℤ)` | "`zp_Y := L_Y^{-2}`" | yes (`0` at `L_Y = 0`) |
| `availParts v = lightParts.filter (v ∈ V(Y) ∧ r(Y)+2 ≤ R)` | "`Y` a light part with `v ∈ Y` and `r(Y) ≤ R-2`" | yes |
| `zoneWeight v`: `some (Y,i) ↦ zp_Y/\|I^U(Y)\|` (`Y ∈ A(v)`, `i ∈ I^U(Y)`), `none ↦ 1 - Σ_{A(v)} zp` | two-step: `P(choice = Y) = zp_Y`, then uniform among `(R-r-1)·4·T^sl_Y = \|I^U(Y)\|` sublabels | yes; same joint law of `(choice, sublabel)`; `prob_zoneLabelLaw_choice` recovers `zp_Y` |
| `zoneLabelLaw v = dite (zpSum ≤ 1) (ofFinset …) (dirac none)` | well defined by (s5:eqZp) | yes: the guard is exactly the sign of the `none` weight; `zoneWeight_sum = 1` unconditionally (uses `zp_eq_zero_of_IU_eq_empty`) |
| `zoneLaw = pi zoneLabelLaw` over `↥G.verts` | "Independently for every vertex `v` of `G`" | yes (TRIAGE §2.5) |
| `Zone ζ Y i = V(Y).filter (zoneOf ζ v = some (Y,i))` | "`Zone_{Y,l,c,σ} := {v ∈ Y : choice(v) = Y and the sublabel of v is (l,c,σ)}`" | yes |
| `zonePhase ζ l v = some c` iff label `= some (_, U l c _)` | "`v` carries a round-`l` zone if `choice(v) ≠ none` and the sublabel has first coordinate `l`; the phase … is the second coordinate `c`" | yes (characterisation lemma missing: M2) |
| `rhoY = zp_Y / ((R-r-1)·4·T^sl_Y)` (real subtraction) | lemZones (ii) | yes; `rhoY_eq_zp_div_card` |

### 1c. `Pool.lean` (s7:defPool)

| Lean | Manuscript | OK |
|---|---|---|
| `poolIdx = (Icc 3 R ×ˢ Icc 1 R).filter (r+2 ≤ l)` | "`(l,r) : 3 ≤ l ≤ R, 1 ≤ r ≤ l-2`" | yes (`r ≤ l-2 ≤ R-2` so `Icc 1 R` loses nothing; `mem_poolIdx`) |
| `qPool l = M_l^(-2:ℤ)`, `piPool l r = 2^(-((l:ℤ)-1-r))` | "`q_l := M_l^{-2}` and `π_{l,r} := 2^{-(l-1-r)}`" | yes; `piPool_eq`, `sum_piPool = 1 - 2^{-(l-2)}` |
| `plabWeight`: `some p ↦ q π` on `poolIdx`, `none ↦ 1 - poolMass` | "`P(plab = (l,r)) = q_l π_{l,r}`, `P(⊥) := 1 - Σ`" | yes |
| `poolLabelLaw = dite (poolMass ≤ 1) …` | "This is a probability distribution: …" (a Γ theorem) | yes; the guard is exactly the sign of the `⊥` weight. Note: the blueprint's extra guard `∀ l, 0 < M l` is not needed (`M_l ∈ ℕ`; `(0:ℝ)^(-2:ℤ) = 0`, weights stay `≥ 0`) |
| `poolLaw = pi poolLabelLaw` over `↥G.verts` | "Every vertex `v` of `G` independently draws" | yes |
| `poolSet`, `poolL`, `poolRound` | `Pool_{l,r}`, `Pool_l = ⋃_{r=1}^{l-2}`, `r(w)` (junk 0 off the pool) | yes (`disjoint_poolL`, `disjoint_poolSet`, `poolRound_eq`) |

### 1d. `Law.lean` (s7:defSchedule stage 1)

- `Coord = (Σ Y : ancestors, E(H_Y)) ⊕ (V(G) ⊕ ((Σ Y, jsSites Y) ⊕ V(G)))`, `coordLaw` = `edgeLaw` /
  `zoneLabelLaw v` / `jsLabelLaw l` / `poolLabelLaw`; `law = (pi coordLaw).map ofCoords`;
  `ofCoords`/`toCoords` mutually inverse (`Outcome.toCoords_ofCoords`, `ofCoords_toCoords`).
- `Outcome` has the four TRIAGE §2.7 fields `col`, `zone`, `js`, `pool`, with the TRIAGE types
  (`col Y : E(H_Y) → Bool × Option LentTag × Fin (kown Y)`, `zone : ↥G.verts → Option ZIdx`,
  `js Y : sites → Option ℕ`, `pool : ↥G.verts → Option (ℕ×ℕ)`).
- "four mutually independent families", "The data of distinct ancestors are independent",
  "colours of distinct edges are independent", lemZones (iv), defPool "independent of all other
  stage-1 data": all instances of `indepFun_of_dependsOn` / `iIndepFun_of_dependsOn`
  (`indepFun_col_js`, `iIndepFun_cOut`, `iIndepFun_col_edges`, `indepFun_colJS_zone`,
  `indepFun_cOut_zone`, `indepFun_cOutAt_zone`, `indepFun_rest_pool`, `indepFun_cOut_pool`,
  `iIndepFun_zone`, `iIndepFun_pool`). Marginals `map_col`, `map_js`, `map_cOut`, `map_cOutAt`,
  `map_zone`, `map_pool`, `map_toCoords_apply`.
- The HB Run model is used unchanged (`ancestors`, `lightParts`, `ancVerts`, `ancGraph`, `ancEps`,
  `ancS`, `LY`, `lam`, `M`, `s`, `isLight`, `R`).

## 2. Edge cases

- **`r ≥ R-1`**: `lateRounds = ∅` ⇒ `IU = IJS = IJV = ∅`, `k_lend = 0`, `idxLaw = dirac none`,
  no JS sites, no U-zones for `Y`, `COLa`'s lent quantifier and `COLb`, `COLc` vacuous, the last
  conjunct of `COLg` holds; `pY = 0` and `rhoY` junk (guards recorded in the design note).
- **Standalone `Y`**: `IU = ∅`; the own label is drawn and never read (`COLa`'s fourth conjunct is
  `isLight → …`); `COLe` switches on `isLight`.
- **Tiny `Y`**: `L_Y < 16` ⇒ `J_Y = 0`, `k_own = 1` (only `M`; tested). `L_Y = 0` ⇒ `T^sl = 0`,
  `IU = ∅`, `zp = 0`, and `zoneWeight_sum` still holds.
- **`M_l`**: `MOf d ≥ 2^40` for every `d` (scratch B `two_pow_le_MOf`), so `1 - M^{-2} ∈ (0,1)`
  and `q_l ≤ 2^{-80}` on every run; the JS law needs no guard, and the pool guard is satisfied on
  the test list `run3` (`poolMass_run3_le`, scratch B).
- **Off-ancestor reads**: `colAt`/`jsAt`/`cOutAt`/`labAt` are junk (bits `false`, indices `none`,
  own `0`, labels `∗`); the design-note guard `Y ∈ run.ancestors G` is right. In particular an
  off-ancestor `lentClass` is empty (used by `EG.Lib.Chain.StageInst.mem_lentIdx_of_mem_lentClass`).
- **Zones with a non-U tag / non-light `Y`**: empty on the support (scratch B
  `Zone_eq_empty_of_not_mem_IU`); `disjoint_Zone` holds for every `ζ`.
- **`8 * klend` at `k_lend = 0`**: real division by `0` gives `0`, read only under `∀ i ∈ lentIdx`
  (empty). Same for `16 * klend` in `COLa_iff_of_isLight`.
- **Shared edges of two ancestors** would be two coordinates; the definitions do not rely on
  propStructure (iii), and every consumer names the ancestor (`LJV_{Y,l}`, `Own_Y`), so nothing
  reads "the colour of an edge of `G`" without `Y`.

## 3. Probability laws (weights and independence), re-derived

- `jsLabelLaw`: `Σ = K^JS ρ + (1 - M^{-2}) = 1`; `prob_jsLabelLaw_some/none`; `KJS_mul_rhoJS`.
  On the joint law, `P(lab_{Y,l}(u) ≠ ∗) = K^JS_l ρ_l` (scratch A `prob_labAt_ne_none`, the
  s6:lemLost (i) ingredient).
- `idxLaw`: `prob_idxLaw_some = 1/k_lend`; `prob_mem_LJV = 1/2 · 1/k_lend = p_Y` (defCOL
  "Derived quantities"); on the joint law: scratch A `prob_mem_LJV_law`.
- `ownLaw`: `P(e ∈ ownClass o) = 1/(2 k_own)` for every own label `o`, in particular for `M`
  (scratch B `prob_mem_ownClass`; s5:lemE1 (a) "`P(wu ∈ M_Y) = 1/2 · 1/k_own`"). Not in the Lib (M3).
- Zones: `prob_zoneLabelLaw_some = ρ_Y`, `prob_zoneLabelLaw_choice = zp_Y`,
  `prob_zoneLabelLaw_none = 1 - Σ zp`; `isRSubset_Zone` (lemZones (ii) in law form under the
  per-vertex guards); transported to the joint law in 3 lines (scratch A `isRSubset_Zone_law`).
- Pools: `prob_poolLabelLaw_some = q π`, `prob_poolLabelLaw_none = 1 - poolMass`, `sum_piPool`;
  a non-degenerate instance: on `run3`, `P(plab = (3,1)) = q_3/2 > 0` (scratch B `pool_pos_run3`).
- `T_j`: `isRSubset_Tj` (`ρ_l`-random), `disjoint_Tj` (every outcome).
- Independence: the two general principles cover every manuscript claim; the per-vertex mixed
  shapes E1-INDEP (edge `wu` + zone label of `u`) and CAND-INDEP-MODEL (edge `uw` + pool label of
  `w`) are one call each, with a 6-line `Sym2` disjointness argument (scratch A
  `iIndepFun_edge_pool`, `iIndepFun_edge_zone`).
- Conditional laws given the bits (COL-RANDOM-EDGESET, fix round 1): `map_idx_cond_edgeBits`,
  `map_own_cond_edgeBits`, `idxLaw_eq_of_nonempty` present; the transport `↥lentIdx ≃ Fin k_lend`
  remains for the lemCOL prover (as recorded).

## 4. Can every downstream use be stated?

Elaborated against the built modules (scratch A, 0 errors), in addition to round 1's Scratch1:

| Use | Shape checked |
|---|---|
| s3:lemCOL Spec (a)–(c), (e), (g) | round 1 (`μ.map D = colLaw`, `μ.IndepFun D Vs`, `∀ ω ∈ supp, COLg`); the joint law supplies `map_cOutAt`, `indepFun_cOutAt_zone.comp id (fun ζ i => Zone G run ζ Y i)` (re-checked) |
| s3:lemCOLJV rows 3, 4, 9, 10 | `klend`, `kown`, `tY`, `pY`, `Tslot` are ℕ/ℝ-valued as the rows need (no new check needed) |
| s5:defStages (E1) | `zonePhase ω.zone l u = none`, `s(w,u) ∈ (ownM G run Y (ω.colAt Y)).edges`, with `A_Y` a parameter (`E1` in scratch A) |
| s5:defStages demoted / parent-bad | `¬ COLa G run Y (ω.cOutAt Y)`; `¬ COLc G run Y (ω.cOutAt Y) (fun i => Zone G run ω.zone Y i)` |
| s5:lemE1 (a) independence; (c) joint independence and ρ-random zones | `iIndepFun_edge_zone`; `indepFun_cOutAt_zone` + `isRSubset_Zone_law` |
| s5:lemChild PV instantiation | `fun (j : Fin (Vortex.pvJ \|V(Y)\|)) (c : Fin 4) => ownR G run Y col j c` type-checks (the PV index type is definitionally `Fin (JY G run Y)`), `ownM` for `M` |
| s5:lemParent | `LU G run Y c l ph σ`, `Zone`, `tY`, `σ < Tslot` — all present with ℕ/`Fin 4` indices |
| s5:lemExpect / s7 functionals | `(law G run).expect (fun ω => 80 * dem ω + 369 * lp ω)` |
| s6:defLending, JS-LC, consOrder, MIX-C | `EG.Chain.StageData.ofOutcome ω d dem lp` exists and `coherent_ofOutcome` proves the stage-1 facts on the support; `COLa_iff_of_not_isLight` gives MIX-C's `(2^{-5}, s_l/4)` |
| s6:lemLost (i) | `prob_labAt_ne_none` |
| s7:defCand, candMean | `(poolSet G ω.pool l r).filter (s(u,w) ∈ (LJV G run Y (ω.colAt Y) l).edges)`; `qPool * piPool * pY * deg` (`cand`, `candMean` in scratch A) |
| s7:lemCand (i) | `iIndepFun_edge_pool`, `prob_mem_LJV_law`, `prob_poolLabelLaw_some` |
| s7 RoundInput (pool, pool round, LJV classes) | `(poolL G ω.pool l, poolRound ω.pool)`, `(LJV …).edges` |

No missing field, no wrong index type.

## 5. Issues

### Minor

- **M1. Support characterisation of the joint law is missing.** TRIAGE §2.7 makes every
  fixed-outcome statement quantify `ω ∈ (Stage1.law G run).supp`, but the Lib gives only
  `col_mem_supp_colouringLaw` and `COLg_of_mem_supp_law`; `EG.Lib.Chain.StageInst` already had to
  re-derive `js_mem_supp_jsLaw` and `lt_KJS_of_labAt` itself. Missing and needed downstream:
  - `mem_supp_law_iff : ω ∈ (law G run).supp ↔ ∀ c, ω.toCoords c ∈ (coordLaw G run c).supp`
    (5 lines via `law_w : (law G run).w ω = (pi coordLaw).w ω.toCoords` and `mem_supp_pi`);
  - `zone_mem_supp : ω ∈ supp → ω.zone v = none ∨ ∃ Y i, ω.zone v = some (Y,i) ∧ Y ∈ availParts G run v ∧ i ∈ IU G run Y`
    (s5: "choice(v) = Y" implies `v ∈ Y`, `Y` light, `r ≤ R-2`, and the sublabel is a U-index;
    needed for `extph` in lemChild and for the "Equivalently" sentence of defZones);
  - `pool_mem_supp : ω ∈ supp → ω.pool v = none ∨ ∃ l r, ω.pool v = some (l,r) ∧ (l,r) ∈ poolIdx run`
    (s7:lemMULT/RoundInput: `w ∈ Pool_l` gives `1 ≤ r(w)`, `r(w)+2 ≤ l ≤ R`).
  All three are proved in `/tmp/s1rev2/ScratchA.lean` (§1) in ~55 lines; add them to
  `EG/Lib/Stage1/Law.lean`. No Defs change.
- **M2. No API lemma for `zonePhase`.** `EG/Lib/Stage1/Zones.lean` has none. Needed:
  `zonePhase_eq_some_iff : zonePhase ζ l v = some c ↔ ∃ Y σ, zoneOf ζ v = some (Y, LentTag.U l c σ)`
  and its support form `zonePhase ω.zone l v = some c ↔ ∃ Y σ, v ∈ Zone G run ω.zone Y (U l c σ)`,
  which is literally s5:defZones "Equivalently, `v` carries a round-`l` zone of phase `c` iff
  `v ∈ Zone_{Y,l,c,σ}` for some light part `Y` and some `σ`" (true on the support only, since
  `Zone ⊆ V(Y)`). Both proved in scratch A (§2, ~30 lines, using M1's `zone_mem_supp`). Used by
  s5:defStages (E1), lemChild (`extph`), lemParent (arc vertices in no round-`l` phase-`c` zone).
- **M3. Own-class edge probability.** `prob_mem_LJV` exists but its own-class twin does not:
  `prob_mem_ownClass : (colouringLaw G run Y).prob {c | e ∈ (ownClass G run Y c o).edges} = 1/(2 k_own)`
  (scratch B, 15 lines; s5:lemE1 (a) "`P(wu ∈ M_Y) = 1/2 · 1/k_own`" is the instance
  `o = ownIdx N none`). Also convenient: the per-edge joint-law marginal
  `(law G run).map (fun ω => ω.col Y e) = edgeLaw G run Y` (it is `map_toCoords_apply` at
  `Sum.inl ⟨Y, e⟩`, but consumers should not have to know the coordinate encoding).
- **M4. Packaged per-vertex independence shapes.** E1-INDEP and CAND-INDEP-MODEL are each one
  `iIndepFun_of_dependsOn` call plus a `Sym2.eq_iff` disjointness argument that s5 and s7 would
  otherwise both write. Suggest adding `iIndepFun_edge_zone` / `iIndepFun_edge_pool` (scratch A §3,
  ~25 lines each) to `EG/Lib/Stage1/Law.lean`, or at least the generic
  "edge coordinate of `Y` and a vertex coordinate are disjoint" helper. Optional.

### Cosmetic

- **C1.** `stage1.md` "Size" line is stale after fix round 1 (Lib is 1342 lines, tests 223; it
  says 1215 / 172).
- **C2.** The proposed CONVENTIONS "Stage 1" block and the T0 row `T0-colg-supp` are still only in
  `stage1.md` (CONVENTIONS.md is locked; integrator action, as the note says). Until merged, the
  blueprint names `EG.Lend.*`, `run G Y`, `T`, `tauJS`, `JSSite`, `stage1Law`, `S3.stage1Dist`,
  `ω.zlab`, `ω.lab`, `ω.LJS`, `ω.Mcls`, and the s7a paths `EG/Defs/Quot/Pool.lean`,
  `EG/Defs/Quot/Schedule.lean` (for stage 1) remain superseded without a locked record.
- **C3.** `Pool.lean`'s guard is `poolMass ≤ 1` alone; the s7a blueprint lean_shape also guarded
  `∀ l, 0 < M l`. The Lean guard is correct and weaker (see §1c); record this in the design note so
  a reader of the blueprint does not look for the second conjunct.
- **C4.** `EGTest/Stage1.lean` still exercises only degenerate zone and pool laws (`run1`: all
  mass on `none`/`⊥`). A non-degenerate pool check is available from scratch B
  (`pool_pos_run3`: `0 < P(plab = (3,1))` on `run3`, using `MOf d ≥ 2^40`); a non-degenerate
  zone law needs a run with a light part of ≥ 2 vertices and `R ≥ r+2`, which is not needed for
  the lock (agreed with round 1 M5).

## 6. T0 readings (agree with the design note and round 1; no T1/T2)

- **COL-EMPTY-INDEX / standalone own label (D-S1-4).** `idx = dirac none` when `lentIdx = ∅`; an
  own label is drawn for every ancestor. Both are extra independent coordinates that no manuscript
  law reads.
- **ZONE-TWO-STEP (D-S1-8).** The one-step law has the same joint law of `(choice, sublabel)`;
  the two-step marginal is `prob_zoneLabelLaw_choice`.
- **COL(g) on the support (D-S1-10, T0-colg-supp).** Agreed: "Item (g) always holds" is read for
  `ω ∈ (colLaw G run Y).supp`; a label assignment of weight 0 (bit `true`, index `none`, `r ≤ R-2`)
  violates the lent-class partition.
- **Consumer exclusivity** is a design rule of s4–s6 (COL-CONSUMERS-NOT-A-PROPERTY). Agreed.
- **`J_Y` via `Nat.floor`** (`k_own = 1` for tiny `Y`): junk outside the manuscript's domain
  (light parts have `L_Y ≥ 102·2^8` under Γ); recorded in TRIAGE §2.7.

## Scratch files

- `/tmp/s1rev2/ScratchA.lean`: `law_w`, `mem_supp_law_iff`, `zone_mem_supp`, `pool_mem_supp`,
  `zonePhase_eq_some_iff`, `zonePhase_eq_some_iff_mem_Zone`, `iIndepFun_edge_pool`,
  `iIndepFun_edge_zone`, `prob_labAt_ne_none`, `prob_mem_LJV_law`, `isRSubset_Zone_law`, the
  PV own-class family, `E1`, `parentBad`, `demoted`, `cand`, `candMean`, the lemExpect functional,
  RoundInput pool data, `StageData.ofOutcome`, the lemCOL (c) joint-independence shape,
  `(1.6:ℝ) = 8/5`.
- `/tmp/s1rev2/ScratchB.lean`: `two_pow_le_MOf`, `qPool_pos`, `qPool_le`, `poolMass_run3_le`,
  `pool_pos_run3`, `Zone_eq_empty_of_not_mem_IU`, `prob_mem_ownClass` (and the `ownM` instance).
