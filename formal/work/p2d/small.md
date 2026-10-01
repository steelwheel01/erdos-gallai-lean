# P2-D [small]: small foundations (TRIAGE §3, Defs order items 1–6): design note

Status: everything compiles, with 0 errors, 0 `sorry` and 0 warnings in the new and edited files.
- The lint is clean (`python3 scripts/lint.py`: 0 findings).
- The axiom scan (`scripts/Axioms.lean --prefix EG`, over all new Defs and Lib modules) inspects 464 constants and finds 0 `sorryAx` and 0 violations.
- Consumers of the moved `Obj.isEdge` rebuild cleanly: `EG.Lib.Found.Fnum`, `EG.Proof.Found.EG0`, `EGTest.Fnum` and `EGTest.Objects`.
- No Spec statement and no proof of a manuscript lemma was written.

## Files

| File | Kind | Contents |
|---|---|---|
| `EG/Defs/Objects.lean` | edit (add only) | `Obj.isEdge` (moved from `EG/Lib/Found/Fnum.lean`; `IsDecomp`, `Obj`, `Obj.edges`, `Obj.WF` and `cycleEdges` are unchanged) |
| `EG/Defs/Graph.lean` | edit (add only) | `FGraph.nbrSetDeg`, `FGraph.IsWellExpanding`; new import `Mathlib.Data.Real.Basic` |
| `EG/Defs/Log.lean` | new | `logIter`, `tower`, `logStar` |
| `EG/Defs/Constants.lean` | new | `epsC`, `sigmaC`, `Cp`, `Aexp` |
| `EG/Defs/PathDecomp.lean` | new | `IsPathDecomp`, `pathEndCount`, `IsPathCycleDecomp` |
| `EG/Defs/Components.lean` | new | `edgeVerts`, `edgeGraph`, `edgeComps`, `compVerts`, `compEdges`, `IsNonBridge`, `IsPendant` |
| `EG/Defs/Gamma/Core.lean` | new | `Gamma1a` … `Gamma1e`, `Gamma1Items`, `Gamma1core`, `Gamma2a` |
| `EG/Lib/Found/Fnum.lean` | edit | the `isEdge` definition removed (now in Defs); every lemma about it is kept, unchanged |
| `EG/Lib/Found/Log.lean` | new | log / tower / log\* API (below) |
| `EG/Lib/Found/Constants.lean` | new | value lemmas |
| `EG/Lib/Found/Gamma.lean` | new | Γ1core / Γ2a API |
| `EG/Lib/Found/NbrSetDeg.lean` | new | `nbrSetDeg` / `IsWellExpanding` API |
| `EG/Lib/Found/PathDecomp.lean` | new | path-decomposition API |
| `EG/Lib/Found/Components.lean` | new | component / bridge / pendant API |
| `EGTest/Defs2.lean` | new | unit tests for all of the above |

The root files `EG.lean` and `EGTest.lean` are not edited. The new modules must be added to them by `scripts/gen_roots.py` (integrator).

## Definitions, with the manuscript text

### Item 1: `Obj.isEdge` (Defs/Objects) and `nbrSetDeg`, `IsWellExpanding` (Defs/Graph)

- **`EG.Obj.isEdge : Obj V → Bool`** (`.edge _ ↦ true`, `.cycle _ ↦ false`).
  - [s1:defObject]: "An *object* is a cycle (of length at least 3) or a single edge."
  - The number of single edges of `D` is `D.countP Obj.isEdge`. It is used in v6 s1:factEG0(a) ("at most h − 1 of which are single edges") and in the s4 vortex finishes.
  - The body is identical to the former Lib definition. The Lib lemmas (`isEdge_edge`, `countP_isEdge_*`, …) stay in `EG/Lib/Found/Fnum.lean` and still prove by `rfl`.
- **`EG.FGraph.nbrSetDeg H U (d : ℝ) : Finset V := (H.verts \ U).filter (d ≤ |N_H(v) ∩ U|)`**.
  - [s1:citProp12]: "For U ⊆ V(G) and d > 0 let N_{G,d}(U) be the set of vertices of V(G) \ U with at least d neighbours in U."
  - [s3:propP13s] (proof): "Nbr_{G−F,d}(U) for the set of vertices outside U that have at least d neighbours in U in the graph G − F". This is `(G.deleteEdges F).nbrSetDeg U d`.
  - It is `noncomputable` because real `≤` has no computable decidability. `nbrSetDeg_natCast` gives the decidable form for an integer `d`.
- **`EG.FGraph.IsWellExpanding H (θ : ℝ) U : Prop := θ * |U| ≤ |Nbr_H(U)|`**.
  - [s3:lemL17s]: "Call U ⊆ V(G) *well-expanding* if |Nbr_G(U)| ≥ θ_*|U|."
  - [s1:citLem19] (proof sketch): "Call U′ well-expanding if |Nbr_G(U′)| ≥ |U′| log^{24} n". This is `θ = log^{24} n`.
  - The neighbourhood is taken in G, not in G − F, as both texts say.

### Item 2: `EG/Defs/Log.lean`

[s1:convGraphs](b): "log = log₂ throughout … We put log^{[0]}x := x and log^{[k]}x := log(log^{[k−1]}x), and log\*x is the least integer k ≥ 0 with log^{[k]}x ≤ 1."
- **`logIter k x := (Real.logb 2)^[k] x`**.
- **`logStar x : ℕ := sInf {k | logIter k x ≤ 1}`**.

Proof of [s2:lemLacunary](iv): "Let tw(0) := 1 and tw(j+1) := 2^{tw(j)}."
- **`tower : ℕ → ℝ`**, with `tower 0 = 1` and `tower (j+1) = (2:ℝ) ^ tower j` (`Real.rpow`).

### Item 3: `EG/Defs/Constants.lean`

[s1:defConstants](i): "ε := 2^{−5}, σ := 100, C′ := 103 and A := 105."
- **`epsC : ℝ := 2 ^ (-5 : ℤ)`**
- **`sigmaC : ℕ := 100`**
- **`Cp : ℕ := 103`**
- **`Aexp : ℕ := 105`**

### Item 4: `EG/Defs/PathDecomp.lean`

[s1:citCor22]: "Every graph can be decomposed into paths such that each vertex is an end of at most two of the paths … every path has two distinct ends in W …"

s4 (E): "Let 𝒫 be a decomposition of an edge set F into (non-trivial) paths. For every vertex v the number of paths of 𝒫 having v as an end …"

[s1:citThm21]: "Every n-vertex graph can be decomposed into at most n/2 paths and cycles."

- **`IsPathDecomp (F : Set (Sym2 V)) (P : List (List V))`** holds when:
  - every `p ∈ P` has `2 ≤ p.length` and `p.Nodup`;
  - `(P.flatMap walkEdges).Nodup`;
  - `∀ e, e ∈ P.flatMap walkEdges ↔ e ∈ F`.
- **`pathEndCount P v := P.countP (p.head? = some v ∨ p.getLast? = some v)`**.
- **`IsPathCycleDecomp F P C`**: the paths are as above; each `c ∈ C` satisfies `(Obj.cycle c).WF`; and the concatenation `P.flatMap walkEdges ++ C.flatMap cycleEdges` is Nodup and has exactly the edges of F.

### Item 5: `EG/Defs/Components.lean`

[s6:lemPAR]: "let V(E_ab) be the set of vertices incident with an edge of E_ab. Call a connected component of E_ab *odd* if it has an odd number of edges. In each odd component choose one edge that is either a non-bridge or a pendant edge (an edge with an end of degree 1) of that component".

[s6:defDesign]: "(Y,l) is *giant* iff some connected component of Bead_{Y,l} has more than 2γ_l edges".

- **`edgeVerts E := E.biUnion Sym2.toFinset`**.
- **`edgeGraph E := SimpleGraph.fromEdgeSet ↑E`**.
- **`edgeComps E := (edgeVerts E).image (edgeGraph E).connectedComponentMk`**.
- **`compVerts E C`** is the set of vertices of `V(E)` in C.
- **`compEdges E C := E.filter (∀ v ∈ e, mk v = C)`**.
- **`IsNonBridge E e := e ∈ E ∧ ¬ (edgeGraph E).IsBridge e`**, using Mathlib's `IsBridge`.
- **`IsPendant E e := e ∈ E ∧ ∃ v ∈ e, degE E v = 1`**.

### Item 6: `EG/Defs/Gamma/Core.lean`

[s1:condG1]: "D_* > 2 …; and for every real μ ≥ log₂log₂D_*, with λ := 2^μ:
- (a) μ ≥ 2^8;
- (b) 2^μ ≥ 2^{14}Aμ^3;
- (c) 2A log₂(Aμ) ≤ 1.6μ;
- (d) 2log₂μ + 8 ≤ μ;
- (e) λ^{36} ≥ 2^{240}(Aμ)^{46A};
- (f) …"

[s1:condG2](a): "D_* ≥ 2^{117}".

The Lean definitions:
- **`Gamma1a μ := 2^8 ≤ μ`**
- **`Gamma1b μ := 2^14 * A * μ^3 ≤ 2^μ`**
- **`Gamma1c μ := 2 * A * logb 2 (A * μ) ≤ 1.6 * μ`**
- **`Gamma1d μ := 2 * logb 2 μ + 8 ≤ μ`**
- **`Gamma1e μ := 2^240 * (A * μ)^(46 * A) ≤ (2^μ)^36`**
- **`Gamma1Items μ`** is the conjunction of these five items.
- **`Gamma1core D := 2 < D ∧ ∀ μ, logb 2 (logb 2 D) ≤ μ → Gamma1Items μ`**
- **`Gamma2a D := 2^117 ≤ D`**

## Decisions (and why)

1. **`Obj.isEdge` is moved, not duplicated.** The Lean environment cannot hold two declarations with the same name. The definition moves from `EG/Lib/Found/Fnum.lean` to `EG/Defs/Objects.lean` with the same body, and its API lemmas stay in Lib. The TRIAGE §2.11 and s4 blueprint requirement is that PV/VX Specs can mention it from Defs.
2. **Locked Defs files: add only.** In `Objects.lean` and `Graph.lean` no existing declaration was touched. `Graph.lean` gains `public import Mathlib.Data.Real.Basic`, because `nbrSetDeg` and `IsWellExpanding` have real thresholds.
   - The kernel hashes of the existing locked constants are unaffected.
   - The *file* SHA-256 records of these two files in `LOCK.json` will change, so the integrator must re-lock them. `scripts/lock.py check` was not run: it needs `lake build EG`, which agents must not run.
3. **`IsWellExpanding` lives in `Defs/Graph.lean`, not `Defs/Link/Star.lean`.** The task placed it there, and TRIAGE §2.11 had proposed Star.lean. Graph.lean is the better home:
   - it is θ-parametrized and used both with `θ = θ_*` (s3) and with `θ = log^{24}n` (s1:citLem19);
   - it only needs `nbrSet`.

   Star.lean should reference `FGraph.IsWellExpanding` and not redefine it.
4. **`nbrSetDeg` has a real threshold `d`.** B-M Prop 12 takes a real `d > 0`; s3 uses an integer `d_*`, cast. It is defined for all `d` and `U`, with "neighbours in U" being `N_H(v) ∩ U`. For `d ≤ 0` every vertex of `V(H) \ U` qualifies. The manuscript uses only `d > 0`, and `nbrSetDeg_subset_nbrSet` needs `0 < d`.
5. **Logs.**
   - `logIter` is the plain iterate of the total `Real.logb 2`.
   - `logStar` uses `sInf`, as TRIAGE §2.3 requires, so the definition has no proof term. Non-emptiness is proved in Lib (`exists_logIter_le_one`, via `x ≤ tower k` for some k), so `sInf` really is the least element.
   - `logIter` can revisit values `> 1` after going negative, because `logb 2 x = logb 2 |x|`. `log*` takes the *least* k, so this never matters. `logStar_eq_zero_iff : log* x = 0 ↔ x ≤ 1` holds for every real x, and so does `logStar_le_iff_le_tower : log* x ≤ k ↔ x ≤ tw(k)`.
   - `tower` is real-valued (TRIAGE §2.3), with `2^{tw j}` as `Real.rpow`.
6. **Constant names and types.**
   - The Greek names `ε` and `σ` are standard bound-variable names (`IsExpander G ε s`), so a global `EG.ε` would be shadowed or confusing. The constants are `epsC` and `sigmaC`. `Cp` and `Aexp` follow TRIAGE §2.4.
   - `σ`, `C′` and `A` are `ℕ`, because the manuscript uses them as exponents (`2^{σ+15}`, `(log₂D)^{C′}`, `(Aμ)^{46A}`, `(Aμ)^{2A}`). In real expressions they appear through a cast.
   - `ε = 2^{-5}` is real (`zpow`); `epsC_eq : epsC = 1/32`.
7. **Γ1 items are separate definitions** (`Gamma1a`–`Gamma1e`) plus the conjunction `Gamma1Items`. The manuscript cites them individually ("by Γ1(c) at u", "Γ1(a),(b) at μ"), so Specs and proofs can name the item they use (TRIAGE §2.6 principle).
8. **Γ1 encoding.**
   - `λ = 2^μ` is `Real.rpow`, and `λ^{36}` is `(2^μ)^36` with natural exponent 36.
   - `(Aμ)^{46A}` uses the natural exponent `46·Aexp = 4830`, and `2^{14}Aμ^3` uses the natural exponent 3.
   - `1.6` is the real literal, which is exactly `8/5`; the tests check `(1.6:ℝ) = 8/5` and the unfolded forms of (b), (c) and (e).
   - `D > 2` is kept as in the text. It makes `log₂log₂D` positive, which the ray transfer lemmas need.
9. **Eventualities.**
   - Γ1 is a condition on the whole ray `μ ≥ log₂log₂D`, so it is upward closed in D; this is proved in `Gamma1core.mono`. Γ2(a) is a lower bound (`Gamma2a.mono`).
   - The claims that Γ1 holds for all sufficiently large D and that Γ2(a) is implied by Γ1 are stated in the manuscript.
     - Γ2(a) from Γ1 is the easy implication `Gamma1core.gamma2a`, via `log₂D ≥ 2^{256}` (`Gamma1core.two_pow_256_le_logb`).
     - "Every sufficiently large D satisfies Γ1" belongs to s7:lemGammaSat and is not proved here, because it is a manuscript lemma.
   - Item (f) (COL-JV column 3), Γ3 and Γ4 belong to later Defs files (TRIAGE §3 items 14 and 34). Γ2(b),(c) are lemmas, never definitions.
10. **Path decompositions.**
    - Paths must have at least 2 vertices ("(non-trivial) paths" in (E); C22-TRIVIAL), and they have no repeated vertex, so the ends are distinct.
    - `pathEndCount` therefore counts both the paths having v as an end and the path ends at v.
    - Paths are unoriented in effect: a path and its reverse are both allowed, and ends are "first or last".
    - An F containing a loop has no path decomposition (`IsPathDecomp.not_isDiag`). Statements use loopless F, as with `IsDecomp`.
    - `IsPathCycleDecomp` (for the stage-α Lovász hypothesis, s1 blueprint) was added beyond the task list. It is cheap, has the same shape, and `isPathCycleDecomp_nil_right` connects it to `IsPathDecomp`. Drop it if the integrator prefers to defer it.
11. **Components.**
    - The edge set E is read as the graph `(V(E), E)` via Mathlib's `fromEdgeSet`, which drops loops. Components are Mathlib's `ConnectedComponent`s restricted to those that meet `V(E)`; the singleton components of vertices outside `V(E)` are excluded (PAR-COMPONENT-ISOLATED).
    - "Non-bridge / pendant *of that component*" is encoded on the whole edge set, which is equivalent:
      - a bridge is a local property: its ends are not connected in `E − e`;
      - a vertex's degree in its component equals `degE E v`.
    - `compEdges` uses "all ends in C". For a non-loop edge of E, both ends always lie in one component (`mem_compEdges_of_mem`), and distinct components have disjoint edge sets (`disjoint_compEdges`).
    - Loops in E are outside the manuscript's domain: they count in `edgeVerts` and `degE` but are not graph edges. Statements use loopless E.
    - The finsets over the quotient type use classical decidability and are `noncomputable`.

## Lib API (small lemmas, all proved)

- **Log** (`EG.Lib.Found.Log`):
  - iterates and tower: `logIter_zero/succ/succ'/one`, `tower_zero/succ`, `one_le_tower`, `tower_pos`, `logb_tower_succ`, `logIter_tower`, `le_tower_self`, `exists_le_tower`;
  - elementary inequalities: `add_one_le_two_rpow`, `logb_le_sub_one`;
  - log\*: `exists_logIter_le_one`, `logIter_logStar_le_one`, `logStar_le_of_logIter_le_one`, `one_lt_logIter_of_lt_logStar`, `logStar_eq_zero_iff`, `logStar_of_one_lt`, `logStar_le_iff_le_tower`, `lt_logStar_iff_tower_lt`, `logStar_tower`, `logStar_mono`, `logStar_two_rpow`, `logStar_le_self`.
  - Not yet provided: the growth fact `log* = o(log log)` and `logStar_le_one_add_log` (listed in TRIAGE §2.3). They are proof-side lemmas for s2/s6.
- **Constants**: `epsC_eq`, `epsC_pos`, `sigmaC_eq`, `Cp_eq`, `Aexp_eq`, `cast_sigmaC/Cp/Aexp` (simp).
- **Gamma**:
  - accessors: `Gamma1Items.a`…`.e`, `Gamma1core.two_lt`, `.items`;
  - bounds and transfers: `.one_lt_logb`, `loglog_mono`, `.mono`, `.items_loglog`, `.two_pow_eight_le_loglog`, `.two_pow_256_le_logb`, `.items_logb`, `.gamma2a`, `Gamma2a.mono`.
- **NbrSetDeg**: `mem_nbrSetDeg`, `nbrSetDeg_natCast`, `mem_nbrSetDeg_iff_ceil`, `nbrSetDeg_subset_sdiff/verts`, `disjoint_nbrSetDeg`, `nbrSetDeg_subset_nbrSet`, `nbrSetDeg_anti`, `isWellExpanding_iff`, `isWellExpanding_empty`, `IsWellExpanding.anti`.
- **PathDecomp**:
  - general: `not_isDiag_of_mem_walkEdges`;
  - `IsPathDecomp` accessors and facts: `.two_le_length`, `.nodup`, `.mem_iff`, `.edges_mem`, `.not_isDiag`;
  - constructors: `isPathDecomp_nil`, `isPathDecomp_singleton`;
  - end counts: `pathEndCount_nil/cons/le_length`;
  - `isPathCycleDecomp_nil_right`.
- **Components**: `mem_edgeVerts`, `edgeVerts_mono`, `edgeGraph_adj`, `edgeSet_edgeGraph`, `mem_edgeComps`, `mem_compVerts`, `mem_compEdges`, `compEdges_subset`, `mem_compEdges_of_mem`, `disjoint_compEdges`, `isNonBridge_mk_iff`, `IsNonBridge.mem`, `IsPendant.mem`.

## Unit tests (`EGTest/Defs2.lean`, all pass)

- **`isEdge`**: values on objects, and a `countP` over a list.
- **`nbrSetDeg` and `IsWellExpanding`**:
  - on the graph `{01,02,12,13}`: `N_{·,1}({0,1}) = {2,3}`, `N_{·,2} = {2}`, `N_{·,3} = ∅`;
  - the real threshold 1.5 behaves like 2, and U itself is excluded;
  - `IsWellExpanding` holds at θ = 1 but not at θ = 2, and the empty set is well-expanding.
- **Logs**:
  - `tw(1..3) = 2, 4, 16` and `log^{[2]}16 = 2`;
  - log\* of 1, 1/2 and −5 is 0; `log*2 = 1`, `log*16 = 3`, `log*17 = 4` (the jump just above a tower value), and `log*(2^16) = 4`.
- **Constants**: the values, and a σ-exponent check.
- **Γ**:
  - (a) holds at 256 and fails at 255; (d) holds at 256;
  - `¬Gamma1Items 0`, `Gamma2a (2^117)` and `¬Gamma2a 1`;
  - the encodings of (b), (c) and (e) are exact;
  - `¬Gamma1core 3` (the ray is non-trivial);
  - upward closure together with Γ2(a).
- **Paths**:
  - P3 as one path and as two paths (one reversed);
  - end counts;
  - rejected: a trivial path, an edge used twice, a walk with a repeated vertex, and a loop;
  - the triangle as a single cycle in `IsPathCycleDecomp`.
- **Components**, on `E = {01,12,20,23,45}`:
  - `edgeVerts`, adjacency, and that 0 and 3 lie in the same component; the component of 4 is in `edgeComps`;
  - `23 ∈ compEdges (comp 0)`;
  - 23 is pendant and 01 is not;
  - 01 is a non-bridge, and 23 is a bridge (not a non-bridge).

## Open points for the integrator / reviewers

- Re-lock the file hashes of `EG/Defs/Objects.lean` and `EG/Defs/Graph.lean`, and add the new modules to the roots (`gen_roots.py`).
- Star.lean (item 11) should *use* `FGraph.IsWellExpanding`; the name is taken.
- `EGCheck/BridgeLemmas.lean` imports `EG.Defs.Objects`. It was not rebuilt: it has no name clash (no `isEdge` in EGCheck), and the Objects change only adds a declaration.

## Fix round 1 (response to `work/p2d/small.review1.md`)

No `EG/Defs/**` file was changed in this round (all locked-constant hashes stay as reviewed).
Changed: `EG/Lib/Found/Gamma.lean`, `EG/Lib/Found/Log.lean`, `EG/Lib/Found/Components.lean`,
`EGTest/Defs2.lean`, `CONVENTIONS.md`, `work/p2/TRIAGE.md`, `work/p2/blueprint_s1.md`,
`work/p2/blueprint_s2a.md`, `work/p2/blueprint_s3a.md`, `work/p2/blueprint_s6b.md`.
Builds: `lake build EG.Lib.Found.Gamma EG.Lib.Found.Components` (with `EG.Lib.Found.Log`) OK;
`scripts/check.sh EGTest/Defs2.lean` 0 errors; `scripts/lint.py` 0 findings;
`scripts/Axioms.lean` on Gamma/Components: 0 sorryAx, 0 violations. No other module imports the
three changed Lib files.

| # | Item | Verdict | Action |
|---|---|---|---|
| M1 | no positive Γ1 test | valid | **Fixed.** Lib (`EG.Lib.Found.Gamma`): `gamma1Items_of_le : 2^20 ≤ μ → Gamma1Items μ` (all five items on the whole ray, via `t = log₂μ`, `μ ≥ 1024(t−9)` from Bernoulli, `A = 105 ≤ 2^7`), `eventually_gamma1Items` (`∀ᶠ μ in atTop`), `gamma1core_two_rpow_two_rpow` (`Gamma1core (2^{2^{2^20}})`), `exists_gamma1core`, `eventually_gamma1core` (`∀ᶠ D in atTop`). Tests: `Gamma1Items (2^20)`, its items (a),(e), `∃ D, Gamma1core D ∧ Gamma2a D`, the eventuality. This is only the (a)–(e) part of the eventuality claim of s7:lemGammaSat with an explicit non-optimised threshold; it does not replace that Spec. Item (f) (`Gamma1f`) will need its own non-vacuity check when it is defined (noted in the Gamma.lean header). |
| M2 | `logStar_le_one_add_log`, `log* = o(log log)` missing | valid (proof-side) | **Fixed now** rather than deferred (cheap): `logStar_eq_two_add`, `logStar_le_two_add_loglog` (`log* y ≤ 2 + log₂log₂ y`, `y ≥ 4`; the TRIAGE name `logStar_le_one_add_log` refers to this statement, recorded in TRIAGE §2.3), `logStar_le_three_add_logloglog` (`y ≥ 16`), `logStar_isLittleO_loglog` (`(fun y => (logStar y : ℝ)) =o[atTop] (fun y => logb 2 (logb 2 y))`). Tests added. |
| M3 | IsWellExpanding placement in TRIAGE/blueprint_s3a | valid | **Fixed.** TRIAGE §2.11 and §3 item 11, and blueprint_s3a (module row, (eqStar) paragraph, both formalization lines, the three defs_needed rows, the lean_shape) now say: `EG.FGraph.IsWellExpanding` lives in `EG/Defs/Graph.lean`; Star.lean uses it and does not redefine it. Checked: the current `EG/Defs/Link/Star.lean` (another agent's) already refers to `EG.FGraph.IsWellExpanding` and defines no duplicate. Also a CONVENTIONS line. |
| M4 | LOCK.json file SHAs of Graph.lean/Objects.lean | valid (integrator) | **Integrator action**, not done here (LOCK.json is integrator-owned): re-lock those two file hashes with an approval, then full `lake build EG` + `scripts/lock.py check`. This round did not touch any Defs file, so nothing further changes. |
| M5 | no component map / component-local lemmas | valid | **Fixed** (`EG.Lib.Found.Components`): `edgeGraph_mono`, `compMap h : (edgeGraph E).ConnectedComponent → (edgeGraph E').ConnectedComponent` for `h : E ⊆ E'` (Mathlib `ConnectedComponent.map` of `Hom.ofLE`, `@[expose]`), `compMap_mk` (rfl), `compMap_mem_edgeComps`, `compEdges_subset_compMap`, `card_compEdges_le_compMap` (`(compEdges E C).card ≤ (compEdges E' (compMap h C)).card`); component-local: `mem_compEdges_of_mem_of_mk` (every edge of `E` at a vertex of `C`, loops included, is in `compEdges E C`), `degE_compEdges`, `isPendant_compEdges_iff`, `reachable_deleteEdges_compEdges`, `isNonBridge_compEdges_iff` (for `e ∈ compEdges E C`: `IsPendant/IsNonBridge (compEdges E C) e ↔ IsPendant/IsNonBridge E e`). This replaces the docstring-only argument of decision 11 by proofs. Tests added. |
| M6 | loop behaviour only in docstrings | valid | **Fixed.** CONVENTIONS.md (Graphs section): edgeComps / compEdges / IsNonBridge / IsPendant / IsPathDecomp / IsPathCycleDecomp are for loopless edge sets only, as for `fnum`, with the concrete odd behaviours listed. Also added to TRIAGE §2.12. |
| C1 | EG0 Spec docstring says isEdge is in Fnum.lean | valid (cosmetic) | **Deferred as advised**: `EG/Spec/Found/EG0.lean` is a protected, locked Spec file; fix the docstring (`EG/Defs/Objects.lean`) at its next approved re-lock. Not edited. |
| C2 | constant names differ from TRIAGE/blueprints | valid (cosmetic) | **Fixed.** Final names (`epsC`, `sigmaC`, `Cp`, `Aexp`) recorded in TRIAGE §2.4 and §2.12 and in a new CONVENTIONS "Constants and Γ" section; `EG.CpC`/`EG.AexpC` replaced by `EG.Cp`/`EG.Aexp` in blueprint_s1, blueprint_s2a and blueprint_s6b. |
| C3 | IsPathCycleDecomp beyond the task list | valid (keep) | **Kept** and recorded in blueprint_s1 (s1:citThm21, after the lean_shape): the stage-α Lovász hypothesis is stated with `IsPathCycleDecomp`; dropping trivial paths is lossless. |

## Fix round 2 (response to `work/p2d/small.review2.md`)

No `EG/Defs/**` file was changed in this round (the reviewed and approved definitions, and all
locked-constant hashes, stay as they were). Changed: `EG/Lib/Found/Log.lean`,
`EG/Lib/Found/Gamma.lean`, `EGTest/Defs2.lean`, `CONVENTIONS.md`, `work/p2/TRIAGE.md` (§2.3 line),
`work/p2/blueprint_s1.md`, `work/p2/blueprint_s2a.md`, `work/p2/blueprint_s2b.md`,
`work/p2/blueprint_s6a.md`.
Builds: `lake build EG.Lib.Found.Gamma` (with `EG.Lib.Found.Log`) OK;
`scripts/check.sh EGTest/Defs2.lean` rc=0, 0 errors, 0 sorry; `scripts/lint.py` 0 findings;
`scripts/Axioms.lean --prefix EG --no-sorry EG.Lib.Found.Gamma EG.Lib.Found.Log`: 99 constants,
0 sorryAx, 0 violations. Only `EG.Lib.Found.Gamma` and `EGTest.Defs2` import the changed Lib files
(the `EG.Lib.Found.LogMono` importers are unaffected); both changes are additions only.

| # | Item | Verdict | Action |
|---|---|---|---|
| M1 | missing transfer `Gamma1core D → log₂D ≤ x → Gamma1Items (log₂x)` and `log* x ≤ 1 + log x` | valid | **Fixed.** `EG.Gamma1core.items_logb_of_le` (Lib Gamma, the reviewer's one-liner) and `EG.logStar_le_one_add_logb (hx : 1 ≤ x) : (logStar x : ℝ) ≤ 1 + logb 2 x` (Lib Log; s6.tex:262 verbatim; proof: `x = 1` directly, else `log* x = 1 + log*(log x)` and either `log x ≥ 1` with `logStar_le_self` or `log*(log x) = 0`). Tests in Defs2 (endpoint `x = 1`, `x = 3`, the transfer). Module headers list both. TRIAGE §2.3: the listed `logStar_le_one_add_log` is now identified with `logStar_le_one_add_logb` (round 1 had mapped it to the sharper `logStar_le_two_add_loglog`, which stays as an extra); the Log.lean docstring of `logStar_le_two_add_loglog` was adjusted accordingly; blueprint s6a (tower facts bullet) and blueprint s2b (Gamma hypotheses bullet) now name the provided Lib lemmas. |
| M2 | LOCK.json file hashes, new Defs files in the lock, root files | valid (integrator) | **Integrator action**, not done here (LOCK.json, `EG.lean`, `EGTest.lean` are integrator-owned/protected): re-lock the file SHA-256 of `EG/Defs/Graph.lean` and `EG/Defs/Objects.lean` with an approval (38/38 constants unchanged per the reviewer), add `EG/Defs/{Log,Constants,PathDecomp,Components}.lean` and `EG/Defs/Gamma/Core.lean` (plus the two re-hashed files) to the lock, run `scripts/gen_roots.py`, then full `lake build EG` and `scripts/lock.py check`. |
| M3 | no negative Γ1 test on the ray of (a) | valid | **Fixed.** `example : ¬ Gamma1c 256` and `example : ¬ Gamma1e 256` added to `EGTest/Defs2.lean` (Γ section, after the positive checks), with the reviewer's proofs; together with `Gamma1a 256`, `Gamma1d 256` and `gamma1Items_of_le` (`2^20`) they pin a genuine threshold between `2^8` and `2^20`. |
| C1 | `IsPathDecomp ↑F P` does not elaborate | valid, verified | **Fixed.** Scratch check: `∃ P, IsPathDecomp ↑F P`, `∃ D, IsDecomp ↑F D` and `∃ P C, IsPathCycleDecomp ↑H.edges P C` fail with "expected `Set (Sym2 ?m)`"; with the second argument's type already known (`(P : List (List V))`, `∃ D : List (Obj V), …`) `↑F` works; `(F : Set (Sym2 V))` works in all cases. New CONVENTIONS line (Objects and f): always write `(F : Set (Sym2 V))`. Blueprint s1 (Cor 22 Spec and `IsPathDecomp.length_le_card`, the untyped-binder cases) rewritten; the other blueprint occurrences have typed binders and elaborate, and the CONVENTIONS rule covers them when the Specs are written. |
| C2 | numerals in the s6a CONC(iii) sketch; EG0 docstring | valid | **Fixed** (blueprint part): s6a CONC(iii) now reads `(2 : ℝ) ^ (EG.sigmaC + 14) * … + 100 * EG.epsC * … / ((EG.Cp : ℝ) * …)` (checked against s6.tex:302, s6:thmCONC(iii)). Same sync applied to the other inline `2 ^ (-5 : ℤ)` = ε occurrences in blueprint s2a (323, 388–390, 715) and s2b (153, 288); left as is: s2a:604 (`ancEps`, the ε/2 vs ε split, numerals exact) and s4:188 (a range bound on `εO`, not the constant ε). The `EG/Spec/Found/EG0.lean` docstring remains **deferred by design** to the next approved re-lock of that protected file. |
