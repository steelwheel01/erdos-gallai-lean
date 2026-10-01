# P2-D [small] definition review, round 1 (clean-room)

Reviewer: clean-room definition reviewer, 2026-09-26. Scope: TRIAGE §3 Defs order items 1–6, as
listed in `work/p2d/small.md`. No Lean file was edited.

**Verdict: APPROVE.** No major issues. Six minor items and three cosmetic ones are listed at the
end; none of them blocks the lock.

## What was checked

- **Sources read.**
  - `AGENTS.md`, `CONVENTIONS.md`, `work/p2/TRIAGE.md` (§2.3, 2.4, 2.9, 2.11, §3);
  - blueprints s1, s2b, s3a, s4, s5 and s6 (every use of these names);
  - manuscript s1.tex: convGraphs, citProp12, citLem19 sketch, citThm21, citCor22, defConstants, condGamma;
  - manuscript s2.tex: lemLacunary, the tw paragraph and the log* facts;
  - manuscript s3.tex: propP13s proof, lemL17s;
  - manuscript s4.tex: (E), PV(b),(c);
  - manuscript s6.tex: lemPAR with its proof, defDesign, JS-LC Steps 3–5.
- **Builds.** The oleans of all 14 touched `EG` modules are newer than their sources.
  - `lake env lean EGTest/Defs2.lean`: 0 errors.
  - `python3 scripts/lint.py`: 0 findings.
- **Locked constants.** `scripts/Lock.lean` was run on `EG.Defs.{Graph,Objects,Walk,Expander,Fnum}` (read-only) and compared with `LOCK.json`.
  - All **52** locked constants in these modules have unchanged kernel hashes, so the new import `Mathlib.Data.Real.Basic` in Graph.lean did not change any existing definition.
  - Only the file SHA entries of `EG/Defs/Graph.lean` and `EG/Defs/Objects.lean` change, so they must be re-locked.
  - `EG.Obj.isEdge` was never a locked constant. Every importer that uses it (Spec/Proof EG0, Lib Fnum, EGTest Fnum) was rebuilt after the move.
- **Scratch tests** (`$SCRATCH/T1.lean` and `T2.lean`, all pass):
  - **`log*` values:**
    - `log* 3 = 2` (not a tower value), `log* 0 = 0`;
    - `log* 65537 = 5`, just above `tw 4 = 65536`.
  - **Γ non-vacuity spot check:** each of `Gamma1a` … `Gamma1e` holds at `μ = 2^20`. The unfolded (b), (c) and (e) at a concrete μ confirm that the exponents `3`, `46·A = 4830`, `36` and the rpow placement are sane.
  - **Γ negative checks:** `¬Gamma2a (2^116)` and `¬Gamma1core 4`.
  - **Components** on the edge set {01, 12, 34, 45, 35, 56}:
    - the end edges 01 and 56 are pendant;
    - the triangle edge 34 is not pendant, and it is a non-bridge (reachability through 5 in `E − 34`);
    - the loop edge case: `IsNonBridge {77} s(7,7)` is true and `7 ∈ edgeVerts`. This is outside the domain and documented.
  - **Path decompositions:**
    - `IsPathDecomp` rejects a path whose edge is not in F;
    - `pathEndCount [[0,1,2],[2,3]] 2 = 2`.

## Per definition: back-translation, manuscript, edge cases, downstream uses

### 1. `Obj.isEdge` (Defs/Objects): faithful
- Back-translation: "the object is a single edge". The body is identical to the former Lib version, and `#print` confirms `EG.Obj.isEdge` is visible from `EG.Defs.Objects` alone.
- Downstream uses: the EG0 counts `D.countP Obj.isEdge + 1 ≤ H.card` and `≤ W.card` (blueprint s1), and the VX⁺ single-edge count (blueprint s4). Both can be stated.

### `FGraph.nbrSetDeg` (Defs/Graph): faithful
- Lean: `(H.verts \ U).filter (d ≤ |N_H(v) ∩ U|)`, which is "vertices of V(G)\U with at least d neighbours in U" (s1:citProp12).
- `H.nbrs` is restricted to `H.verts`, so this is exact even when `U ⊄ V(H)`.
- The s3:propP13s proof says "an integer d ≥ 1 … vertices outside U … in G−F". That is `(G.deleteEdges F).nbrSetDeg U (d:ℝ)`, and `deleteEdges` keeps `verts`.
- The real threshold serves both B-M Prop 12 (real `d`) and P13\* (integer `d_*`, cast).
- For `d ≤ 0` every vertex of `V\U` qualifies. The manuscript uses only `d > 0`, and this is documented.
- Downstream (blueprints s1 and s3a): `((G.deleteEdges F).nbrSetDeg U d).card` in the P12 Spec. It can be stated.

### `FGraph.IsWellExpanding` (Defs/Graph): faithful
- Lean: `θ·|U| ≤ |Nbr_H(U)|`. This is s3:lemL17s "|Nbr_G(U)| ≥ θ_*|U|" with θ = θ_*, and s1:citLem19 with θ = log^{24} n.
- The neighbourhood is taken in G, not G−F, as the text says.
- Argument order `G.IsWellExpanding θ U` matches the s3a blueprint sketches (L17s, P18s(i)).
- Placement deviation: TRIAGE §2.11 and §3 item 11 put this in Star.lean; it is now in Graph.lean. The reason is sound (it depends on θ only). See minor item M3.

### 2. `logIter`, `tower`, `logStar` (Defs/Log): faithful
- **`logIter`.** `(logb 2)^[k] x` equals log^{[k]} x. The Lean iterate unfolds on the inside, the manuscript on the outside; they agree by `iterate_succ_apply'` (`logIter_succ'`).
- **`logStar`.** `sInf {k | logIter k x ≤ 1}` is "the least integer k ≥ 0 with log^{[k]}x ≤ 1".
  - Non-emptiness is proved for every real x (`exists_logIter_le_one`), so `sInf` is the minimum.
  - Before the first hit, all iterates are > 1, so the total `logb` never leaves its genuine domain on the relevant prefix.
  - Hand check: `log*17 = 4` (test) matches the manuscript's "log* z = j iff tw(j−1) < z ≤ tw(j)".
- **`tower`.** `tw 0 = 1`, `tw(j+1) = 2^{tw j}` (rpow). This matches s2.tex:1126 exactly.
- **Downstream uses, all statable with `(logStar x : ℝ)` casts:**
  - s2 lemLacunary(iv), with `F(x) = (2 log*(2^x)+2)/η(x)`;
  - lemTower(a),(d): `R − r ≤ 2 log* d_r + 2` in ℕ with addition, `λ_r ≥ 2^{2 log* d_r + 2}`;
  - s6 epsCONC: `log* D / log D`, `log* D / (C' log log D)`.

### 3. `epsC`, `sigmaC`, `Cp`, `Aexp` (Defs/Constants): faithful
- s1:defConstants(i) gives ε = 2^{−5} (the real zpow `2^(−5:ℤ)`), σ = 100, C′ = 103 and A = 105.
- **Types.** σ, C′ and A are ℕ because they occur as exponents: `2^{σ+15}`, `(log D)^{C′}`, `(Aμ)^{46A}`, `(Aμ)^{2A}`.
- **Real uses** go through casts: `200ε`, `C′ log log D`, `λ^{σ+2.5}` as `((sigmaC:ℝ)+5/2)`.
- **ε in expanders.** `IsExpander epsC s` type-checks.
- **Names** differ from the letters in TRIAGE §2.4 and from the s1/s2a blueprints (`CpC`, `AexpC`). See cosmetic item C2.

### 4. `IsPathDecomp`, `pathEndCount`, `IsPathCycleDecomp` (Defs/PathDecomp): faithful
- **`IsPathDecomp`.** Each member is a vertex list with ≥ 2 vertices and no repeated vertex. The walk edges concatenate to a duplicate-free list with exactly the edges of F.
  - This is "decomposition of F into (non-trivial) paths", as in s4 (E), s1:citCor22 and PV(b): "paths of length at least 1 with two distinct ends".
  - Consistent with `IsPathIn` (Walk.lean) and with `IsDecomp`: F is a `Set`, and loopy F is impossible.
- **`pathEndCount`** counts the paths whose first or last vertex is v. Because members are Nodup with ≥ 2 vertices, this is both "#paths having v as an end" and "#path ends at v". So the three uses read correctly:
  - (E) parity: `pathEndCount P v ≡ degE F v (mod 2)`;
  - Cor22: `≤ 2`;
  - PV(c): `≤ degE H0 x`.
- **`IsPathCycleDecomp`** (beyond the task list) is the right shape for the stage-α Lovász hypothesis (LOV-TRUTH):
  - restricting to non-trivial paths loses nothing, because trivial paths carry no edges and can be dropped, which lowers the count;
  - cycles are `Obj.WF` (Nodup, length ≥ 3).

  So `∀ H : FGraph V, ∃ P C, IsPathCycleDecomp ↑H.edges P C ∧ 2*(P.length + C.length) ≤ H.card` is a true statement.
- Downstream (blueprint s4 PV): `IsPathDecomp ↑(H0 \ Hobj) (arcs.map Prod.fst)` and `pathEndCount … x ≤ degE H0 x`. Both can be stated.

### 5. Components (Defs/Components): faithful
- **Definitions.**
  - `edgeVerts E` = V(E) (s6:lemPAR).
  - `edgeGraph E` = `fromEdgeSet E`.
  - `edgeComps E` = the components that meet V(E). These are exactly the components of the graph (V(E), E), and each of them has an edge.
  - `compEdges E C` = the edges with both ends in C.
- **Mathlib `IsBridge`** is `Sym2.lift (¬ (G.deleteEdges {e}).Reachable v w)`. So `IsNonBridge E s(u,v)` for an edge of E means u and v stay connected in E − e. That is the manuscript's "C − e is connected" (PAR proof, "Even components after deletion").
- **"Of that component" = global.** The equivalence is argued correctly:
  - bridges are determined within the component;
  - a vertex's degree in its component equals `degE E v`.
- **Isolated-vertex components** of a bipartite E_ab with sides V_a, V_b have 0 edges, so they are never odd. Excluding them does not change "#odd components ≤ |V(E_ab)|/2".
- **Downstream statements that can be written:**
  - PAR: `∀ C ∈ edgeComps E, Odd (compEdges E C).card → …`, the count `((edgeComps E).filter (Odd ∘ card ∘ compEdges E)).card`, and `IsNonBridge E e ∨ IsPendant E e`.
  - defDesign "giant": `∃ C ∈ edgeComps Bead, 2*γ < (compEdges Bead C).card`. Bead_{Y,l} is an edge set (s6.tex:252).
  - JS-LC Steps 3–5 (proof-internal): `compVerts` and `compEdges`.
- **Loops** are outside the domain and documented: a loop is counted in `compEdges`/`degE` and is a "non-bridge".

### 6. `Gamma1a`–`Gamma1e`, `Gamma1Items`, `Gamma1core`, `Gamma2a` (Defs/Gamma/Core): faithful
Each item quoted against s1.tex:1602–1620:

| Item | Manuscript | Lean |
|---|---|---|
| (a) | μ ≥ 2^8 | `2^8 ≤ μ` |
| (b) | 2^μ ≥ 2^{14}Aμ^3 | `2^14·A·μ^3 ≤ 2^μ` (rpow) |
| (c) | 2A log₂(Aμ) ≤ 1.6μ | `2·A·logb 2 (A·μ) ≤ 1.6·μ` (the literal 1.6 is exactly 8/5) |
| (d) | 2 log₂μ + 8 ≤ μ | `2·logb 2 μ + 8 ≤ μ` |
| (e) | λ^{36} ≥ 2^{240}(Aμ)^{46A}, λ = 2^μ | `2^240·(A·μ)^(46·A) ≤ (2^μ)^36` |

- **`Gamma1core D`** = `2 < D ∧ ∀ μ, logb 2 (logb 2 D) ≤ μ → Gamma1Items μ`. This is the Γ1 text without (f), exactly as TRIAGE §2.4 prescribes; (f) goes to `Gamma1f` / COLTable.
- **`Gamma2a D`** = `2^117 ≤ D`.
- **Eventuality** (s1:tabOrder) is realized as the manuscript defines it: a condition on the ray, upward closed (`Gamma1core.mono`).
- **Transfer lemmas** requested by blueprint s2b are present: `items_loglog` (μ = log log d for d ≥ D), `items_logb` (μ = log D) and `two_pow_256_le_logb`.
- **Satisfiability.** The spot check at μ = 2^20 passes. Every item is eventually true in μ (rpow dominates the polylog terms), so `Gamma1core D` holds for large D. The formal proof belongs to s7:lemGammaSat.

## Issues

### Minor
- **M1 (non-vacuity test of Γ).**
  - Problem: EGTest has only negative Γ1 tests (`¬Gamma1core 3`, `¬Gamma1Items 0`). Every s2–s7 Spec assumes `Gamma1core`, so an encoding slip that makes it unsatisfiable would make them all vacuous.
  - Fix: add the positive spot check `Gamma1Items (2^20)` (the reviewer's scratch proof is about 25 lines). Ideally also add a Lib lemma `∀ᶠ μ in atTop, Gamma1Items μ` (hence `∃ D, Gamma1core D`) early, before the Specs that assume it are locked, instead of waiting for s7:lemGammaSat.
- **M2 (Log API gap).** `logStar_le_one_add_log` (for z ≥ 4: log* z ≤ 2 + log log z) and the growth fact `log* = o(log log)` are listed in TRIAGE §2.3 but not provided. They are proof-side, so this does not block the lock; schedule them with P-3.
- **M3 (TRIAGE/blueprint sync).** `IsWellExpanding` now lives in `Defs/Graph.lean`. Update TRIAGE §2.11 and §3 item 11 and blueprint_s3a, so that `Defs/Link/Star.lean` does not define a second copy.
- **M4 (re-lock).**
  - File SHA entries of `EG/Defs/Graph.lean` and `EG/Defs/Objects.lean` change. The reviewer checked that the own-hashes of the 52 locked constants in Graph/Objects/Walk/Expander/Fnum are unchanged; the integrator must still re-lock these files.
  - Also run a full `lake build EG`: the new `Mathlib.Data.Real.Basic` import in Graph.lean reaches every importer, even though no locked hash moved.
- **M5 (Components, Lib).** JS-LC Step 3 compares components of R_Y ⊆ Bead_{Y,l}: "every component of R_Y lies inside a component of Bead and has at most as many edges". The two component types are different (they depend on E).
  - Add Lib lemmas: a map `edgeComps E → edgeComps E'` for `E ⊆ E'`, and `(compEdges E C).card ≤ (compEdges E' (map C)).card`.
  - Also add a lemma that `IsPendant`/`IsNonBridge` "of that component" are equivalent to the definitions (currently argued only in the docstring).
  - This is Lib work, not a Defs change.
- **M6 (Components/PathDecomp, loops).** Behaviour on loopy E is documented but not in CONVENTIONS.
  - A loop is a "non-bridge", forms a one-edge (odd) component, and is counted by `IsPendant`'s `degE`.
  - F with a loop has no path decomposition.

  Add one CONVENTIONS line: "`edgeComps`/`IsNonBridge`/`IsPendant`/`IsPathDecomp`: loopless edge sets only (as for `fnum`)".

### Cosmetic
- **C1.** `EG/Spec/Found/EG0.lean:27` docstring still says `D.countP EG.Obj.isEdge` "of `EG/Lib/Found/Fnum.lean`". It is stale, and it sits in a locked Spec file, so fix it only at the next approved re-lock.
- **C2.** Constant names. TRIAGE §2.4 writes `ε`, `σ`; blueprints s1/s2a write `EG.CpC`, `EG.AexpC`. The implemented names `epsC`, `sigmaC`, `Cp`, `Aexp` should be recorded in CONVENTIONS/TRIAGE §2.12, so later Spec authors don't reference the blueprint names.
- **C3.** `IsPathCycleDecomp` was added beyond the task list. It is correct (see §4) and cheap; keep it, and record in blueprint s1 (citThm21) that the Lovász hypothesis uses it.
