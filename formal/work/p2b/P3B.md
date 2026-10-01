# P2b probe unit P3B (probe P-3, part 2), stage 1: statements

Chain: ORIGIN^τ (a), (b) (graft lemmas) → CONC (i)–(iii) → CONC-L (i)–(iv), including the shared
τ- and d\*-sums and the tower facts (s6:eqTowerHalf), (s6:eqTowerEnd) (TRIAGE §4 row P-3, second
half). Refutation target to hit explicitly (TRIAGE §4): **the CONC-L (iv) per-ancestor bound**.
Manuscript: `proofs/manuscript/s2.tex`, `s6.tex` v6.1 (a CANDIDATE proof, AI-reviewed only).
Blueprints: `work/p2/blueprint_s2b.md` (`s2:propOrigin`, `s2:propOV`, `s2:lemLacunary`,
`s2:lemTower`), `work/p2/blueprint_s6a.md` (`s6:thmCONC`, tower facts), `work/p2/blueprint_s6b.md`
(`s6:thmCONCL`). Data model: `work/p2d/hb.md`, `work/p2d/design.md`. Part 1: `work/p2b/P3A.md`.

## Status (stage 1)

- Every file compiles: `lake build` of all new modules below; `LEAN_NUM_THREADS=2
  scripts/check.sh EGTest/ProbeP3B.lean 1200`: rc=0, 0 errors, 0 sorry-warnings. A scratch file
  importing all new modules together with `EG.Proof.HB.{TowerC,GC,ThinCut,EL}`,
  `EG.Lib.{Chain.Design,HB.Run}` compiles (no name clashes).
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`scripts/Axioms.lean --prefix EG` on `EG.Proof.Chain.ConcTower`,
  `EG.Proof.HB.{TowerA,OVRunK,LacunaryGeom}`): 465 constants, 0 violations; `sorryAx` only in the
  four new declared-input stubs `EG.towerA`, `EG.ovK1`, `EG.ovK3`, `EG.lacunaryGeom`.
- Proved already (trivial): `EG.logStarFacts : LogStarFactsStatement` (from `EG.Lib.Found.Log`).
- Everything else is stage 2. No proof file of a probe node contains `sorry`.
- **No math finding of class T1–T3.** The refutation target (CONC-L (iv) per-ancestor bound) was
  re-derived against the TeX and the locked Defs and survives; it is stated in a strengthened form
  (every ancestor, every round `l`, no hypothesis on `D_*`). Two T0 notes (below).

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Probe/P3B/Origin.lean` (**new Defs**) | `EG.Defs.Probe.P3B.Origin` | `EG.HB.Run.OriginBeta`, `EG.HB.Run.OriginAlpha` (edge types (β), (α) of ORIGIN^τ) |
| `EG/Defs/Probe/P3B/TowerFns.lean` (**new Defs**) | `EG.Defs.Probe.P3B.TowerFns` | `EG.Chain.towA`, `towB`, `towC` (the functions `𝖺`, `𝖻`, `𝖼` of s6) |
| `EG/Spec/HB/Origin.lean` | `EG.Spec.HB.Origin` | `OriginTypesStatement` (a), `OriginThinStatement` (b), `OriginGuestCapStatement` (final paragraph) |
| `EG/Spec/Chain/ConcTower.lean` | `EG.Spec.Chain.ConcTower` | `LogStarFactsStatement`, `KStarStatement`, `TowerHalfStatement` (s6:eqTowerHalf), `TowerEndStatement` (s6:eqTowerEnd) |
| `EG/Spec/Chain/CONC.lean` | `EG.Spec.Chain.CONC` | `ConcIStatement`, `ConcIIStatement`, `ConcIIIStatement`, `ConcTauSumStatement`, `ConcDStarSumStatement` |
| `EG/Spec/Chain/CONCL.lean` | `EG.Spec.Chain.CONCL` | `ConcLIStatement`, `ConcLIIStatement`, `ConcLIIIStatement`, `ConcLAlphaStatement`, `ConcLPerAncestorStatement`, `ConcLGCSumStatement`, `ConcLSumStatement`, `EpsCONCTendstoStatement` |
| `EG/Spec/HB/TowerA.lean` | `EG.Spec.HB.TowerA` | `TowerAStatement` (declared input) |
| `EG/Spec/HB/OVRunK.lean` | `EG.Spec.HB.OVRunK` | `OVK1Statement`, `OVK3Statement` (declared inputs) |
| `EG/Spec/HB/LacunaryGeom.lean` | `EG.Spec.HB.LacunaryGeom` | `LacunaryGeomStatement` (declared input) |
| `EG/Proof/HB/TowerA.lean` | `EG.Proof.HB.TowerA` | stub `EG.towerA` (`sorry`, DECLARED INPUT) |
| `EG/Proof/HB/OVRunK.lean` | `EG.Proof.HB.OVRunK` | stubs `EG.ovK1`, `EG.ovK3` (`sorry`, DECLARED INPUT) |
| `EG/Proof/HB/LacunaryGeom.lean` | `EG.Proof.HB.LacunaryGeom` | stub `EG.lacunaryGeom` (`sorry`, DECLARED INPUT) |
| `EG/Proof/Chain/ConcTower.lean` | `EG.Proof.Chain.ConcTower` | `EG.logStarFacts` (proved) |
| `EGTest/ProbeP3B.lean` | `EGTest.ProbeP3B` | non-vacuity checks, parse checks |

Statements are in namespace `EG.Spec`, proofs in namespace `EG`. Every run statement quantifies
`∀ (V : Type u) [DecidableEq V]`.

Root imports for the orchestrator to add (I did not edit `EG.lean` / `EGTest.lean`):
- to `EG`: `EG.Defs.Probe.P3B.{Origin,TowerFns}`, `EG.Spec.HB.{Origin,TowerA,OVRunK,LacunaryGeom}`,
  `EG.Spec.Chain.{ConcTower,CONC,CONCL}`, `EG.Proof.HB.{TowerA,OVRunK,LacunaryGeom}`,
  `EG.Proof.Chain.ConcTower`;
- to `EGTest`: `EGTest.ProbeP3B`.

## Nodes: label → Lean names

| Label | Role | Statement(s) | Proof name(s) (stage 2 unless marked) |
|---|---|---|---|
| s2:propOrigin (a) | probe | `OriginTypesStatement` | `EG.originTypes` |
| s2:propOrigin (b) | probe | `OriginThinStatement` | `EG.originThin` |
| s2:propOrigin (final paragraph) | probe (cheap; from lemGC (ii)) | `OriginGuestCapStatement` | `EG.originGuestCap` |
| s2:propOrigin (c) | pointer, no new Spec (blueprint OR-C-POINTER) | = (K3) second clause, `OVK3Statement` | declared input `EG.ovK3` |
| s6 `log*` facts (text before s6:thmCONC) | probe | `LogStarFactsStatement`, `KStarStatement` | `EG.logStarFacts` (**done**), `EG.kStar` |
| s6:eqTowerHalf | probe | `TowerHalfStatement` | `EG.towerHalf` |
| s6:eqTowerEnd | probe | `TowerEndStatement` | `EG.towerEnd` |
| s6:thmCONC (i), (ii), (iii) | probe | `ConcIStatement`, `ConcIIStatement`, `ConcIIIStatement` | `EG.concI`, `EG.concII`, `EG.concIII` |
| s6:thmCONC (iv) | meta (no statement; automatic from `∀ δ`) | — | — |
| s6:thmCONC proof of (iii) / s6:thmCONCL proof of (iv): shared τ-sum, d\*-sum | probe | `ConcTauSumStatement`, `ConcDStarSumStatement` | `EG.concTauSum`, `EG.concDStarSum` |
| s6:thmCONCL (i), (ii), (iii) | probe | `ConcLIStatement`, `ConcLIIStatement`, `ConcLIIIStatement` | `EG.concLI`, `EG.concLII`, `EG.concLIII` |
| s6:thmCONCL (iv) `α < θ^GC` | probe | `ConcLAlphaStatement` | `EG.concLAlpha` |
| s6:thmCONCL (iv) per-ancestor bound (**refutation target**) | probe | `ConcLPerAncestorStatement` | `EG.concLPerAncestor` |
| s6:thmCONCL proof of (iv), θ^GC-terms | probe | `ConcLGCSumStatement` | `EG.concLGCSum` |
| s6:thmCONCL (iv) sum | probe | `ConcLSumStatement` | `EG.concLSum` |
| s6:thmCONCL (iv) `ε_CONC → 0` | probe | `EpsCONCTendstoStatement` | `EG.epsCONC_tendsto` |
| s2:lemTower (a) | **declared input** | `TowerAStatement` | stub `EG.towerA` |
| s2:lemTower (c) | **declared input** (existing, P3A) | `TowerCStatement` (`EG/Spec/HB/TowerC.lean`) | stub `EG.towerC` (P3A) |
| s2:propOV (K1), (K3) | **declared input** | `OVK1Statement`, `OVK3Statement` | stubs `EG.ovK1`, `EG.ovK3` |
| s2:lemLacunary (i) | **declared input** | `LacunaryGeomStatement` | stub `EG.lacunaryGeom` |

Used and already proved by P3A (not inputs): `EG.gc` (lemGC (ii), (iii)), `EG.thinCut`
(lemThinCut), `EG.sepI`/`EG.sepII` (lemSEP), `EG.edgeLaminarity` (lemEL; not needed, see below).
The graft lemmas the stage-2 proof of ORIGIN needs are mostly in `EG/Lib/HB/SplitTree.lean` and
`EG/Lib/HB/Run.lean` already (`deleted_twoLevel`, `tauRun_dup_subset_DupStar`,
`existsUnique_piece_of_notMem_DupStar`, `exists_tauRun_leaf_of_mem_prePartAddrs`,
`X0_append_of_mem_bigPieceAddrs`, `pieceOf_mem_bigPieceAddrs`, `Valid.isTauRun`,
`Valid.wf_twoLevel`, `graph_edges_subset_of_le`); blueprint OR-GRAFT-DUP items (1)–(4) are covered.

## Declared inputs, with justification

1. **[s2:lemTower] (a) `TowerAStatement`**, stub `EG.towerA` (new, `EG/Spec/HB/TowerA.lean`).
   - Used by: CONC (iii) and the two shared sums ("`R - r ≤ 2 log* d_r + 2`", "`R-r-1 ≤ 2 log* d_r + 1`"),
     the θ^GC-sum, and (s6:eqTowerHalf) ("`x ≥ d_{r+1}^{1/A} = 2^{y/A}` by Lemma [s2:lemTower](a)").
   - Not a node of probe P-3: its proof needs [s2:propDegRec], [s2:propStructure] (iii) and a `log*`
     induction (blueprint s2b, "(a) ~150 lines"). Owner: s2 tower unit. The full Tower Spec must
     import this file.
   - All of (a) is stated (not only the used clauses), so the Tower unit can import it unchanged.
2. **[s2:lemTower] (c) `TowerCStatement`** (existing stub `EG.towerC` of P3A).
   - Used by: the τ-sum ("`τ_r/P_r ≤ 2^{σ+11}/λ_r`").
3. **[s2:propOV] (K1), (K3) `OVK1Statement`, `OVK3Statement`**, stubs `EG.ovK1`, `EG.ovK3` (new,
   `EG/Spec/HB/OVRunK.lean`).
   - Used by: τ-sum ("at most `1.37 n/P_r` ancestors of round `r`"), θ^GC-sum (`Σ|Z^0| ≤ 1.37n`,
     `#pre-parts ≤ 1.37n/P_r`), d\*-sum (`Σ_Y |Y^0 ∩ Dup*_r| ≤ 16εn/log P_r`); ORIGIN (c) is (K3).
   - Not a node of probe P-3: the proof is the composite-tree application of Lemma OV at
     `c = 1.6` (needs lemCap (ii) for every τ-run) and the LCA argument (blueprint s2b, ~550
     lines). Owner: s2 overlap unit. The full propOV Spec must import this file.
   - Hypothesis `Gamma2a Dstar` (blueprint OV-IMPLICIT-DSTAR). (K2), (F11) and the leaf masses
     are not stated (not used by P-3).
4. **[s2:lemLacunary] (i) `LacunaryGeomStatement`**, stub `EG.lacunaryGeom` (new,
   `EG/Spec/HB/LacunaryGeom.lean`).
   - Used by: every tower sum ("By (s6:eqTowerHalf) and Lemma [s2:lemLacunary](i)").
   - Elementary (induction `X_r ≤ 2^{-(R-r)} X_R`); owner s2 lacunary unit. **P3B can discharge it
     in stage 2 (~40 lines) if the orchestrator assigns it** (open question 1).

Not declared: [s2:lemEL] (cited by CONC-L (i) for "`h ∈ Y`"). The stage-2 proof uses the
exclusivity of ORIGIN (a) instead (an edge `hu` with `h ∈ Y = Y^0 \ S_Y` is neither (β) (`h ∈ Y^0`)
nor (α) (`h ∉ S_Y`)); `EG.edgeLaminarity` is proved anyway (P3A). [s2:lemCap] (ii), cited
parenthetically in the proof of ORIGIN (a), is not needed (blueprint OR-THINCUT-NO-GAMMA:
`s_r < τ_r` holds for every `d`). [s2:propStructure] (iii) (`E(G_l) ⊆ E(G_{r+1})`) is the Lib lemma
`Run.graph_edges_subset_of_le`.

## Definitions used

- Locked: `EG/Defs/HB/{SplitTree,Round,Run}.lean` (`Run.Valid`, `R`, `graph`, `graph'`, `d`,
  `lam`, `P`, `tau`, `thetaGC`, `pieceAddrs`, `piece`, `pieceOf`, `tauRun`, `twoLevel`,
  `prePartAddrs`, `Z0`, `X0`, `DupStar`, `guests`, `isL1`, `isLight`, `Std`, `stdParts`,
  `lightParts`, `ancestors`, `nuAnc`; `STree.deleted`, `leafAddrs`);
  `EG/Defs/Chain/Design.lean` (`Designation`, `IsDesignation`, `mY`, `dStar`, `alphaY`);
  `EG/Defs/Chain/Constants.lean` (`epsCONC`); `EG/Defs/Log.lean` (`logStar`, `tower`);
  `EG/Defs/Constants.lean` (`epsC`, `sigmaC`, `Cp`, `Aexp`); `EG/Defs/Gamma/Core.lean`
  (`Gamma1core`, `Gamma2a`); `EG.FGraph.eBetween`.
- **New Defs files** (to be reviewed):
  - `EG/Defs/Probe/P3B/Origin.lean`: `Run.OriginBeta run G r a u x := x ∉ Y^0 ∧ s(u,x) ∈
    deleted(τ-run of run.pieceOf r a, rooted at its piece graph)`;
    `Run.OriginAlpha run G r a u x := isLight ∧ x ∈ S_Y ∧ s(u,x) ∈ E(X^0_Y)` (blueprint s2b
    `TypeBeta`/`TypeAlpha`, OR-TYPE-DEF: deletion by the τ-run of the piece, not "some node of the
    two-level recursion").
  - `EG/Defs/Probe/P3B/TowerFns.lean`: `towA d := (2 log* d + 2)/log d`,
    `towB d := (2 log* d + 1)/log log d`, `towC d := (2 log* d + 1)/(log d)^{1/2}` (rpow `1/2`,
    as in `epsCONC`). Named `tow*` because `EG.towerC` is the lemTower (c) stub.

Checked while writing (no existing definition looks wrong for this chain):
- `dStar` reads `Dup*_{r(Y)}` (`run.DupStar G Y.1`), `alphaY` reads `V(Y) \ Dup*_r` with
  `V(Y) = run.ancVerts` and `Z_u` as `∃ a ∈ Std_l`, `mY` is `G.verts.sup classDeg` — all literal.
- `epsCONC` is the displayed formula (parse check in `EGTest.ProbeP3B`).
- `thetaGC` is a natural-number ceiling with `Real.rpow` `λ^{-1/2}` (junk `0` when `λ_r = 0`; see
  T0 note T0-CONCL-ALPHA).

## Back-translation of every statement (plain mathematics next to the TeX)

Notation: a valid run of `G` (`n = |V(G)|`), rounds `1 ≤ r ≤ R`, pre-parts are addresses `a`,
`Y^0 = Z0 r a`, `S_Y` guests, `X^0_Y`, `Dup*_r`, `τ_r ∈ ℕ` (`≥ 1` for every `d`), `k_* = log* D_*`,
`log = log₂`. "Γ" = `Gamma1core D_*`.

### ORIGIN^τ (s2:propOrigin)

**`OriginTypesStatement`** — TeX (a): "`u` lies in a unique `s = 0` piece `𝒫` and in a unique
leaf of the two-level recursion, namely `Y` (so `Y^0 ⊆ V(𝒫)`). Every edge `ux` of `G_{r+1}` is of
exactly one of the following two types: (β) … (α) … A standalone `Y` (GC-parts included) has no
edges of type (α). Since `E(G_l) ⊆ E(G_{r+1})` for `l > r`, the same classification applies to the
edges `ux` of `G_l`."
- Lean: for a valid run, `r ∈ [1,R]`, a round-`r` pre-part `a`, and `u ∈ Y^0 \ Dup*_r`:
  - the piece `𝒫 = pieceOf r a` is an `s = 0` piece, and a piece `q` contains `u` iff `q = 𝒫`;
  - a leaf `b` of the two-level recursion contains `u` iff `b = a`;
  - `Y^0 ⊆ V(𝒫)`;
  - for every `l > r` and every `x` with `ux ∈ E(G_l)`: either (β: `x ∉ Y^0` and `ux` is in the
    deleted set of the τ-run of `𝒫`) and `x ∈ V(𝒫)` and not (α), or (α: `Y` light, `x ∈ S_Y`,
    `ux ∈ E(X^0_Y)`) and not (β) and `ux` is not in the deleted set of the τ-run of `𝒫` (the
    "not deleted" of the (α) parenthetical; added in fix round 1, review C2);
  - if `Y` is standalone, no such edge is of type (α) (definitional: (α) contains "`Y` light";
    fix round 1, review C1).
- No hypothesis on `D_*`.

**`OriginThinStatement`** — TeX (b): "For every vertex `h` and every round `l > r`,
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l) is of type (β)} ≤ τ_r − 1`."
- Lean: same context (no `u`); for every `h ∈ V` and `l > r`, the number of `u ∈ Y^0 \ Dup*_r`
  with `hu ∈ E(G_l)` and `hu` of type (β) (core end `u`, other end `h`) is at most `τ_r − 1`
  (natural-number subtraction, exact since `τ_r ≥ 1`).

**`OriginGuestCapStatement`** — TeX (final paragraph): "a guest `x` of a light `Y` is the guest end
of fewer than `θ^GC_r(Y^0)` edges of type (α) (Lemma [s2:lemGC](ii))".
- Lean: for a light round-`r` pre-part, a guest `x ∈ S_Y` and `l > r`, fewer than `θ^GC_r(Y^0)`
  vertices `u ∈ Y^0 \ Dup*_r` have `ux ∈ E(G_l)` of type (α).
- The other two clauses of the paragraph are the setting of (a) (`u ∉ Dup*_r`) and its
  exhaustiveness ("no third type").

### The `log*` facts and the tower facts (s6.tex, before s6:thmCONC)

**`LogStarFactsStatement`** — TeX: "For `x ≥ 1` and an integer `k ≥ 0`, `log* x ≤ k` iff
`x ≤ 𝖳_k`. For `x > 1`, `log* x = 1 + log*(log x)`. And `log* x ≤ 1 + log x` for all `x ≥ 1`."
- Lean: exactly these three facts (`𝖳_k = EG.tower k`). **Proved** (`EG.logStarFacts`).

**`KStarStatement`** — TeX: "By Γ1(a) at `μ = log log D_*`, `log log D_* ≥ 2^8 > 16`, so
`D_* > 2^{65536} = 𝖳_5` and `k_* ≥ 6`."
- Lean: under Γ: `log log D_* ≥ 2^8`, `log log D_* > 16`, `𝖳_5 < D_*`, `6 ≤ log* D_*`.

**`TowerHalfStatement`** — TeX (s6:eqTowerHalf): "for every valid run and every `r < R`,
`𝖺(d_r) ≤ ½𝖺(d_{r+1})`, `𝖻(d_r) ≤ ½𝖻(d_{r+1})`, `𝖼(d_r) ≤ ½𝖼(d_{r+1})`."
- Lean: under Γ, for a valid run and `1 ≤ r < R`, the three halving inequalities at `d_r`,
  `d_{r+1}`.

**`TowerEndStatement`** — TeX (s6:eqTowerEnd): "for every `d ≥ D_*`, `𝖺(d) ≤ (2k_*+4)/log D_*`,
`𝖻(d) ≤ (2k_*+3)/log log D_*`, `𝖼(d) ≤ (2k_*+3)/(log D_*)^{1/2}`."
- Lean: under Γ, for every real `d ≥ D_*`, the three bounds.

### Theorem CONC (s6:thmCONC)

**`ConcIStatement`** — TeX (i): "for every `Y ∈ Std_r`, every `l ≥ r+1` and every vertex `h`:
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1`."
- Lean: for a valid run, every `r`, every `a ∈ Std_r`, every `l ≥ r + 1`, every `h`:
  `#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1`. No `δ` (the statement does not mention it), no Γ.

**`ConcIIStatement`** — TeX (ii): "`m_{Y,l} ≤ τ_r − 1 + d^*_{Y,l}` for every `Y ∈ Std_r` and every
`l`."
- Lean: for a valid run and every designation `δ`, every `a ∈ Std_r` and every `l ∈ ℕ`:
  `m_{(r,a),l} ≤ τ_r − 1 + d^*_{(r,a),l}`. No Γ.

**`ConcIIIStatement`** — TeX (iii): "`Σ_{(Y,l): Y standalone} m_{Y,l} ≤ 2^{σ+14} n log* D_*/log D_*
+ 100 ε n log* D_*/(C' log log D_*)`."
- Lean: under Γ, for a valid run and every designation:
  `Σ_{l=1}^{R} Σ_{Y standalone ancestor} m_{Y,l} ≤ 2^{σ+14} n k_*/log D_* + 100 ε n k_*/(C' log log D_*)`.

**`ConcTauSumStatement`** — TeX (proof of CONC (iii), τ-term, and of CONC-L (iv), "applies verbatim"
to all ancestors): "… `≤ 2^{σ+14} n log* D_*/log D_*`".
- Lean: under Γ, for a valid run: `Σ_{Y ancestor} Σ_{l = r(Y)+2}^{R} (τ_{r(Y)} − 1) ≤
  2^{σ+14} n k_*/log D_*`.

**`ConcDStarSumStatement`** — TeX (d\*-term): "`Σ_{(Y,l)} d^*_{Y,l} ≤ … ≤ 80 ε n log* D_*/(C' log log D_*)`";
CONC-L: "it applies to all ancestors together".
- Lean: under Γ, for a valid run and every designation: `Σ_{l=1}^{R} Σ_{Y ancestor} d^*_{Y,l} ≤
  80 ε n k_*/(C' log log D_*)`.

### Theorem CONC-L (s6:thmCONCL)

Context of (i)–(iii): a valid run, a light pre-part `a` of round `r` (the light part
`Y = Y^0 \ S_Y`), `l ≥ r + 1`.

**`ConcLIStatement`** — TeX (i): "If `h ∉ S_Y`: `#{u ∈ Y \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1`, and
there are no such `u` if `h ∈ Y`."
- Lean: for `h ∉ S_Y`: `#{u ∈ (Y^0 \ S_Y) \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1`; and if moreover
  `h ∈ Y^0 \ S_Y`, that set is empty. No Γ.

**`ConcLIIStatement`** — TeX (ii): "If `h ∈ S_Y`: every such `hu` is an edge of `X^0_Y`, and their
number is at most `e_{X^0_Y}(h, Y)`."
- Lean: for `h ∈ S_Y`: every `u ∈ (Y^0 \ S_Y) \ Dup*_r` with `hu ∈ E(G_l)` has `hu ∈ E(X^0_Y)`, and
  the number of such `u` is at most `e_{X^0_Y}({h}, Y^0 \ S_Y)`. No Γ.

**`ConcLIIIStatement`** — TeX (iii): "For every designation, `m_{Y,l} ≤ max(τ_r − 1, α_{Y,l}) +
d^*_{Y,l}`."
- Lean: for every designation, `m_{(r,a),l} ≤ max(τ_r − 1, α_{(r,a),l}) + d^*_{(r,a),l}`. No Γ.

**`ConcLAlphaStatement`** — TeX (iv): "`α_{Y,l} < θ^GC_r(Y^0)`."
- Lean: under Γ, for every designation, `α_{(r,a),l} < θ^GC_r(Y^0)`.

**`ConcLPerAncestorStatement`** (refutation target) — TeX (proof of (iv)): "`m_{Y,l} ≤ (τ_r−1) +
(θ^GC_r(Y^0)−1) + d^*_{Y,l}` (`Y` light), `m_{Y,l} ≤ τ_r−1+d^*_{Y,l}` (`Y` standalone), the latter
by Theorem [s6:thmCONC](ii); GC-parts are standalone".
- Lean: for a valid run, every designation, every ancestor `Y = (r,a)` and every `l ∈ ℕ`: if `Y` is
  light, `m_{Y,l} ≤ (τ_r − 1) + (θ^GC_r(Y^0) − 1) + d^*_{Y,l}`; if not, `m_{Y,l} ≤ τ_r − 1 +
  d^*_{Y,l}`. No Γ (see below).

**`ConcLGCSumStatement`** — TeX (proof of (iv), θ^GC-terms): "`Σ_{(Y,l), Y light} θ^GC_r(Y^0) ≤ … ≤
4n(2 log* D_* + 2)/(log D_*)^{1/2}`".
- Lean: under Γ, for a valid run: `Σ_{Y light part} Σ_{l = r(Y)+2}^{R} θ^GC_{r(Y)}(Y^0) ≤
  4n(2k_* + 2)/(log D_*)^{1/2}`.

**`ConcLSumStatement`** — TeX (iv): "For every valid run and every designation, summing over *all*
ancestors (light and standalone, GC-parts included), `Σ_{(Y,l)} m_{Y,l} ≤ ε_CONC(D_*) n`".
- Lean: under Γ, for a valid run and every designation:
  `Σ_{l=1}^{R} Σ_{Y ancestor} m_{Y,l} ≤ ε_CONC(D_*) · n` (`epsCONC`, the displayed formula).

**`EpsCONCTendstoStatement`** — TeX (iv): "`ε_CONC(D_*) → 0` as `D_* → ∞`."
- Lean: `Tendsto epsCONC atTop (𝓝 0)`. ("depends only on `D_*`" is definitional.)

### Declared inputs

**`TowerAStatement`** — TeX [s2:lemTower] (a): "`λ_r ≥ d_{r+1}^{1/A}` for `r ≤ R`; `d_{r+2} ≤ λ_r`
for `r ≤ R−1`; `R − r ≤ 2 log* d_r − 1`, in particular `R − r ≤ 2 log* d_r + 2` (`r ≤ R`); and
`λ_r ≥ λ_{l−2}` whenever `r ≤ l−2 ≤ R`."
- Lean: under Γ, for a valid run with `d_1 ≥ D_*`: the five clauses, with `r ∈ [1,R]`
  (resp. `1 ≤ r`, `r + 1 ≤ R`; resp. `1 ≤ r`, `r + 2 ≤ l ≤ R + 2`), the two `R − r` bounds in `ℤ`.

**`OVK1Statement`** — TeX (K1): "`Σ|Z^0| ≤ 1.37 n` …; `|Std_r| ≤ 1.37 n/P_r`; the number of ancestors
of round `r` is at most `1.37 n/P_r` …; hence … `ν_l ≤ 1.37 n Σ_{r ≤ l−2} P_r^{−1}`."
- Lean: under `D_* ≥ 2^{117}`, for a valid run: for `r ∈ [1,R]` the three bounds (ancestors of
  round `r` = `{Y ∈ ancestors : Y.1 = r}`); for every `l`, `ν_l ≤ 1.37 n Σ_{r ∈ [1,R], r+2 ≤ l} 1/P_r`.

**`OVK3Statement`** — TeX (K3): "the total size `Σ|Z^0|` of the round-`r` pre-parts failing (L1) is
at most `30.4 ε n/log P_r`, and `Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n/log P_r`".
- Lean: under `D_* ≥ 2^{117}`, for a valid run and `r ∈ [1,R]`: the two bounds.

**`LacunaryGeomStatement`** — TeX [s2:lemLacunary] (i): "If `X_1,…,X_R ≥ 0` and `X_r ≤ X_{r+1}/2`
for all `r < R`, then `Σ_{r≤R} X_r ≤ 2X_R` and `Σ_{r≤R}(R−r+1)X_r ≤ 4X_R`."
- Lean: for `R ≥ 1`, a real sequence nonnegative on `[1,R]` with the halving condition on
  `[1,R)`: the two bounds.

## Deviations from the literal TeX (for the statement reviewer)

1. **Hypotheses dropped (stronger statements, all re-derived as true):**
   - ORIGIN (a), (b), final paragraph; CONC (i), (ii); CONC-L (i)–(iii); the per-ancestor bound:
     no hypothesis on `D_*` (the manuscript's standing assumption Γ is not used by their proofs;
     blueprint OR-THINCUT-NO-GAMMA).
   - CONC (iii), the three sums, CONC-L (iv), (s6:eqTowerHalf): no `d_1 ≥ D_*` (implied by `Valid`
     when `R ≥ 1`; for `R = 0` the sums are empty, and `r < R` forces `R ≥ 2`); no `n ≥ N_0`
     (TRIAGE §2.6).
   - The per-ancestor bound: every ancestor and every round `l` (not only `r(Y) + 2 ≤ l ≤ R`), and
     no Γ: `α ≤ θ^GC − 1` holds for every valid run (each guest has fewer than `θ^GC` core edges by
     [s2:lemGC] (ii); `α = 0` if `S_Y = ∅`), and `m_{Y,l} = 0` outside the class range.
   - `ConcIStatement`: no designation (the text quantifies it, but (i) does not read it).
2. **Hypotheses added (standing assumption made explicit):** `Gamma1core Dstar` on KStar, the tower
   facts, CONC (iii), the three sums, `ConcLAlphaStatement`, `ConcLSumStatement` (blueprint
   CONC-IMPLICIT-HYPS, CONCL-HYPS); `Gamma2a` on the (K1), (K3) inputs (OV-IMPLICIT-DSTAR).
3. **Sum index sets:** `Σ_{(Y,l)}` is `Σ_{l ∈ [1,R]} Σ_{Y}` over `run.stdParts` (CONC (iii)) or
   `run.ancestors` (CONC-L (iv), the d\*-sum) (design note `design.md`, "Notes for Spec
   authors"); the τ- and θ^GC-sums range over `r(Y) + 2 ≤ l ≤ R`, exactly the pairs with possibly
   `m_{Y,l} ≠ 0`, as in the TeX ("each `Y` occurs for at most `R − r − 1` values of `l`").
4. **Shared sums stated for all ancestors** (the form CONC-L (iv) uses); the standalone sums of
   the proof of CONC (iii) are sub-sums of nonnegative terms.
5. **Implicit conjuncts made explicit:** ORIGIN (a): `𝒫` is a piece, and `x ∈ V(𝒫)` in the (β)
   branch; "exactly one" as an exclusive disjunction; (a) for every `l > r`.
6. **ORIGIN (c)** is not restated (it is (K3), declared input `OVK3Statement`).
7. **CONC (iv)** is meta and has no statement (automatic from `∀ δ`).

## T0 notes (encoding; no manuscript change needed)

- **T0-CONCL-ALPHA.** `α_{Y,l} < θ^GC_r(Y^0)` can fail in Lean for a junk `D_*` (`θ^GC = 0` when
  `λ_r ≤ 0`, i.e. for every `d_r ≤ 1`, since Lean's `λ^{-1/2} = 0` for every `λ ≤ 0` (`Real.rpow_def_of_neg`, review 2 C4)): this gives `θ^GC = 0`, and a light
  part with `S_Y = ∅` would have `α = 0 ≮ 0`. (Not exhibited: no valid run with `d_r = 1` and a
  light part with `S_Y = ∅` was constructed; fix round 1, review C4.) Under the standing assumption (`D_* > 2`, so `λ_r > 1`, `P_r ≥ 1`, `θ^GC ≥ 1`) it is
  true. `ConcLAlphaStatement` carries `Gamma1core`. (The per-ancestor bound, which is what (iv)'s
  sum consumes, needs no Γ.)
- **T0-CONCL-EL.** CONC-L (i) cites Lemma EL for "no such `u` if `h ∈ Y`". ORIGIN (a) alone gives
  it (an edge `hu`, `h ∈ Y^0 \ S_Y`, is neither (β) nor (α)). EL is proved (P3A) either way.
- ORIGIN (a)'s parenthetical appeal to Lemma Cap (ii) and CONC-L's citations of SEP, thin cut are
  provenance only (blueprint deps_notes); the stage-2 proof uses `EG.thinCut` on the τ-run of the
  piece, which needs only `0 < τ_r` and `s_r < τ_r` (true for every `d`).

## Refutation target: the CONC-L (iv) per-ancestor bound

Re-derived line by line against s6.tex (proof of CONC-L (iii), (iv)) and the locked Defs
(`classDeg`, `mY`, `dStar`, `alphaY`):
- Fix a light `Y` of round `r`, `l`, `h`. By `IsDesignation`, a port `u` counted in `d_{Y,l}(h)`
  has `u ∈ V(Y) = Y^0 \ S_Y` and `r + 2 ≤ l`; the edge `hu ∈ E_l(Z) ⊆ E(G_l) ⊆ E(G_{r+1})`.
- `u ∈ Dup*_r`: distinct `u` (at fixed `h`, `u ↦ hu` is injective), all counted by `d^*_{Y,l}`.
- `u ∉ Dup*_r`: by ORIGIN (a) the edge is (β) (then `h ∉ Y^0`) or (α) (then `h ∈ S_Y`).
  - `h ∉ Y^0`: all such edges are (β); ORIGIN (b) (thin cut on the τ-run of the piece above `Y`,
    with `Y^0 \ Dup*_r ⊆ V(leaf) \ Dup(τ-run)`) bounds them by `τ_r − 1`.
  - `h ∈ Y`: impossible (neither type).
  - `h ∈ S_Y`: each such `u` is in the set defining `α_{Y,l}` at `x = h` (the edge lies in
    `E_l(Z_u)`), so at most `α_{Y,l}`; and each such edge is (α), hence in `E(X^0_Y)` between `h`
    and `Y^0 \ S_Y`, so `α_{Y,l} ≤ e_{X^0_Y}(h, Y) ≤ θ^GC − 1` by rule (GC) ([s2:lemGC] (ii),
    proved as `EG.gc`).
- Exactly one of the three cases holds for `h`, so `d_{Y,l}(h) ≤ max(τ_r − 1, α) + d^* ≤
  (τ_r − 1) + (θ^GC − 1) + d^*`; standalone `Y` (GC-parts included, `Y ∈ Std_r`): only the (β) case,
  `≤ τ_r − 1 + d^*` (CONC (ii)).
- Possible failure points checked: (1) a port `u ∈ Y` with `u ∈ S_Y`? No: `u ∉ D_r ⊇ S_Y` when
  `u ∉ Dup*_r`, and `V(Y)` excludes `S_Y` anyway; (2) edges of `G_l` at `u` that are neither in a
  leaf nor deleted? No: SEP (i) on the two-level recursion (every edge of `G'_r` is in exactly one
  leaf or deleted once), `E(G_l) ⊆ E(G'_r)`; (3) an edge deleted at a first-level node? No:
  `s = 0` splits delete nothing (`deleted_twoLevel`); (4) the thin-cut count uses `Dup` of the
  τ-run, not `Dup*_r`: `Dup(τ-run) ⊆ Dup*_r` (`tauRun_dup_subset_DupStar`), so the set
  `Y^0 \ Dup*_r` is contained in the thin-cut set; (5) `α` defined with `E_l(Z_u)` (not
  `E(G_l)`): only helps; (6) `θ^GC − 1` in `ℕ` when `θ^GC = 0`: then (GC) forces `S_Y = ∅`, so
  `α = 0` and the bound still holds.
- The summation of (iv) (τ-, d\*-, θ^GC-terms; `1.37·16/3 < 8`, `2k+4 ≤ 8k/3`, `2k+3 ≤ 2.5k` for
  `k ≥ 6`, `1.37 + 1.37/P_r·λ^{1/2} ≤ 1.38`, `2.76(2k+3) ≤ 4(2k+2)`) and (s6:eqTowerHalf/End)
  (including `2^{y/(2A)} ≥ 16y²`, `y ≥ 2Av(7+2v)`, `t(2t+6) ≤ 2^t`, `t(2t+5)² ≤ 2^t`) were
  re-derived; all correct. **No counterexample; verdict: the per-ancestor bound holds** (as a
  statement stronger than the TeX's). It remains a stage-2 proof obligation
  (`EG.concLPerAncestor`).

## Non-vacuity (`EGTest/ProbeP3B.lean`, compiles, 0 sorry)

- ORIGIN: `run1` (valid, `K3`, one round, pre-parts `{0},{1},{2}`), round `1`, pre-part `[false]`,
  `0 ∈ Y^0 \ Dup*_1` (`Dup*_1 = ∅` by `decide`).
- CONC (i)–(ii), CONC-L (i)–(iii), per-ancestor: every function is a designation of `run1`
  (`isDesignation_run1`), `[false]` is light, `(1,[false])` is an ancestor.
- Γ-statements: `Gamma1core D`, a valid run (no rounds, `E2`) and a designation are jointly
  satisfiable; `TowerEnd`/`KStar`: `Gamma1core D`, `D ≤ d`.
- `LacunaryGeom`: `X_r = 2^r`, `R = 3`.
- Parse checks: `towA/B/C`, `OriginBeta/Alpha`, `epsCONC`; value `𝖺(𝖳_2) = 3`.
- Not exercised: a valid run with a (β)-edge, a guest, or a class (`R ≥ 3`) — impossible at toy
  size (a τ-run split needs a non-`(ε, s_r)`-expander with `s_r ≥ 40^{100}`; a run with `R ≥ 3`
  under Γ needs `d_1 ≥ 2^{2^{256}}`). The conclusions are therefore checked only in degenerate
  form. The round-local non-idle τ-split of P3A (`NonIdleTau`) exercises thin cut, which (b)
  transports.

## Hazards for stage 2

- **H1 (sum re-indexing).** `Σ_{Y ∈ ancestors}` must be re-indexed as `Σ_{r ∈ [1,R]} Σ_{a ∈ prePartAddrs r}`
  (`ancestors = parts`, a `biUnion` of images; Lib lemma `sum_ancestors`), and
  `Σ_l Σ_Y` swapped. `stdParts`, `lightParts` are filters of `parts`.
- **H2 (tower real analysis, ~300 lines).** Monotonicity of `(2 log t + 6)/t`, `(7 + 2 log t)/t`,
  `(2 log t + 5)/t^{1/2}` on `t ≥ 4`; `2^{y/(2A)} ≥ 16y²` from `y ≥ 2^{14}Av³`, `v ≥ 2^8`; `log*`
  identities from `EG.Lib.Found.Log`. `EG.Lib.Found.LogMono` has `div_logb_pow_le_div_logb_pow`.
- **H3 (`ε_CONC → 0`).** Use `logStar_isLittleO_loglog` and `logStar_le_three_add_logloglog`;
  each of the three terms separately.
- **H4 (ℕ subtractions).** `τ_r ≥ 1` for every `d` (`M_r ≥ 2^{40}` ⇒ `Λ_r ≥ 40` ⇒ `s_r ≥ 1` ⇒
  `τ_r ≥ 128·1600`): to be proved in stage 2 (no such Lib lemma exists yet; ~25 lines: `2^{40} ≤ M` ⇒ `40 ≤ Λ` ⇒ `1 ≤ s` ⇒ `1 ≤ τ`); `θ^GC − 1` handled by the case `S_Y = ∅`.
- **H5 (thin cut transport, ORIGIN (b)).** `IsTauRun ε s_r τ_r 𝒫 ⇒ IsTauSplitTree ε τ_r 𝒫`
  needs `(s_r : ℝ) < τ_r` for every `d` (as H4). Leaf of the τ-run at `b` with `a = pieceOf a ++ b`
  (`exists_tauRun_leaf_of_mem_prePartAddrs`).
- **H6 (ORIGIN (a), (R5) analysis).** A non-deleted edge `ux ∈ E(X^0_Y)` of `G_{r+1}` would be
  assigned by `Round.assign` step (1) (standalone, or light with `x ∉ S_Y`); reuse the GC Lib
  (`EG/Lib/HB/GC.lean`) pattern.
- **H7 (d\*-sum injectivity).** Per `l`: `Σ_{Y} d^*_{Y,l} ≤ Σ_{r+2 ≤ l} Σ_a |Z^0 ∩ Dup*_r|` via
  `u ↦ (δ l u, u)` and `u ∈ V(Y(u)) ⊆ Y(u)^0` (`IsDesignation.mem_ancVerts`, `partVerts_subset_Z0`).
- **H8 (λ_r monotone, log P_r ≥ C' log λ_r).** `P_r = ⌈λ_r^{103}⌉ ≥ λ_r^{103}` with `λ_r ≥ 2^{256}`
  under Γ.

## Open questions for the orchestrator / reviewers

1. **Lacunary (i)**: accept it as a declared input, or assign it to P3B stage 2 (~40 lines)?
2. **ORIGIN (c)**: acceptable as a pointer to `OVK3Statement` (no separate statement)?
3. **Shared sums over all ancestors** (instead of two standalone/all variants): acceptable?
4. **`ConcLAlphaStatement` with `Gamma1core`** (T0-CONCL-ALPHA): acceptable, or state
   `S_Y ≠ ∅ → α < θ^GC` without Γ in addition?
5. **Ownership of the new input Specs** `TowerA`, `OVRunK`, `LacunaryGeom`: the future full
   Tower/propOV/Lacunary Specs must import them (their docstrings say so).

## Fix round 1 (review `work/p2b/P3B.review1.md`, verdict APPROVE; 1 minor, 4 cosmetic)

Each issue was re-checked before it was fixed.
- **M1 (minor; Γ-statements witnessed only with `R = 0`): fixed** (the suggested sign checks, done
  now instead of stage 2). `EGTest/ProbeP3B.lean`, new section "Sign checks of the right-hand
  sides under Γ1". Under `Gamma1core D` and `n > 0`, it proves that each right-hand side is `> 0`:
  - `ConcTauSum`: `2^{σ+14} n k/log D`;
  - `ConcDStarSum`: `80 ε n k/(C' loglog D)`;
  - `ConcIII`: the sum of the two terms;
  - `ConcLGCSum`: `4n(2k+2)/(log D)^{1/2}`;
  - `ConcLSum`: `epsCONC D > 0` (`epsCONC_pos`), hence `ε_CONC n > 0`;
  - for `d ≥ D`: `towA d`, `towB d`, `towC d > 0` (`TowerHalf`) and the three right-hand sides of
    `TowerEnd`.

  Helper `gamma_pos`: `log D > 0`, `loglog D > 0` and `log* D ≥ 1`. It uses `logStar_eq_zero_iff`.
  - `ConcLAlpha` has no closed-form right-hand side (`θ^GC` depends on the run), so it is not
    covered.
  - The fact that no run with `R ≥ 1` under Γ can be built is unchanged (it is intrinsic).
- **C1 (standalone ⇒ no (α) is definitional): fixed.** The remark is added to the docstring of
  `OriginTypesStatement` and to its module docstring ("holds by definition, since
  `Run.OriginAlpha` contains `run.isLight`; the TeX sentence is equally definitional"). Verified:
  `OriginAlpha := isLight ∧ …`.
- **C2 ((α) parenthetical "not deleted" not stated): fixed.** A conjunct is added to the (α) branch
  of `OriginTypesStatement`: `s(u,x) ∉ (run.tauRun r (run.pieceOf r a)).deleted (run.piece G r
  (run.pieceOf r a))`. The docstrings are updated, and so is the back-translation above.
  - This strengthens the statement, and it is true: `ux ∈ E(X^0_Y)`, and `X^0_Y` is the leaf graph
    of the grafted `τ`-run at the suffix address. By [s2:lemSEP](i) on that `τ`-run (a WF tree),
    an edge of a leaf is in no `F''_ν`.
  - "Not assigned at round `r`, and passes down" is the hypothesis `ux ∈ E(G_{r+1})` itself, so it
    is not restated.
  - Nothing downstream uses the new conjunct. The stage-2 proof of `EG.originTypes` needs SEP (i)
    on the `τ`-run of the piece, which is also used for (β).
- **C3 (label "(preamble)" on text before thmCONC): fixed.** `LogStarFactsStatement`,
  `KStarStatement` and `EG.logStarFacts` now read "[s6:thmCONC] (s6, text before s6:thmCONC, not
  part of the theorem …)".
- **C4 ("fails" asserted, not exhibited): fixed.** T0-CONCL-ALPHA above and the module docstring of
  `EG/Spec/Chain/CONCL.lean` now say "can fail (`θ^GC = 0` when `λ_r = 0`)", and state that no valid
  run with `d_r = 1` and a light part with `S_Y = ∅` was exhibited. `ConcLAlphaStatement` still
  carries `Gamma1core` (the standing assumption), as the reviewer agrees.

Checks after the fixes:
- `lake build` of `EG.Spec.HB.Origin`, `EG.Spec.Chain.{ConcTower,CONC,CONCL}` and
  `EG.Proof.Chain.ConcTower`: OK.
- `scripts/check.sh EGTest/ProbeP3B.lean`: 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.

## Round-2 cosmetics and stage-1 re-run (2026-09-30 ~00:30 UTC)

The workflow ran stage 1 again after round 2 (review `work/p2b/P3B.review2.md`, verdict APPROVE, 4
cosmetic items). The existing Specs, stubs and tests were **kept unchanged**. Rewriting approved
statements would force a new review cycle for no gain. What was re-checked against the current tree:
- `lake build` of all 13 P3B modules: OK. The only sorry warnings are the 4 declared-input stubs.
- `scripts/check.sh EGTest/ProbeP3B.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.

Review-2 cosmetic items:
- **C1: fixed.** H4 now says `τ_r ≥ 1` is still to be proved in stage 2. The Lib lemma
  `one_le_tauOf` does not exist.
- **C2: fixed.** The docstrings of `towA/towB/towC` in `EG/Defs/Probe/P3B/TowerFns.lean` now read
  "(s6, text before s6:thmCONC, not part of the theorem)". Only the docstrings changed; the
  definitions are the same.
- **C3: open (optional, stage 2).** A valid one-round run with a guest, to witness the hypotheses
  of `OriginGuestCapStatement` and `ConcLIIStatement`.
- **C4: fixed in this note** (T0-CONCL-ALPHA: `θ^GC = 0` for every `d_r ≤ 1`). The docstring of the
  locked Spec file `EG/Spec/Chain/CONCL.lean` still says "e.g. `d_r = 1`". That remains correct
  because it is an example, so it was not edited.

## Proof round 1 (stage 2)

Progress log (written incrementally).
- **Proved (0 sorry):** `EG.originTypes`, `EG.originThin`, `EG.originGuestCap`
  (`EG/Proof/HB/Origin.lean`); `EG.concI`, `EG.concII` (`EG/Proof/Chain/CONC.lean`);
  `EG.concLI`, `EG.concLII`, `EG.concLIII`, `EG.concLAlpha`, **`EG.concLPerAncestor`** (the
  refutation target; `EG/Proof/Chain/CONCL.lean`). No declared input is used by these.
  Notes: the thin cut is applied through `STree.IsTauRun.tauLabels` + `STree.thinCut_lt`, which
  needs only `τ_r > 0` (`HB.Run.one_le_tauOf`, every `d`); `s_r < τ_r` is not needed.
  `α ≤ θ^GC - 1` holds for every valid run (`Chain.alphaY_le_thetaGC_sub_one`); Γ1 is used only
  for `θ^GC ≥ 1` (`Chain.one_le_thetaGC`).
- **Proved (0 sorry):** `EG.kStar`, `EG.towerEnd`, `EG.towerHalf` (`EG/Proof/Chain/ConcTower.lean`;
  real analysis in the new Lib file `EG/Lib/Chain/TowerFacts.lean`: growth lemma `Chain.grow`
  replaces the monotonicity of `(2 log t + 6)/t` etc.; `half_core`, `end_core` are the manuscript's
  "middle inequalities"). `towerHalf` uses the declared input `EG.towerA` (first clause only).
- **Proved (0 sorry):** `EG.concTauSum`, `EG.concDStarSum`, `EG.concLGCSum`, `EG.concIII`,
  `EG.concLSum` (`EG/Proof/Chain/ConcSums.lean`: re-indexing `sum_ancestors`, `sum_Icc_swap`;
  `tower_sum_le` = (s6:eqTowerHalf) + Lacunary (i); per-round bounds via (K1)/(K3), lemTower (a),
  (c); `sum_thetaGC_le` (`Σ_a θ^GC ≤ 1.38 n λ_r^{-1/2}`); `mY_le_ite` packages the per-ancestor
  bound for the sums); `EG.epsCONC_tendsto` (`EG/Proof/Chain/EpsCONC.lean`, from the GAMMA Lib
  lemma `EG.Chain.tendsto_epsCONC` in `EG/Lib/Gamma/Eps.lean`).
- Declared inputs used by the sums: `EG.towerA`, `EG.towerC`, `EG.ovK1`, `EG.ovK3`,
  `EG.lacunaryGeom` (all stubs, as listed above). No other `sorry`.

### Proof round 1: final state (after container restart, 2026-09-30 ~02:05 UTC)

- **All probe nodes proved, 0 remaining.** `lake build EG.Proof.HB.Origin EG.Proof.Chain.{CONC,
  CONCL,ConcTower,ConcSums,EpsCONC}`: OK (only the stub `sorry` warnings). Cosmetic: the deprecated
  `push_neg` in `ConcTower.lean` (towerEnd) was replaced by `push Not`.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan (`scripts/Axioms.lean --prefix EG` on the six proof modules): 1807 constants,
  0 violations. `sorryAx` appears in 13 constants: the 5 declared-input stubs (`towerA`, `towerC`,
  `ovK1`, `ovK3`, `lacunaryGeom`) and, transitively through them only, `towerHalf`,
  `tower_sum_le`, `sum_thetaGC_le`, `concTauSum`, `concDStarSum`, `concLGCSum`, `concIII`,
  `concLSum`. Origin (a), (b), guest cap, CONC (i), (ii), CONC-L (i)–(iii), `concLAlpha`, the
  per-ancestor bound, `kStar`, `towerEnd`, `logStarFacts`, `epsCONC_tendsto` are sorry-free.
- Refutation target (CONC-L (iv) per-ancestor bound): **proved** (`EG.concLPerAncestor`, no Γ, no
  declared input). No math finding of class T1–T3.
