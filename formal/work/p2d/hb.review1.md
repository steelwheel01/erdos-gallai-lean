# P2-D [hb] definition review, round 1 (clean room)

Reviewer: clean-room Defs reviewer, round 1, 2026-09-26.
Scope: `EG/Defs/HB/Witness.lean`, `EG/Defs/HB/SplitTree.lean`, `EG/Defs/HB/Round.lean`, `EG/Defs/HB/Run.lean`, and, for usability, `EG/Lib/HB/{SplitTree,Run}.lean` and `EGTest/HB.lean`.
Checked against:
- manuscript v6.1 `proofs/manuscript/s2.tex`, lines 41–133, 135–160, 220–235, 278–320, 376–410 and 503–633;
- TRIAGE §2.1–§2.4 and §2.12;
- the `defs_needed` lists and the Lean sketches of `blueprint_s2a`, `s2b`, `s3b`, `s5`, `s6a`, `s6b`, `s7a` and `s7b`;
- the design note `work/p2d/hb.md`.

I did not edit any Lean file.

## Verdict: APPROVE (no major issue)

- Every definition back-translates to the quoted manuscript text.
- The edge cases are either junk values that no statement reads, or they are handled by guards.
- Every downstream use listed in the blueprints can be stated with the provided objects and index types.
- The issues below are API gaps, test depth, and docstring slips. None of them changes the meaning of a Def.

Build state, re-checked:
- The `.olean` files for all four Defs and both Lib files are present.
- `python3 scripts/lint.py` reports 0 findings.
- Two scratch files I wrote compile with 0 errors and no `sorry` (see "Non-vacuity" below).

## Back-translation, definition by definition

### Witness.lean

| Lean | Back-translation | Manuscript | OK |
|---|---|---|---|
| `IsWitness H ε s U F` | U ⊆ V(H), F ⊆ E(H), 1 ≤ \|U\| ≤ 2\|H\|/3, \|F\| ≤ s\|U\|, \|Nbr_{H−F}(U)\| < ε\|U\|/log₂²\|H\| | defWitness display | yes |

`IsWitness` is literally the negated body of `IsExpander`: `not_isExpander_iff_exists_isWitness` is proved by `push Not; rfl`. `nbrSet` is taken in V(H)∖U, as in s1:convGraphs(c).

| Lean | Back-translation | Manuscript | OK |
|---|---|---|---|
| `witN`, `witF0` | N = Nbr_{H−F}(U); F₀ = E_H(U, V∖(U∪N)) | "For a witness … put N, F₀" | yes. Taking N as the argument makes Fact (c) definitional. |
| `tauHout` … `tauF2` | rules (1) and (2), with the real comparison `τ ≤ deg` | defTauRules (1)–(2) | yes, checked symbol by symbol |
| `tauG1`, `tauG2` | H[U'∪N''] − F'', and H − U' − E(G₁) − F'' | literal children | yes |
| `splitFst`, `splitSnd`, `splitDel` | H[U'∪N''], H[V∖U'] − E(H[N'']), and E_H(U', V∖(U'∪N'')) | lemSEP, (eqSplit) | yes |

(eqSplit) is correctly left as a statement. The trees use the SEP forms, and they agree with the literal children whenever U'∩N'' = ∅. That condition is part of `WF`, and Fact (a) gives it for τ-rule labels.

### SplitTree.lean

| Lean | Back-translation | OK |
|---|---|---|
| `STree`, `Addr`, `nodeAddrs` / `leafAddrs` / `internalAddrs`, `labelAt` | a finite binary tree of choices; leaves are named by address, so equal vertex sets stay distinct | yes |
| `graphAtD` | H_ν, computed by `splitFst` / `splitSnd`; total (past a leaf it returns the leaf graph) | yes |
| `WF` | "disjoint U'_ν, N''_ν ⊆ V(H_ν)" at internal nodes | yes |
| `delAt`, `deleted`, `leafMass`, `dup` | F''_ν; the deleted edges; S; Dup (counted by leaf address) | yes |
| `DeltaGe`, `dupGe` (real M) | Δ_{≥M} and dup_{≥M}(v) | yes |
| `OVHyp ε c` | WF, m ≥ 2, \|ν₁\| ≤ ¾m, \|N''\| ≤ cε\|U'\|/log²m | yes |

On `OVHyp`: dropping n₀ ≥ 1 only strengthens OV. At n₀ = 0 the root must be a leaf, so S = 0.

| Lean | Back-translation | OK |
|---|---|---|
| `graft`, `leafPrefix` | attach f a at leaf a, so a node of f a gets address a ++ b; the piece above a node | yes (recursion checked by hand) |
| `StopsAt` | leaf ⇔ P, over all nodes | yes (both directions, HB-STOPRULE) |
| `IsS0Rec` | WF, plus at each internal node a witness with s = 0 and label (U, Nbr_{H_ν}(U)) | yes |
| `IsTauSplitTree` | the hypothesis of lemThinCut: s_ν < τ, a witness, and τ-rule labels | yes |
| `IsTauRun ε (s:ℕ) τ` | WF, StopsAt(ε,s)-expander, and τ-rule labels from a witness with parameter s | yes |
| `cOV` | log₂(4/3) | yes |

### Round.lean

Parameters, checked against (R0)–(R2) and (GC) of v6.1:
- λ, t^HB, T = t^HB·d and Λ are in ℝ.
- M = ⌈max(2^40, 2^16·T·log⁴T)⌉₊ is in ℕ.
- s = ⌈Λ^σ⌉, P = ⌈λ^{C'}⌉, τ = ⌈128 s log²M⌉ and θ^GC = ⌈z·λ^{−1/2}⌉ are ceilings in ℕ.
- σ and C' are the locked `sigmaC` and `Cp`, as ℕ exponents.

This agrees with TRIAGE §2.1. `TOf = tHBOf d * d` equals TRIAGE's `d * log²d`.

Remark: Λ ≥ 40 holds unconditionally (M ≥ 2^40). Hence τ_l > s_l ≥ 1 for every d, so the τ-rules are always used in their intended range τ > s, even without Γ.

Round objects, each back-translated and compared with the text quoted in the docstrings:
- **Cycles and G'_l.**
  - `CyclesValid` has three parts: WF long cycles in G_l, the flattened edge list `Nodup` (pairwise edge-disjoint), and no WF cycle of length ≥ T in G'_l. This is (R1) read as "any maximal family" (TRIAGE §2.12).
  - `graph'` is G_l − E(Cyc_l).
- **The recursions.**
  - `twoLevel`: τ-runs are grafted only at pieces with |𝒫| ≥ P_l.
  - `prePartAddrs`: the leaves of `twoLevel` with ≥ P_l vertices.
  - `DupStar`: leaves of any size.
- **(R4).**
  - `mu` counts by address, and `D = {μ ≥ 2}` over the union of the pre-parts.
  - `home` is the first entry of the home order that is a pre-part containing v.
  - `guests` is S_Z.
  - `isL1` is 2|S| ≤ |Z⁰| in ℕ.
  - `isL2` counts neighbours in G'_l[Z⁰], not X⁰ (HB-L2-GRAPH).
  - `isGC` is: ∀ x ∈ S, |N_{X⁰}(x) ∩ (Z⁰∖S)| < θ.
  - `isLight`, `isGCPart` and `Std` follow from these.
- **Parts.** `partVerts` is Z⁰∖S_Z or Z⁰. `X` is X⁰ minus the vertices S_Z. `partGraph` is X_Z or X⁰_Z.
- **(R5).** `assign` chains three steps in priority order with `Option.or`:
  1. part-graph edges;
  2. otherwise, the first light part in the home order containing both ends;
  3. otherwise, the first standalone pre-part in the home order containing both ends.

  `E` and `passed` are filters of `assign` over E(G'_l). `next` keeps V(H).
- **`Valid`.** It contains `CyclesValid`, `IsS0Rec`, the s=0 stopping rule (both directions), τ-runs at big pieces with (ε, s_l, τ_l), and a home order that is `Nodup` with entry set equal to the pre-parts.
- **Design constraint** (TRIAGE §2.2, lemGC(i)). I checked by reading that `prePartAddrs`, `mu`, `D`, `home` and `guests` do not reference `isLight` or `isGC`.

### Run.lean

**Run structure.** A `Run` holds the choices only, one per round.
- `choice l = rounds[l−1]` (1-indexed).
- `graph` is defined by recursion: G₁ = G, then `next` for 1 ≤ l ≤ R, and constant afterwards.
- `Valid` is: ∀ l ∈ [1,R], D_* ≤ d_l ∧ `Round.Valid`, together with d_{R+1} < D_*. This is exactly (R0) with R := l−1.
- `E0 = E(G_{R+1})`.
- The guards (`prePartAddrs`, `pieceAddrs`, `D`, `DupStar`, `mu`, `E`, `assign`, `cycles`) give TRIAGE's stationarity: Std_l = ∅ and E_l = ∅ for l > R.

**Ancestors.**
- `PartId = ℕ × Addr`, and `parts = ancestors = {(l,a) : l ∈ [1,R], a a pre-part}` (ANC-BIJECTION).
- For each ancestor Y:

  | Lean | Quantity | Light Y | Standalone Y |
  |---|---|---|---|
  | `ancVerts` | V(Y) | Y⁰∖S_Y | Y⁰ |
  | `ancGraph` | H_Y | X_Y | X⁰_Y |
  | `ancEps` | ε_Y | 2^{−6} | 2^{−5} |
  | `ancS` | s_Y | s_r/2 (in ℝ) | s_r |

- `LY` = log₂\|V(Y)\|.
- `anc` uses r + 2 ≤ l. It is ∅ for l ≤ 2, and there is a test for this.

**Port sets.** `hubs`, `ports`, `fresh` and `classed` are A_Z, U_Z, F_Z and Q_Z.

**Counts.**
- `dup` is Σ_w (μ−1) with ℕ truncation, which is (·)⁺.
- `mult` counts pre-parts whose part vertex set contains w.
- `nuAnc` counts ancestors with r + 2 ≤ l.
- `j0` and `j1` take values in `WithTop ℕ`.

**Functions of reals.**
- `epsA D = 31ε/(C'·log₂log₂D)` and `psiPool x = (6 log₂x + 12)/x` are verbatim.
- `HypH` is (H), with the domain [x₀,∞) kept as `x0 ≤ x` and `x0 ≤ y` (D-HB-20). I checked that this reading is safe:
  - (iii) applies (H) only at y = λ_r and x = λ_{r+1}, both ≥ x₀ = log D_*, since d_r ≥ D_* for r ≤ R.
  - (iv) only has to prove the weaker predicate.
  - So (iii)∘(iv) is unaffected, and the literal domain reading is kept. The s2b sketch omits `x0 ≤ y`; the Def is the one to follow.

## Downstream coverage (defs_needed of s2a/s2b/s3b/s5/s6a/s6b/s7a/s7b)

I tallied every `run.*` and `EG.HB.*` name in the blueprints. Everything they read is present, sometimes under a different name:

| Blueprint name | Def to use |
|---|---|
| `run.allAncestors`, `run.ancestorSet` | `run.ancestors` |
| `run.H Y` | `run.ancGraph G Y` |
| `run.Mr` | `run.M` |
| `EG.HB.psi` | `psiPool` |
| `run.isStd Y` | `Y ∈ run.stdParts G` |

These are renames for the Spec authors, not gaps. The objects that are left Spec-local by design (D-HB-25) are one-line functions of the provided objects: `EdgeSrc`, `TypeAlpha`, `TypeBeta`, `lightIncidences`, `Parentless`, `IsClassedPort`, and KJS/KHUB/tJS (these are s3/s7 Defs).

The index types match TRIAGE §2.1:

| Object | Type |
|---|---|
| `Std` | `Finset Addr` |
| `lightParts`, `ancestors`, `anc` | `Finset PartId` |
| a designation | `ℕ → V → PartId` |
| JS sites | `{(l,y) : r + 2 ≤ l ≤ R}` via `run.R` |
| M, s, P, τ, θ | ℕ |
| d, λ, T, Λ | ℝ |

## Non-vacuity (scratch tests; not added to the repo)

The scratch files are in the session scratchpad (`/tmp/claude-0/…/scratchpad/`). Both compile with `lake env lean`: 0 errors, no `sorry`.

1. **`HBScratch1.lean`: a genuine τ-run.** The test in `EGTest/HB.lean` only has single-leaf τ-runs, so the split clause of `IsTauRun` was never exercised.
   - Setup: H is two disjoint edges 01 and 23 on `Fin 4`, with s = 1 and τ = 2. The tree splits `({0,1},∅)`, then `({0},∅)` and `({2},∅)`, using the witnesses `({0,1},∅)`, `({0},{01})` and `({2},{23})`.
   - `t.IsTauRun epsC 1 2 H2` is proved, including the τ-rule label equalities through `tauU1`/`tauN2` and both directions of the stopping rule.
   - Also proved: `t.deleted H2 = {01, 23}` and `t.dup H2 = ∅`.
   - So the τ-rules, `witN`, `IsWitness` and the address arithmetic fit together, and edge deletion is exercised.
2. **`HBScratch2.lean`: (R4)/(R5) semantics on overlapping pre-parts.** The K₃ run in `EGTest/HB.lean` has D = ∅, no guests and an empty assignment.
   - Setup: G = K₃ (d = 2, P = 1), and the choice splits `({0},{1})`, giving pre-parts [false] = {0,1} and [true] = {1,2}. The choice is not a valid round; only the functions are exercised.
   - Proved: `D = {1}`; `home 1 = some [false]`; `S_[true] = {1}`; `S_[false] = ∅`; [true] is light, with (GC) evaluated through `thetaGC 2 2 = 2`; `partVerts [true] = {2}`; and `(partGraph [true]).edges = ∅`, because X deletes the guest.
   - Also proved: `assign 01 = some [false]` (step 1), and `assign 12 = none`. Edge 12 lies in X⁰ of [true] but meets its guest, and no light part contains both of its ends, so it passes down.
   - This matches a hand reading of (R4) and (R5).

## Issues

| # | Severity | Location | Issue | Suggested fix |
|---|---|---|---|---|
| 1 | minor | `EG/Lib/HB/Run.lean` | Characterization lemmas that blueprints s2a (HB-DATAMODEL, CAP-RUN-API) and s2b name as prerequisites are missing: E_l(Z) ⊆ (partVerts Z).sym2; Z⁰ ⊆ V(G) and X⁰_Z ≤ G'_l; "a pre-part is a leaf of the τ-run of its big piece, with X⁰ = (tauRun q).graphAtD (piece q) b", which D-HB-9 says is a later lemma; and `pieceOf a ∈ pieceAddrs` for a pre-part a. They are true for the current Defs; I checked E ⊆ partVerts.sym2 step by step through `assign`. | Add them to Lib before the s2 Specs are written. No Def change. |
| 2 | minor | `Run.tauRun`, `Run.piece` (Run.lean:120, 127) | `run.tauRun l q` is unconstrained junk for pieces with \|q\| < P_l, and for q not a piece. The s2b sketches (propStructure, propOrigin) use a `run.bigPieceAddrs G l` that does not exist. A Spec that ranges over `run.pieceAddrs l` and reads `tauRun` without the size filter would read junk. | Add `bigPieceAddrs G l := (run.pieceAddrs l).filter (P_l ≤ \|piece\|)`, or a CONVENTIONS line: "read `tauRun` only at big pieces". |
| 3 | minor | `Run.thetaGC` (Run.lean:106) | It takes `z : ℕ`, but blueprint s6b writes `run.thetaGC G r a`. The Def is usable, as `run.thetaGC G r (run.Z0 G r a).card`. | Add a CONVENTIONS note, or an address-form wrapper. |
| 4 | minor | `EGTest/HB.lean` | The only positive tests are degenerate: every τ-run is a single leaf; D = ∅, no guests, all parts light; and E_l = ∅. | Add the two scratch tests above (a genuine τ-run; overlapping pre-parts with a guest and a passed-down edge). |
| 5 | cosmetic | `Run.choice` (Run.lean:61) | `getD (l-1)` gives `choice 0 = rounds[0]`, so the unguarded wrappers at l = 0 read round 1. This is harmless, because the index sets are empty at l = 0. | Say so in the docstring, or use `if l = 0 then default`. |
| 6 | cosmetic | Witness.lean module doc (line 17) | It cites `EG.Lib.HB.Witness`, which does not exist. The lemma is in `EG.Lib.HB.SplitTree`. | Fix the reference. |
| 7 | cosmetic | Run.lean module doc (line 21) | It says "stationary for `l > R + 1`", but it is stationary from l = R+1 (`graph_of_R_lt`). | Change to "for `l ≥ R + 1`". |
| 8 | cosmetic | `Run.ancEps` (Run.lean:282) | It uses the literals `2^(-5:ℤ)` and `2^(-6:ℤ)` rather than `epsC`. They are definitionally equal. | Optional: use `epsC` and `epsC / 2`, so that `simp [epsC]` is not needed. |
| 9 | cosmetic | `IsTauRun` / `IsWitness` casts | The witness inside `IsTauRun ε (s:ℕ)` has parameter `↑s`, so witness lemmas stated with a literal `(1:ℝ)` need `Nat.cast_one`. I hit this in scratch test 1. | A note in the Lib docstring, or a `simp` lemma. |

Design deviations I checked and accept:
- D-HB-1: `Round.Valid H c` without the TRIAGE arguments `n` and `Dstar`. n = \|V(H)\| and D_* enters only through `Run.Valid`, so the content is the same.
- D-HB-2: `STree` as its own inductive.
- D-HB-14: `Run` as a one-field structure.
- D-HB-21: plain `@[expose]` defs rather than `irreducible_def`. The latter expands to the forbidden `opaque` form.

## Summary for the orchestrator

Approve. The Defs are faithful, total and usable. Issues 1–4 (Lib lemmas, a `bigPieceAddrs` helper or convention, a thetaGC note, stronger tests) can be done in Lib and tests after the lock, since none of them needs a Def change. Items 5–9 are docstring or cosmetic fixes; if applied before locking, they are the only edits to Defs files.
