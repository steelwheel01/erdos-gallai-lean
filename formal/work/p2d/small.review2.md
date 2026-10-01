# P2-D [small] definition review, round 2 (clean-room)

Reviewer: clean-room definition reviewer (round 2), 2026-09-26. Scope: TRIAGE §3 Defs order
items 1–6 as implemented in `EG/Defs/{Objects,Graph,Log,Constants,PathDecomp,Components}.lean`
and `EG/Defs/Gamma/Core.lean`, with the Lib API in `EG/Lib/Found/*` and the tests in
`EGTest/Defs2.lean`, after fix round 1 (`work/p2d/small.md`, "Fix round 1"). No Lean file was
edited; scratch tests live under the session scratchpad (`R2.lean`).

**Verdict: APPROVE (ready to lock).** No major issue. Every definition back-translates to the
quoted manuscript text, is total with the fallbacks documented, and every downstream use listed in
the blueprints (s1, s2b, s3a, s3b, s4, s5, s6a, s6b, s7) can be stated with the given types. All
round-1 items are closed except the two that were explicitly deferred to the integrator/next
re-lock (M4, C1), which are still open and still non-blocking. Three minor and two cosmetic items
are listed at the end.

## What was checked (independently of round 1)

- **Sources.** `AGENTS.md`, `CONVENTIONS.md`, `TRIAGE.md` (§2.3, §2.4, §2.9, §2.11, §2.12, §3),
  `small.md`, `small.review1.md`; blueprint uses of every reviewed name (grep over all 11
  blueprints); manuscript s1.tex (convGraphs 566–599, citProp12 826–840, citLem19 995–1012,
  citThm21/citCor22 1015–1035, defConstants 1519–1560, condGamma 1594–1730), s2.tex (lemLacunary
  1035–1060, the tw paragraph 1115–1142, lemTower 1144–1180), s3.tex (propP13s 286–320, lemL17s
  402–415), s4.tex ((E) 68–75, lemPV statement 400–455 incl. (b),(c)), s6.tex (lemPAR 105–130,
  defDesign 238–260, the log* facts 262–295, ε_CONC 343–349, JS-LC Step 3), s7.tex (lemGammaSat
  1447–1500).
- **Builds and hygiene.** `python3 scripts/lint.py`: 0 findings. The oleans of all 14 touched `EG`
  modules and of every `isEdge` consumer (`EG.Spec/Proof.Found.EG0`, `EG.Lib.Found.{Fnum,
  FGraphFnum, FnumMain}`, `EGTest.{Fnum,Objects}`) are newer than their sources.
  `scripts/check.sh EGTest/Defs2.lean`: 0 errors, 0 sorry. `grep sorry` over all new/edited
  files: none. `def isEdge` is gone from `EG/Lib/Found/Fnum.lean` (moved, not duplicated).
- **The consumer round 1 left unbuilt.** `EGCheck/BridgeLemmas.lean` (imports `EG.Defs.Objects`;
  its olean predates the edit) was single-file checked: `rc=0 errors=0`. No name clash.
- **Lock.** `scripts/Lock.lean` was run read-only on `EG.Defs.Graph EG.Defs.Objects` and the
  records were hashed with the exact formula of `scripts/lock.py` (own hash and closure hash,
  `GENERATED` filter): **all 38 locked constants of these two modules are unchanged** (38/38,
  0 changed, 0 missing). The only unlocked constants in the two modules are exactly
  `EG.FGraph.IsWellExpanding`, `EG.FGraph.nbrSetDeg`, `EG.Obj.isEdge`. The file SHA-256 of
  `EG/Defs/Graph.lean` and `EG/Defs/Objects.lean` differs from `LOCK.json` (expected: add-only
  edits); `EG/Defs/Walk.lean` still matches.
- **Scratch tests (all pass, `R2.lean`).**
  - log*: `log* 4 = 2` (= tw 2), `log* 5 = 3` (jump just above tw 2), `log*(2^{2^{16}}) = 5`
    (= tw 5), `log* 0 = 0`; the total-`logb` detour `logIter 2 (1/2) = logb 2 (−1) = 0` is
    harmless because `logStar` takes the least `k` (`logStar (1/2) = 0` in EGTest).
  - Γ1 encoding is not trivially satisfied by (a): `¬Gamma1c 256` (needs `log₂(105·256) ≥ 14`,
    so `210·14 > 409.6`) and `¬Gamma1e 256` (`36·256 < 240 + 4830·14`); together with
    `gamma1Items_of_le : 2^20 ≤ μ → Gamma1Items μ` (Lib, tested) the items have a genuine
    threshold between `2^8` and `2^20`, as the manuscript's "sufficiently large μ" requires.
  - `nbrSetDeg` with `U ⊄ V(H)`: `K.nbrSetDeg {0,7} 1 = {1,2}`, `… 2 = ∅` (vertices of `U` outside
    `V(H)` are ignored, the result is inside `V(H) \ U`); `d = 0` gives all of `V(H) \ U`
    (documented, out of domain); the P13* form `(K.deleteEdges {02}).nbrSetDeg {0,1} 2 = ∅`,
    `… 1 = {2,3}`.
  - Path decompositions: `P₄ = 0-1-2-3` as `[[1,0],[1,2,3]]` (one path reversed) is accepted,
    `pathEndCount … 1 = 2 = deg 1` (the parity claim of (E) at an inner vertex of degree 2 that
    is an end of two paths); the closed list `[0,1,2,0]` is rejected.
  - Components: `compEdges E (comp 4) = {45}` for `E = {01,12,20,23,45}` (proved by a walk
    invariant, so the negative direction "no other edge lies in that component" is real), hence
    that component is odd; loops: `IsPendant {77} 77`, `7 ∈ edgeVerts {77}`, and the loop is in
    `compEdges` of its own component (documented out-of-domain behaviour, now also in
    CONVENTIONS).
  - Statement shapes type-check: `IsExpander epsC s`; Γ3 `2·N0 ≤ (log₂ D)^Cp`; the full
    ε_CONC formula with `sigmaC`, `epsC`, `Cp`, `logStar`; `λ^{σ+2.5}` as
    `lam ^ ((sigmaC : ℝ) + 5/2)`; lemTower (a),(d) in ℕ and ℝ; the Cor 22, (E), PV(b),(c) and
    Lovász forms; the PAR Spec (odd components, `IsNonBridge ∨ IsPendant`, `2·#odd ≤ |V(E)|`)
    and the defDesign "giant" form; the s2b transfer `Gamma1core D → log₂ D ≤ x →
    Gamma1Items (log₂ x)` is a one-liner from `Gamma1core.items` (see M1).

## Per definition: back-translation, manuscript text, edge cases, downstream uses

### Item 1a. `Obj.isEdge` (Defs/Objects) — faithful
- Lean: `.edge _ ↦ true`, `.cycle _ ↦ false`. [s1:defObject] "An object is a cycle (of length at
  least 3) or a single edge": `isEdge` is the "single edge" branch. Body identical to the former
  Lib definition (the Lib `rfl` lemmas still compile).
- Uses: v6 s1:factEG0(a) "at most h − 1 of which are single edges" (`D.countP Obj.isEdge + 1 ≤ …`,
  s1 blueprint), s4:thmVXp single-edge count (s4.tex:796). Statable.
- Locked constants of Objects.lean unchanged (9/9).

### Item 1b. `FGraph.nbrSetDeg H U d` (Defs/Graph) — faithful
- Lean: `(H.verts \ U).filter (d ≤ |N_H(v) ∩ U|)`. [s1:citProp12] "For U ⊆ V(G) and d > 0 let
  N_{G,d}(U) be the set of vertices of V(G) \ U with at least d neighbours in U." Exact.
- s3:propP13s (proof): "an integer d ≥ 1, write Nbr_{G−F,d}(U) for the set of vertices outside U
  that have at least d neighbours in U in the graph G − F" = `(G.deleteEdges F).nbrSetDeg U (d:ℝ)`
  (`deleteEdges` keeps `verts`, so "outside U" = `V(G) \ U`). Exact.
- Real `d` serves both (Prop 12 real, P13* integer cast); `nbrSetDeg_natCast` gives the decidable
  form; `d ≤ 0` documented. `[DecidableEq V]` as for `nbrs`.
- Uses: BMProp12Statement (s1), P13s Spec (s3a). Statable (both blueprints write exactly this).

### Item 1c. `FGraph.IsWellExpanding H θ U` (Defs/Graph) — faithful
- Lean: `θ·|U| ≤ |Nbr_H(U)|`. [s3:lemL17s] "Call U ⊆ V(G) well-expanding if |Nbr_G(U)| ≥ θ_*|U|";
  [s1:citLem19] sketch with θ = log^{24} n. Neighbourhood in G, not G − F, as both texts say.
- Argument order `G.IsWellExpanding (EG.Star.theta …) U` matches blueprint s3a (L17s, P18s(i)).
  Placement (Graph.lean, not Star.lean) is now recorded in TRIAGE §2.11/§3, blueprint s3a and
  CONVENTIONS; the current `EG/Defs/Link/Star.lean` refers to it and defines no copy (checked).
- Locked constants of Graph.lean unchanged (29/29) despite the new `Mathlib.Data.Real.Basic` import.

### Item 2. `logIter`, `tower`, `logStar` (Defs/Log) — faithful
- `logIter k x = (logb 2)^[k] x`: [s1:convGraphs](b) "log^{[0]}x := x, log^{[k]}x :=
  log(log^{[k−1]}x)", log = log₂. Lean's iterate unfolds inside, the text outside; `logIter_succ'`
  bridges. Exact.
- `logStar x = sInf {k | logIter k x ≤ 1}`: "the least integer k ≥ 0 with log^{[k]}x ≤ 1". Non-
  emptiness proved for every real (`exists_logIter_le_one`), so `sInf` is the minimum
  (`Nat.sInf_mem`; `InfSet ℕ` is Mathlib's `Nat.find`-based instance). On the relevant prefix all
  iterates are `> 1`, so the total `logb` never leaves the genuine domain. TRIAGE §2.3 (`sInf`, no
  proof term) respected.
- `tower 0 = 1`, `tower (j+1) = 2^{tower j}` (rpow): s2.tex:1126 "tw(0) := 1, tw(j+1) := 2^{tw(j)}"
  and s6.tex:262 `T_0 := 1, T_{i+1} := 2^{T_i}`. Exact.
- Uses (all statable with `(logStar x : ℝ)` casts or in ℕ): lemLacunary(iv) `F(x) = (2 log*(2^x)+2)/η(x)`;
  lemTower(a) `R − r ≤ 2 log* d_r + 2` (ℕ), (d) `2^{2 log* d_r + 2} ≤ λ_r`; s5 eqLY; s6
  CONC(iii)/CONC-L(iv), ε_CONC; s6 tower facts `log* x ≤ k ↔ x ≤ T_k` (`logStar_le_iff_le_tower`),
  `log* x = 1 + log*(log x)` (`logStar_of_one_lt`), `log* x ≤ 1 + log x` (provided as
  `logStar_le_two_add_loglog` for `x ≥ 4`; the s6.tex:262 form `log* x ≤ 1 + log x` for `x ≥ 1`
  follows from it and `logStar_le_self`, see M1); growth `logStar_isLittleO_loglog`.

### Item 3. `epsC`, `sigmaC`, `Cp`, `Aexp` (Defs/Constants) — faithful
- [s1:defConstants](i) "ε := 2^{−5}, σ := 100, C′ := 103 and A := 105": `epsC : ℝ := 2^(−5:ℤ)`,
  `sigmaC Cp Aexp : ℕ`. Types justified by the exponent uses (`2^{σ+15}`, `(log D)^{C′}`,
  `(Aμ)^{46A}`); real uses via casts (`cast_sigmaC/Cp/Aexp` simp). `IsExpander epsC s` type-checks.
- Names are now recorded in CONVENTIONS ("Constants and Γ") and TRIAGE §2.4/§2.12, and the
  blueprint names `CpC`/`AexpC` were replaced (round-1 C2 closed). See C2 below for one remaining
  blueprint sketch that inlines numerals.

### Item 4. `IsPathDecomp`, `pathEndCount`, `IsPathCycleDecomp` (Defs/PathDecomp) — faithful
- `IsPathDecomp F P`: every `p ∈ P` has `2 ≤ p.length ∧ p.Nodup`; `(P.flatMap walkEdges).Nodup`;
  `∀ e, e ∈ P.flatMap walkEdges ↔ e ∈ F`. This is s4 (E) "a decomposition of an edge set F into
  (non-trivial) paths" and PV(b) "pairwise edge-disjoint paths of length at least 1, each has two
  distinct ends"; a `Nodup` list with ≥ 2 vertices has distinct ends. Same `Set (Sym2 V)` shape as
  `IsDecomp`; loopy `F` has no decomposition (`IsPathDecomp.not_isDiag`, now a CONVENTIONS rule).
- `pathEndCount P v = P.countP (head? = v ∨ getLast? = v)`: "the number of paths of 𝒫 having v as
  an end" ((E)), "each vertex is an end of at most two of the paths" (Cor 22), "every vertex x is
  an end of at most deg_{H0}(x) arcs" (PV(c), s4.tex:447). Since members are `Nodup` with ≥ 2
  vertices, this equals the number of path ends at `v`, so the parity claim of (E) reads correctly
  (`pathEndCount P v ≡ degE F v (mod 2)`). Members are distinct as lists (a repeated member would
  repeat edges), so `countP` over the list is the count over the family.
- `IsPathCycleDecomp F P C`: paths as above, `(Obj.cycle c).WF` (Nodup, ≥ 3 vertices),
  concatenated edge list Nodup and equal to `F`. Shape of the stage-α Lovász hypothesis
  `∃ P C, IsPathCycleDecomp ↑H.edges P C ∧ 2*(P.length + C.length) ≤ H.card` (s1:citThm21 "at
  most n/2 paths and cycles"); restricting to non-trivial paths loses nothing (dropping trivial
  paths lowers the count). Recorded in blueprint s1 (round-1 C3 closed).
- Uses: Cor22 Spec, (E), PV(b),(c) with `arcs.map Prod.fst`, Lovász. Statable (see C1 on the
  coercion spelling).

### Item 5. Components (Defs/Components) — faithful
- `edgeVerts E = E.biUnion toFinset`: [s6:lemPAR] "V(E_ab) … the set of vertices incident with an
  edge of E_ab".
- `edgeGraph E = fromEdgeSet ↑E` (`Adj u v ↔ s(u,v) ∈ E ∧ u ≠ v`, checked in Mathlib);
  `edgeComps E = (edgeVerts E).image connectedComponentMk`: the components of `(V(E), E)`
  (isolated vertices of `V` excluded, PAR-COMPONENT-ISOLATED); `compVerts`, `compEdges E C =
  E.filter (∀ v ∈ e, mk v = C)`: "a connected component … has an odd number of edges" (PAR),
  "some connected component of Bead_{Y,l} has more than 2γ_l edges" (defDesign).
- `IsNonBridge E e = e ∈ E ∧ ¬ IsBridge e`, with Mathlib `IsBridge G e := Sym2.lift (¬ (G.deleteEdges
  {e}).Reachable v w) e` (Connected.lean:759): a non-bridge `uv` of `E` keeps `u`, `v` connected in
  `E − uv`, i.e. "C − e is connected" in the PAR proof. `IsPendant E e = e ∈ E ∧ ∃ v ∈ e, degE E v
  = 1`: "a pendant edge (an edge with an end of degree 1)".
- "of that component" is now proved, not only argued: `isNonBridge_compEdges_iff`,
  `isPendant_compEdges_iff`, `degE_compEdges` (round-1 M5 closed); the JS-LC Step 3 comparison has
  `compMap`, `compMap_mem_edgeComps`, `card_compEdges_le_compMap`.
- Uses: PAR Spec (odd components, chosen edges, `2·#odd ≤ |V(E)|`), defDesign giant, JS-LC Steps
  3–5. Statable (scratch-typed).

### Item 6. `Gamma1a`–`Gamma1e`, `Gamma1Items`, `Gamma1core`, `Gamma2a` (Defs/Gamma/Core) — faithful
| Item | s1.tex:1602–1612 | Lean |
|---|---|---|
| (a) | μ ≥ 2^8 | `2^8 ≤ μ` |
| (b) | 2^μ ≥ 2^{14} A μ^3 | `2^14 * A * μ^3 ≤ 2^μ` (npow 3, rpow in μ) |
| (c) | 2A log₂(Aμ) ≤ 1.6 μ | `2 * A * logb 2 (A*μ) ≤ 1.6 * μ` (1.6 = 8/5, tested) |
| (d) | 2 log₂μ + 8 ≤ μ | `2 * logb 2 μ + 8 ≤ μ` |
| (e) | λ^{36} ≥ 2^{240}(Aμ)^{46A}, λ = 2^μ | `2^240 * (A*μ)^(46*A) ≤ (2^μ)^36` (46·A = 4830, tested) |

- `Gamma1core D = 2 < D ∧ ∀ μ, logb 2 (logb 2 D) ≤ μ → Gamma1Items μ`: "D_* > 2 …; and for every
  real μ ≥ log₂log₂D_*, with λ := 2^μ, the following hold: (a)–(e)". Item (f) deferred to
  `Gamma1f` (TRIAGE §2.4). `Gamma2a D = 2^117 ≤ D`: [s1:condG2](a).
- Eventuality semantics: upward closed in `D` (`Gamma1core.mono`), Γ2(a) from Γ1
  (`Gamma1core.gamma2a`), values at `log₂log₂d` (`d ≥ D`) and at `log₂D` (`items_loglog`,
  `items_logb`), `log₂D ≥ 2^{256}` — all the transfers the s2b/s6a blueprints ask for.
- Non-vacuity (round-1 M1 closed): `gamma1Items_of_le` (`μ ≥ 2^20`), `eventually_gamma1Items`,
  `gamma1core_two_rpow_two_rpow`, `exists_gamma1core`, `eventually_gamma1core`; my scratch adds
  the negative side `¬Gamma1c 256`, `¬Gamma1e 256`, so the encoding is neither vacuous nor
  trivial. The eventuality claim of s7:lemGammaSat(i) for (a)–(e) is thereby already available;
  its Spec is unaffected.
- Uses: `Gamma1core Dstar` / `Gamma2a Dstar` as hypotheses in every s2–s7 Spec (Dstar : ℝ),
  `RunHyp`, `Gamma1 := Gamma1core ∧ Gamma1f`. Statable.

## Round-1 items: status
| # | Status |
|---|---|
| M1 positive Γ test | closed (Lib + tests, re-verified) |
| M2 log* growth | closed (`logStar_le_two_add_loglog`, `logStar_isLittleO_loglog`, tests) |
| M3 TRIAGE/blueprint sync | closed (TRIAGE §2.11/§3, blueprint s3a, CONVENTIONS, Star.lean checked) |
| M4 re-lock file hashes | **open, integrator** (verified: only file SHAs differ; 38/38 constants unchanged) |
| M5 component map / local lemmas | closed (`compMap*`, `isNonBridge_compEdges_iff`, `isPendant_compEdges_iff`, tests) |
| M6 loop convention | closed (CONVENTIONS Graphs section, TRIAGE §2.12) |
| C1 EG0 docstring | **open by design** (locked Spec file; fix at next approved re-lock) |
| C2 constant names | closed (CONVENTIONS, TRIAGE, blueprints s1/s2a/s6b) |
| C3 IsPathCycleDecomp | closed (kept, recorded in blueprint s1) |

## Issues

### Minor
- **M1 (Lib gap, not a Defs change).** Blueprint s2b (lemLacunary(iv), s2b:539) asks for the
  transfer `Gamma1core D → log₂ D ≤ x → Gamma1Items (log₂ x)`; only `items_loglog` (at
  `log₂log₂ d`) and `items_logb` (at `log₂ D`) exist. It is a one-liner
  (`h.items (Real.logb_le_logb_of_le (by norm_num) (zero_lt_one.trans h.one_lt_logb) hx)`,
  scratch-checked); add it as `Gamma1core.items_logb_of_le` to `EG/Lib/Found/Gamma.lean` so the
  three s2b sketches do not each re-derive it. Similarly, s6.tex:262 states `log* x ≤ 1 + log x`
  for all `x ≥ 1`; the Lib has the sharper `logStar_le_two_add_loglog` (`x ≥ 4`) and
  `logStar_le_self`; a two-line `logStar_le_one_add_logb (1 ≤ x)` would match the manuscript
  wording used by CONC. Proof-side; does not block the lock.
- **M2 (integration, still open from round 1).** (i) `LOCK.json` file hashes of
  `EG/Defs/Graph.lean` and `EG/Defs/Objects.lean` must be re-recorded with an approval (constants
  verified unchanged, 38/38); the seven new Defs files must be added to the lock when the new
  modules are locked. (ii) `EG.lean`/`EGTest.lean` do not yet import the new modules or
  `EGTest.Defs2` (`gen_roots.py`); `EGTest/Defs2.olean` is therefore absent from `.lake` although
  the file checks clean. (iii) A full `lake build EG` + `scripts/lock.py check` after (i)–(ii).
- **M3 (test coverage, optional).** EGTest has no negative Γ1 test at a value on the ray from (a)
  (all negatives are at μ ≤ 255 or D ≤ 4), so a future accidental weakening of (c) or (e) to
  something implied by (a) would pass the suite. Add `¬Gamma1c 256` and `¬Gamma1e 256` (proofs in
  the scratch file, ~15 lines) to `EGTest/Defs2.lean`.

### Cosmetic
- **C1 (usage note).** `IsPathDecomp ↑F P` with `F : Finset (Sym2 V)` does not elaborate as
  written in blueprints s1/s4 (`↑F` is elaborated before `V` is known: "expected `Set (Sym2 ?m)`");
  `(F : Set (Sym2 V))` works. The same holds for the locked `IsDecomp`. One line in CONVENTIONS
  ("write `(F : Set (Sym2 V))`, not `↑F`") would save every s4 Spec author a round trip.
- **C2 (blueprint sync).** Blueprint s6a's CONC(iii) sketch (s6a:623–624) still inlines
  `2 ^ (100 + 14)`, `2 ^ (-5 : ℤ)` and `103` instead of `sigmaC`, `epsC`, `Cp`; the Spec must use
  the named constants (CONVENTIONS "Constants and Γ"). Also the stale `EG/Spec/Found/EG0.lean:27`
  docstring (round-1 C1) remains, by design, until the next approved re-lock.
