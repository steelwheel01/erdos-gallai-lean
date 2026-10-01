# P2-D [light] — clean-room definition review, round 1

Reviewer: clean-room Defs reviewer (round 1), 2026-09-26. Scope: `EG/Defs/Light/Stages.lean`,
`EG/Defs/Light/Constants.lean` (plus the Lib/EGTest files they ship with), against manuscript v6.1
`s5.tex` (setting l. 9–24, s5:defZones l. 28–44, s5:defStages l. 79–107, s5:lemE1, s5:lemExpect,
s5:lemChild l. 163–207, s5:lemParent l. 211–323), `s3.tex` s3:lemHB (l. 910–920), the locked HB
Run model and the Stage-1 layer (`EG/Defs/Stage1/{COL,Zones,Law}.lean`), TRIAGE §2.7/§2.8/§3
items 19–20, `blueprint_s5.md` (defStages, lemE1, lemExpect, lemChild, lemParent, lemKRED) and
`blueprint_s4.md` (s4:lemPV data). No Lean file was edited.

## Verdict: APPROVE (no major issue), with 4 minor and 2 cosmetic items

Every definition back-translates to the manuscript text it quotes; edge cases (r ≥ R−1,
standalone Y, l ≤ 2, empty Rt, off-support outcomes) behave as the text says or are harmless
junk behind the documented guards; every downstream use listed in blueprint_s5 (and the s6/s7
reads of `demoted`/`dem`/`lp`/`Bad`, the s7 reads of `ε_U`, `ε_ch`) can be stated with the
provided names and index types. The minor items are interface/layering choices that are cheap
to fix now (the files are PENDING) and expensive after the lock.

## Checks performed

- Read `light.md`, both Defs files, `EG/Lib/Light/{Stages,Constants}.lean` (statement lines),
  `EGTest/Light.lean`; the Stage-1 defs `COLa`, `COLc`, `IU`, `Tslot`, `tY`, `JY`, `kown`,
  `ownIdx`, `ownR`, `ownM`, `Own`, `Lend`, `lentClass`, `LU`, `Zone`, `zoneOf`, `zonePhase`,
  `Outcome.{colAt,cOutAt}`; the Run defs `lightParts`, `parts`, `ancVerts`, `ancGraph`,
  `partGraph`, `X`, `E`, `ancEps`, `ancS`, `LY`, `lam`, `s`, `nuAnc`; `IsPathIn`, `IsThrough`,
  `walkEdges`, `pathLength`, `pathEndCount`, `degE`, `IsPathConnected`; `EG.Chain.epsK`;
  `StageData.ofOutcome`, `lendBad`.
- `python3 -I scripts/lint.py`: 0 findings. `python3 scripts/lock.py check` could not run in my
  session (`scripts/Lock.lean` needs the whole `EG` built; `EG.Defs.Quot.Constants.olean` is
  missing — another task's module, not built here; I did not start a full `lake build` on the
  shared machine). The author reports 0 violations; the orchestrator should re-run it.
- Scratch file (scratchpad `LightRev.lean`, `lake env lean`, 0 errors):
  - `IsHBFamily K3 1 1 (fun w => {w+1})` holds (non-vacuous);
  - `¬ ∃ A, IsHBFamily K3 3 10 A` (the size clause bites: `|N(0)| = 2`);
  - `¬ IsHBFamily K3 1 0 (fun w => {w+1})` (the multiplicity clause bites);
  - `epsU 4 = 2462 * 2^(-205)` and `epsU D = 2462 * (logb 2 D)^(-205)` by `rfl` (parse check:
    the power applies to `log₂ D`, not to `D`);
  - PV's `ext x ≠ some c` for `childData` implies the `ArcHyp` zone clause
    (`not_mem_Zone_of_zonePhase_ne`), with no support hypothesis;
  - signatures of `E1`, `demoted`, `parU`, `ArcHyp`, `lentUAvail`, `IsConnector` (implicit
    `G run` read off `ω`).

## Back-translation, definition by definition

| Lean | Back-translation | Manuscript | Match |
|---|---|---|---|
| `IsHBFamily X m b A` | ∀ w ∈ V(X): A w ⊆ N_X(w), \|A w\| = m; ∀ u: #{w ∈ V(X) : u ∈ A w} ≤ b | s3:lemHB "every vertex `w` has a set `A(w) ⊆ N_X(w)` with `\|A(w)\| = m`, such that every vertex of `X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`" | yes (∀ u : V is equivalent: A w ⊆ N_X(w) ⊆ V(X)); count is over indices w, i.e. the family, as the text ("of the sets A(w), w ∈ V(X)") |
| `vm`, `vb` | ⌈L^6⌉₊, ⌈2^7 L^2 vm⌉₊ with L = log₂\|V(Y)\| via `pvM`, `pvB` | "`vm_Y := ⌈L_Y^6⌉`, `vb_Y := ⌈2^7L_Y^2vm_Y⌉`"; s3:lemHB b = ⌈128 L²m⌉ at ε' = 2^-6 | yes (rfl lemmas) |
| `AY` | ε-choice of an HB family for `X_Y`, vm, vb | "We fix one such family by a fixed rule; it depends only on the run" | yes; meaningful only under StagesHBStatement (Spec), `AY_spec` |
| `E1 ω Y` | ∀ l ∈ [r, R], ∀ w ∈ V(Y): L^5/8 ≤ #{u ∈ A_Y(w) : wu ∈ E(M_Y), zonePhase l u = none} | (E1) verbatim | yes; `M_Y = ownM` (label `ownIdx none` = M), "carries no round-l zone" = `zonePhase … = none` (zonePhase returns `some c` exactly for U-tags with first coordinate l) |
| `demoted` | ¬E1 ∨ ¬COLa(Y) | "(E1) fails for Y or a COL(a) event fails for Y" + the explicit list | yes; for light Y `COLa` has ε = 2^-6, s_Y/4 = s_r/8, lent s_Y/(8k_lend) = s_r/(16k_lend), own s_r/(16k_own) (`demoted_iff_of_isLight`) |
| `parentBad` | ¬COLc(Y) for Vs i = Zone_{Y,i} | "for some (l,c,σ), r+2 ≤ l ≤ R, c ∈ [4], σ ∈ [T^sl_Y], LU_{Y,l,c,σ} not (2^12L_Y^4, t_Y)-path connected through Zone_{Y,l,c,σ} (multiset sense)" | yes (`parentBad_iff_of_isLight`; `IsPathConnected` quantifies over indexed pair families = multisets); false for r ≥ R−1 and for standalone Y (IU = ∅), as the text says |
| `goodParent`, `Bad` | light ∧ ¬dem ∧ ¬pb; lightParts.filter (dem ∨ pb) | verbatim | yes |
| `goodParents ω l` | good parents with r(Y)+2 ≤ l | "good parent of round ≤ l−2" | yes (∅ for l ≤ 2) |
| `Rt ω Z`, `Pl ω Z` | V(Z) ∩ ⋃_{Y ∈ goodParents Z.1} V(Y); V(Z) \ Rt | verbatim, l = r(Z) | yes; "no light part outside Bad of round ≤ l−2 contains v" is literally `v ∉ Rt` (eqPl / propParentless(iii) with the set `Bad ω`) |
| `parU ω l v` | some (a min-round good parent of round ≤ l−2 containing v) / none | "the good parent of the smallest round ≤ l−2 that contains v" | yes; the ε-property holds whenever the guard holds (finite nonempty set has a min-round element), `parU_spec`; tie-break irrelevant (unique by propStructure(iv)); taking `l` is the literal reading (D-L-4), and lemParent only uses "a good parent of round ≤ l−2 containing v" |
| `dem`, `lp` | Σ_{Y light, demoted}\|Y\|; Σ_{Y ∈ Bad}\|Y\|(R − r(Y)) in ℕ | verbatim | yes; `R − Y.1` exact since lightParts ⊆ parts ⊆ rounds [1,R] |
| `ChildData`, `childData` | Z = V(Z), O = X_Z, sO = s_l/2, A = A_Z, J = J_Z, R (j,c) = R_{j,c}, M = M_Z, sOwn = s_l/(16k_own), Rt, Pl, ext v = zonePhase ω.zone l v | lemChild data list + "O = X_Z … (2^-6, s_l/2)-expander", "s' := s_l/(16k_own)" | yes; own-class index type `Fin (pvJ \|Z\|) × Fin 4` is definitionally PV's (test `Iff.rfl`); `E1_childData` gives (E1') (vertex count = edge count, u ↦ wu injective) |
| `Arc`, `arcEdges`, `childParts`, `bundleEdges` | (vertex list, phase); union of walk edges; non-demoted light parts of round l; ⋃_Z edges of phase-c arcs of Z | lemChild (b), lemParent "U-bundle B_{l,c} … E(B_{l,c}) the union of their edge sets" | yes (arcs of parts outside `childParts` not read) |
| `ArcHyp` | ∀ Z ∈ childParts l: Own_Z ⊆ H0 ⊆ E_l(Z); arc edge lists jointly Nodup; each arc IsPathIn H0, ≥ 1 edge, both ends in Rt(Z), every vertex outside every Zone_{Y,l,c,σ} of its phase c; #arcs ≤ 14(J_Z+1)\|Z\|; pathEndCount ≤ deg_{H0} and ≤ \|Z\|−1; Rt = ∅ → no arcs | lemParent hypotheses + lemChild (b)–(d) | yes. The zone clause is the literal text of (b) and is implied by PV(b) (`ext x ≠ c`, checked); it is exactly what the cycle claim (Step 7 (2)) uses. `IsPathIn H0` gives the unstated-but-used facts of (F-d): vertices in Z (`ArcHyp.mem_verts`, via (R5) steps (1)/(2) for light parts), edges in E_l(Z), two distinct ends (`head_ne_getLast`). Nodup of the concatenated edge lists = pairwise edge-disjoint (also across reversed orientation, as `Sym2`) |
| `lentUAvail`, `IsConnector` | ⋃_{Y ∈ goodParents l} ⋃_{σ < T^sl_Y} E(LU_{Y,l,c,σ}); path in LU with interior in Zone | lemParent (i) verbatim | yes (σ 0-based, as `IU`) |
| `Jbar` | sup of J_Z over light Z of round l (0 if none) | lemParent preamble | yes |
| `epsU` | 2462·(log₂ D)^(−205) (zpow) | s5:lemExpect | yes (value/parse checked) |
| `epsChain` | `EG.Chain.epsK` = 614/D + log₂(2A log₂(A log₂log₂D))/(371 (log₂log₂D)^2), A = 105 | s5:lemParent (ii) | yes (formula of `epsK` compared character by character; G-S5-1 respected) |

Probability laws: this task introduces no law. The randomness read by the statuses is exactly
the locked (1a) colouring of Y (`ω.colAt Y`) and (1b) zone labels (`ω.zone`), as the text's last
sentence of s5:defStages says ((E1): colouring of Y + choices/sublabels; COL(a): colouring of Y;
parent-bad: colouring of Y + zones of Y). For lemE1(a) the needed fact `wu ∈ E(H_Y)` for
`u ∈ A_Y(w)` follows from `IsHBFamily` (A w ⊆ N_{X_Y}(w)) and `ancGraph = X` for light Y
(`ancGraph_eq_X_of_isLight`), so the colour of `wu` is a coordinate of the law. OK.

## Downstream statability (blueprint_s5 + consumers)

| Consumer | Needs | Status |
|---|---|---|
| StagesHBStatement | `IsHBFamily (run.X …) (vm) (vb) (AY)`, `vm` vs `s_r/2` | statable |
| EqPlStatement | Σ over `(run.lightParts G).filter (¬ demoted ω ·)` of `(Pl ω Z).card` ≤ 2n + `lp ω` | statable; propParentless(iii) takes `Bad ω : Finset PartId` |
| lemE1 (a)(b)(c) | `(law G run).prob {ω \| ¬ E1 ω Y}`, `{demoted ω Y}`, `{Y ∈ Bad ω}`; (c) is lemCOL(c) with `Vs := Zone … Y` — `parentBad` is literally `¬ COLc` with that family (D-L-3) | statable |
| lemExpect | `expect (80·dem + 369·lp)` ≤ `epsU Dstar · n`; `tendsto_epsU` | statable |
| lemChild Tier-1/Tier-2 (probe P-4) | PV instance from `childData ω Z` (no cast), (E1') via `E1_childData`; conclusion (b)–(d) per Z | statable, but see MINOR-1 / MINOR-2 |
| lemParent (probe P-4) | `ArcHyp`, `bundleEdges`, `lentUAvail`, `IsConnector`, `parU ω l`, `goodParents`, `Jbar`, `run.nuAnc`, `run.M`, `run.lam G (l-2)` (l ≥ 3), `epsChain`, `tendsto_epsChain` | statable; per-(l,c) disjointness of LentU across l is a K-RED-level fact (distinct tags ⇒ distinct classes), fine |
| lemDemoted (1) | `not_goodParent_of_demoted` | statable |
| K-RED | `dem`, `lp`, `demoted`, `childParts`, `ArcHyp` per round; `Kstd` / `LentExtHyp` of blueprint §lemKRED are not defined anywhere — expressible inline from `run.Std`, `run.E`, `Stage1.LJS/LJV` (outside this task's scope; noted for the K-RED Spec author) | statable |
| s6 `StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)`, `lendBad` | types `PartId → Prop`, `ℕ`, `ℕ` | tested, no cast |
| s7 lemGammaSat / Γ4 | `epsU`, `epsChain` and their limits | provided (`tendsto_epsU`, `tendsto_epsChain`) |

## Issues

### MINOR-1 — lemChild (b)–(d) have no shared per-part Def; `ArcHyp` hard-codes them under `∀ Z ∈ childParts`
`ArcHyp` bundles lemChild (b)–(d) (+ the H_0 sandwich) inside `∀ Z ∈ childParts ω l`. The
lemChild Spec (Tier-1: ∀ H_0 ∃ H^obj, arcs; Tier-2: on G_Z) must state the *same* (b)–(d) per
part, so either the Spec author retypes the clauses (two copies that can drift: e.g. one with
the zone form, one with the `ext ≠ c` form; one with `≤ |Z|−1`, one without) or states lemChild
in terms of `ArcHyp` with a singleton `childParts`, which is not possible. K-RED then has to
prove `ArcHyp` from the lemChild conclusion clause by clause.
**Suggested fix (additive, before the lock):** a per-part predicate
`ArcSys ω Z H0 (as : List (Arc V)) : Prop` (the current body with `Z.1` for `l`), and
`ArcHyp ω l H0 arcs := ∀ Z ∈ childParts ω l, ArcSys ω Z H0 (arcs Z)` (or keep `ArcHyp` and add
`ArcHyp_iff : ArcHyp ω l H0 arcs ↔ ∀ Z ∈ childParts ω l, ArcSys ω Z H0 (arcs Z)` with
`ArcSys` carrying `run.E G Z.1 Z.2`). The lemChild Spec then concludes `ArcSys` for the arcs it
produces.

### MINOR-2 — `ChildData` vs the s4 PV data record (TRIAGE §2.8 "The PV Spec must export its data record")
`ChildData` is a Defs-layer record in `EG.Light`; TRIAGE §2.8 says the s4 PV Spec exports *its*
data record and hypotheses as named Defs. If s4 introduces its own `PV.Data` (field names, maybe
`O.card`-indexed own classes, `Option (Fin 4)` ext), lemChild needs a field-by-field bridge and
two records describe the same data. The design note's interface request (own classes indexed by
`Fin (pvJ Z.card)` with `Z` the vertex-set argument, not `O.card`) is correct and must reach the
s4 Spec author.
**Suggested fix:** decide now which record is canonical: either the PV Spec takes `ChildData V`
(move the structure to a Vortex-layer Defs file, e.g. `EG/Defs/Vortex.lean` or a new
`EG/Defs/Vortex/PVData.lean`, keeping `childData` in `EG.Light`), or the PV Spec takes unbundled
arguments with exactly these types. Record the decision in TRIAGE §2.8 (PV-OWNCLASS-INDEX,
PV-EXT-ENCODING are already consistent with `childData`).

### MINOR-3 — `IsHBFamily` lives in `EG.Light` (s5 layer) but is the conclusion shape of s3:lemHB and a hypothesis of s4:lemPV
`IsHBFamily` has no Stage-1/s5 content; the s3 lemHB Spec (blueprint s3b: `EG/Spec/Link/HB.lean`)
and the s4 PV Spec (hypothesis (1)) need the same predicate. Placing it in
`EG.Defs.Light.Stages` forces those earlier-layer Specs to import the s5 Defs (and through them
`Stage1.Law`, `PathDecomp`), or to restate the predicate inline (then StagesHBStatement ↔ HB Spec
↔ PV hypothesis need bridging lemmas and the shapes can drift, e.g. count over `Z` vs over
`X.verts`, `∀ u : V` vs `∀ u ∈ V(X)`).
**Suggested fix:** move `IsHBFamily` to a low Defs module (`EG/Defs/Expander.lean` next to
`IsPathConnected`, or `EG/Defs/Vortex.lean`) under a neutral namespace (`EG.FGraph.IsHBFamily`
or `EG.IsHBFamily`) before the lock; `AY` keeps using it.

### MINOR-4 — lock check not reproduced
`scripts/lock.py check` needs all of `EG` built; it failed in this session for an unrelated
missing module (`EG.Defs.Quot.Constants`). The author's "0 violations" is plausible (only new
files, PENDING) but must be re-run by the orchestrator after the next full build.

### COSMETIC-1 — `ArcHyp` clause (d) and the `≤ |Z|−1` clause
(d) "Rt(Z) = ∅ → no arcs" is implied by "both ends in Rt(Z)" (every arc is a nonempty list);
kept for literalness, fine. Similarly `pathEndCount ≤ |Z|−1` follows from `≤ degE H0 x` and
`H0 ⊆ E_l(Z) ⊆ (V(Z)).sym2` (loopless). Harmless; a docstring sentence saying both are
redundant (and why) would stop a Spec author from "simplifying" one of them away in the
lemChild Spec only.

### COSMETIC-2 — non-vacuity tests are degenerate
The only concrete run (`run1` on `K_3`) has one-vertex light parts, `L_Y = 0` and R = 1, so
(E1)/COL(a) hold trivially, `parentBad`, `Rt`, `parU`, `ArcHyp` are tested only in their empty
cases. No concrete test shows `demoted ω Y` or `parentBad ω Y` *true*, `Rt ≠ ∅`, or an
`ArcHyp` with a nonempty arc. I checked by inspection that each is a non-trivial predicate
(and added the `IsHBFamily` true/false checks in scratch). A richer test run (≥ 3 rounds) is a
P2b/P3 item, not a blocker; consider adding the `IsHBFamily` K3 examples above to
`EGTest/Light.lean`.

## Edge cases checked

- r ≥ R−1: `IU = ∅` ⇒ never parent-bad (`not_parentBad_of_R_lt`); `lentIdx = ∅` ⇒ no lent
  COL(a) conjuncts; `s_lent` junk division by `k_lend = 0` never read. Matches the text.
- Standalone Y: `parentBad` false, `demoted` junk but every consumer guards by `lightParts`
  (`Bad`, `dem`, `goodParent`, `childParts`, s6 `lendBad`).
- l ≤ 2: `goodParents = ∅`, `Rt = ∅`, `Pl = V(Z)`, `parU = none` (lemChild (d) "in particular
  if l ≤ 2").
- (E1) for l > r(Y) (child rounds) is included, as the text says (paid for in lemE1(a)).
- Off-support outcomes (junk colourings for non-ancestors, non-U zone tags): statuses defined,
  meaning only on `supp`; no status depends on anything but `ω.colAt Y` and `ω.zone`.
- `AY` when no HB family exists: arbitrary; every use goes through StagesHBStatement.
- `epsU`, `epsChain` for small D (log ≤ 0): real junk; uses assume Γ.

## Summary for the orchestrator

Approve for lock after deciding MINOR-1..3 (all additive/relocation changes to PENDING files;
none changes the meaning of any definition). No T1/T2 manuscript issue found. The design
decisions D-L-1 … D-L-7 are sound; D-L-3 (statuses as the literal Stage-1 COL events) and D-L-6
(any arc systems with the child-side properties; zone form implied by PV's ext form) in
particular make lemE1(c), lemChild and lemParent statable without re-encoding.
