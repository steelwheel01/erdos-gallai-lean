# P2-D [light] — clean-room definition review, round 2

Reviewer: clean-room Defs reviewer (round 2), 2026-09-26. Scope: `EG/Defs/Light/Stages.lean`,
`EG/Defs/Light/Constants.lean` and the two files created by fix round 1 that they depend on,
`EG/Defs/Link/HBFamily.lean` (`EG.IsHBFamily`) and `EG/Defs/Vortex/PVData.lean`
(`EG.Vortex.PVData`), with the shipped `EG/Lib/Light/{Stages,Constants}.lean` and
`EGTest/Light.lean`. Compared against manuscript v6.1 `s5.tex` (setting l. 9–24, s5:defZones
l. 28–44, s5:defStages l. 79–107, s5:lemE1, s5:lemExpect, s5:lemChild l. 163–207, s5:lemParent
l. 211–260, s5:lemDemoted, s5:lemKRED preamble), `s3.tex` s3:lemHB, `s4.tex` s4:lemPV (l. 400–456),
the locked HB Run model (`EG/Defs/HB/Run.lean`), the Stage-1 layer
(`EG/Defs/Stage1/{COL,Zones,Law}.lean`), `EG/Defs/Chain/{Constants,StageInst}.lean`,
`EG/Defs/Quot/Constants.lean`, TRIAGE §2.7/§2.8/§3 items 19–20/§4 P-4, `blueprint_s5.md`
(defStages, lemE1, lemExpect, lemChild, lemParent, lemDemoted, lemKRED), `blueprint_s4.md`
(s4:lemPV lean_shape) and the s6b/s7 blueprint reads of the s5 names. Round-1 review:
`light.review1.md`; design note: `light.md` (with its fix-round-1 section). No Lean file was
edited.

## Verdict: APPROVE for lock — no major, no minor; 3 cosmetic (documentation-only) items

All six round-1 items are correctly resolved (checked file by file, see §"Round-1 items"). Every
definition back-translates to the text it quotes; every edge case behaves as the text says or is
harmless junk behind a documented guard; the statuses read exactly the stage-1 coordinates the
manuscript names; and every downstream statement of blueprint_s5 — including the two probe P-4
consumers (lemChild's PV instance and lemParent's arc input) and the s6/s7 reads — was **written
out and compiled** against the Defs in a scratch file (below). In addition the transfer
"PV conclusion (blueprint s4 shape) on `childData ω Z` ⟹ `ArcSys ω Z H0 as`" was **proved**
in scratch, so the lemChild Spec can conclude `ArcSys` from the PV Spec with no re-encoding.

## Checks performed

- Read all files listed above in full (Defs, Lib statement lines and proofs, tests).
- `python3 -I scripts/lint.py`: 0 findings. `python3 scripts/lock.py check` (ran in this session,
  full `EG` oleans present): `419 locked constants, 133 locked files; 0 violations, 462 pending`;
  the four new Defs files are PENDING (this closes round-1 MINOR-4).
- `scripts/check.sh EGTest/Light.lean 900`: rc 0, 0 errors, 0 sorry.
- Axiom scan `lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.Light.Stages
  EG.Lib.Light.Constants`: 1935 constants, 0 `sorryAx`, 0 meta-scan hits, 0 violations.
- Scratch file (scratchpad `LightRev2.lean`, `lake env lean`, 0 errors; not part of the repo):
  1. `#check` of every Def: `E1 demoted parentBad : Outcome G run → PartId → Prop`,
     `parU : Outcome G run → ℕ → V → Option PartId`, `childData : … → Vortex.PVData V`,
     `ArcSys : … → PartId → Finset (Sym2 V) → List (Arc V) → Prop`, `ArcHyp`, `bundleEdges`,
     `lentUAvail`, `IsConnector`, `Jbar : FGraph V → Run V → ℕ → ℕ`, `epsU epsChain : ℝ → ℝ`
     (implicit `G run` read off `ω`, D-L-1; explicit `G run` for run-only functions).
  2. Parse of the constants: `epsU D = 2462 * (logb 2 D) ^ (-205 : ℤ)` (`rfl`; the power applies
     to `log₂ D`), `epsU 4 = 2462 · 2^{-205}`, and `epsChain D` equals the s5:lemParent (ii)
     formula with `A = 105` substituted (`norm_num [Aexp]`).
  3. lemE1 (a)(b)(c) as `(law G run).prob {ω | ¬ E1 ω Y}`, `{ω | demoted ω Y}`, `{ω | Y ∈ Bad ω}`;
     lemE1 (c)'s event is *literally* `¬ COLc G run Y (ω.cOutAt Y) (fun i => Zone G run ω.zone Y i)`
     (`Iff.rfl`), the shape the s3 lemCOL(c) Spec takes.
  4. lemExpect as `(law G run).expect (fun ω => 80 * (dem ω : ℝ) + 369 * (lp ω : ℝ)) ≤ epsU Dstar * G.card`;
     (eqPl) as `Σ_{Z ∈ (run.lightParts G).filter (¬ demoted ω ·)} |Pl ω Z| ≤ 2n + lp ω`
     (needs `open Classical`, COSMETIC-2).
  5. lemChild Tier-1: `∀ ω ∈ (law G run).supp, ∀ Z ∈ run.lightParts G, ¬ demoted ω Z → ∀ H0,
     H0Adm ω Z H0 → ∃ Hobj D as, Hobj ⊆ H0 ∧ Disjoint Hobj (arcEdges as) ∧ Hobj ∪ arcEdges as = H0
     ∧ IsDecomp ↑Hobj D ∧ D.length ≤ 369 * (Pl ω Z).card ∧ ArcSys ω Z H0 as`; and the full PV
     hypothesis list of blueprint_s4 (PVSize, `O.verts = Z`, expansion of `O` and of every own
     class, `IsHBFamily D.O (pvM D.Z.card) (pvB D.Z.card) D.A`, `2^145 L^41 ≤ sOwn`, pairwise
     edge-disjointness incl. `M`, `Rt ⊔ Pl = Z`, (E1′)) typechecks on `childData ω Z` with no
     cast; `Rt ⊔ Pl = Z` and (E1′) are already Lib facts (`disjoint_Rt_Pl`, `Rt_union_Pl`,
     `E1_childData` + `Pl_subset`); `logb 2 (childData ω Z).Z.card = run.LY G Z` and
     `(childData ω Z).R (j, c) = ownR … j c` are `rfl`.
  6. **Theorem `arcSys_of_pv`** (proved, 0 sorry): for light `Z`, `H0Adm ω Z H0`, and the arc
     part of the PV conclusion in the blueprint-s4 shape for `childData ω Z`
     (`IsPathDecomp ↑(H0 \ Hobj) (arcs.map Prod.fst)`, ends `∃ x ∈ D.Rt`, `∀ x ∈ a.1, D.ext x ≠
     some a.2`, `arcs.length ≤ 4(pvJ |Z| + 1)|Z|`, `pathEndCount ≤ degE H0`, `∀ x ∈ O.verts,
     degE H0 x ≤ |Z| - 1`, `Rt = ∅ → arcs = []`), `ArcSys ω Z H0 arcs` holds. The `x ∉ Z` case
     of the `≤ |Z|-1` clause uses `H0 ⊆ E_l(Z) ⊆ V(Z).sym2` (`degE H0 x = 0`), the zone clause
     uses `not_mem_Zone_of_zonePhase_ne`, the length bound is `4 ≤ 14`.
  7. lemParent (A) and (B) in the blueprint shape, with `ArcHyp`, `bundleEdges`, `lentUAvail`,
     `IsConnector` (guarded by `Y ∈ goodParents ω l`, `σ < Tslot G run Y`), pairwise disjointness of
     the four `LentU_{l,c}`, `cap`, `Jbar G run l`, `run.M G l`, `run.nuAnc G l`,
     `run.lam G (l - 2)`, `epsChain Dstar`. Step 6 (a good parent's class `LU_{Y,l,c,σ}` is
     `(2^{12}L_Y^4, t_Y)`-path connected through its zone) and Step 2 (`par` of an arc end is a
     good parent of round `≤ l-2` containing it) proved from `goodParent`, `mem_IU`, `ArcHyp`,
     `mem_Rt_iff_parU`, `parU_spec`.
  8. K-RED: `Kstd` from `run.Std`/`run.E`, `LentExtHyp` from `LJS`/`LJV`/`lateRounds`/`KJS`,
     the conclusion with `IsDecomp ↑(G.edges \ Kstd \ ⋃ Lext)` and the cost
     `(D/2 + 745 + epsChain D) n + 80 dem + 369 lp`; `H0Adm ω Z (E_l(Z) \ Lrem)` from
     `Own_Z ⊆ E_l(Z)` and `Disjoint Own_Z Lrem` (the round-step hypothesis of K-RED (1)).
  9. s6 record `StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)` (no cast); edge cases:
     standalone `Y` never parent-bad, `E1` vacuous for `r(Y) > R`, `Jbar = 0` with no light
     part of round `l`.

## Back-translation, definition by definition

| Lean | Reads as | Manuscript (quoted in the docstring) | Match |
|---|---|---|---|
| `EG.IsHBFamily X m b A` | ∀ w ∈ V(X): A w ⊆ N_X(w) ∧ \|A w\| = m; ∀ u : V, #{w ∈ V(X) : u ∈ A w} ≤ b | s3:lemHB "every vertex `w` has a set `A(w) ⊆ N_X(w)` with `\|A(w)\| = m`, such that every vertex of `X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`" | yes; `∀ u : V` ⇔ `∀ u ∈ V(X)` since `A w ⊆ N_X(w) ⊆ V(X)` (docstring says so); neutral namespace, imports only `EG.Defs.Graph` |
| `vm G run Y`, `vb G run Y` | `pvM \|V(Y)\|`, `pvB \|V(Y)\|` = `⌈L_Y^6⌉₊`, `⌈2^7 L_Y^2 vm⌉₊` (`vm_eq`, `vb_eq` rfl) | "`vm_Y := ⌈L_Y^6⌉`, `vb_Y := ⌈2^7L_Y^2vm_Y⌉`"; lemHB `b = ⌈2mL²/ε'⌉ = ⌈128L²m⌉` at `ε' = 2^{-6}` | yes (`2/2^{-6} = 2^7`) |
| `AY G run Y` | `Classical.epsilon (IsHBFamily X_Y vm vb)` | "provides sets `A_Y(w) ⊆ N_{X_Y}(w)` … We fix one such family by a fixed rule; it depends only on the run" | yes: a function of `G run Y` only; `AY_spec` under existence (StagesHBStatement) |
| `E1 ω Y` | ∀ l ∈ [r(Y), R], ∀ w ∈ V(Y): `L_Y^5/8 ≤ #{u ∈ A_Y(w) : wu ∈ E(M_Y) ∧ zonePhase ω.zone l u = none}` | "(E1) holds for `Y` if for every round `l` with `r ≤ l ≤ R` and every `w ∈ Y`: `#{u ∈ A_Y(w) : wu ∈ M_Y and u carries no round-l zone} ≥ L_Y^5/8`" | yes; `M_Y = ownM` = own label `4J_Y` via `ownIdx … none` (the same bijection `ownR` uses, so `M` is one label everywhere: CHILD-PV-INTERFACE); "carries no round-`l` zone" = `zonePhase = none` by s5:defZones (`zonePhase_eq_none_iff`) |
| `demoted ω Y` | `¬E1 ∨ ¬COLa G run Y (ω.cOutAt Y)` | "(E1) fails for `Y` or a COL(a) event fails for `Y`, that is, …" (the four-item list) | yes; for light `Y`, `COLa_iff_of_isLight` unfolds to exactly the list with `(2^{-6}, s_r/8)`, `s_r/(16k_lend)`, `s_r/(16k_own)` (`demoted_iff_of_isLight`) |
| `parentBad ω Y` | `¬COLc … (fun i => Zone G run ω.zone Y i)` | "for some `(l,c,σ)` with `r+2 ≤ l ≤ R`, `c ∈ [4]`, `σ ∈ [T^sl_Y]`, the class `LU_{Y,l,c,σ}` is not `(2^{12}L_Y^4, t_Y)`-path connected through `Zone_{Y,l,c,σ}` (multiset sense)" | yes (`parentBad_iff_of_isLight`; `IsPathConnected` is the indexed-family = multiset form; `t_Y = tY` cast to ℝ inside `COLc`); "if `r ≥ R-1` … never parent-bad" = `not_parentBad_of_R_lt`; standalone never parent-bad |
| `goodParent`, `Bad` | light ∧ ¬dem ∧ ¬pb; `lightParts.filter (dem ∨ pb)` | verbatim | yes |
| `goodParents ω l` | `lightParts.filter (goodParent ∧ r(Y)+2 ≤ l)` | "good parent of round `≤ l-2`" (Rt, par, Step 2 nodes, (i)) | yes; `∅` for `l ≤ 2` |
| `Rt ω Z`, `Pl ω Z` | `V(Z) ∩ ⋃_{Y ∈ goodParents Z.1} V(Y)`; `V(Z) \ Rt` | "`Rt(Z) := Z ∩ ⋃{Y : Y a good parent of round ≤ l-2}`, `Pl(Z) := Z \ Rt(Z)`" | yes (`l = r(Z)`; total in `Z`) |
| `parU ω l v` | `some` of a min-round element of `{Y ∈ goodParents l : v ∈ V(Y)}` if nonempty, else `none` | "the good parent of the smallest round `≤ l-2` that contains `v` … depends only on `v` and on the round `l`" | yes; `parU_spec`, `mem_Rt_iff_parU`; tie-break by `Classical.epsilon` (unique under propStructure (iv), a Spec) |
| `dem ω`, `lp ω` | `Σ_{Y light, demoted} \|V(Y)\|`; `Σ_{Y ∈ Bad} \|V(Y)\| (R - r(Y))` in ℕ | "`dem := Σ_{Y demoted}\|Y\|`, `lp := Σ_{Y∈Bad}\|Y\|(R-r(Y))`" | yes; `R - r(Y)` exact (`Bad ⊆ lightParts ⊆ parts`, rounds in `[1,R]`) |
| `Vortex.PVData V` | record `Z O sO A R M sOwn Rt Pl ext`, `R : Fin (pvJ Z.card) × Fin 4 → FGraph V`, `ext : V → Option (Fin 4)` | s4:lemPV data list (quoted); `J = ⌊log₂(L/8)⌋`, `m`, `b` are parameters of `N = \|Z\|`, not data | yes; `sO`, `sOwn` are fields because the hypotheses `2m ≤ s_O`, `s' ≥ 2^{145}L^{41}` are about them |
| `childData ω Z` | `Z = V(Z)`, `O = X_Z`, `sO = s_l/2`, `A = A_Z`, `R (j,c) = R_{j,c}`, `M = M_Z`, `sOwn = s_l/(16k_own)`, `Rt`, `Pl`, `ext v = zonePhase ω.zone l v` | s5:lemChild's four bullets + its proof's "`O = X_Z` is a spanning `(2^{-6}, s_l/2)`-expander", "`s' := s_l/(16k_own)`" | yes; index type of `R` is definitionally that of `ownR` (`childData_R` rfl, `JY = pvJ \|V(Z)\|`); `ext` is PV-EXT-ENCODING (`none` = `*`), well defined by construction |
| `Arc V`, `arcEdges as` | `List V × Fin 4`; `(⋃ walkEdges).toFinset` | lemChild (b) "paths … each carrying a phase `c ∈ [4]`" | yes |
| `childParts ω l` | `lightParts.filter (Z.1 = l ∧ ¬demoted)` | "the letter `Z` ranges over the non-demoted light parts of round `l`" | yes |
| `H0Adm ω Z H0` | `E(Own_Z) ⊆ H0 ∧ H0 ⊆ E_l(Z)` | lemParent/lemChild "`Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`" | yes |
| `ArcSys ω Z H0 as` | jointly `Nodup` edge lists; each arc `IsPathIn H0`, `≥ 1` edge, both ends in `Rt(Z)`, every vertex `∉ Zone_{Y,l,c,σ}` for all `Y σ`; `#as ≤ 14(J_Z+1)\|Z\|`; `pathEndCount ≤ deg_{H0}` and `≤ \|Z\|-1`; `Rt = ∅ → as = []` | lemChild (b), (c), (d) (quoted) | yes; the `IsPathIn H0` clause is the "H^arc(Z) ⊆ H_0(Z)" part of (b) and gives (F-d)'s implicit facts (`ArcSys.mem_verts`, `head_ne_getLast`); the two redundant clauses are documented as such |
| `ArcHyp ω l H0 arcs` | `∀ Z ∈ childParts ω l, H0Adm ∧ ArcSys` | lemParent hypothesis "for every non-demoted light part `Z` of round `l`, an edge set `H_0(Z)` with `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`; the arcs of `Z` are those given by Lemma lemChild" (read as "any arcs with (b)–(d)", PAR-ARCS-INPUT) | yes |
| `bundleEdges ω l arcs c` | `⋃_{Z ∈ childParts l} arcEdges (phase-c arcs of Z)` | "`B_{l,c}` is the set of all phase-`c` arcs of all non-demoted light parts of round `l`; `E(B_{l,c})` the union of their edge sets" | yes (edge set only; the arcs themselves are `arcs Z`) |
| `lentUAvail ω l c` | `⋃_{Y ∈ goodParents l} ⋃_{σ < T^sl_Y} E(LU_{Y,l,c,σ})` | (i) "`⋃_Y ⋃_{σ∈[T^sl_Y]} LU_{Y,l,c,σ}`, the union over the good parents `Y` of rounds `≤ l-2`" | yes (`σ` 0-based as in `IU`) |
| `IsConnector ω l c Y σ p` | `IsPathIn E(LU_{Y,l,c,σ}) p ∧ IsThrough Zone_{Y,l,c,σ} p` | (i) "a *connector*, a path in `LU_{Y,l,c,σ}` all of whose interior vertices lie in `Zone_{Y,l,c,σ}`" | yes (total in `Y`, `σ`: COSMETIC-1) |
| `Jbar G run l` | `sup_{Z light, Z.1 = l} J_Z` | "`J̄_l := max{J_Z : Z a light part of round l}` (and `0` if there is none)" | yes |
| `epsU D` | `2462 · (log₂ D)^{-205}` (zpow) | s5:lemExpect "`ε_U(D_*) := 2462 (log₂ D_*)^{-205}`" | yes (parse checked) |
| `epsChain D` | `EG.Chain.epsK D` | s5:lemParent (ii) formula = s5:lemKRED "`ε_K := ε_ch`" | yes; one copy of the formula (G-S5-1), `epsChain_eq` compared term by term with the TeX; `EG/Defs/Quot/Constants.lean` already reads `Light.epsU` and `epsK`, so no second copy exists anywhere |

Probability laws: this task introduces no law and changes none. Each status reads exactly the
coordinates the last sentence of s5:defStages names — (E1): `ω.colAt Y` (the colouring of `Y`)
and `ω.zone` (choices and sublabels); COL(a): `ω.colAt Y` only (`COLa` reads `ω.1`); parent-bad:
`ω.colAt Y` and the zones of `Y` (`Zone G run ω.zone Y ·`). Nothing reads `ω.js`, `ω.pool`, any
later edge set or any later random choice. `AY` is a function of the run alone, as the text
requires for lemE1 (a) ("The sets `A_Y(w)` are fixed").

## Downstream statability (blueprint_s5 and the s6/s7 consumers)

| Consumer | Needs from this task | Status |
|---|---|---|
| StagesHBStatement, EqPlStatement | `vm`, `vb`, `AY`, `IsHBFamily (run.X …)`; `Pl`, `demoted`, `lp`, `Bad` (for propParentless (iii)) | statable (scratch 4) |
| lemE1 (a)(b)(c) | `E1`, `demoted`, `Bad`; (c) = lemCOL(c) with `Vs := Zone … Y` | statable, event literally `¬ COLc` (scratch 3) |
| lemExpect | `dem`, `lp`, `epsU`, `tendsto_epsU` | statable (scratch 4); limit provided |
| lemChild Tier-1/Tier-2 (P-4) | `childData` as a `PVData`, `H0Adm`, `ArcSys`, `Pl`, `E1_childData` | statable; PV hypotheses typecheck with no cast; **PV conclusion ⟹ `ArcSys` proved** (scratch 5–6) |
| lemParent (A)/(B) (P-4) | `ArcHyp`, `bundleEdges`, `lentUAvail`, `IsConnector`, `goodParents`, `parU`, `Jbar`, `run.nuAnc`, `run.M`, `run.lam`, `epsChain`, `tendsto_epsChain`; Step 5 `tY`, Step 6 `¬parentBad` | statable (scratch 7) |
| lemDemoted (1) | `not_goodParent_of_demoted` | provided |
| K-RED | `dem`, `lp`, `demoted`, `childParts`, `ArcHyp`, `H0Adm`, `Pl`, `epsChain`; `Kstd`/`LentExtHyp` inline from `run.Std`, `run.E`, `Stage1.LJS/LJV` (outside this task, as in round 1) | statable (scratch 8) |
| s6 `StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)`, `lendBad` (`isLight ∧ demoted`), `XU = 80 dem + 369 lp` | types `PartId → Prop`, `ℕ`, `ℕ` | tested, no cast |
| s7 `Quot.epsX`, `eps1`, `Gamma4`, lemGammaSat | `Light.epsU`, `epsK = epsChain`, the two limits | already wired (`EG/Defs/Quot/Constants.lean`, `EG/Lib/Quot/Constants.lean`) |

## Round-1 items (all correctly resolved)

- MINOR-1: `ArcSys` (lemChild (b)–(d) per part, with `l := Z.1`) and `H0Adm` exist; `ArcHyp` is
  `∀ Z ∈ childParts ω l, H0Adm ∧ ArcSys` (`ArcHyp_iff` is `Iff.rfl`). The lemChild Spec can
  conclude `ArcSys` directly (scratch 5–6). Correct.
- MINOR-2: `EG.Vortex.PVData` in `EG/Defs/Vortex/PVData.lean` is the canonical record; `J`, `m`,
  `b` are not fields; `R` is indexed by `Fin (pvJ Z.card) × Fin 4` with `Z` the vertex-set field;
  `childData ω Z : PVData V` fills `R` with no cast. Recorded in TRIAGE §2.8 (PV-DATA-RECORD).
  Correct; the design change (dropping the free field `J`) removes a hypothesis the PV Spec would
  otherwise need and cannot introduce a mismatch, since `pvJ` is defined once in `EG.Defs.Vortex`.
- MINOR-3: `EG.IsHBFamily` in `EG/Defs/Link/HBFamily.lean` (imports `EG.Defs.Graph` only), same
  body. Recorded (HB-FAMILY). Correct; the locked `Expander.lean`/`Vortex.lean` were rightly not
  touched.
- MINOR-4: lock check reproduced here: 0 violations.
- COSMETIC-1: the `ArcSys` docstring names both redundant clauses and why. Correct.
- COSMETIC-2: the three `IsHBFamily` examples on `K_3` are in `EGTest/Light.lean` (`decide`);
  the multi-round test run remains open (COSMETIC-3 below).

## Issues (none blocks the lock)

### COSMETIC-1 — `IsConnector` and `lentUAvail`: add the `(Y, σ)` guard to the design note
`IsConnector ω l c Y σ p` is total in `Y : PartId` and `σ : ℕ`; a lemParent (i) Spec must read it
only at `Y ∈ goodParents ω l` and `σ < Tslot G run Y` (the blueprint's `IsConnectorEdge` has both;
scratch 7 writes them). The "Guards for Spec authors" list in `light.md` does not mention this.
One line to add. No code change.

### COSMETIC-2 — `demoted` has no `Decidable` instance: Spec filters need `open Classical`
`(run.lightParts G).filter (fun Z => ¬ demoted ω Z)` (eqPl's summation set, K-RED's round sets)
fails to elaborate without `open Classical in` / `classical` (scratch 4 hit this). The Defs
themselves use `open Classical in` correctly (`Bad`, `goodParents`, `childParts`, `dem`). One
line for the guard list; the s3/Stage-1 Defs have the same property, so this is a general
CONVENTIONS remark rather than an s5 defect.

### COSMETIC-3 — non-vacuity beyond the one-round `K_3` run (carried from round 1)
Still no concrete run in which `demoted`, `parentBad`, `Rt ≠ ∅`, `parU = some _` or a nonempty
`ArcSys` occurs (it needs `R ≥ 3` and `L_Y > 0`). Round 1 classed this P2b/P3, and I agree: the
predicates are non-trivial by inspection (each clause was exercised in scratch 6–7 in the
generic setting, and `arcSys_of_pv` shows the arc clauses are exactly PV's). Not a blocker.

## Edge cases re-checked

- `r(Y) ≥ R-1`: `IU = ∅` ⇒ never parent-bad; `lentIdx = ∅` ⇒ no lent COL(a) conjunct; the real
  division `s_r/(16·0)` is never read. `|V(Y)| = 1`: `L_Y = 0`, `vm = 0`, `Tslot = 0`, `IU = ∅`,
  (E1) trivially true, `IsHBFamily X 0 b (fun _ => ∅)` holds.
- `l ≤ 2`: `goodParents = ∅`, `Rt = ∅`, `Pl = V(Z)`, `parU = none`, so lemChild (d) "in particular
  if `l ≤ 2`" is `Rt_eq_empty_of_le_two`.
- Junk arguments: standalone `Y` (statuses defined, `parentBad` false, consumers guard by
  `lightParts`); `r(Y) > R` (`E1` vacuous, `R - r(Y) = 0`, never in `Bad`); `Z ∉ childParts`
  (its `H0 Z`, `arcs Z` are never read by `ArcHyp`/`bundleEdges`); `x ∉ V(G)` (`zoneOf = none`,
  so `zonePhase = none`, `x` in no zone).
- Off-support `ω`: a zone label with a JS/JV tag gives `zonePhase = none` and an empty zone; the own
  classes may fail to partition `Own_Y`; every statement quantifies `ω ∈ (law G run).supp`
  (STAGES-STAGE1-SUPPORT), and no Def depends on it.
- `epsU`, `epsChain` for small `D` (`log ≤ 0`): real junk; every use assumes Γ; the limits hold
  regardless.

## Summary for the orchestrator

Lock `EG/Defs/Light/Stages.lean`, `EG/Defs/Light/Constants.lean`, `EG/Defs/Link/HBFamily.lean`
and `EG/Defs/Vortex/PVData.lean` as they are. The three cosmetic items are one-line additions to
`light.md`'s guard list (and one CONVENTIONS remark), plus the already-planned richer test run.
No T1/T2 manuscript issue found; the readings recorded in `light.md` (D-L-1 … D-L-7, the
"any arcs with (b)–(d)" reading of lemParent's hypothesis, the round argument of `par`) are the
ones the proofs need, and the PV → `ArcSys` transfer confirms that probe P-4's two s5 sites
(lemChild, lemParent) can be stated and chained on these Defs without re-encoding.
