# P2-D [light]: stage-2 statuses of light parts, child data, arc hypotheses, ε_U, ε_ch (s5:defStages; s5 constants)

Status: 2 Defs files, 2 Lib files and 1 test file compile with 0 errors, 0 warnings and 0 `sorry`
(`scripts/check.sh`, `LEAN_NUM_THREADS=2`; `lake build EG.Lib.Light.Stages EG.Lib.Light.Constants` succeeds).
`python3 -I scripts/lint.py`: 0 findings. `python3 scripts/lock.py check`: 0 violations (the new Defs are
PENDING). Axiom scan `lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.Light.Stages EG.Lib.Light.Constants`:
1928 constants, 0 `sorryAx`, 0 meta-scan hits, 0 violations.

Manuscript: `proofs/manuscript/s5.tex` v6.1 — setting paragraph (l. 9–24), Definition s5:defStages (l. 79–109),
Lemma s5:lemChild (l. 163–186, the PV data), Lemma s5:lemParent (preamble, statement and (F-a)–(F-d), l. 205–246),
Lemma s5:lemExpect (ε_U), s5:lemParent (ii) (ε_ch). TRIAGE §3 items 19 and 20.

Built on the **locked** HB Run model (`EG.HB.Run`, `PartId`, `run.lightParts/ancVerts/ancGraph/X/E/LY/s/lam/M/nuAnc`)
and the Stage-1 layer (`EG.Stage1.Outcome`, `COLa`, `COLc`, `Own`, `ownR`, `ownM`, `LU`, `JY`, `kown`, `Tslot`,
`tY`, `Zone`, `zonePhase`), both unchanged. No existing file was changed. The root files `EG.lean`, `EGTest.lean`
are not edited.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Link/HBFamily.lean` | `EG.Defs.Link.HBFamily` | `EG.IsHBFamily` (fix round 1: moved here from `Light.Stages`) |
| `EG/Defs/Vortex/PVData.lean` | `EG.Defs.Vortex.PVData` | `EG.Vortex.PVData` (fix round 1: the canonical Lemma-PV data record, replaces `EG.Light.ChildData`) |
| `EG/Defs/Light/Stages.lean` | `EG.Defs.Light.Stages` | `vm`, `vb`, `AY`, `E1`, `demoted`, `parentBad`, `goodParent`, `Bad`, `goodParents`, `Rt`, `Pl`, `parU`, `dem`, `lp`; `childData` (a `Vortex.PVData`); `Arc`, `arcEdges`, `childParts`, `H0Adm`, `ArcSys`, `ArcHyp`, `bundleEdges`, `lentUAvail`, `IsConnector`, `Jbar` |
| `EG/Defs/Light/Constants.lean` | `EG.Defs.Light.Constants` | `epsU`, `epsChain` (`:= EG.Chain.epsK`) |
| `EG/Lib/Light/Stages.lean` | `EG.Lib.Light.Stages` | `vm_eq`, `vb_eq` (rfl), `AY_spec`; `isLight_of_mem_lightParts`, `X_verts_of_isLight`, `ancGraph_eq_X_of_isLight`, `E_subset_sym2`, `mem_partVerts_of_mem_E`; `demoted_iff(_of_isLight)`, `parentBad_iff_of_isLight`, `not_parentBad_of_R_lt`, `not_parentBad_of_not_isLight`, `mem_Bad`, `Bad_subset_lightParts`, `goodParent_iff_not_mem_Bad`, `not_goodParent_of_demoted`, `mem_goodParents`, `goodParents_eq_empty_of_le_two`; `mem_Rt`, `mem_Pl`, `Rt_subset`, `Pl_subset`, `disjoint_Rt_Pl`, `Rt_union_Pl`, `Rt_eq_empty_of_le_two`, `Pl_eq_of_le_two`, `parU_isSome_iff`, `parU_spec`, `mem_Rt_iff_parU`; `not_mem_Zone_of_zonePhase_ne`, `mem_arcEdges`, `mem_bundleEdges`, `mem_childParts`, `ArcSys.mem_verts`, `ArcSys.head_ne_getLast`, `ArcSys.nil`, `ArcHyp_iff`, `ArcHyp.mem_verts`, `ArcHyp.head_ne_getLast`, `ArcHyp.nil`; `childData_*` simp lemmas (incl. `childData_R`, `childData_M`), `childData_J` (`JY G run Z = pvJ (childData ω Z).Z.card`, rfl), `E1_childData` |
| `EG/Lib/Light/Constants.lean` | `EG.Lib.Light.Constants` | `epsChain_eq_epsK` (rfl), `epsU_eq`, `epsChain_eq`, `epsU_pos`, `epsU_nonneg`, `logb_two_le_two_mul`, `tendsto_epsU`, `tendsto_epsChain_aux`, `tendsto_epsChain` |
| `EGTest/Light.lean` | — | constants (`ε_U(2) = 2462`, limits), PV index type without cast, (E1) ⇒ (E1'), generic status facts, the s6 record `StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)` and its coherence on the support; on the valid run `run1` on `K_3`: (E1), COL(a), not demoted, not parent-bad, good parents, `Bad = ∅`, `dem = lp = 0`, `Rt = ∅`, `Pl = V(Z)`, `par` undefined, `ArcHyp` of the empty arc systems; `childData` is a `Vortex.PVData`; `ArcHyp` from per-part `ArcSys`; `IsHBFamily` on `K_3` (one true instance, the size and the multiplicity clause each refuting one) |

Size (after fix round 1): Defs 295 + 38 + 36 + 70 lines, Lib 412 + 116 lines, tests 262 lines.

Root imports for the orchestrator to add: to `EG`: `EG.Defs.Link.HBFamily`, `EG.Defs.Vortex.PVData`, `EG.Defs.Light.Stages`, `EG.Defs.Light.Constants`,
`EG.Lib.Light.Stages`, `EG.Lib.Light.Constants`; to `EGTest`: `EGTest.Light` (imports `EGTest.HB`).

## Definitions, with the manuscript text

All in namespace `EG.Light`. Functions of the run alone take `G run` explicitly and first (Stage-1 convention
D-S1-1): `vm G run Y`, `vb G run Y`, `AY G run Y`, `Jbar G run l`. Functions of a stage-1 outcome
`ω : EG.Stage1.Outcome G run` take `G run` **implicitly** (decision D-L-1).

| Lean | Manuscript (s5:defStages unless said) | Encoding |
|---|---|---|
| `IsHBFamily X m b A` | s3:lemHB conclusion: "`A(w) ⊆ N_X(w)` with `\|A(w)\| = m`, every vertex in at most `b` of the sets" | count over `w ∈ V(X)`, the shape of the lemHB Spec (blueprint s3b) |
| `vm G run Y` | "`vm_Y := ⌈L_Y^6⌉`" | `Vortex.pvM \|V(Y)\|` (same term; `vm_eq` rfl) |
| `vb G run Y` | "`vb_Y := ⌈2^7 L_Y^2 vm_Y⌉`" | `Vortex.pvB \|V(Y)\|` (`vb_eq` rfl) |
| `AY G run Y` | "provides sets `A_Y(w)` … We fix one such family by a fixed rule; it depends only on the run" | `Classical.epsilon (IsHBFamily (run.X G Y.1 Y.2) vm vb)`; `AY_spec` |
| `E1 ω Y` | "(E1) holds for `Y` if for every round `l` with `r ≤ l ≤ R` and every `w ∈ Y`: `#{u ∈ A_Y(w) : wu ∈ M_Y and u carries no round-l zone} ≥ L_Y^5/8`" | `M_Y = ownM G run Y (ω.colAt Y)`; "no round-`l` zone" = `zonePhase ω.zone l u = none` |
| `demoted ω Y` | "(E1) fails for `Y` or a COL(a) event fails for `Y`" | `¬ E1 ω Y ∨ ¬ Stage1.COLa G run Y (ω.cOutAt Y)`; the explicit list: `demoted_iff_of_isLight` |
| `parentBad ω Y` | "for some `(l,c,σ)` with `r+2 ≤ l ≤ R`, `c ∈ [4]`, `σ ∈ [T^sl_Y]`, the class `LU_{Y,l,c,σ}` is not `(2^{12}L_Y^4, t_Y)`-path connected through `Zone_{Y,l,c,σ}`" | `¬ Stage1.COLc G run Y (ω.cOutAt Y) (Zone G run ω.zone Y ·)` (D-L-3); explicit form: `parentBad_iff_of_isLight` |
| `goodParent ω Y` | "a light part that is neither demoted nor parent-bad" | includes `Y ∈ run.lightParts G` |
| `Bad ω` | "`Bad := {demoted light parts} ∪ {parent-bad light parts}`" | `Finset PartId` |
| `goodParents ω l` | "the good parents of rounds `≤ l-2`" (Rt(Z); the nodes of `UQ_{l,c,i}`) | `Y.1 + 2 ≤ l`; empty for `l ≤ 2` |
| `Rt ω Z`, `Pl ω Z` | "`Rt(Z) := Z ∩ ⋃{Y : Y a good parent of round ≤ l-2}`, `Pl(Z) := Z \ Rt(Z)`" | `l = Z.1`; total in `Z` |
| `parU ω l v` | "the good parent of the smallest round `≤ l-2` that contains `v`" | `Option PartId` (D-L-4) |
| `dem ω`, `lp ω` | "`dem := Σ_{Y demoted}\|Y\|`", "`lp := Σ_{Y∈Bad}\|Y\|(R - r(Y))`" | `ℕ`; `R - Y.1` exact since `Y.1 ≤ R` for light parts |
| `Vortex.PVData`, `childData ω Z` | s5:lemChild "Apply Lemma PV to the vertex set `Z` with the following data: `O := H_Z = X_Z`, `A(w) := A_Z(w)`, own classes `R_{j,c}` (`0 ≤ j < J_Z`) and `M = M_Z`, `Rt := Rt(Z)`, `Pl := Pl(Z)`, `ext(v) := c` / `*`"; `s_O = s_l/2`, `s' = s_l/(16k_own)` from its proof | record with fields `Z O sO A R M sOwn Rt Pl ext`, `R` indexed by `Fin (pvJ Z.card) × Fin 4` (D-L-5, fix round 1) |
| `Arc V`, `arcEdges` | lemChild (b): arcs are paths "each carrying a phase `c ∈ [4]`" | `List V × Fin 4` |
| `childParts ω l` | "the non-demoted light parts of round `l`" | |
| `H0Adm ω Z H0`, `ArcSys ω Z H0 as` | "`Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`"; lemChild (b)–(d) for one part | D-L-6 (fix round 1) |
| `ArcHyp ω l H0 arcs` | lemParent hypotheses + lemChild (b)–(d) as used in (F-d) | `∀ Z ∈ childParts ω l, H0Adm ∧ ArcSys` (D-L-6) |
| `bundleEdges ω l arcs c` | "the U-bundle `B_{l,c}` is the set of all phase-`c` arcs of all non-demoted light parts of round `l`; `E(B_{l,c})` the union of their edge sets" | |
| `lentUAvail ω l c` | lemParent (i) "`⋃_Y ⋃_{σ∈[T^sl_Y]} LU_{Y,l,c,σ}`, the union over the good parents `Y` of rounds `≤ l-2`" | |
| `IsConnector ω l c Y σ p` | lemParent (i) "a *connector*, a path in `LU_{Y,l,c,σ}` all of whose interior vertices lie in `Zone_{Y,l,c,σ}`" | `IsPathIn … ∧ IsThrough …` |
| `Jbar G run l` | "`J̄_l := max{J_Z : Z a light part of round l}` (and `0` if there is none)" | `Finset.sup` in `ℕ` |
| `epsU D` | s5:lemExpect "`ε_U(D_*) := 2462 (log₂ D_*)^{-205}`" | `zpow` |
| `epsChain D` | s5:lemParent (ii) `ε_ch` | `EG.Chain.epsK D` (G-S5-1: one copy of the formula) |

## Decisions

**D-L-1 (implicit `G run` for functions of `ω`).** `demoted ω Y`, `dem ω`, `lp ω`, `Rt ω Z`, `Pl ω Z`, `parU ω l v`,
`Bad ω`, `goodParents ω l`, `childData ω Z`, `ArcHyp ω l H0 arcs`, … read `G` and `run` from the type of
`ω : Stage1.Outcome G run` (as `Outcome.colAt/cOutAt/labAt` and `StageData.ofOutcome` do). TRIAGE item 20 writes
`demoted ω run G`; the types it asks for are kept exactly (`demoted ω : PartId → Prop`, `dem ω lp ω : ℕ`), so the s6
record is `StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)` with no cast (tested, and `coherent_ofOutcome` applies).

**D-L-2 (vm, vb, A_Y).** `vm`/`vb` are defined as `Vortex.pvM`/`Vortex.pvB` at `N = |V(Y)|` — the same terms as
`⌈L_Y^6⌉₊`, `⌈2^7 L_Y^2 vm_Y⌉₊` (`rfl`) — so the sets `A_Z` have literally the parameters Lemma PV requires.
`A_Y := Classical.epsilon (IsHBFamily X_Y vm_Y vb_Y)`: total, a function of the run only ("depends only on the
run"). The graph is `run.X G Y.1 Y.2` (the text: "applied to `X_Y`"); for light `Y`, `run.ancGraph G Y = X_Y` and
`V(X_Y) = V(Y)` (`ancGraph_eq_X_of_isLight`, `X_verts_of_isLight`). The existence of a family (Γ, validity, lemHB)
and "`2vm_Y ≤ s_r/2`" are the StagesHBStatement Spec, not Defs.

**D-L-3 (statuses reuse the Stage-1 events; total, no light guard).** "COL(a) fails" is `¬ Stage1.COLa`, and
parent-bad is `¬ Stage1.COLc` for the zone family of `Y` — the exact events of s3:lemCOL (a), (c), so that the
s5:lemE1 (b), (c) proofs apply the COL Specs without re-encoding (lemE1 (c): "Lemma s3:lemCOL(c), applied with this
family"). For light `Y` they unfold to the lists of s5:defStages (`demoted_iff_of_isLight`,
`parentBad_iff_of_isLight`; the index set `I^U(Y)` is exactly `{(l,c,σ) : r+2 ≤ l ≤ R, c ∈ [4], σ < T^sl_Y}`).
"If `r ≥ R-1` … never parent-bad" is `not_parentBad_of_R_lt`. `demoted` and `parentBad` are defined for every
`Y : PartId` (junk for standalone `Y`, where `parentBad` is always false); `Bad`, `dem`, `goodParent` restrict to
light parts, and s6 `lendBad` carries its own light guard (TRIAGE item 20).

**D-L-4 (`par(v)` takes the round).** "`par(v)` depends only on `v` and on the round `l` of the part in which it is
used": `parU ω l v : Option PartId`, `some` of a good parent of round `≤ l-2` containing `v` with the smallest round
(`Classical.epsilon` of the minimality property; unique by s2:propStructure (iv), which is a Spec), `none` iff there is
none. `v ∈ Rt(Z) ↔ v ∈ V(Z) ∧ (parU ω Z.1 v).isSome` (`mem_Rt_iff_parU`); `parU_spec` gives the properties. The
blueprint's `l`-free `parU ω v` is not used: with `l` the definition is literal and needs no uniqueness to be
meaningful.

**D-L-5 (the child data record; revised in fix round 1).** `childData ω Z` is a value of the canonical Lemma-PV
record `EG.Vortex.PVData V` (`EG/Defs/Vortex/PVData.lean`; TRIAGE §2.8 PV-DATA-RECORD): the eight data of the lemChild
instantiation plus `sO`, `sOwn`. Its own-class family is `R : Fin (pvJ Z.card) × Fin 4 → FGraph V` (indexed by the
vertex-set field; `J` is not a field), and `Z := run.ancVerts G Z`, so `JY G run Z` is definitionally
`Vortex.pvJ (childData ω Z).Z.card` (`childData_J`, rfl; the EGTest example checks that a predicate over
`Fin (pvJ Zs.card) × Fin 4 → FGraph V` accepts it with no cast). (Before fix round 1: a record `EG.Light.ChildData`
with a free field `J`.)
**Interface request for the s4 PV Spec (PV-OWNCLASS-INDEX):** index the own classes by `Fin (pvJ Z.card)` where `Z`
is the vertex-set argument of the Spec (with the hypothesis `O.verts = Z`), not by `Fin (pvJ O.card)`:
`(childData ω Z).O.card = |V(X_Z)|` equals `|V(Z)|` only propositionally (for light `Z`, `X_verts_of_isLight`),
so the `O.card` form would force a cast in lemChild. `ext v := zonePhase ω.zone Z.1 v` (`none` = `*`,
blueprint PV-EXT-ENCODING). (E1) at `l = r(Z)` gives (E1') in the child-data form (`E1_childData`; (E1) counts the
vertices `u ∈ A_Z(w)`, the PV Spec's `filter` over `A w` counts the same set).

**D-L-6 (arc hypotheses; PAR-ARCS-INPUT).** lemParent's "the arcs of `Z` are those given by Lemma s5:lemChild for this
`H_0(Z)`" becomes `ArcHyp ω l H0 arcs`: for every non-demoted light `Z` of round `l`,
- `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)` (the lemParent hypothesis on `H_0`);
- (b): the arc edge lists concatenate to a duplicate-free list (pairwise edge-disjoint), each arc is a path in `H_0(Z)`
  (as `H^arc(Z) ⊆ H_0(Z)`) with `≥ 1` edge, both ends in `Rt(Z)`, and every vertex of a phase-`c` arc lies in no
  round-`l` phase-`c` zone, written literally `∀ Y σ, x ∉ Zone_{Y,l,c,σ}`. This is implied by the PV form
  `ext(x) ≠ c` for **every** assignment of the zone labels (`not_mem_Zone_of_zonePhase_ne`), so it is the weaker
  hypothesis;
- (c): `≤ 14(J_Z+1)|Z|` arcs; every `x` is an end (`pathEndCount`) of `≤ deg_{H_0(Z)}(x)` and `≤ |Z| - 1` arcs;
- (d): `Rt(Z) = ∅ → no arcs` (redundant given the ends in `Rt(Z)`; kept for literalness).
Any arc systems with these properties are admissible, so lemParent becomes a deterministic lemma with a more
general input; K-RED feeds it the arcs of the ChildExists corollary. (F-d)'s derived facts are Lib lemmas:
`ArcHyp.mem_verts` (every arc vertex lies in `Z`), `ArcHyp.head_ne_getLast` (two distinct ends). The arcs of
parts outside `childParts ω l` are not read (`bundleEdges` filters them).

**D-L-7 (constants).** `epsU D := 2462 * logb 2 D ^ (-205 : ℤ)`; `epsChain D := EG.Chain.epsK D` (TRIAGE item 20,
G-S5-1). The limits `ε_U → 0` and `ε_ch → 0` (claimed in s5:lemExpect and s5:lemParent, used by s7:lemGammaSat) are
proved as API lemmas `tendsto_epsU`, `tendsto_epsChain` (squeeze `0 ≤ log₂(2A log₂(Ay))/(371y²) ≤ 8A²/(371y)` for
`y = log₂log₂ D ≥ 1`); they depend on no run and no Γ.

## Guards for Spec authors

- Every status is total; read it at light parts `Y ∈ run.lightParts G` and outcomes `ω ∈ (Stage1.law G run).supp`
  (STAGES-STAGE1-SUPPORT; the own classes partition `Own_Y` only on the support, `COLg_of_mem_supp_law`).
- `AY` is meaningful only when a Lemma-HB family exists (StagesHBStatement under RunHyp).
- `parU ω l v` is read at `v ∈ Rt(Z)`, `l = Z.1`; its uniqueness is propStructure (iv).
- `childData ω Z` is meant for a non-demoted light `Z`; its `O.verts = Z` needs `isLight` (`X_verts_of_isLight`).
- `Rt`, `Pl` are total in `Z`; eqPl sums over `(run.lightParts G).filter (¬ demoted ω ·)`.
- `ArcHyp` is about the round-`l` non-demoted light parts only; write rounds as `3 ≤ l ∧ l ≤ run.R` in lemParent.

## Manuscript readings (no T1/T2 found)

- **s5:defStages, par(v).** "the good parent of the smallest round `≤ l-2`": a tie (two good parents of the same
  smallest round containing `v`) is impossible by propStructure (iv); the Def chooses by `Classical.epsilon` and does
  not need the uniqueness (D-L-4).
- **s5:lemParent, "the arcs of `Z` are those given by Lemma s5:lemChild".** lemChild only asserts existence; read as
  "any arcs with the properties (b)–(d) of lemChild" (D-L-6). The proof uses only (F-a)–(F-d).
- **s5:lemChild (b), "lies in no round-`l` phase-`c` zone".** Encoded literally (zone membership), which is implied by
  PV's `ext(x) ≠ c` for every zone-label assignment (no support hypothesis needed).
- **s5:defStages, statuses for `r ≥ R-1` and for standalone parts.** Encoded totally (D-L-3), no law changes.

## Fix round 1 (2026-09-26; review `light.review1.md`)

All six items checked against the files and the manuscript. All are valid. Five are fixed; MINOR-4
is a process item and is resolved by re-running the lock check. Every change is additive or a
relocation inside PENDING files. The meaning of every definition is unchanged except for the record
type (`J` is no longer a field; see MINOR-2).

- **MINOR-1 (valid, fixed).** `ArcHyp` had lemChild (b)–(d) inline. There are now two new per-part
  Defs in `EG.Light`:
  - `H0Adm ω Z H0 := Own_Z ⊆ H0 ∧ H0 ⊆ E_{Z.1}(Z)`;
  - `ArcSys ω Z H0 as`: lemChild (b)–(d), with the old body and `l := Z.1`.

  `ArcHyp ω l H0 arcs := ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z) ∧ ArcSys ω Z (H0 Z) (arcs Z)`.
  This is equivalent to the old body, since `Z.1 = l` on `childParts ω l`. The lemChild Spec
  (Tier-1/Tier-2) takes `H0Adm` as its hypothesis and concludes
  `∃ Hobj as, H0 = Hobj ⊔ arcEdges as ∧ (a) ∧ ArcSys ω Z H0 as`. K-RED then gets `ArcHyp` without
  rebuilding it (EGTest example). I split `H0Adm` off because it is the *hypothesis* of lemChild,
  not part of its conclusion. New Lib lemmas: `ArcSys.mem_verts` (needs `H0Adm`),
  `ArcSys.head_ne_getLast`, `ArcSys.nil`, `ArcHyp_iff`. The `ArcHyp.*` lemmas are now one-line
  corollaries.
- **MINOR-2 (valid, fixed, option 1).** The canonical record is `EG.Vortex.PVData V` in the new
  `EG/Defs/Vortex/PVData.lean`. Its docstring quotes the data list of s4:lemPV, and
  `childData ω Z : Vortex.PVData V` stays in `EG.Light`. `EG.Light.ChildData` is removed; no other
  file used it. One design change: the free field `J` is gone, and the own classes are
  `R : Fin (pvJ Z.card) × Fin 4 → FGraph V`, indexed by the vertex-set field. In lemPV, `J` is
  defined from `N` ("Put `J := ⌊log₂(L/8)⌋`") and is not a datum. So the PV Spec needs no
  hypothesis `D.J = pvJ D.Z.card`, and it cannot mix `D.J` with `pvJ N`. `childData` still fills
  `R` from `ownR` with no cast (`JY G run Z ≡ pvJ |V(Z)|`). The Lib lemma `childData_J` is now
  `JY G run Z = pvJ (childData ω Z).Z.card` (rfl). `m` and `b` are not fields either (`pvM`,
  `pvB`). `sO` and `sOwn` stay fields, because the hypotheses `2m ≤ s_O` and `s' ≥ 2^{145}L^{41}`
  are about them. The decision is recorded in TRIAGE §2.8 (PV-DATA-RECORD), next to
  PV-OWNCLASS-INDEX and PV-EXT-ENCODING. The PV *hypotheses* as named Defs remain with the s4 Spec
  author.
- **MINOR-3 (valid, fixed).** `IsHBFamily` moved, with the same body, to the new
  `EG/Defs/Link/HBFamily.lean` as `EG.IsHBFamily`, which imports only `EG.Defs.Graph`. I did not
  use `EG/Defs/Expander.lean` or `EG/Defs/Vortex.lean`: both are locked by file hash, so appending
  to them would be a lock violation. Inside `namespace EG.Light` the name `IsHBFamily` resolves to
  `EG.IsHBFamily`, so `AY`, `AY_spec` and the tests are textually unchanged. Recorded in TRIAGE
  §2.8 (HB-FAMILY).
- **MINOR-4 (process, resolved).** All `EG/Defs` and `EG/Spec` oleans were present in this session.
  `python3 scripts/lock.py check` gives `419 locked constants, 133 locked files; 0 violations,
  462 pending`; the new Defs are PENDING.
- **COSMETIC-1 (valid, fixed).** The `ArcSys` docstring now says that clause (d) and the bound
  `pathEndCount ≤ |Z| - 1` are redundant, why (ends in `Rt(Z)`; `H_0 ⊆ E_l(Z) ⊆ V(Z).sym2`,
  loopless), and that both are kept for literalness.
- **COSMETIC-2 (valid, partly fixed).** Added to `EGTest/Light.lean`, all proved by `decide`:
  - `IsHBFamily K3 1 1 (fun w => {w+1})`;
  - `¬ ∃ A, IsHBFamily K3 3 10 A`;
  - `¬ IsHBFamily K3 1 0 (fun w => {w+1})`.

  Also added: `childData` as a `Vortex.PVData`, `ArcHyp` from per-part `ArcSys`, and `ArcSys.nil`.
  Still to do (P2b/P3): a multi-round test run in which `demoted` or `parentBad` is true, `Rt ≠ ∅`,
  and an `ArcSys` has a nonempty arc.

Checks after the fix:
- `lake build` of `EG.Defs.Link.HBFamily`, `EG.Defs.Vortex.PVData`, `EG.Lib.Light.Stages` and
  `EG.Lib.Light.Constants`: 0 errors, 0 warnings.
- `scripts/check.sh EGTest/Light.lean`: rc 0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Lock check: 0 violations.
- Axiom scan: 1935 constants, 0 `sorryAx`, 0 violations.
