# P2-D [quot]: the s7 quotient layer (s7:defCand, s7:defSchedule rounds, s7:consRound, X', the s7 constants, Γ4, c_EG): design note

Status: 6 Defs files, 5 Lib files and 1 test file compile with 0 errors, 0 warnings and 0 `sorry`
(`scripts/check.sh`, `LEAN_NUM_THREADS=2`). `python3 -I scripts/lint.py`: 0 findings.
`python3 -I scripts/lock.py check`: 419 locked constants, 133 locked files, **0 violations** (the new
Defs are PENDING). Axiom scan `scripts/Axioms.lean --prefix EG EG.Lib.Quot.Round EG.Lib.Quot.Constants
EG.Lib.Quot.Xprime EG.Defs.Main.Gamma`: 2988 constants, 0 `sorryAx`, 0 violations.
Manuscript: v6.1 `proofs/manuscript/s7.tex` (defCand l.54–81, defSchedule l.158–204, consRound
l.231–391 including the *Fixed rules* paragraph l.236–271, lemMULT l.517, lemCC l.715, lemVstar
l.881, lemPay (a2) l.919, defXprime l.986, lemEXprime l.1004, lemUHsplit l.1052–1075,
propCost l.1230–1245), `s1.tex` (condGamma Γ4, defConstants (iv)–(vi), thmMain).

No existing file was changed. The locked HB Run model (`EG.HB.Run`, `PartId`, work/p2d/hb.md), the
Stage-1 layer (`EG.Stage1.*`, work/p2d/stage1.md) and the s6 interfaces (`EG.Chain.*`,
work/p2d/design.md) are used as they are.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Quot/Cand.lean` | `EG.Defs.Quot.Cand` | `HcdOf`, `thultOf` (formulas), `Hcd`, `thult` (run forms), `cand`, `candMean`, `JVBad` |
| `EG/Defs/Quot/Schedule.lean` | `EG.Defs.Quot.Schedule` | `Lists`, `Orders`, `Xi`, `subset3Law`, `listsLaw`, `ordersLaw`, `roundLaw`, readers `etaAt`, `zetaAt`, `sortByRank`, `inOrder` |
| `EG/Defs/Quot/Round.lean` | `EG.Defs.Quot.Round` | `RoundInput` (+ `J`, `Hcd`, `thult`, `KHUB`, `cand`, `multAt`, **`Valid`**, **`ofPast`**, items, payments (a), live sets, hub/fresh/PAR items, `clive`, `ultra`, `kh`, `groupCap`); `ParObj`, `REnd`, `LayerEdge`, `QTag`, **`QVert`**, `parTag`, `hubTag`, `pairUp`, `leftover`, `listOf`, `E1State`; **`Rules`** (+ cherries, unpaired legs, PAR objects, greedy colouring, HUB lists, SDR, (e1) fold, `E'`, (e2), junctions, loops, junction edges, `qEdge`, layer edges, ranks, **`Q`**, `mHub`, `mPar`, `copies`, `payrd`, `MarkovEvent`, **`xiChosen`**, `layerOf`, `interior`, **`liftObj`**, `lentJV`, `paidEdges`, `objs`, `out`, `quotient`, `e1Items`, **`Rules.Valid`**) |
| `EG/Defs/Quot/Xprime.lean` | `EG.Defs.Quot.Xprime` | `tCC`, `XVl`, `XV`, `poolWeight`, `jvBadPorts`, `Xpool`, `Xprime` |
| `EG/Defs/Quot/Constants.lean` | `EG.Defs.Quot.Constants` | `epsX`, `detl`, `FQ`, `eps2`, `thetaQ`, `eps1`, `C0` |
| `EG/Defs/Main/Gamma.lean` | `EG.Defs.Main.Gamma` | `EG.Gamma4`, `EG.cEG` (**`GammaCond` pending**, see "Open items") |
| `EG/Lib/Quot/Cand.lean` | `EG.Lib.Quot.Cand` | `HcdOf_def`, `Hcd_def`, `thult_def`, `mem_cand`, `cand_subset_poolSet`, `cand_subset_poolL`, `cand_subset_nbrs` (coherent `S`), `cand_subset_verts`, `JVBad.mem_classedPorts`, `not_JVBad_iff` |
| `EG/Lib/Quot/Schedule.lean` | `EG.Lib.Quot.Schedule` | `mem_sortByRank`, `nodup_sortByRank`, `mem_inOrder`, `nodup_inOrder`, `length_inOrder`, `etaAt_of_mem`, `zetaAt_of_mem`, `card_of_mem_supp_subset3Law` |
| `EG/Lib/Quot/Round.lean` | `EG.Lib.Quot.Round` | `ofPast_*` (rfl/simp), `ofPast_Hcd`, `ofPast_thult`, **`ofPast_J`** (under `JPlusProps`), **`ofPast_cand`**, `mem_items`, `live_subset_items`, `mem_live`, `not_mem_pool_of_mem_live` ("Live ∩ Pool_l = ∅"), `mem_hubItems`, `mem_hubItemsAt`, `mem_frPorts`, `mem_parItems`, `ultra_iff`, `groupCap_pos`, `clive_le_kh_mul_groupCap`, `mem_of_mem_pairUp`, `mem_of_leftover`, `lt_of_mem_listOf`, `disjoint_listOf`, `card_listOf`, `Q_edges`, `Q_verts`, `mem_qEdges`, `Q_noIsolated`, `copies_eq`, `xiChosen_spec`, `groupStd`, `groupStd_lt`, `card_groupStd_le`, `sdrFun`, `std0`, `std`, **`std_valid`**, **`Rules.exists_valid`** |
| `EG/Lib/Quot/Constants.lean` | `EG.Lib.Quot.Constants` | `epsX_eq_psiPool`, `thetaQ_eq`, `eps1_eq_epsChain`, `C0_eq`, `le_tCC`, `tCC_le` |
| `EG/Lib/Quot/Xprime.lean` | `EG.Lib.Quot.Xprime` | `Xprime_eq`, `poolWeight_of_mem`, `poolWeight_of_not_mem`, `XV_le_Xprime`, `Xpool_le_Xprime`, `XU_le_Xprime`, `mem_jvBadPorts` |
| `EGTest/Quot.lean` | — | see "Tests" |

Size: Defs 1151 lines (Round.lean 777), Lib 590, tests 205.

## Decisions

**D-Q-1 (the past is a parameter; TRIAGE §2.10, binding).** `RoundInput V` is the past *as read by the
round step*: `G`, `l`, `M ∈ ℕ`, `lam = λ_{l-2}`, `ancs : Finset PartId` with `ancVerts`, `ljv Y` (= `LJV_{Y,l}`),
`lendGood`, `pool` (= `Pool_l`) with `poolRound` (= `r(w)`), the role sets `hubs` (`D_l`), `fresh` (`⋃F_Z`),
`ports` (`⋃Q*_Z`), `lost` (`Lost_l`), `cls` (= `Y(·)`), `jvBad`, and the four J-classes. Classes are `PartId`s
(no abstract ancestor type: this avoids a `Type` field and the nonemptiness issue of MINOR-4 in design.md;
`r(Y) = Y.1`). `Hcd`, `thult`, `KHUB`, `cand` and `multAt` are **defined** from the fields
(`RoundInput.Hcd = HcdOf M lam`, the same formula as the run form `Quot.Hcd`, so `ofPast_Hcd` is `rfl`;
ULTRA-HCD-LAMBDA). `E[·|Past_l]` is the expectation under `roundLaw I.G I.M` with `I` fixed; freshness of
`ξ_l` is definitional.

**D-Q-2 (`RoundInput.Valid`).** Exactly the properties the round lemmas use (blueprint s7a
ROUND-INPUT-INTERFACE, checked against every proof step of WellDef, MULT, Simple, Lift, CC, Ultra, Pay):
`M_ge` (`2^40 ≤ M`), `Hcd_ge` (`2^10 M^10 ≤ Hcd`), `roles` (six pairwise disjointnesses, J3),
`hub_typed`/`fr_typed`/`par_typed`/`lost_typed` (the endpoint types of s6:lemJplus; the classes are then
pairwise disjoint, a consequence), `J_sub` (`J ⊆ E(G)`), **`J1` aggregated** (the shape of
`EG.Chain.JPlusProps.J1hub_ports`), `J2` (`∀ v ∉ hubs, degE J v ≤ M − 1`, the shape of
`JPlusProps.degE_types_le`), `J2tot`, `cls_anc`, `cls_round` (`1 ≤ r(u)`, `r(u) + 2 ≤ l`), `cls_mem`
(`u ∈ V(Y(u))`), `ljv_in` (`LJV ⊆ E(G)`, ends in `V(Y)`), `ljv_disj` (distinct ancestors), `ljv_J`
(junction edges are not J-edges), `lendGood_ports`, `good_cand` (lemCand(iv)), `pool_sub`, `ports_sub`
("at most `n` ports", Pay(c)). `J^par`'s "different classes" is not a field (unused in s7, ROUND-JPAR-CLASSES-UNUSED).

**D-Q-3 (`ofPast`; TRIAGE §3 item 31, MINOR-A of design.md).** `hubs := run.D G l`,
`fresh := freshCentres`, `ports := qsRound`, `lost := lostRound`, `cls := δ l`, `ljv Y := S.ljv Y l`,
`lendGood := ¬ lendBad`, `pool := Stage1.poolL G π l`, `poolRound := Stage1.poolRound π`,
`jvBad := JVBad run G δ S π l`, the four classes `Chain.Jlost/Jhub/Jfr/Jpar run G δ S l J`,
`ancs := run.ancestors G`, `ancVerts := run.ancVerts G`. `ofPast_J`: under `JPlusProps` the four classes
recombine to `J`. `ofPast_cand`: `I.cand u = Quot.cand … u` whenever `1 ≤ r(u)` and `r(u) + 2 ≤ l` (true for
every classed port of a designation). **`ofPast_valid` is not proved here** (it is a Spec obligation needing
s2:propStructure(iii), lemCand and Γ; see "Interface map").

**D-Q-4 (fixed rules = argument types; v6.1 *Fixed rules*, TRIAGE §1a patch set R).** `Rules I` has
* functions of `Past_l` alone (data fields, no argument): `pairing : V → List V`, `parOrder`, `group`;
* functions of `Past_l` and the lists (argument `Lists I.G I.M`): `sdr`, `e1Order`, `vertOrder`, `e2Order`;
* unrestricted (argument `Xi I.G I.M`): `rankOrder` (g) and `dec` (h).
So no rule of (b)–(e) can read the orders `≺_u` ("None of the rules of steps (b)–(e) reads the orders `≺_u`"),
and the rules of (b), (c) cannot read `ξ_l` at all. Through `I` the rules may depend on anything in the past
(including earlier `ξ_{l'}`), as the text allows. Every round Spec reads `∀ R : Rules I, R.Valid → …`.
Encodings: the pairing *and* the choice of the unpaired leg are one list per fresh centre (consecutive pairs
= cherries, last element of an odd list = the leg; every pairing with a leg choice has this form); the grouping
is a group number per hub item (0-based); the rank order is one list of layer edges (the rank of an edge is one
more than the number of earlier edges of the list in the same layer on the same two vertices); `Dec_l` is the
rule `dec` (the text lists (h) among the fixed rules; TRIAGE §1a Lean side has `rank` and `dec` as fields).

**D-Q-5 (`Rules.Valid`).** Side conditions only: pairing lists enumerate the live `J^fr` ports at each fresh
centre once; `parOrder` enumerates the PAR objects once; groups of a non-ultra hub are numbered `< k_h` and
have `≤ ⌈Hcd/8⌉` items; where an SDR exists the rule picks one ("If no such choice exists, all live hub items
of `u` are paid" is the construction, not a rule condition); `e1Order` enumerates the coloured items of
non-ultra hubs; `vertOrder` enumerates `V(G)`; `e2Order L u` enumerates `E'(u)`; `rankOrder` enumerates the
layer edges; `dec ξ` is a decomposition of `E(Q_l)` with `f(Q_l)` objects. **Non-vacuity proved:**
`Rules.exists_valid : I.Valid → ∃ R, R.Valid` (via `std_valid (0 < Hcd)`: `toList` enumerations, blocks of
`⌈Hcd/8⌉` for the groups using `c_h ≤ k_h⌈Hcd/8⌉`, a chosen SDR, a chosen optimal decomposition), which is
the manuscript's "Rules with these arguments exist".

**D-Q-6 (total construction with fallbacks; ROUND-TOTALITY).** Greedy colouring with no free colour: the
object stays uncoloured (it then has no layer edge); (e1) with no free candidate: no junction; (e2) end not in
the list or too few candidates: no junction; a PAR object with missing or equal junctions has no layer edge.
Lemma s7:lemWellDef states (under `I.Valid`, `R.Valid`) that no fallback is taken.

**D-Q-7 (objects of the construction).** Items `= J \ J^lost` (`items`); the vertices of an item are its two
ends; (a2) "a vertex in `Pool_l`" = an end in `pool`; (a3) "a JV-bad port end" = an end in `ports` that is
JV-bad. Hub items are pairs `(h,u) ∈ hubs × ports` with `s(h,u)` a live `J^hub` item (`hubItems`); fresh items
at `x` are their ports (`frPorts x`); `J^par` items are edges, turned into `ParObj.par u v` with
`(u,v) = Quot.out e`. `ParObj.cherry x u u'`. Ends of PAR objects are indexed by `Bool` (`REnd.par o b`);
ends of hub items are `REnd.hub h u`. HUB colours are the naturals `< 4M` (0-based `Fin (4M)` values); the
`i`-th group (0-based) of a non-ultra hub gets `{η(3i), η(3i+1), η(3i+2)}` = `listOf η i` (manuscript 1-based
`{η_h(3i−2), η_h(3i−1), η_h(3i)}`; ROUND-FIN-OFFSET); an ultra item's list is `ζ_{h,u}`. PAR colours: least
free colour in `[0, 3M)` (first fit, "coloured greedily").

**D-Q-8 (the (e1) fold).** `e1State L = (e1Order L).foldl e1Step ⟨∅, ∅, none⟩` with explicit `Used(u)`,
`Used_κ(h)` and junction maps; a step for a coloured item of a non-ultra hub picks the first element of
`vertOrder L` in `Cand(u) \ Used(u) \ Used_κ(h)` (`e1Free`) and adds it to both sets. Other entries are skipped.

**D-Q-9 (the orders and (e2)).** `≺_u` is a rank `↥G.verts ≃ Fin n`; `inOrder O u C` lists `C ∩ V(G)` in
increasing rank; `e_i` (the `i`-th entry of `e2Order L u`, 0-based) gets the `i`-th element of
`inOrder O u (Cand(u) \ Used(u))` (`e2Junc`).

**D-Q-10 (round randomness; SCHED-XI-TYPES).** `Lists G M = (↥V(G) → Perm (Fin 4M)) × (↥V(G) × ↥V(G) →
Finset (Fin 4M))`, `Orders G = ↥V(G) → (↥V(G) ≃ Fin n)`, `Xi = Lists × Orders`;
`roundLaw = (pi uniform-perm × pi subset3Law) × pi uniform-rank`. `ζ` takes values in `Finset (Fin 4M)` with
law uniform on 3-subsets (`subset3Law`; junk `dirac ∅` for `4M < 3`, never the case) — so `Xi` is inhabited for
every `M` and `xiChosen` needs no guard. `ζ` is drawn for **all** ordered pairs, including `h = u` (extra
independent coordinates, never read). Readers `etaAt`, `zetaAt`, `inOrder` take `V`-arguments (junk off `V(G)`).

**D-Q-11 (quotient; TRIAGE §2.10 QVert).** `QVert V = QTag × V`, `QTag = Bool × ℕ × ℕ × Bool` = (kind: `false`
PAR / `true` HUB, colour, **rank**, **side**: `true` hub copy / `false` junction copy). `qEdge ξ ι e`: a PAR
object of colour `κ` whose ends have junctions `w₁ ≠ w₂` gives `s((parTag κ ι, w₁), (parTag κ ι, w₂))`; a
coloured hub item `(h,u)` of colour `κ` with junction `w` gives `s((hubTag κ ι true, h), (hubTag κ ι false, w))`.
`Q ξ` has `edges = ⋃_{e ∈ layerEdges} qEdge (rank e) e` and `verts =` ends of edges; `loopless` is proved
in the Def (`qEdge_not_isDiag`: PAR by `w₁ ≠ w₂`, HUB by the side tag). Rank-injectivity (distinct layer edges
give distinct `Q`-edges, "every item lies in exactly one edge of `Q_l`") is **not** definitional: it follows
from `R.Valid.rankOrder` (Nodup) and is part of s7:lemSimple/lemLift (probe P-1). `rank ξ e` = 1 + #(entries before the first
occurrence of `e` in `rankOrder ξ` whose rank-`0` `Q`-edge equals that of `e`); the prefix test is
`decide (e' ≠ e)` (fix round 2, r2-1: not `e' != e`).

**D-Q-12 (lift; ROUND-LIFT-ROTATION).** `liftObj ξ (.edge q)` = the J-edges of the PAR object of `q` as single
edges, or the single edge `hu`; `liftObj ξ (.cycle c)` = one cycle whose vertex list is
`(c.zip (c.rotate 1)).flatMap (fun ab => ab.1.2 :: interior (layerOf s(ab.1, ab.2)) ab.1.2)`, where `interior`
of a PAR object entered at `w` is `p (x) q` (`p` the end with junction `w`) and of a hub item `(h,u)` is `[u]`.
This gives `w_0 p_0 (x_0) q_0 w_1 …` for PAR cycles and `h_0 u_0 w_0 u'_0 h_1 …` for HUB cycles from any start
and direction (no rotation needed). `layerOf` picks the layer edge of a `Q`-edge (unique by rank-injectivity).
`lentJV ξ` = the junction edges lying on an edge of a lifted cycle of `dec ξ` (literal); `objs ξ` = the paid
single edges ((a), (b), (d), (e3)) followed by the lifts of `dec ξ`.

**D-Q-13 (Markov choice; TRIAGE §2.10).** `MarkovEvent ξ` is the event of (f) with both expectations under
`roundLaw`; `xiChosen := if h : ∃ ξ, 0 < w ξ ∧ MarkovEvent ξ then choose h else arbitrary`;
`xiChosen_spec` gives positivity and the event when the hypothesis holds (Markov (b) gives it: Spec obligation of
s7:lemOneOutcome(3)). `out = (objs xiChosen, lentJV xiChosen)` is the J-consumer output, `quotient = Q xiChosen`.

**D-Q-14 (stage-1 functionals; CAND-MEAN-DEF).** `JVBad` uses the closed-form mean `candMean = q_l π_{l,r} p_Y
deg_{H_Y}(u)` (lemCand(ii) proves it is `E|Cand_l(u)|`); only classed ports of round `l` can be JV-bad. The
stage-1 outcome is read through `S : StageData V` and the pool labels `π` (as in design.md D-DES-1); for an
outcome `ω` these are `StageData.ofOutcome ω …` and `ω.pool`. `X_{V,l}`, `X_V`, `ω_l(v)` (`poolWeight`),
`X_pool`, `X'` are natural numbers (`M_l ≥ 2^40`, so `M_l − 1` in `ℕ` is exact). `tCC M = ⌈2 log₂ M⌉₊` is one
constant for lemCC(iii) and `X_{V,l}` (VSTAR-TCC-DEF).

**D-Q-15 (constants).** Exactly the defining formulas: `epsX` (lemEXprime), `detl` (lemUHsplit, uses
`thult run G l` and `λ_{l-2}`), `FQ` (`x^{-90.2}` rpow), `eps2`, `thetaQ = eps2`, `eps1` (names `ε_K =
Chain.epsK`, `= Light.epsChain` by `rfl`), `C0 = D/2 + 1085 + ε_1`, `Gamma4 D := ε_1 ≤ 6 ∧ ε_2 ≤ 1/4`,
`cEG N0 D := max (C0/(1 − 2θ_Q)) (N0/2)`. Decimal literals (`10.3`, `2.1`, `1.5`, `90.2`) are exact
rationals in `ℝ`.

## Interface map: `RoundInput.Valid` ← run, `δ`, `S`, `π`, `J` (for `ofPast_valid`, joint review with design.md)

| field | source |
|---|---|
| `M_ge` | `Stage1.two_pow_le_M` (unconditional) |
| `Hcd_ge` | s7:lemCand(iv) (Γ1, COL-JV row 11) |
| `roles` | the six role-disjointness lemmas of `EG.Lib.Chain.Lending` |
| `*_typed` | `Chain.Jhub/Jfr/Jpar/Jlost` filters + `IsJ*Edge` (hubs ⊆ D_l, qs ⊆ qsRound, lost ⊆ lostRound) |
| `J_sub`, `J2tot` | `JPlusProps.subset_edges`, `J2card`, `ofPast_J` |
| `J1` | `JPlusProps.J1hub_ports` (verbatim shape) |
| `J2` | `JPlusProps.degE_types_le` (verbatim shape) |
| `cls_anc`, `cls_round`, `cls_mem` | `IsDesignation.mem_ancestors`, `one_le_round`, `round_add_two_le`, `mem_ancVerts` |
| `ljv_in` | `StageData.Coherent.ljv_subset_graph_edges` + `ancGraph` verts = `ancVerts` |
| `ljv_disj`, `ljv_J` | s2:propStructure(iii) (+ `Coherent.ljv_eq_empty` for `l ∉ lateRounds`) |
| `lendGood_ports` | `not_lendBad_of_mem_qs` |
| `good_cand` | s7:lemCand(ii),(iv) + `ofPast_cand` |
| `pool_sub`, `ports_sub` | `Stage1.mem_poolL`, `qs ⊆ Z^0 ⊆ V(G)` |

## Tests (`EGTest/Quot.lean`)

- `I1` (graph on `Fin 3` with edges `01`, `02`; one `J^hub` edge `01`, hub `0`, port `1` of class `(1,[])`,
  `M = 2^40`, `λ = 64`): **`I1.Valid`** (so `Valid` is satisfiable with a nonempty `J`); `paidJVBad = {01}`,
  `live = ∅` (the port is JV-bad); `∃ R : Rules I1, R.Valid`.
- `I2` (two `J^hub` edges `01`, `02` at hub `0`, both ports of the same class): **`¬ I2.Valid`** — (J1) has
  content.
- `I3` (`M = 1`, invalid, port JV-good, nothing pooled): `live = {01}`, `hubItems = {(0,1)}`, `clive 0 = 1`.
- `pairUp`, `leftover` (rfl), `listOf 1 2 = {6,7,8}` on `[12]` (decide), `card_listOf`, `disjoint_listOf`,
  the 3-subset law, and parse checks of `C0`, `eps2`, `Gamma4`, `cEG`, `FQ`, `tCC 4 = 4`.

## Notes for Spec authors (probe P-1 and s7 Specs)

- Round Specs: `∀ (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid → …`; run-level Specs instantiate
  `I := RoundInput.ofPast run G δ S ω.pool l J` with `JPlusProps run G δ S l J` and `S.Coherent run G`.
- `E[X | Past_l]` = `(roundLaw I.G I.M).expect X`; "given the lists" = fix `L` and use
  `(ordersLaw I.G).expect (fun O => X (L, O))`; the Cuckoo bound (WellDef(iii)) is a statement about
  `(listsLaw I.G I.M).prob {L | ¬ R.SDRExists L u}`.
- MULT: `R.mHub ξ κ h w ≤ I.multAt (I.poolRound w) w`; sub-layer counts read `Q.verts` by tag
  (`(hubTag κ ι false, w) ∈ (R.Q ξ).verts`). CC: `R.mPar ξ κ w w'`.
- Lift(ii) is for every `D` with `IsDecomp (R.Q ξ).edges D` (lifts are `D.flatMap (R.liftObj ξ)`), Lift(iv) is
  `JC2 I.J (R.lentJV ξ) (R.objs ξ)` and the JC1 inclusion through `ofPast`.
- Concrete-type pitfall: the decidability instances inside `RoundInput.Valid` (e.g. `J1`'s filter) are the
  generic ones; on a concrete `V` (e.g. `Fin 3`) typeclass synthesis finds a different instance
  (`Nat.decidableExistsFin`), and `Finset.card_filter_le`/`Finset.mem_filter` then fail with "synthesized
  instance is not definitionally equal". Use lemmas taking the instance by unification (`{_ : DecidablePred p}`,
  see `EGTest.Quot.card_filter_le'`, `mem_filter_of`) or `convert`.

## Manuscript issues

None new (no T1/T2/T3). T0 readings recorded here (no manuscript change needed): ζ drawn for all ordered pairs
(including `h = u`); pairing and unpaired-leg choice encoded as one list; groups numbered from 0 with lists
`{η(3i), η(3i+1), η(3i+2)}`; "split into `k_h` groups" read as "group numbers `< k_h`, each group of size
`≤ ⌈Hcd/8⌉`" (empty groups allowed; the text needs no more); the vertices of an item are its two ends; greedy
colouring is first-fit; `Dec_l` is a rule field (text: "chosen by a fixed deterministic rule").

## Open items

1. **`GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` is not defined yet.** It needs `Gamma1`
   and `Gamma3` of `EG/Defs/Gamma/Full.lean` (TRIAGE §3 item 14), which does not exist in the working tree at
   the time of writing. Defining local copies of `Gamma1`/`Gamma3` here would create a second locked copy of
   those conditions, so `EG/Defs/Main/Gamma.lean` holds `Gamma4` and `cEG` only; `GammaCond` is one additive
   line once item 14 exists (`import EG.Defs.Gamma.Full`).
2. `RoundInput.ofPast_valid` (Spec/Proof, joint with design.md) and the run-level J-consumer instance
   (`out := roundOut run G δ S π`, whose `jc1`/`jc2` use `RoundInput.chosenRules_valid` and
   `ofPast_valid`; fix round 1).
3. Root files `EG.lean`/`EGTest.lean` are integrator-owned: add `EG.Defs.Quot.{Cand,Schedule,Round,Xprime,
   Constants}`, `EG.Defs.Main.Gamma`, `EG.Lib.Quot.{Cand,Schedule,Round,Constants,Xprime}`, `EGTest.Quot`.

## Fix round 1 (review `work/p2d/quot.review1.md`, verdict APPROVE, 6 minor/cosmetic findings)

Every finding was checked against the files; all six are valid. No existing definition body changed
(`python3 -I scripts/lock.py check`: 419 locked constants, 133 locked files, **0 violations**; the s7
Defs are still PENDING). All changes are additive except one kernel-identical spelling
(`Quot.out` → `_root_.Quot.out`) and docstrings.

| id | verdict | action |
|---|---|---|
| m1 `GammaCond` missing | valid, **still blocked** | `EG/Defs/Gamma/Full.lean` (TRIAGE §3 item 14: `Gamma1f`, `Gamma1`, `N0Cond`, `Gamma3`, `RunHyp`) still does not exist (checked: no `def Gamma1`/`Gamma3`/`N0Cond` anywhere in `EG/`). Defining local copies would create a second locked copy of Γ1/Γ3, so nothing is added. `EG/Defs/Main/Gamma.lean` is **not complete**: `GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` is one additive line plus `public import EG.Defs.Gamma.Full` once item 14 lands (Open item 1). Locking `Gamma4`/`cEG` now is fine. |
| m2 `ofPast_multAt` | valid, **fixed** | `EG.Quot.ofPast_multAt : (RoundInput.ofPast run G δ S π l J).multAt r w = run.mult G r w` for **every** `r` (Lib, `EG/Lib/Quot/Round.lean`): the filter of `run.ancestors G` by `Y.1 = r ∧ w ∈ V(Y)` is the image of `(run.prePartAddrs G r).filter (w ∈ partVerts)` under the injection `a ↦ (r, a)` (`Run.mem_ancestors`). UHsplit(ii) can now match the junction-copy bound with the `X_{V,l}` term. |
| m3 colour / `roundLaw` shapes | valid, **fixed (docs)** | `CONVENTIONS.md` is a **locked file** (`lock.py`: "locked file changed or missing: CONVENTIONS.md" on a trial edit, which was reverted byte-for-byte from `HEAD`), so the rule is recorded in the header of `EG/Defs/Quot/Schedule.lean` (docstring only) and under "Notes for Spec authors" below, with a proposed CONVENTIONS text for the integrator. |
| m4 `EG.Quot` shadows core `Quot` | valid, **fixed** | `parObjsPar` now writes `_root_.Quot.out` (kernel term unchanged; docstring says why). Checked: no `EG.Quot.{out,mk,sound,ind,lift,rec}` exists. The rule "never declare these names; write `_root_.Quot.*`" is in the Notes below and the proposed CONVENTIONS text. (The hazard is real: `ext ⟨r', a⟩` on a `Finset PartId` goal in `EG.Quot` produced a raw `Quot.lift` goal while writing `ofPast_multAt`; `apply Finset.ext` avoids it.) |
| m5 one chosen rule | valid, **fixed (Defs addition)** | The blueprint (s7b S7-ROUNDSTEP-IN-DEFS, JV-SAME-Q) needs the J-consumer to be a Defs-level deterministic function that a Spec (thmJVps) can name, and Specs import no Lib file, so the choice is a **Defs** addition in `EG/Defs/Quot/Round.lean` (total, no proof inside): `RoundInput.junkRules` (all lists empty, numbers `0`), `RoundInput.chosenRules := if h : ∃ R, R.Valid then choose h else junkRules`, and the run-level `roundOut run G δ S π l J := (ofPast …).chosenRules.out` (type of `JConsumer.out` for fixed `run G δ S π`) and `roundQuotient run G δ S π l J := (ofPast …).chosenRules.quotient`. Lib: `RoundInput.chosenRules_valid : I.Valid → I.chosenRules.Valid`, `roundOut_eq`, `roundQuotient_eq` (rfl), `roundOut_roundQuotient` (one rule `R`, valid when the input is, gives both, with the same `R.xiChosen`). |
| m6 no valid test with a live item | valid, **fixed** | The reviewer's scratch `/tmp/quotrev1/NonVacuity.lean` is added as `namespace EGTest.Quot.Live` of `EGTest/Quot.lean` (`N` an `irreducible_def`): `I_valid`, `I_live = {01}`, `I_hubItems`, `¬ ultra 0`, `kh 0 = 1`, **`Q_nonempty`** (every valid rule, every `ξ`: `Q_l` has an edge), plus `chosen_Q_nonempty` (the chosen rules' quotient has an edge, via `chosenRules_valid`). Change: `set_option exponentiation.threshold` is **not** on the lint allowlist (`lint.py` reported it), so the option was removed and every literal exponent is kept `≤ 256`: `N := (2^250)^2`, `Hcd = Hval := 64^95/(8 (2^40)^2)` (`= 2^487`). Also parse checks of `roundOut`, `roundQuotient`, `ofPast_multAt`. Peak RSS 2.6 GB, 7 s. |

Checks after the fix round: `scripts/check.sh` (`LEAN_NUM_THREADS=2`) 0 errors / 0 warnings / 0 `sorry` on
`EG/Defs/Quot/Round.lean`, `EG/Defs/Quot/Schedule.lean`, `EG/Lib/Quot/Round.lean`, `EGTest/Quot.lean`;
`lake build EG.Lib.Quot.{Round,Constants,Xprime,Cand,Schedule} EG.Defs.Main.Gamma` succeeds;
`python3 -I scripts/lint.py` 0 findings; `lock.py check` 0 violations; axiom scan
`--prefix EG EG.Lib.Quot.Round EG.Lib.Quot.Constants EG.Lib.Quot.Xprime EG.Defs.Main.Gamma`: 2999 constants,
0 `sorryAx`, 0 violations.

New declarations: Defs `EG.Quot.RoundInput.junkRules`, `EG.Quot.RoundInput.chosenRules`, `EG.Quot.roundOut`,
`EG.Quot.roundQuotient`; Lib `EG.Quot.ofPast_multAt`, `EG.Quot.RoundInput.chosenRules_valid`,
`EG.Quot.roundOut_eq`, `EG.Quot.roundQuotient_eq`, `EG.Quot.roundOut_roundQuotient`.

### Notes for Spec authors (fix round 1; proposed `CONVENTIONS.md` section for the integrator)

```
## The s7 quotient layer (EG.Defs.Quot; design note work/p2d/quot.md)
- Colours are natural numbers, not `Fin`: PAR colours `κ < 3 * I.M`, HUB colours `κ < 4 * I.M`
  (0-based). Sum over `Finset.range (3 * I.M)` / `Finset.range (4 * I.M)`. The round law is
  `roundLaw I.G I.M` (the factor 4 is inside `Lists`), not `roundLaw I.G (4 * I.M)` as the blueprint
  lean_shapes write. Ranks `ι` are naturals `≥ 1`.
- Round Specs read `∀ I : RoundInput V, I.Valid → ∀ R : Rules I, R.Valid → …`; run-level Specs use
  the ONE chosen rule: `roundOut run G δ S π l J` (J-consumer output) and `roundQuotient run G δ S π l J`
  (= `Q_l`) come from the same `RoundInput.chosenRules` and the same `ξ_l` (JV-SAME-Q). Never pair
  an `out` of one rule with the quotient of another.
- `multAt` of `RoundInput.ofPast` is the run's `mult` (`EG.Quot.ofPast_multAt`, every `r`).
- The namespace `EG.Quot` shadows core `Quot` inside `namespace EG`: never declare
  `EG.Quot.{out, mk, sound, ind, lift, rec, liftOn, recOn, hrecOn}`; write `_root_.Quot.out` (etc.)
  for the core constants in s7 code.
```

## Fix round 2 (review `work/p2d/quot.review2.md`, verdict APPROVE, 3 minor + 3 cosmetic findings)

Every finding was checked against the files. One definition body changed (`Rules.rank`, PENDING, reviewer's
option for r2-1); everything else is additive or docs. `python3 scripts/lock.py check`: 419 locked constants,
133 locked files, **0 violations**, 466 pending (the s7 Defs are still PENDING).

| id | verdict | action |
|---|---|---|
| r2-1 `rank` uses `Sum.instBEq` | valid, **worse than reported; fixed in the Defs body** | Verified: no `LawfulBEq (ParObj V ⊕ V × V)`. Moreover, in a **module** file (every `EG/Lib/**`, `EG/Proof/**`) the body of the derived `Sum.instBEq.beq` (core, `deriving instance BEq for Sum`) is not exposed: `rfl`, `unfold Sum.instBEq.beq`, `rw`, `simp only [Sum.instBEq.beq]` and the equation lemmas all fail (checked in a module scratch: `Sum.instBEq.beq (inr a) (inl b) = false` is not provable by `rfl`, `Sum.instBEq.beq.eq_2` is unknown). The reviewer's helper `bne_inl_inl` only works in non-module files (EGTest). So the suggested Lib lemma `LayerEdge.bne_eq` / a `LawfulBEq` instance cannot be proved where lemSimple/MULT/`layerOf` proofs live. Fix: the body of `Rules.rank` now tests the prefix with `fun e' => decide (e' ≠ e)` (the reviewer's alternative; same values, uses the derived `DecidableEq` of `ParObj` and `Prod`, which is lawful through `decide_eq_true_iff`). Docstring says why. No other `==`/`!=` in the s7 Defs: `e2Junc`'s `idxOf?` on `REnd V` elaborates to `instBEqOfDecidableEq` (lawful, checked with `pp.explicit`), and every `find?` predicate is a `decide`. Lib additions: `Rules.one_le_rank`, `Rules.rank_head` (both proved in the module `EG/Lib/Quot/Round.lean`, which shows `rank` is now workable there). |
| r2-2 `GammaCond` missing | valid, **still blocked** | `EG/Defs/Gamma/` still holds only `Core.lean` (`Gamma1a`–`Gamma1e`, `Gamma1core`, `Gamma2a`; no `Gamma1`, `Gamma3`, `N0Cond`; checked by grep). No local copies (Open item 1 unchanged). `Gamma4` and `cEG` are lockable now. |
| r2-3 PAR path untested | valid, **fixed** | The reviewer's scratch `/tmp/quotrev2/ParTest.lean` is added to `EGTest/Quot.lean` as `namespace EGTest.Quot.Par` (no new root import needed). Changes: the helper `bne_inl_inl` is dropped (the new `rank` body needs none; `rank_eq` is now `simp [Rules.rank, h, hne, hq]` with `hne : inl o₁ ≠ inl o₂`); unused-`hR` / unused-simp-arg linter warnings removed (`omit hR in` on `parObjs_eq`, `colourStep_zero`, `colouredHub_eq`, `e1Items_eq`, `E'_o₁`, `E'_o₂`, `exists_valid_rules`, call sites adjusted). Proved for every valid rule and every `ξ`: `parColour_eq`, `junction_o₁/₂`, `not_looped`, `layerEdges_eq`, `rank_eq` (the rank split `(1,2)`/`(2,1)`), `Q_edges`, `Q_card_edges = 2`, `Q_card = 4`, `layerOf_E`, `lift_edges`, `exists_valid_rules`. Whole test file: 0 errors, 0 warnings, 0 `sorry`, 8.6 s, 2.6 GB RSS, 931 lines. |
| r2-4 blueprint shape deltas | valid, **fixed (docs)** | Appended to the proposed CONVENTIONS section below. |
| r2-5 `rank` docstring terse | valid, **fixed** | Reworded: "…the same layer and the same two vertices (compared through their rank-`0` `Q`-edge `qEdge ξ 0`, i.e. the same kind, colour and end pair)". |
| r2-6 root imports | valid, integrator-owned | Unchanged (Open item 3); the PAR tests live in `EGTest/Quot.lean`, so the import list is the same. |

Checks after the fix round: `scripts/check.sh` (`LEAN_NUM_THREADS=2`) on `EG/Defs/Quot/Round.lean` and
`EGTest/Quot.lean`: 0 errors, 0 `sorry`; `lake build EG.Lib.Quot.{Round,Constants,Xprime,Cand,Schedule}
EG.Defs.Main.Gamma` succeeds; `python3 -I scripts/lint.py` 0 findings; `lock.py check` 0 violations; axiom scan
`--prefix EG EG.Lib.Quot.Round EG.Lib.Quot.Constants EG.Lib.Quot.Xprime EG.Defs.Main.Gamma`: 3003 constants,
0 `sorryAx`, 0 violations.

Changed/new declarations: Defs `EG.Quot.Rules.rank` (body: `decide (e' ≠ e)` in place of `e' != e`; docstring);
Lib `EG.Quot.Rules.one_le_rank`, `EG.Quot.Rules.rank_head`; tests `EGTest.Quot.Par.*`.

### Notes for Spec authors (fix round 2 additions to the proposed `CONVENTIONS.md` section)

```
- Shapes that differ from the blueprint lean_shapes (s7a/s7b):
  * `ζ_{h,u}` takes values in `Finset (Fin (4 * M))` under `subset3Law` (support = the 3-subsets),
    not the subtype `{s // s.card = 3}`.
  * `listsLaw` / `roundLaw` are products of `FinDist.pi`s (`(pi uniform-perm).prod (pi subset3Law)`,
    then `.prod ordersLaw`), not `FinDist.uniform` of the whole type (equal in law, different terms).
  * `MarkovEvent`, `xiChosen`, `copies`, `payrd` are per rule `R : Rules I` (`R.MarkovEvent ξ`,
    `R.xiChosen`), not per `(ω, l, J)`.
  * There is no `RoundOutput` record and no `roundStep`: use `R.Q ξ`, `R.objs ξ`, `R.lentJV ξ`
    (run level: `roundOut`, `roundQuotient`).
  * The HUB grouping is `R.group : V × V → ℕ` (per hub item `(h, u)`), not `hubGroups : V → Sym2 V → ℕ`.
  * Ranks `ι` start at `1` (`Rules.one_le_rank`): sub-layer sums run over `ι ≥ 1`
    (`Finset.range k` needs the shift `ι + 1`).
- `Rules.rank` compares entries of the rank order with `decide (e' ≠ e)`; never reason about
  `!=`/`==` on `LayerEdge V` (`Sum.instBEq` is not lawful and its body is not exposed in modules).
```
