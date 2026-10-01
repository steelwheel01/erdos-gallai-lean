# Clean-room definition review, round 2: P2-D [quot] (s7 quotient layer)

Reviewer: clean-room definition reviewer (round 2). Date 2026-09-26.
Scope: `EG/Defs/Quot/{Cand,Schedule,Round,Xprime,Constants}.lean`, `EG/Defs/Main/Gamma.lean`, the
Lib API `EG/Lib/Quot/*`, `EGTest/Quot.lean`, design note `work/p2d/quot.md` (with its fix round 1).
References: manuscript v6.1 `s7.tex` (defPool l.30, defCand l.54, defSchedule l.158, consRound
l.231–435 with the *Fixed rules* paragraph l.236–271, lemWellDef, lemMULT, lemSimple, lemLift, lemCC,
lemUltra, lemVstar, lemPay, defXprime, lemEXprime, lemUHsplit, lemOneOutcome, propCost, thmJVps,
lemGammaSat, thmMainProof), `s1.tex` (thmMain, defConstants, condGamma Γ4; `\cTot = 1085`,
`\cTotR = 1091` checked in `preamble.tex`), blueprints `work/p2/blueprint_s7a.md`,
`blueprint_s7b.md`, `work/p2/TRIAGE.md` §1a (patch set R), §2.10, §3 items 29–34, the locked HB
Run model and the pending `EG.Chain.JPlusProps` / `EG.Chain.JConsumer` / `EG.Stage1.*`.
No Lean file was edited. This review was done independently of round 1 (`quot.review1.md`) and then
compared with it; §5 records the status of the six round-1 findings.

## Verdict

**APPROVE.** 0 major findings. 3 minor and 3 cosmetic findings (§6); none changes a definition body
(one of them offers an optional body change while the Defs are still PENDING). Every definition
back-translates to its defining text; the `Rules` argument types are exactly the v6.1 *Fixed rules*
restrictions; the round law has the right weights and independence structure; every downstream use
in blueprints s7a/s7b (and the run-level J-consumer instance) can be stated with the given fields
and index types.

Checks run (all in the current working tree, HEAD `8f1422b` + untracked P2-D files):
- `python3 -I scripts/lint.py`: 0 findings.
- `python3 scripts/lock.py check`: 419 locked constants, 133 locked files, 0 violations, 466 pending
  (the s7 Defs are PENDING, as expected).
- `lake build EG.Lib.Quot.Round EG.Lib.Quot.Constants EG.Lib.Quot.Xprime EG.Defs.Main.Gamma`: up to
  date (2089 jobs, nothing rebuilt).
- `scripts/check.sh EGTest/Quot.lean` (`LEAN_NUM_THREADS=2`): 0 errors, 0 sorry, 7.3 s, 2.6 GB RSS.
- New non-vacuity scratch `/tmp/quotrev2/ParTest.lean` (copy of
  `…/scratchpad/quotrev2/ParTest.lean`, 460 lines): 0 errors, 0 sorry, 7.5 s, 2.6 GB RSS. See §4.
- `EG/Defs/Gamma/Full.lean` (TRIAGE §3 item 14) still does not exist (`ls EG/Defs/Gamma/`:
  `Core.lean` only), so `GammaCond` is still blocked (§5, m1).

## 1. Back-translation, definition by definition

### 1.1 Cand.lean (s7:defCand, lemCand(ii) closed form)

| Lean | reading | manuscript text | ✓ |
|---|---|---|---|
| `HcdOf M λ = λ^95 / (8 M²)`; `Hcd run G l = HcdOf (M_l) (λ_{l-2})` | Hcd_l | "`Hcd_l := λ_{l-2}^{95}/(8M_l^2)`" | ✓ |
| `thultOf M H = ⌊M·H/7⌋₊`; `thult` | θ^ult_l | (c) "`θ^ult_l := ⌊M_l Hcd_l/7⌋`" | ✓ |
| `cand G δ S π l u = (poolSet G π l r(u)).filter (s(u,w) ∈ S.ljv (δ l u) l)` | Cand_l(u) | "`Cand_l(u) := {w ∈ Pool_{l,r(u)} : uw ∈ LJV_{Y,l}}`" | ✓ (`Y(u) = δ l u`, `r(u) = (δ l u).1`) |
| `candMean = q_l · π_{l,r} · p_Y · deg_{H_Y}(u)` | E\|Cand_l(u)\| | lemCand(ii) first equality; `q_l = M_l^{-2}`, `π_{l,r} = 2^{-(l-1-r)}` (defPool l.37, checked against `Stage1.qPool`/`piPool`) | ✓ T0 CAND-MEAN-DEF |
| `JVBad = u ∈ classedPorts run G l ∧ |cand| < candMean/2` | JV-bad | "JV-bad if `|Cand_l(u)| < ½ E|Cand_l(u)|` … applies to every classed port, whether or not it lies in `Lost_l`" | ✓ strict `<`, lost ports included |

Edge cases: `l ≤ 2` reads `λ_{l-2}` at the truncated index (junk, the Specs range over `l ∈ [3,R]`);
`pY` is junk for `k_lend = 0`, impossible for a class (`r ≤ l−2 ≤ R−2`); `u ∉ V(H_Y)` gives
`candMean = 0` and a JV-good `u`, excluded by a valid designation and then covered by lemCand.

### 1.2 Schedule.lean (s7:defSchedule, "Rounds")

| Lean | manuscript | ✓ |
|---|---|---|
| `Lists G M = (↥V(G) → Perm (Fin 4M)) × (↥V(G) × ↥V(G) → Finset (Fin 4M))` | "a uniformly random bijection `η_h : [4M_l] → [4M_l]` for every vertex `h`; a uniformly random 3-subset `ζ_{h,u} ⊆ [4M_l]` for every ordered pair `(h,u)` of distinct vertices" | ✓; `ζ` also for `h = u` (T0, never read: `hubList` reads `ζ_{h,u}` only for a hub `h` and a port `u`, disjoint by `roles`) |
| `Orders G = ↥V(G) → (↥V(G) ≃ Fin n)` | "a uniformly random linear order `≺_u` of `V(G)` for every vertex `u`" | ✓ rank encoding; `v ≺_u v'` iff `rank v < rank v'` |
| `Xi = Lists × Orders`; `roundLaw = listsLaw.prod ordersLaw` with `listsLaw = (pi uniform-Perm).prod (pi subset3Law)`, `ordersLaw = pi uniform-rank` | "mutually independent variables" | ✓ |
| `subset3Law K = (uniform {s // s.card = 3}).map val` (junk `dirac ∅` for `K < 3`) | "uniformly random 3-subset" | ✓ (weight `1/C(K,3)` on each 3-subset, 0 elsewhere; `card_of_mem_supp_subset3Law`) |
| `sortByRank o C` = `C ∩ V(G)` by increasing rank; `inOrder O u C` uses `O ⟨u,_⟩` | (e2) "`w_1 ≺_u w_2 ≺_u ⋯` the elements of `Cand_l(u) \ Used(u)` in the order `≺_u`" | ✓ the order of the **port** `u` |
| `etaAt`, `zetaAt` (identity / `∅` off `V(G)`) | — | ✓ never read off `V(G)`: hubs and ports are ends of `J ⊆ E(G)` |

"`E[·|Past_l]`" is `(roundLaw I.G I.M).expect` with the past as the parameter `I` — definitional
freshness (D-Q-1); "given the lists" is `(ordersLaw I.G).expect (fun O => X (L, O))`, correct because
`roundLaw` is a product (the conditioning lemma is a Lib item for the probes).

### 1.3 Round.lean (s7:consRound)

**RoundInput / Valid.** Every field of `Valid` was re-derived from a proof step of WellDef(i)–(v),
MULT, Simple, Lift(i)–(iv), CC(i), Ultra(i), Pay(a1)–(e) and JC1/JC2; nothing is missing and nothing
is unprovable for `ofPast` (interface map of quot.md re-checked against the Lib names that now exist:
`disjoint_D_qsRound` etc., `not_lendBad_of_mem_qs`, `Coherent.ljv_sub` / `ljv_eq_empty` /
`ljv_subset_edges`, `JPlusProps.J1hub_ports`, `degE_types_le`, `J2card`, `union_types`). Two points
worth recording:
- **Exclusivity of the four J-classes is not a field and need not be**: it follows from
  `hub_typed`/`fr_typed`/`par_typed`/`lost_typed` and the six disjointnesses in `roles` (an edge in two
  classes would put a hub, fresh centre or lost centre into `ports`, or a hub into `fresh ∪ lost`).
  JC2 (each item covered exactly once) needs only this derived form.
- **`Valid.J1` versus `JPlusProps.J1hub`**: `J1` filters `I.Jhub` by the structural predicate
  `∃ u ∈ ports, e = s(h,u) ∧ cls u = Y` for every `h : V`, while `J1hub` filters `J` by
  `IsJhubEdge h Y` for `h ∈ D_l`. For `ofPast` the first set is contained in the second (the
  reversed orientation `h ∈ qsRound ∩ D_l` is excluded by `disjoint_D_qsRound`), and for `h ∉ D_l`
  it is empty; so the field transfers. It is the aggregated form (TRIAGE MULT-J1) ✓.

**(a)** `items = J \ Jlost` ✓; `paidPool` (an end in `Pool_l`) ✓; `paidJVBad` (an end that is a
port and JV-bad) ✓; `live`, `liveVerts` ✓; `hubItems ⊆ hubs × ports` (no double count: `roles`) ✓;
`frPorts x`, `parItems` ✓.

**(b)** `pairing x : List V` — consecutive pairs = cherries, odd last element = unpaired leg; with
`Valid.pairing` (Nodup, covers `frPorts x`) this is exactly a pairing plus a leg choice ✓;
`parObjs = parObjsPar ∪ cherries` ✓; `Conflict` = shared end or shared middle ✓; `colourStep` /
`parColour` = first-fit over `parOrder` in `[0,3M)`, self excluded by `o' ≠ o` ✓ (fallback `none`).

**(c)** `clive`, `ultra` (`θ^ult < c_live`), `kh = ⌈8c/Hcd⌉₊`, `groupCap = ⌈Hcd/8⌉₊` ✓;
`hubList` = `listOf η_h (group it)` (non-ultra) / `ζ_{h,u}` (ultra) ✓; `listOf η i =
{η(3i),η(3i+1),η(3i+2)}` (0-based form of the 1-based text) ✓, disjoint for `i ≠ j`
(`disjoint_listOf`), 3 elements for `3i+3 ≤ 4M` (`card_listOf`) ✓.

**(d)** `SDRExists` is the Hall form (pairwise distinct colours from the items' lists) ✓;
`hubColour` = the rule's colour when an SDR exists at the port, else `none`; `sdrPaid` = all live hub
items of a port without an SDR ✓.

**(e1)** `foldl` over `e1Order L` with explicit `Used(u)`, `Used_κ(h)`, junction map; the step
picks the first `w` of `vertOrder L` in `Cand(u) \ Used(u) \ Used_κ(h)` and adds it to both sets;
uncoloured items and items of ultra hubs are skipped ✓ (fallback: no junction).

**(e2)** `E' L u` = the ends at `u` of all PAR objects plus the coloured ultra-hub items at `u` ✓;
`e2Junc`: the `i`-th entry of `e2Order L u` receives the `i`-th element of
`inOrder O u (Cand(u) \ Used(u))` ✓ (`used` reads `L` only). The orders `ξ.2` enter the whole
construction **only** through `inOrder` inside `e2Junc`, which reads `O ⟨u,_⟩` for the end's own port
`u` — this is the manuscript's "within steps (a)–(f), the orders `≺_u` enter only through the
assignment `e_i ↦ w_i`", and CC(i)'s "the junction of the κ-end at `x` is a function of `≺_x`
alone", definitionally.

**(e3)** `Looped` (both junctions exist and agree) ✓; `loopPaid` = `edgeList` of looped objects (one
edge for a `J^par` item, two for a cherry) ✓; `unpaidPar` ✓; `junctionEdges` = `s(u,w)` for every end
of a coloured hub item or of an unpaid PAR object with junction `w` ✓.

**(g)** `layerEdges = unpaidPar ⊕ colouredHub` ✓; `qEdge ξ ι`: PAR → `s((parTag κ ι, w₁),
(parTag κ ι, w₂))` when `w₁ ≠ w₂`, HUB → `s((hubTag κ ι true, h), (hubTag κ ι false, w))` ✓;
`rank ξ e` = 1 + #(entries of `rankOrder ξ` strictly before the first occurrence of `e` with the same
rank-0 `Q`-edge, i.e. the same kind, colour and end pair) ✓ = "the `i`-th edge of such a list has
rank `i`", ranks start at 1, and a global list realizes every family of per-(layer, pair) orders.
Rank-injectivity under `Valid.rankOrder` (Nodup + coverage) was re-derived: a later entry with the
same rank-0 edge counts the earlier one, so ranks strictly increase along equal-identity entries;
this is the content of lemSimple, not a definition (D-Q-11) ✓. `Q ξ`: `edges = ⋃ qEdge (rank e) e`,
`verts` = ends of edges ("isolated vertices deleted"), `loopless` proved in the Def
(`qEdge_not_isDiag`: PAR by `w₁ ≠ w₂`, HUB by the side tag) ✓. `QVert V = QTag × V : Type` for
`V : Type` ✓ (HIHyp).

**(f)** `copies = |V(Q)|`, `payrd = |sdrPaid ∪ loopPaid|` (disjoint under `Valid`: `J^hub` versus
`J^fr`/`J^par` edges) ✓; `MarkovEvent` with both expectations under `roundLaw` ✓; `xiChosen` with
`Classical.arbitrary` fallback (Xi is inhabited for every `M`) ✓.

**(h)** `layerOf` (unique under lemSimple) ✓; `interior` (PAR object entered at its end with
junction `a`: `p (x) q`; hub item: `[u]`) ✓; `liftObj (.edge q)` = the one or two J-edges / the
edge `hu` ✓; `liftObj (.cycle c)` = one cycle with vertex list
`⋃_{(a,b) consecutive} a.2 :: interior (layerOf s(a,b)) a.2`, which I re-checked by hand for PAR
cycles (`w₀ p₀ (x₀) q₀ w₁ …`) and HUB cycles in both directions and from either kind of start vertex
(`h₀ u₀ w₀ u'₀ h₁ …`, or `w₀ u₀ h₀ u'_{m-1} w_{m-1} …` reversed) ✓; `lentJV` = junction edges on a
lifted cycle of `dec ξ` (literal) ✓; `paidEdges = paidA ∪ unpairedLegs ∪ sdrPaid ∪ loopPaid`,
`objs` = paid single edges ++ lifts ✓; `out`, `quotient` on `xiChosen` ✓.

**Rules (v6.1 *Fixed rules*).** The docstring quotes the paragraph correctly (compared with
s7.tex l.236–271). Argument types:

| rule | text allows | Lean | ✓ |
|---|---|---|---|
| (b) pairing + unpaired leg | Past only | `pairing : V → List V` | ✓ |
| (b) colouring order | Past only | `parOrder : List (ParObj V)` | ✓ |
| (c) grouping + numbering | Past only | `group : V × V → ℕ` | ✓ |
| (d) SDR | Past + lists | `sdr : Lists → V × V → ℕ` | ✓ |
| (e1) processing order, order of `V(G)` | Past + lists | `e1Order`, `vertOrder : Lists → …` | ✓ (v6.1 puts the `V(G)` order in the lists bullet; the blueprint's past-only `vertOrder` is superseded) |
| (e2) order of `E'(u)` | Past + lists | `e2Order : Lists → V → List (REnd V)` | ✓ |
| (g) rank order, (h) `Dec_l` | Past + `ξ_l` | `rankOrder`, `dec : Xi → …` | ✓ |

No field of (b)–(e) has an `Orders` argument; (b), (c) have no `ξ` argument at all. Dependence on the
past (including earlier `ξ_{l'}`) is through the choice of `R : Rules I` for each `I`; the run-level
`chosenRules` is a deterministic function of `ofPast … l J` ✓.

**Rules.Valid** holds side conditions only, each no stronger than the text: enumerations (Nodup +
exact set) of `frPorts x`, `parObjs`, `e1Items`, `V(G)`, `E' L u`, `layerEdges ξ`; groups numbered
`< k_h` with `≤ ⌈Hcd/8⌉` items (empty groups allowed, T0 recorded — harmless: WellDef(iii) uses only
per-item uniformity and UHsplit's `3k_h` bound is unchanged); the SDR rule returns an SDR where one
exists; `dec ξ` is an `IsDecomp` (WF objects) of `E(Q)` of length `fnum`. Every manuscript-admissible
rule is `Valid`, and `Rules.exists_valid` (`std_valid`, `0 < Hcd`) is the text's "Rules with these
arguments exist" ✓.

**chosenRules / roundOut / roundQuotient (fix round 1, m5).** `chosenRules := if h : ∃ R, R.Valid
then choose h else junkRules` (Defs, total), `roundOut run G δ S π : ℕ → Finset (Sym2 V) → List (Obj V)
× Finset (Sym2 V)` has exactly the type of `EG.Chain.JConsumer.out`, and `roundQuotient` uses the same
rules and the same `xiChosen` (`roundOut_roundQuotient`) ✓ JV-SAME-Q.

### 1.4 Xprime.lean, Constants.lean, Main/Gamma.lean

`tCC M = ⌈2 log₂ M⌉₊` ✓ (one constant for CC(iii) and `X_{V,l}`); `XVl = 3M(t+1)|Pool_l| + 4M
Σ_{w∈Pool_l} mult_{r(w)}(w)`, `XV = Σ_{l∈[3,R]}` ✓; `poolWeight` (`c^agg_{v,l}` on `D_l`, else `M_l`)
✓; `jvBadPorts` ✓; `Xpool` ✓ (`M_l − 1` exact in ℕ); `Xprime = XU + Xpool + XV` ✓; `epsX` ✓; `detl`
✓ (all four terms, `log₂ θ^ult_l`, `λ_{l-2}^95`); `FQ` ✓ (rpow); `eps2`, `thetaQ` ✓; `eps1` ✓ (six
terms, `ε_K = Chain.epsK = Light.epsChain` by `rfl`); `C0 = D/2 + 1085 + ε₁` ✓ (`\cTot = 1085`);
`Gamma4 D = ε₁ ≤ 6 ∧ ε₂ ≤ 1/4` ✓; `cEG N0 D = max (C0/(1 − 2θ_Q)) (N0/2)` ✓. `GammaCond` missing
(§5 m1, §6 r2-2).

## 2. Probability laws

- Weights: `uniform (Perm (Fin 4M))` = `1/(4M)!`; `subset3Law (4M)` = `1/C(4M,3)` on 3-subsets;
  `uniform (↥V(G) ≃ Fin n)` = `1/n!`. `FinDist.prod` is `compProd` with a constant kernel (the
  product law), `pi` is the product over the index. So `roundLaw` is the joint law of mutually
  independent `η_h`, `ζ_{h,u}`, `≺_u` ✓.
- Independence structure used later is definitional: SDR failure at `u` reads `L` only; the (e1)
  state reads `L` only; the junction of an end at `x` reads `(L, O ⟨x,_⟩)` only; distinct hubs read
  distinct `η` coordinates. Cuckoo (WellDef(iii)), CC(i), Ultra(i) and Pay(c) are therefore
  statable and true for these laws.
- Pushforward facts needed by the probes are Lib items, not Defs: the image of `{3i,3i+1,3i+2}`
  under a uniform permutation is a uniform 3-subset (for `3i+3 ≤ 4M`); the `i`-th element of a fixed
  `C ⊆ V(G)` in a uniform rank order is uniform on `C`; conditioning `roundLaw` on `{ξ.1 = L}` is
  `dirac L ⊗ ordersLaw`.

## 3. Downstream statability (blueprints s7a, s7b) — re-checked

| statement | ingredients | status |
|---|---|---|
| WellDef(i),(ii),(iv),(v) | `parObjs`, `Conflict`, `parColour`, `ultra`, `kh`, `e1Items`, `e1State`, `used`, `E'`, `cand`, `Hcd`, `M` | ✓ |
| WellDef(iii) Cuckoo | `(listsLaw I.G I.M).prob {L \| ¬ R.SDRExists L u}` | ✓ |
| MULT (+ sub-layer counts, PAR-MULT identity) | `mHub`, `mPar`, `multAt`, `poolRound`, tag membership in `(R.Q ξ).verts` | ✓; `ofPast_multAt` bridges to `run.mult` |
| Simple | `qEdge`, `rank`, `layerEdges`, `Q_noIsolated` | ✓ (rank-injectivity is the content) |
| Lift(i)–(iv), JC1–JC3 | `liftObj`, `layerOf`, `lentJV`, `objs`, `junctionEdges`, `Chain.JC1/JC2` via `ofPast` | ✓ |
| CC(i)–(iii), Ultra(i)–(iv) | `ordersLaw`, `FinDist.cond`, `iIndepFun`, `parColour`, `junction`, `mPar`, `mHub`, `tCC`, `clive`, `thult`, `lam` | ✓ |
| Pay(a1)–(e) (run level) | `Jlost`, `paidPool`, `paidJVBad`, `unpairedLegs`, `sdrPaid`, `loopPaid`, `payrd`, `MarkovEvent`, `paidEdges`, `poolWeight`, `cAgg` | ✓ |
| Vstar, defXprime, EXprime | `XVl`, `XV`, `Xpool`, `Xprime`, `epsX`, `Stage1.law`, `StageData.ofOutcome ω …`, `ω.pool : ↥G.verts → Option (ℕ × ℕ)` | ✓ (types checked) |
| UHsplit(i)–(iv) | `copies`, tag filters on `Q.verts`, `detl`, `FQ`, `eps2`, `thetaQ`, `MarkovEvent`, `xiChosen`, `roundQuotient` | ✓ |
| OneOutcome(3) | `xiChosen_spec` + `half_le_prob_le_four_mul_expect_and` (copies, payrd ≥ 0) | ✓ |
| propCost, thmJVps | `roundOut`, `roundQuotient` (one rule, one `ξ`), `eps1`, `C0`, `QVert V : Type` for HIHyp | ✓ |
| J-consumer instance | `JConsumer.out := roundOut run G δ S π` (type identical); `jc1`, `jc2` from Lift(iv) + `ofPast_valid` | ✓ |
| lemGammaSat(iii), thmMainProof | `Gamma4`, `cEG`, **`GammaCond`** | `GammaCond` missing (r2-2) |

Index types: colours ℕ (`< 3M` PAR, `< 4M` HUB), ranks ℕ (`≥ 1`), vertices `V`, random families
over `↥G.verts`, `ζ` values `Finset (Fin 4M)`. No wrong index type. Blueprint-shape deltas for Spec
authors are listed in r2-4.

## 4. Non-vacuity: the PAR path and the rank split (`/tmp/quotrev2/ParTest.lean`)

The committed tests exercise the HUB path only (`Live.Q_nonempty`: (c) → (d) → (e1) → (g)). No test
touched (b) colouring, (e2), (e3), the rank split of parallel edges, or the lift. I built one:
`V = ℕ`, ports `0,1,2,3`, pooled vertices `4,5`, `J^par = {02, 13}`, `LJV = {04, 14, 25, 35}` (so
`cand 0 = cand 1 = {4}`, `cand 2 = cand 3 = {5}`), no hubs, no fresh centres, `M = 1`, `λ = 2`
(the input is not `Valid` — that is irrelevant here, `Rules.Valid` and the construction do not need
it; `Rules.std_valid` applies since `Hcd > 0`). Proved for **every** `R : Rules I` with `R.Valid` and
**every** `ξ` (0 errors, 0 sorry, 7.5 s, 2.6 GB):
- `parColour o₁ = some 0 ∧ parColour o₂ = some 0` (first fit in either colouring order; the two
  objects do not conflict);
- `E' L (endAt b) = {REnd.par o b}`, `e2Order` forced, `used = ∅`, and every end receives the
  junction `4` (ports `0,1`) or `5` (ports `2,3`) through `inOrder` — independently of the orders and
  of the unknown orientation of `Quot.out` in `parObjsPar`;
- neither object is looped; `layerEdges ξ = {inl o₁, inl o₂}`; both rank-0 `Q`-edges coincide
  (`[4][5]` in PAR colour `0`);
- **`rank` splits them**: `(rank o₁, rank o₂) = (1, 2)` or `(2, 1)` according to the rank list;
- `(R.Q ξ).edges = {E 1, E 2}` with `E ι = s((parTag 0 ι, 4), (parTag 0 ι, 5))`, so
  `|E(Q_l)| = 2` and `|V(Q_l)| = 4` (two sub-layers `(P, 0, 1)`, `(P, 0, 2)`, isolated vertices
  deleted);
- **the lift is correct**: `layerOf` recovers the right object in each rank case and
  `(liftObj ξ (.edge (E 1)) ++ liftObj ξ (.edge (E 2))).toFinset = {edge 02, edge 13}` — the two
  single edges of `Q_l` lift to the two `J^par` items, each once (the JC2 accounting on this input).

So (b), (e2), (e3), (g) incl. the rank split, and (h) for single edges work end to end on a valid
rule. Together with `Live.Q_nonempty` every step of the construction except cherries and the lift
of cycles has now been exercised on a concrete input. (Cherries and cycle lifts need at least three
ports with candidates per PAR cycle — a 3-cycle input is ~2× this file; left to probe P-1, whose
lemLift(ii) proof covers it for every decomposition.)

A by-product of this scratch is finding r2-1 (`LawfulBEq`).

## 5. Fix round 1 verification (round-1 findings m1–m6)

| id | status now | note |
|---|---|---|
| m1 `GammaCond` | **still open**, blocked by TRIAGE item 14 (`EG/Defs/Gamma/Full.lean` absent) | `Main/Gamma.lean` holds `Gamma4`, `cEG` only; both are correct and lockable; `GammaCond` is one additive line + import later. Carried as r2-2. |
| m2 `ofPast_multAt` | fixed (Lib) | statement and proof checked; holds for every `r`. |
| m3 shapes | fixed (docs) | in the `Schedule.lean` header and quot.md "Notes for Spec authors"; CONVENTIONS is locked, so the integrator must paste the proposed section. |
| m4 `_root_.Quot.out` | fixed | `parObjsPar` writes `_root_.Quot.out`; no `EG.Quot.{out,mk,…}` declared (checked by grep). |
| m5 one chosen rule | fixed (Defs addition) | `junkRules`, `chosenRules`, `roundOut`, `roundQuotient` + Lib `chosenRules_valid`, `roundOut_roundQuotient` ✓ (§1.3). |
| m6 live test | fixed | `EGTest.Quot.Live` (`I_valid`, `I_live`, `Q_nonempty`, `chosen_Q_nonempty`) compiles in the current tree. |

## 6. Findings

| id | severity | where | finding | fix |
|---|---|---|---|---|
| r2-1 | minor | `EG/Defs/Quot/Round.lean` `Rules.rank` (l.604–606); Lib | The `takeWhile (fun e' => e' != e)` uses the `BEq (LayerEdge V)` instance `Sum.instBEq` (built from `instBEqOfDecidableEq (ParObj V)` and `instBEqProd`). Core/Mathlib provide **no `LawfulBEq (α ⊕ β)`** instance (`#synth LawfulBEq (ParObj ℕ ⊕ ℕ × ℕ)` fails), so `bne_self_eq_false`, `bne_iff_ne`, `simp` cannot rewrite the test. The definition is semantically right (`Sum.instBEq` is equality for lawful components; the scratch proves `((inl a : LayerEdge ℕ) != inl b) = decide (a ≠ b)` by `show (!(a == b)) = _`), but every proof about `rank` (lemSimple, MULT sub-layer counts, `layerOf` uniqueness) will hit this. | Additive Lib lemmas in `EG/Lib/Quot/Round.lean`: `LayerEdge.bne_eq (e e' : LayerEdge V) : (e != e') = decide (e ≠ e')` (by `cases e <;> cases e'`, using `Prod.instLawfulBEq` and `instLawfulBEq` of `ParObj`), or a local `instance : LawfulBEq (LayerEdge V)`. Alternatively, while the Defs are still PENDING, write the test as `fun e' => decide (e' ≠ e)` (kernel-equivalent behaviour, no BEq detour); either is fine, the Lib route needs no Defs change. |
| r2-2 | minor | `EG/Defs/Main/Gamma.lean` | `GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` is still not defined (`Gamma1`, `Gamma3` do not exist in the tree). thmJVps, lemGammaSat(iii) and thmMainProof need it. Carry-over of m1; not a defect of this task. | Add it additively once TRIAGE item 14 lands; lock `Gamma4`/`cEG` now. Do not create local copies of Γ1/Γ3. |
| r2-3 | minor | `EGTest/Quot.lean` | The PAR path ((b) colouring, (e2) injections, (e3), the rank split of parallel layer edges, `layerOf`/`liftObj` of single edges) is not exercised by any test; only the HUB path is. The scratch of §4 covers it for every valid rule and every `ξ`. | Add `/tmp/quotrev2/ParTest.lean` (namespace to `EGTest.Quot.Par`, ~230 lines of content after the shared helpers, 7 s, 2.6 GB) to `EGTest/Quot.lean`, or as `EGTest/QuotPar.lean`. Its helper `bne_inl_inl` becomes the Lib lemma of r2-1. |
| r2-4 | cosmetic | Spec authors (blueprints s7a/s7b lean_shapes) | Shape deltas beyond m3 that the blueprints still show differently: `ζ` values are `Finset (Fin (4M))` under `subset3Law`, not the subtype `{s // s.card = 3}`; `listsLaw`/`roundLaw` are products of `pi`s, not `FinDist.uniform` of the whole type (equal in law, different terms); `MarkovEvent`, `xiChosen`, `copies`, `payrd` are per rule `R : Rules I` (`R.MarkovEvent ξ`), not per `(ω, l, J)`; the blueprint's `RoundOutput` record and `roundStep` do not exist — use `R.Q ξ`, `R.objs ξ`, `R.lentJV ξ`; the blueprint's `hubGroups : V → Sym2 V → ℕ` is `group : V × V → ℕ`; ranks `ι` start at `1`, so sub-layer sums run over `ι ≥ 1` (`Finset.range k` needs `ι + 1`). | Append to the proposed CONVENTIONS section of quot.md ("Notes for Spec authors"). |
| r2-5 | cosmetic | `EG/Defs/Quot/Round.lean` docstring of `rank` | "(the same edge at rank `0`)" is terse; the comparison is through the rank-0 `Q`-edge, i.e. same kind, colour and end pair. | Reword: "…with the same layer and the same two vertices (compared through their rank-`0` `Q`-edge `qEdge ξ 0`)". |
| r2-6 | cosmetic | root files | `EG.lean` / `EGTest.lean` do not yet import `EG.Defs.Quot.*`, `EG.Defs.Main.Gamma`, `EG.Lib.Quot.*`, `EGTest.Quot` (integrator-owned; quot.md open item 3). | Integrator adds the imports at lock time. |

No major findings: no missing field, no wrong index type, no rule reads more randomness than the
v6.1 text allows, no law has wrong weights or a wrong independence structure, no definition
contradicts its text.

## 7. Recorded T0 readings (confirmed, no manuscript change needed)

`ζ` drawn for all ordered pairs (never read on the diagonal); pairing + unpaired leg as one list;
0-based groups with lists `{η(3i), η(3i+1), η(3i+2)}`; empty groups allowed; first-fit greedy
colouring; `Dec_l` as the rule field `dec`; the closed-form JV threshold `candMean`; colours and
ranks as naturals; `Q.verts` as the ends of edges; the side tag on HUB vertices; the past as the
parameter `I` with `E[·|Past_l] = (roundLaw I.G I.M).expect`. No new T1/T2/T3.

## 8. Items for the joint review with design.md (not findings here)

- `RoundInput.ofPast_valid` (Spec/Proof): sources re-checked field by field (§1.3); it needs Γ1
  (COL-JV row 11 for `Hcd_ge`), lemCand(ii),(iv), s2:propStructure(iii) (for `ljv_disj`, `ljv_J`),
  `run.Valid`, `S.Coherent run G`, `IsDesignation`, and `S`, `π` from the same outcome.
- `candMean = E|Cand_l(u)|` under `Stage1.law` (lemCand(ii)) depends on per-edge independence of
  the COL colouring (CAND-INDEP-MODEL).
