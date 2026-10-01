# Clean-room definition review, round 1: P2-D [quot] (s7 quotient layer)

Reviewer: clean-room definition reviewer (round 1). Date 2026-09-26.
Scope: `EG/Defs/Quot/{Cand,Schedule,Round,Xprime,Constants}.lean`, `EG/Defs/Main/Gamma.lean`, the
Lib API `EG/Lib/Quot/*`, `EGTest/Quot.lean`, design note `work/p2d/quot.md`.
References: manuscript v6.1 `s7.tex` (defCand l.54–81, defSchedule l.158–204, consRound l.231–435
with the *Fixed rules* paragraph l.236–271, lemWellDef, lemMULT, lemSimple, lemLift, lemCC, lemUltra,
lemVstar, lemPay, defXprime, lemEXprime, lemUHsplit, propCost), `s1.tex` (condG4, defConstants),
blueprints `work/p2/blueprint_s7a.md`, `blueprint_s7b.md`, `work/p2/TRIAGE.md` §1a (patch set R),
§2.10 (QVert), and the locked `JPlusProps` / `JConsumer` of the design task.
No Lean file was edited.

## Verdict

**APPROVE.** 0 major findings. 6 minor or cosmetic findings (§6); none changes a definition body.
Every definition matches its defining text. The `Rules` argument types are exactly the v6.1
*Fixed rules* restrictions. The round laws have the right weights and independence. Every downstream
use in blueprints s7a/s7b can be stated with the given fields and types.

Checks run:
- `python3 -I scripts/lint.py`: 0 findings.
- `python3 -I scripts/lock.py check`: 419 locked constants, 0 violations. The new Defs are PENDING.
- Non-vacuity scratch at `/tmp/quotrev1/NonVacuity.lean` (a copy of
  `…/scratchpad/quotrev/NV9.lean`): compiles, 0 errors, 0 `sorry`, peak RSS 2.6 GB. See §4.

## 1. Back-translation and comparison, definition by definition

### Cand.lean (s7:defCand)
| Lean | back-translation | manuscript | verdict |
|---|---|---|---|
| `HcdOf M λ = λ^95/(8M²)`, `Hcd run G l = HcdOf (M_l) (λ_{l-2})` | Hcd_l | "Put `Hcd_l := λ_{l-2}^{95}/(8M_l^2)`" | ✓ |
| `thultOf M H = ⌊M H/7⌋₊`, `thult` | θ^ult_l | (c) "`θ^ult_l := ⌊M_l Hcd_l/7⌋`" | ✓ |
| `cand π l u = {w ∈ Pool_{l,r(u)} : s(u,w) ∈ S.ljv (δ l u) l}` | Cand_l(u) | "`Cand_l(u) := {w ∈ Pool_{l,r(u)} : uw ∈ LJV_{Y,l}}`" | ✓ (`Y(u) = δ l u`, `r(u) = (δ l u).1`) |
| `candMean = q_l π_{l,r} p_Y deg_{H_Y}(u)` | E\|Cand_l(u)\| in closed form | lemCand(ii), first equality | ✓ T0 (CAND-MEAN-DEF, TRIAGE); equality with the stage-1 expectation is a Spec obligation |
| `JVBad = u ∈ classedPorts ∧ \|cand\| < candMean/2` | JV-bad | "`|Cand_l(u)| < ½ E|Cand_l(u)|` … applies to every classed port, whether or not it lies in `Lost_l`" | ✓ `classedPorts` = ⋃ Q_Z (lost ports included); strict `<` as in the text |

Edge cases: `pY` is junk 0 when `k_lend = 0`, i.e. for `r ≥ R−1`. That never happens for a class,
since `r ≤ l−2 ≤ R−2`. For `u ∉ V(H_Y)` we get `candMean = 0` and `u` is JV-good. A valid designation
excludes this (`u ∈ V(Y(u))`, degree `> s_Y`), and `good_cand` then needs lemCand, which is correct.

### Schedule.lean (s7:defSchedule, "Rounds")
| Lean | manuscript | verdict |
|---|---|---|
| `Lists = (V(G) → Perm (Fin 4M)) × (V(G)² → Finset (Fin 4M))` | "a uniformly random bijection `η_h:[4M_l]→[4M_l]` for every vertex `h`; a uniformly random 3-subset `ζ_{h,u}` … for every ordered pair `(h,u)` of distinct vertices" | ✓. ζ is drawn also for `h = u`; these are extra independent coordinates that are never read (T0, recorded) |
| `Orders = V(G) → (V(G) ≃ Fin n)` | "a uniformly random linear order `≺_u` of `V(G)` for every vertex `u`" | ✓. The uniform law on ranks is the uniform law on linear orders |
| `roundLaw = (pi uniform-perm × pi subset3Law) × pi uniform-rank` | "mutually independent variables" | ✓ |
| `subset3Law K = (uniform {s // s.card = 3}).map val` (junk `dirac ∅` if `K < 3`) | "uniformly random 3-subset" | ✓. The weight is `1/C(K,3)` on each 3-subset (`map` of an injective map). The junk case needs `M = 0`, and `Valid` excludes it |
| `inOrder O u C` = `C ∩ V(G)` listed by increasing rank of `O u` | "`w_1 ≺_u w_2 ≺_u ⋯` the elements of `Cand_l(u) \ Used(u)` in the order `≺_u`" | ✓. It uses the order of the **port** `u` |
| `etaAt`, `zetaAt` (junk off `V(G)`) | — | ✓. Hubs and ports are ends of `G`-edges (`J_sub`), so the junk is never read |

"Freshness" and `E[·|Past_l]` are definitional: the past is the parameter `I`, and
`E[X|Past_l] = (roundLaw I.G I.M).expect X`. "Given the lists" is `(ordersLaw I.G).expect (X (L,·))`.
This is correct because `roundLaw` is a product (conditioning on `{ξ.1 = L}` is a Lib lemma for later).

### Round.lean (s7:consRound)
**RoundInput and Valid.** The fields are the past as the round step reads it. Checked against the locked
`JPlusProps` and its Lib shapes:
- `J1` is verbatim `JPlusProps.J1hub_ports`. It holds for every `h`: for `h ∉ D_l` the filter is
  empty because of the roles.
- `J2` is `JPlusProps.degE_types_le` / `J2out`: "a vertex outside `D_l` carries at most `M_l − 1`
  J-edges", which also covers fresh and lost centres. It is used by WellDef(i), (v), Pay(a1), (a3), CC and Ultra.
- `J2tot` is `J2card`, and `J_sub` is `subset_edges` through `ofPast_J`.
- The typed endpoints and `roles` are (i) and (J3).
- `ljv_disj` and `ljv_J` are propStructure(iii) + `Coherent.ljv_sub` / `ljv_eq_empty`. The class of
  round `l` itself has `LJV = ∅`, so `ljv_J` also holds for `Y ∈ Std_l`.
- `lendGood_ports` is `not_lendBad_of_mem_qs`, and `good_cand` is lemCand(iv).

I checked every proof step of WellDef(i)–(v), MULT, Simple, Lift(i)–(iv), CC, Ultra and
Pay(a1)–(c) against the field list. Nothing is missing. For example:
- MULT uses `J1`, `ljv_in` (→ `w ∈ V(Y(u))`), `cls_anc`, the pool round and `multAt`.
- Lift(ii) uses `roles`, `Live ∩ Pool = ∅` (definitional from (a2)), `ljv_in` for adjacency, and
  `ljv_J` for items ≠ junction edges.
- JC1 uses `cls_round`, `lendGood_ports` and `cls_anc`, which give membership in `lendGoodAnc`.

Nothing in the list is unprovable for `ofPast`: the interface map of quot.md was re-checked field
by field.

**Items and payments (a).**
- `items = J \ J^lost` ✓.
- `paidPool` = items with an end in `Pool_l` ✓. The vertices of an item are its two ends: the port
  end(s) and the centre.
- `paidJVBad` = items with an end that is a JV-bad port ✓.
- `live` ✓, `liveVerts` ✓.
- `hubItems ⊆ D_l × ports` ✓. By `roles` a `J^hub` edge has exactly one port end, so there is no
  double counting.
- `frPorts` ✓, `parItems` ✓.

**(b)**
- `pairing x` is one list per fresh centre. Its consecutive pairs are the cherries, and the last
  element of an odd list is the unpaid leg. Every "pairing + choice of unpaired leg" has this form
  and conversely, so quantifying over valid lists is quantifying over admissible pairing rules ✓.
- `parObjs` = the live `J^par` items plus the cherries ✓.
- `parColour` is first-fit greedy over `parOrder` in `[0,3M)`. Conflict = a shared end (port) or a
  shared middle ✓.

**(c)**
- `clive` ✓, `ultra` (`θ^ult < c_h`) ✓, `kh = ⌈8c_h/Hcd⌉₊` ✓, `groupCap = ⌈Hcd/8⌉₊` ✓.
- `hubList` is `listOf (η_h) (group it)` for non-ultra hubs and `ζ_{h,u}` for ultra hubs ✓.
- `listOf η i = {η(3i),η(3i+1),η(3i+2)}` is the 0-based form of the 1-based text ✓.

**(d)**
- `SDRExists` is literally "pairwise distinct colours for its live hub items, each from its
  group's list" ✓.
- `hubColour` / `colouredHub` / `sdrPaid` ✓. On an SDR failure all live hub items of the port are paid.

**(e1)**
- A `foldl` over `e1Order L` with explicit `Used(u)` and `Used_κ(h)`.
- Each step picks the first `w` of `vertOrder L` in `Cand(u) \ Used(u) \ Used_κ(h)` and adds it to
  both sets. Only coloured items of non-ultra hubs are processed ✓.

**(e2)**
- `E'(u)` = the ends at `u` of all PAR objects plus the coloured ultra-hub items at `u` ✓.
- `e2Junc`: the `i`-th entry of `e2Order L u` gets the `i`-th element of
  `inOrder O u (Cand(u) \ Used(u))` ✓.
- `Used` depends on `L` only, and so do `E'` and its order. So given `L` the map is a uniformly
  random injection, independent over ports. This holds definitionally from the types.

**(e3)**
- `Looped` = both junctions exist and are equal ✓.
- `loopPaid` = one edge for a `J^par` object, two for a cherry (`edgeList`) ✓.

**(g)**
- `layerEdges` = unpaid PAR objects plus coloured hub items ✓.
- `qEdge ξ ι` gives `[w₁][w₂]` tagged `(PAR, κ, ι)` when `w₁ ≠ w₂`, and `h[w]` tagged
  `(HUB, κ, ι)` with side tags ✓.
- `rank e` = 1 + #(earlier entries of `rankOrder ξ` with the same rank-0 Q-edge, i.e. the same
  layer and endpoints). This is "the `i`-th edge of such a list has rank `i`" ✓, and ranks start at 1.
- `Q.verts` = the ends of the edges ("isolated vertices deleted") ✓.
- `Q.loopless` is proved in the definition: PAR by `w₁ ≠ w₂`, HUB by the side tag ✓.
- Tags `(kind, κ, ι)` make the sub-layers vertex-disjoint ✓.
- `QVert V = QTag × V : Type` for `V : Type`, as `EG.Spec.HIHyp` needs ✓.

**(f)**
- `copies = |V(Q)|` ✓, `payrd = |sdrPaid ∪ loopPaid|` ✓. The two sets are disjoint: `J^hub` edges
  versus `J^par`/`J^fr` edges.
- `MarkovEvent`: both expectations are under `roundLaw` ✓.
- `xiChosen` chooses a positive-weight outcome in the event, with the fallback `arbitrary` (TRIAGE §2.10) ✓.

**(h)**
- `liftObj (.edge q)` = the one or two J-edges of the PAR object, or `hu` ✓.
- `liftObj (.cycle c)` = one cycle whose vertex list is
  `⋃_{(a,b) consecutive} a.2 :: interior(layerOf ab, a.2)`. Checked by hand:
  - A PAR cycle gives `w₀ p₀ (x₀) q₀ w₁ …` ✓.
  - A HUB cycle gives `h₀ u₀ w₀ u'₀ h₁ …`, and the same when the cycle starts at a junction copy or
    runs in the reverse direction ✓.
  - `c.zip (c.rotate 1)` matches `cycleEdges` ✓.
- `lentJV` = the junction edges lying on an edge of a lifted cycle of `dec ξ` (literal) ✓.
- `objs` = paid single edges ((a), (b) legs, (d), (e3)) followed by the lifts of `dec ξ` ✓.
- `out` has the type of `JConsumer.out` ✓.

**JC2 provability sanity check** (not a proof). Every `J`-edge is covered exactly once:
- `J^lost` and the (a2)/(a3) items are in `paidA`.
- Live `J^par` items are PAR objects, and live `J^fr` items are cherries or unpaired legs
  (`Valid.pairing`).
- Live `J^hub` items are coloured or in `sdrPaid`.
- A PAR object is looped (`loopPaid`) or an unpaid layer edge. Each layer edge is in exactly one
  `Q`-edge (rank-injectivity from `Valid.rankOrder`), and each `Q`-edge is in exactly one member of `dec`.

Junction edges never collide with `J` (`ljv_J`). Every junction edge determines its end: `Used(u)`
plus the injectivity of (e2), and ends are never at pooled vertices. So the definitions support
`JC2 J lentJV objs`, provided no fallback is taken (WellDef).

### Rules and Rules.Valid (v6.1 *Fixed rules*)
| rule (text) | allowed arguments (text) | Lean field type | ✓ |
|---|---|---|---|
| pairing + unpaired leg (b) | Past only | `pairing : V → List V` | ✓ |
| colouring order (b) | Past only | `parOrder : List (ParObj V)` | ✓ |
| grouping + numbering (c) | Past only | `group : V × V → ℕ` | ✓ |
| SDR (d) | Past + lists | `sdr : Lists → V × V → ℕ` | ✓ |
| processing order (e1) | Past + lists | `e1Order : Lists → List (V × V)` | ✓ |
| order of V(G) (e1) | Past + lists | `vertOrder : Lists → List V` | ✓ |
| order of E'(u) (e2) | Past + lists | `e2Order : Lists → V → List (REnd V)` | ✓ |
| rank order (g) | unrestricted | `rankOrder : Xi → List (LayerEdge V)` | ✓ |
| Dec_l (h) | unrestricted | `dec : Xi → List (Obj (QVert V))` | ✓ |

"None of the rules of steps (b)–(e) reads the orders `≺_u` of `ξ_l`": no field of (b)–(e) takes an
`Orders` argument, and none of (b), (c) takes `Lists`. "Through `Past_l` the rules may depend on the
draws `ξ_{l'}`": this is covered because `R : Rules I` is arbitrary for each past `I`. The
construction reads `ξ.2` only in `e2Junc` (through `inOrder`), which is exactly "the orders enter
only through `e_i ↦ w_i`" ✓.

`Rules.Valid` holds the side conditions only, each no stronger than the text:
- each enumeration is Nodup and covers exactly the right set;
- the groups of a non-ultra hub are numbered `< k_h`, each of size `≤ ⌈Hcd/8⌉`;
- where an SDR exists, the rule returns one;
- `dec` is a decomposition of `E(Q)` of length `f(Q)`.

Every manuscript-admissible rule is `Valid`:
- a per-layer, per-pair rank order merges into one global list;
- "exactly `k_h` groups" is a special case of numbers `< k_h`. Empty groups are allowed; this is a
  superset, recorded as T0.

`Rules.exists_valid` ("Rules with these arguments exist") is proved ✓.

### Xprime.lean (lemVstar, lemPay(a2), defXprime) and Constants.lean
- `tCC M = ⌈2log₂M⌉₊`. One constant, shared by lemCC(iii) and X_{V,l} ✓.
- `XVl = 3M(t+1)|Pool_l| + 4M Σ_{w∈Pool_l} mult_{r(w)}(w)` ✓. `XV = Σ_{l∈[3,R]}` ✓.
- `poolWeight` = `c^agg_{v,l}` if `v ∈ D_l`, else `M_l` ✓. `jvBadPorts` = the JV-bad classed ports
  (lost ports included) ✓.
- `Xpool = Σ_{l∈[3,R]} [Σ_{Pool_l} ω_l + (M_l−1)·#JV-bad]` ✓. `Xprime = XU + Xpool + XV` ✓.
  All values are in ℕ, and `M_l − 1` is exact because `M_l ≥ 2^40`.
- `epsX = ε_U + 10.3/D + 2.1(6log₂D+12)/D` ✓ (lemEXprime).
- `detl = 3|D_l| + 78nM/Hcd + 30n/M + 320nM³(log₂θ^ult+8)/λ_{l-2}^95` ✓.
- `FQ(x) = (3184+30400log₂x)x^{-90.2}` ✓ (rpow).
- `eps2 = 12ε_X + 4(3ε_A + 60/D + 2F(log₂D))` ✓, `thetaQ = eps2` ✓.
- `eps1 = ε_K + 169ε_A + 252/D + 1.5ε_CONC + 3ε_X + 9/D` ✓.
- `C0 = D/2 + 1085 + ε_1` ✓ (the macro `\cTot` = 1085 was checked).

### Main/Gamma.lean
- `Gamma4 D := ε_1(D) ≤ 6 ∧ ε_2(D) ≤ 1/4` ✓ (s1 condG4).
- `cEG N0 D = max(C0/(1−2θ_Q), N0/2)` ✓ (defConstants (vi)).
- `GammaCond` is missing: see m1.

## 2. Probability laws
- Weights:
  - `uniform` on `Perm (Fin 4M)` has weight `1/(4M)!`.
  - `subset3Law` has weight `1/C(4M,3)` on each 3-subset and 0 elsewhere (`card_of_mem_supp_subset3Law`).
  - `uniform` on `V(G) ≃ Fin n` has weight `1/n!`.
- Independence: `pi` over vertices and ordered pairs, `prod` of the lists and the orders. This is
  the manuscript's "mutually independent" family.
- Pushforward claims used later are true for these laws:
  - the image of `{3i,3i+1,3i+2}` under a uniform `η` is a uniform 3-subset if `3i+3 ≤ 4M`;
  - the `i`-th element of a fixed `C` in a uniform rank order is uniform on `C`.
  Both are Lib/SCHED-UNIFORM-LEMMAS items, not Defs.
- The SDR-failure event reads only `L`. The junction of an end at `x` reads only `(L, O x)`. So the
  Cuckoo, CC and Ultra independence structure is definitional.

## 3. Downstream statability (blueprints s7a/s7b)
| downstream statement | needs | available |
|---|---|---|
| WellDef(i) palette | `parObjs`, `ParObj.Conflict`, `parColour` | ✓ |
| WellDef(ii) | `ultra`, `clive`, `kh`, `M` | ✓ |
| WellDef(iii) Cuckoo | `(listsLaw I.G I.M).prob {L \| ¬ R.SDRExists L u}` | ✓ |
| WellDef(iv),(v) | `e1State`, `hubColour`, `junction`, `used`, `E'`, `cand` | ✓ |
| MULT (+ sub-layer counts) | `mHub`, `multAt`, `poolRound`, `(hubTag κ ι b, x) ∈ (R.Q ξ).verts` | ✓ |
| PAR-MULT identity (S7-UNLABELLED-PAR-MULT) | `mPar`, `parTag` | ✓ |
| Simple | `qEdge`, `rank`, `layerEdges`, `Q` | ✓ (rank-injectivity is the content, as planned) |
| Lift(i)–(iv), JC1–JC3 | `liftObj`, `lentJV`, `objs`, `junctionEdges`, `Chain.JC1/JC2` via `ofPast` | ✓ |
| CC(i)–(iii) | `ordersLaw`, `FinDist.cond`, `parColour`, `junction`, `mPar`, `tCC` | ✓ |
| Ultra(i)–(iv) | `ordersLaw`, `mHub`, `clive`, `thult`, `lam` (Hcd definitional in λ, M) | ✓ |
| Pay(a1)–(e) | `Jlost`, `paidPool`, `paidJVBad`, `unpairedLegs`, `sdrPaid`, `loopPaid`, `poolWeight` | ✓ |
| Vstar, defXprime, EXprime | `XVl`, `XV`, `Xpool`, `Xprime`, `epsX`, stage-1 law (Stage1) | ✓ |
| UHsplit(i)–(iv) | `copies`, `Q` tags, `detl`, `FQ`, `eps2`, `thetaQ`, `MarkovEvent`, `xiChosen` | ✓ (needs m2's bridge lemma) |
| OneOutcome(3) `xiChosen_mem` | `xiChosen_spec` | ✓ |
| propCost, thmJVps | `out`, `quotient` (same `ξ`), `eps1`, `C0`, `QVert V : Type` | ✓ (see m5) |
| lemGammaSat, thmMainProof | `eps1`, `eps2`, `Gamma4`, `cEG`, **`GammaCond`** | `GammaCond` missing (m1) |

Index types: colours are ℕ (`< 3M` PAR, `< 4M` HUB), ranks are ℕ (≥ 1), vertices are `V`, and
families are indexed by `↥G.verts`. No wrong index type was found. See m3 for the blueprint-shape
differences.

## 4. Non-vacuity (scratch, `/tmp/quotrev1/NonVacuity.lean`)
The existing test `I1` is valid, but nothing in it is live: its only port is JV-bad. `I3` has a live
item, but it is invalid (`M = 1`). A valid input with a live item needs `|Cand(u)| ≥ Hcd ≥ 2^{410}`.
I built one on `V = ℕ` with `N := 2^500` (an `irreducible_def`):
- the graph is the star `1–w` for `w ∈ [2,N)`, plus the edge `01`;
- the hub is `0`, the port is `1`, the class is `(1,[])`;
- `Pool_l = [2,N)`, `LJV = {1w}`;
- `M = 2^40`, `λ = 64`, so `Hcd = 2^487`.

Proved (0 errors, 0 sorry):
- `I_valid : I.Valid`. All 22 fields hold, including `Hcd_ge`, `good_cand` and `J1`/`J2`.
- `I_live : I.live = {s(0,1)}`, `I_hubItems = {(0,1)}`, `¬ I.ultra 0`, `I.kh 0 = 1`.
- `Q_nonempty : ∀ R : Rules I, R.Valid → ∀ ξ, (R.Q ξ).edges.Nonempty`. For every valid rule and
  every outcome:
  - the group is forced to 0;
  - an SDR exists;
  - `e1Order` is forced to `[(0,1)]`;
  - (e1) finds a junction;
  - the coloured hub item gives a HUB edge of `Q`.

So `Valid` and `Rules.Valid` are not vacuous, the construction is not degenerate on valid inputs,
and the (c)/(d)/(e1)/(g) chain works end to end.

A note for later test writers: a first attempt with `def N := 2^500` (reducible) blew up to more
than 9 GB in `simp`/kernel reduction of `Finset.Ico 2 N`. Use `irreducible_def` and
`set_option exponentiation.threshold`.

## 5. Faithfulness of docstrings, labels, conventions
- Every declaration that formalizes text carries a `[s7:…]` / `[s1:…]` / `[s2:…]` label and quotes
  the defining sentence.
- The T0 readings are all recorded in quot.md: ζ for all pairs, the pairing list, 0-based groups,
  empty groups allowed, first-fit greedy, `Dec` as a rule field, and the closed-form JV threshold.
- No forbidden tokens were found. The Lib/test files use `Classical` only through `open Classical in`.

## 6. Findings

| id | severity | where | finding | fix |
|---|---|---|---|---|
| m1 | minor | `EG/Defs/Main/Gamma.lean` | `GammaCond N0 D := Gamma1 ∧ Gamma2a ∧ Gamma3 ∧ Gamma4` is not defined. TRIAGE §3 item 34 lists it here. It is blocked by the missing `EG/Defs/Gamma/Full.lean` (item 14). thmJVps, thmMainProof and lemGammaSat need it. | Add it additively once item 14 lands (one line + import). Until then do not mark Main/Gamma "complete". Locking the present `Gamma4`/`cEG` is fine, since the addition is additive. |
| m2 | minor | `EG/Lib/Quot/Round.lean` | There is no bridge `ofPast_multAt : (ofPast … l J).multAt r w = run.mult G r w` (for `1 ≤ r ≤ R`). `RoundInput.multAt` counts `run.ancestors` of round `r` containing `w`, while `XVl` uses `run.mult` (pre-part addresses of round `r`). UHsplit(ii) ("junction copies ≤ 4M Σ mult_{r(w)}(w)", which is the X_{V,l} term) needs them to agree. By the definitions they do: `run.parts = ⋃_{l∈[1,R]} {(l,a) : a ∈ prePartAddrs l}`, and `prePartAddrs` is `∅` outside `[1,R]`, so the equality even holds for all `r`. | Add the Lib lemma (additive). |
| m3 | cosmetic | CONVENTIONS / Spec authors | Colours are ℕ (`κ < 3M` PAR, `κ < 4M` HUB), not `Fin`. `Lists`/`roundLaw` take `M`, not `4M`. The blueprint lean_shapes write `κ : Fin (4 * I.M)` and `roundLaw I.G (4 * I.M)`. | Add a CONVENTIONS line: "s7 colours are naturals; sum over `Finset.range (3 * I.M)` / `(4 * I.M)`; `roundLaw I.G I.M` (the factor 4 is inside `Lists`)". |
| m4 | cosmetic | namespace `EG.Quot` | Inside `namespace EG` (and `EG.Quot`), the identifiers `Quot.out`, `Quot.mk`, `Quot.sound`, `Quot.ind`, `Quot.lift` resolve to `EG.Quot.*` first. Round.lean itself uses core `Quot.out` (`parObjsPar`). This is correct today only because no `EG.Quot.out` exists. A later addition of such a name would silently change the meaning of new Spec text (locked terms are already elaborated). | Never declare `EG.Quot.{out,mk,sound,ind,lift,rec}`. Write `_root_.Quot.out` in new s7 code, or note this in CONVENTIONS. |
| m5 | minor | Lib (design) | `out` and `quotient` are per rule `R`. The J-consumer instance and thmJVps (JV-SAME-Q) must use the same chosen `R` for both, and the same `ξ` (`xiChosen`, as the Defs already do). | Add one Lib/Proof definition, e.g. `RoundInput.chosenRules (h : I.Valid) := Classical.choose (Rules.exists_valid h)`, and use it for both. |
| m6 | minor | `EGTest/Quot.lean` | No test has a valid input with a live item, so the construction is never exercised on a valid input. | Add the scratch lemmas of §4 (`I_valid`, `I_live`, `Q_nonempty`; ~220 lines, 2.6 GB peak) to EGTest, or a trimmed version. |

No major findings:
- no missing field;
- no wrong index type;
- no rule reads more randomness than allowed;
- no law has wrong weights;
- no definition contradicts its text.

## 7. Items for the joint review with design.md (not findings here)
- `RoundInput.ofPast_valid` (Spec/Proof). Field sources were re-checked (quot.md interface map). They
  need Γ1 (row 11, lemCand), `run.Valid`, `S.Coherent`, `IsDesignation`, and `S`/`π` taken from the
  same outcome.
- The closed-form `candMean` equals `E|Cand_l(u)|` under `Stage1.law` (lemCand(ii)). This depends on
  the per-edge independence of the COL colouring (CAND-INDEP-MODEL).
