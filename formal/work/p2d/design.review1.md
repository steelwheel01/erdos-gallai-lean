# Clean-room definition review, round 1: P2-D [design] (s6 interfaces)

Reviewer: clean-room definition reviewer (round 1), 2026-09-26.
Scope: `EG/Defs/Chain/{Design,Lending,JSet,JConsumer,Constants}.lean`, their Lib API
(`EG/Lib/Chain/{Design,Lending,JSet,JConsumer,Constants}.lean`) and `EGTest/Design.lean`, against manuscript
v6.1 (`s6.tex` 238–260, 390–407, 443–460, 618–677, 757–812; `s5.tex:227`, `s5.tex:360`; `s1.tex:1679–1686`;
`s7.tex:231–245`), blueprints s6a (defDesign, CONC), s6b (all nodes), s7a (RoundInput), s7b (Pay, propCost,
thmJVps, OneOutcome), TRIAGE §1b MULT-J1, §2.8–§2.10, §3 items 24–28 and the gate "items 26, 27, 31 reviewed
together", and the design note `work/p2d/design.md`. No Lean file was edited.

## Verdict: REVISE (additions only; no existing definition needs to change)

All definitions back-translate to the manuscript text, with the readings recorded in design.md. I found no
unfaithful definition, no wrong index type and no wrong probability model. One **major** interface gap blocks
stating the downstream Specs: the stage-data record `StageData` has no coherence predicate and no instantiation
from a stage-1 outcome. JS-LC (probe P-2), s6:lemLost and every s7 Spec that quantifies over `ω` therefore cannot
be stated with the Defs that exist now. The fix is additive, so these five files can be locked as they are once the
additions are reviewed. There are also four minor items and two cosmetic ones.

Mechanical status (re-checked): `python3 -I scripts/lint.py`: 0 findings. `python3 -I scripts/lock.py check`:
0 violations (the new files are PENDING). The built oleans of all ten modules are present.

## 1. Back-translation, definition by definition

| Lean | back-translation | manuscript (quoted) | verdict |
|---|---|---|---|
| `Designation V := ℕ → V → PartId` and `IsDesignation` | for every `l ≥ 3`, every `a ∈ Std_l` and every `u ∈ Q_a`, `δ l u ∈ anc_l(u)` | s6:defDesign "A designation δ assigns, for every round l≥3, to every standalone pre-part Z∈Std_l and every classed port u∈Q_Z an ancestor Y(u)∈anc_l(u) … δ is any deterministic function of the run" | faithful. The round index is needed (DES-CLASS-DEPENDS-ON-ROUND). The function is total, with junk values off the classed ports. It is a parameter bound before any law. Existence (`exists_isDesignation`) uses only the run. |
| `classedPorts l` | `⋃_{a∈Std_l} Q_a` | "a classed port of round l" | faithful |
| `classDeg Y l h` | the number of edges `e ∈ ⋃_{a∈Std_l} E_l(a)` with `e = hu`, `u ∈ Q_a`, `δ l u = Y` | "d_{Y,l}(h):=#{hu∈E_l(Z): Z∈Std_l, u∈Q_Z, Y(u)=Y}" | faithful and literal (it counts edges). `classDeg_eq_card_ports` holds for every run: `E_disjoint` has no validity hypothesis. |
| `mY Y l` | `max_{h∈V(G)} classDeg` (`Finset.sup`, which is 0 on ∅) | "m_{Y,l}:=max_h d_{Y,l}(h), the maximum over all vertices h of G" | faithful |
| `dStar Y l` | the number of `u ∈ classedPorts l` with `δ l u = Y` and `u ∈ Dup*_{Y.1}` | "d*_{Y,l}:=#{u: u a classed port of round l, Y(u)=Y, u∈Dup*_r}" | faithful (`r = r(Y) = Y.1`) |
| `alphaY Y l` | `sup_{x∈S_Y}` of the number of `u ∈ V(Y) \ Dup*_r` with `∃ a∈Std_l, u∈Q_a ∧ δ l u = Y ∧ xu∈E_l(a)` | "α_{Y,l}:=max_{x∈S_Y}#{u∈Y∖Dup*_r: u a classed port of round l, Y(u)=Y, xu∈E_l(Z_u)}, with α_{Y,l}:=0 if S_Y=∅" | faithful. `Z_u` is written with ∃, and uniqueness is a lemma. Only meaningful for light Y, as stated. |
| `Bead Y l` | edges `e ∈ E_l(a)`, `a∈Std_l`, such that `∃ h u, e = hu ∧ u∈Q_a ∧ δ l u = Y ∧ (h∉Q_a ∨ δ l h ≠ Y)` | "Bead_{Y,l}:={hu∈E_l(Z): …, and h∉Q_Z or Y(h)≠Y}" | faithful and literal. An edge with both ends in `Q_a` of class `Y` is excluded under both orientations. |
| `gammaL l` | `⌊P_{l−2}/M_l⌋₊` | "γ_l:=⌊P_{l−2}/M_l⌋" | faithful (M_l ∈ ℕ). The value for l ≤ 2 is junk and never read. |
| `IsGiant Y l` | `∃ C ∈ edgeComps (Bead), 2γ_l < #compEdges C` | "the pair (Y,l) is giant iff some connected component of Bead_{Y,l} has more than 2γ_l edges" | faithful (components of `(V(Bead), Bead)`) |
| `cAggClasses`, `cAgg h l` | `#(δ l)''{u ∈ Q_a, a∈Std_l : hu∈E_l(a)}` | "c^agg_{h,l}:=#{Y: d_{Y,l}(h)≥1}" | faithful. `mem_cAggClasses_iff` gives equality with the set in the text. |
| `cFresh l a x`, `cPP l a u` | the number of distinct classes `δ l v`, `v∈Q_a`, with `xv` (resp. `uv`) `∈ E_l(a)` | "c_x(Z):=#{Y(u): u∈Q_Z, xu∈E_l(Z)}", "c_pp(u):=#{Y(v): v∈Q_Z, uv∈E_l(Z)}" | faithful |
| `StageData` | an axiom-free record: `colA colB demoted : PartId → Prop`, `lab`, `own`, `ljs`, `ljv`, `dem`, `lp` | s6:defLending "Fix a valid run, a designation δ and a stage-1 outcome …" | acceptable (D-DES-1), but see **MAJOR-1** |
| `lendBad Y` | `(light ∧ demoted) ∨ ¬COL(a) ∨ ¬COL(b)` | "Y is a demoted light part …, or an event of Lemma COL(a) fails for Y, or an event of Lemma COL(b) fails for Y" | faithful |
| `lendGoodAnc l` | ancestors with `Y.1+2 ≤ l ∧ ¬lendBad` | "Y a lend-good ancestor of a round ≤ l−2" (JC1, JS-LC) | faithful. `run.ancestors` covers light and standalone parts of rounds [1,R]. |
| `Tj Y l j` | `{y∈V(Y) : lab = some j}` | s3:defCOL(iv) "T_j(Y,l):={y∈V(Y): lab_{Y,l}(y)=j}" | faithful. It duplicates `Stage1.Tj`; see MINOR-2. |
| `lost l a` | `if 3 ≤ l then {u∈Q_a : lendBad(δ l u) ∨ lab(δ l u, l, u) ≠ none} else ∅` | "For l≥3 … Lost_Z:={u∈Q_Z: Y(u) is lend-bad, or lab_{Y(u),l}(u)≠*} … For l≤2 put Lost_Z:=∅" | faithful. `lab` is read only at `Y(u) ∈ anc_l(u)`, i.e. on its domain (LEND-LAB-DOMAIN). |
| `ret`, `qs` | `A∪F∪Lost`, `Q\Lost` | "Ret_Z:=A_Z∪F_Z∪Lost_Z … Q*_Z:=Q_Z∖Lost_Z"; the l≤2 clause is proved as lemmas | faithful |
| `OZ l a` | `X^0_a` if `(l,a)` is lend-bad, else `ofEdges Z^0 (own (l,a))` | "O_Z:=Own_Z if the ancestor Z is lend-good, and O_Z:=X^0_Z otherwise" | faithful. `ofEdges` drops loops and edges leaving `Z^0`, and both are absent from `Own_Z ⊆ E(X^0_Z)`. |
| `lostRound`, `XU` | `⋃_{Std_l} Lost_Z`; `80 dem + 369 lp + Σ_{l∈[1,R]}(169+M_l)|Lost_l|` in ℕ | "Lost_l:=⋃…", "X_U:=80 dem+369 lp+Σ_l(169+M_l)|Lost_l|" | faithful (LEND-XU-RANGE) |
| `freshCentres`, `qsRound` | `⋃ F_Z`, `⋃ Q*_Z` | (J3) "⋃_Z F_Z (fresh centres) and ⋃_Z Q*_Z (classed non-lost ports)" | faithful |
| `IsJparEdge`, `IsJhubEdge`, `IsJfrEdge`, `IsJlostEdge` | for some `a∈Std_l` with `e∈E_l(a)`: both ends in `Q*_a` with different classes / `e = hu`, `h∈A_a`, `u∈Q*_a`, class `δ l u` / likewise for `x∈F_a` / likewise for `v∈Lost_a` | s6:lemJplus type list; "The class of a J^hub-, J^fr- or J^lost-edge hu is Y(u)" | faithful |
| `jBound l` | `Σ_{h∈D_l} c^agg + Σ_{a∈Std_l}[Σ_{x∈F_a} c_x + (M−1)|Lost_a| + ½Σ_{u∈Q_a} c_pp]` in ℝ | (s6:eqJbound) | faithful |
| `JPlusProps` | see §2 | s6:lemJplus (i) exhaustive, (J1)×3 aggregated, (J2)×4, (ii) | faithful |
| `JC1`, `JC2`, `JC3`, `JConsumer` | `L ⊆ ⋃_{Y∈lendGoodAnc l} ljv Y l`; `IsDecomp (J∪L) Ob`; `out : ℕ → Finset → List Obj × Finset` with jc1/jc2 for `3≤l≤R` and JPlusProps inputs | s6:defJconsumer (JC1)–(JC3) | faithful (TRIAGE §2.9) |
| `epsCONC` | `2^{σ+15}·log*D/log D + 200ε·log*D/(C'·log log D) + 4(2log*D+2)/(log D)^{1/2}` | s6.tex:347 and s1.tex:1682 (identical) | faithful. The parse is checked: `Real.logb 2 D ^ (1/2)` is `(log D)^{1/2}`. |
| `epsK` | `614/D + log₂(2A log₂(A log₂log₂D)) / (371 (log₂log₂D)^2)` | s5.tex:227 ε_ch, s5.tex:360 "ε_K(D_*) := ε_ch(D_*)" | faithful. It duplicates s5; see MINOR-3. |
| `epsM` | `epsK + 169 ε_A + 252/D` with the locked `HB.epsA = 31ε/(C' log log D)` | s6:thmMIXC(c) | faithful |

## 2. JPlusProps field by field (the P-2 refutation target)

- `types`: the exhaustive half of (i). The exclusive half is J-independent, and I checked that the six `not_is*Edge`
  lemmas carry no validity hypothesis.
- `J1hub : ∀ h ∈ D_l, ∀ Y, #(J.filter (IsJhubEdge l h Y)) ≤ 1`. The filter runs over the whole of `J`, and
  `IsJhubEdge` contains `∃ a` (any part of round l). This is the **aggregated** (J1) of JS-LC Step 2b and
  TRIAGE MULT-J1. `¬ J1hub` is literally "two J^hub-edges of one class at one hub in one round", the named
  refutation target.
- `J1fr`, `J1lost`: aggregated as well. They are equivalent to the per-part forms because such a centre lies in one
  part.
- `J2end`, `J2cap`, `J2out`, `J2card`: the four sentences of (J2). `J2out` is the "in particular", stated for every
  vertex outside `D_l`, which is what s7 needs. `J2card` is the sharp `n(M_l−1)` (the factor 1.37 is vestigial).
  Natural-number subtraction is harmless because `M_l ≥ 2^40` in every use.
- `freshCap`: (ii).

Nothing is too strong. Every field is a sentence of s6:lemJplus, and the manuscript proves each one with the
proof hypotheses (valid run, lemCap(ii), propStructure(iv)) that the JS-LC Spec will carry. Nothing needed
downstream is missing (§4).

## 3. Edge cases checked

- l ≤ 2: `anc_l = ∅`, so `Q = ∅`, and all class data, `Lost`, `Q*`, `J` (`eq_empty_of_le_two`) and `jBound` vanish.
  `lost` has the literal guard.
- l > R: `Std_l = ∅` and `D_l = ∅` in the guarded run model. `classed G l a` can be non-empty for junk `a` (Z0 of
  the default choice), but every definition reads it only under `a ∈ Std_l`. The only exceptions are the total
  functions `lost`/`qs`/`cFresh`/`cPP` at a raw `a`, and those are read under `a ∈ Std_l` too.
- Pairs `(Y,l)` with `r(Y)+2 > l`: the class data vanish on a designation (`classDeg_eq_zero_of_not_anc`), so the
  sums over `Y ∈ run.ancestors G`, `l ∈ [1,R]` (CONC, CONC-L, MIX-C) are correct.
- Swapped orientation of `s(h,u)`: `IsJhubEdge.unique` and `centre_eq_of_eq` handle it. I derived the s7
  RoundInput form of J1 (below), which needs the swap argument.
- M = 0 (junk): `gammaL` gives `x/0 = 0`, and nothing else divides.

## 4. Can every downstream use be stated? (scratch checks under `/tmp/designrev/`)

`Check1.lean` and `Check2.lean` compile with 0 errors (`lake env lean`). They contain:
1. **RoundInput.Valid.J1 from JPlusProps.** For all `h`:
   `#((Jhub l J).filter (∃ u ∈ qsRound l, e = s(h,u) ∧ δ l u = Y)) ≤ 1`. This is proved from `J1hub_all` and
   `disjoint_D_qsRound`. It is the exact s7a shape, and it is true for every run.
2. **s7:lemPay (a2) / s7:lemEXprime fact.** A J^hub-edge of class Y at h gives `1 ≤ classDeg Y l h` and
   `Y ∈ cAggClasses h l`.
3. **RoundInput.Valid.J2 from `J2out` and `union_types`.**
4. **Instantiation sketch** `instSD G run ω dem' dem lp : StageData V` from `EG.Stage1.Outcome`, following the
   D-DES-1 contract. It type-checks against the (pending) Stage1 Defs: `COLa/COLb (ω.cOutAt Y)`, `ω.labAt`,
   `(Own/LJS/LJV …).edges`. I also proved `Chain.Tj (instSD …) = Stage1.Tj (ω.jsAt Y)`.
5. **Spec shapes.** The MIX-C Option B′ statement, with `b : ℕ → Finset → ℝ` and `∃ Js, (∀ l ∈ [3,R],
   JPlusProps … (Js l)) ∧ ∃ D, IsDecomp E(G) D ∧ …`, type-checks against `JConsumer`/`JPlusProps`/`lostRound`/`mY`.
   So does the JS-LC giant sum `Σ_{Y ∈ ancestors, IsGiant Y l} 1.5·mY`.

Downstream uses (blueprints):

| use | statable now? |
|---|---|
| s6:thmCONC(ii),(iii), thmCONCL(iii),(iv) (`mY`, `dStar`, `alphaY`, sums over ancestors × [1,R]) | yes |
| s6:lemJSLC: `J ⊆ ⋃B_Z`, `LentJS ⊆ ⋃_{Y∈lendGoodAnc, j<KJS} S.ljs Y l j`, cycle bound with `IsGiant`/`mY`, `jBound`, `JPlusProps` | the **conclusion** is statable. The **hypotheses** it needs about `S` are not defined anywhere (MAJOR-1). |
| s6:lemLost (probabilities of `u ∈ lost`, `E|Lost_l|`, `E X_U` over the stage-1 law) | **no**: it needs `S` as a function of `ω` (MAJOR-1) |
| s6:thmMIXC B′ (for "any stage-1 outcome") | shape yes; instantiation needs MAJOR-1 |
| s7a RoundInput.Valid via `ofPast_valid`: roles, typed, J1, J2, J2tot, cls_round, cls_mem, lendGood_ports | yes (checks 1 and 3 plus the Lib lemmas listed in design.md) |
| s7a ljv_in, ljv_disj, ljv_J | only from stage-1 facts about `S.ljv`, which are not in the record (MAJOR-1; see also MINOR-4) |
| s7b lemPay (a1),(a2),(b), lemEXprime (`cAgg`, pool weights), defXprime (`XU`), propCost bracket | yes, given an instantiated `S` (MAJOR-1) |

## 5. Probability laws and independence

These files define no laws. δ is a parameter bound before any `FinDist`, as DES-DETERMINISTIC and s6:lemLost(i)
("the designation is deterministic, so Y is fixed") require. `StageData` is law-free. The laws enter only
through the instantiation (the pushforward of `Stage1.law` under `ω ↦ S ω`). s6:lemJplus(v) (edge colours are
independent) correctly stays out of `JPlusProps`, as a property of `Stage1.law`. No weights to check here.

## 6. Findings

### MAJOR-1: the stage-data record has no coherence predicate and no instantiation, so JS-LC, s6:lemLost and the s7 Specs cannot be stated

- **Where:** `EG/Defs/Chain/Lending.lean`, `structure StageData` (D-DES-1).
- **The problem.** The record is axiom-free by design, so any statement "for every S" must carry the stage-1
  facts it uses as hypotheses. JS-LC (probe P-2) uses at least these:
  - `colB Y` ⇒ `(ofEdges V(Y) (S.ljs Y l j)).IsPathConnected (2^12 L_Y^4) (t^JS_l) (Tj Y l j)` for
    `l ∈ [r+2,R]`, `j < K^JS_l`;
  - `S.ljs Y l j ⊆ E(H_Y)`, and `S.ljv Y l ⊆ E(H_Y)`;
  - pairwise disjointness of the classes `ljs Y l j` over `j`, and of `ljs`/`ljv`/`own`, which the
    decomposition-disjointness and lemLent(iii) arguments need.

  s7a's `ljv_in`/`ljv_disj`/`ljv_J` need the `ljv` facts. JConsumer's "of G" (D-DES-8) needs `LJV ⊆ E(G)`.
  Right now none of this exists as a named, reviewed Defs object. The JS-LC Spec author would have to write the
  bundle inline, and a wrong inline bundle is the classic vacuity or undischargeability risk of a locked Spec.
- **Also missing: the instantiation.** s6:lemLost ("probabilities over the stage-1 outcome") and every s7 Spec
  that quantifies `ω ∈ (Stage1.law G run).supp` need `S` as a function of `ω`. The instantiation is only a
  contract in the design note. My check 4 shows it type-checks for all fields except `demoted`/`dem`/`lp`, which
  wait for the s5 Defs.
- **Fix (additive, no change to the five files):**
  - Add `EG/Defs/Chain/StageInst.lean` with `StageData.ofOutcome`. It can be parametrized by the s5 status data
    (`demoted`, `dem`, `lp`) until `EG/Defs/Light/**` exists.
  - Add `structure StageData.Coherent run G S : Prop` with the fields listed above. Put `colB_conn` in exactly
    the `Stage1.COLb` form, with `KJS`/`tJS`/`LY` from the Stage1 layer.
  - Prove `Coherent (ofOutcome ω)` for `ω ∈ supp` (COLg is an event on the support), and prove the bridge
    `Chain.Tj (ofOutcome ω) = Stage1.Tj` (done in my scratch check 4).
  - State JSLCStatement as `∀ S, S.Coherent run G → …`. It then transfers to every instantiated ω.
  - Review these additions jointly with items 26, 27 and 31, as TRIAGE requires.

### MINOR-1: the tests exercise the class data and J-types only at vacuous values

- **Where:** `EGTest/Design.lean`.
- **The problem.** In `run3`, `E_3 = ∅` (round 1 assigns every edge). So `classDeg`, `mY`, `Bead`, `IsGiant`,
  `cAgg`, `cFresh`, `cPP`, `alphaY`, all four `IsJ*Edge` and `JPlusProps` are tested only at 0/∅/false. A
  definition that is constantly 0 would pass. The positive test of `lost`/`qs`/`ret` is good.
- **Fix.** Add abstract positive unit lemmas to Lib and tests:
  - `IsJhubEdge.one_le_classDeg` and `IsJhubEdge.mem_cAggClasses` (my check 2; s7:lemPay (a2) needs exactly
    these);
  - the s7-shape J1 lemma `JPlusProps.J1hub_ports` (my check 1; `ofPast_valid` needs it);
  - if possible, a round with `E_l(Z) ≠ ∅` and a one-edge J satisfying `JPlusProps`.

### MINOR-2: `EG.Chain.Tj` duplicates `EG.Stage1.Tj`

The two agree on the instantiation (proved in scratch check 4). Add the bridge as a Lib lemma once
`StageData.ofOutcome` exists, so that s6 and s3 statements about T_j cannot drift apart.

### MINOR-3: `epsK` duplicates s5's ε_ch (D-DES-9)

Two locked copies of one formula are a lock hazard: if the s5 author writes `epsChain` with a different parse,
the planned `rfl` lemma fails, and one locked definition would have to change. The s5 Defs should define
`epsChain` as `EG.Chain.epsK`, or import it. Record this as a gating item for `EG/Defs/Light/Constants.lean`.

### MINOR-4 (joint-review note for `RoundInput.ofPast_valid`, not a defect here)

- `ljv_J : ∀ Y, Disjoint (I.ljv Y) J` holds for Stage1 classes only on the support. Off the support, a
  colouring may tag an edge of `H_{(l,a)} ⊆ E_l(a)` with `JV l`.
- `ofPast` should therefore set `I.ljv Y := S.ljv Y l` only for `Y.1 + 2 ≤ l` (else ∅), or quantify ω over the
  support.
- `RoundInput.cls : V → A` also needs `A` nonempty (e.g. `A := ↥(run.ancestors G)` plus a default), or an
  `Option`.

### COSMETIC-1

`J2end` and `freshCap` are implied by the other fields: `J2end` by `types` + `E_disjoint`, which holds for every
run; `freshCap` by `J2out`, since fresh centres lie outside `D_l`. They are kept as literal sentences of the lemma,
which is fine. No change.

### COSMETIC-2

The argument order is inconsistent (`cAgg h l` versus `cFresh l a x` / `cPP l a u`). This does not matter for
correctness. If it is ever changed, it must be changed before the lock.

## 7. Summary for the integrator

- The five Defs files are faithful to v6.1, total, and usable by every s6/s7 use in the blueprints.
- `JPlusProps` is exactly the aggregated J⁺ interface that s7a `RoundInput.Valid` and MIX-C B′ read. I checked
  the J1/J2/typed derivations in Lean.
- Before P-2's JSLCStatement and s6:lemLost can be written, add (additively) `StageData.Coherent` and
  `StageData.ofOutcome` (MAJOR-1). Review them together with items 26, 27 and 31.
- The minor items can be done alongside.
