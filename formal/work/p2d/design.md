# P2-D [design]: the s6 interfaces (s6:defDesign, s6:defLending, s6:lemJplus, s6:defJconsumer, ε_CONC, ε_M): design note

Status: all eleven files compile with 0 errors, 0 warnings and 0 `sorry`. `python3 -I scripts/lint.py` reports 0
findings. `python3 -I scripts/lock.py check` reports 0 violations (the new files are PENDING). The axiom scan
`lake env lean --run scripts/Axioms.lean --prefix EG EG.Lib.Chain.JConsumer EG.Lib.Chain.Constants` inspects 1183
constants and finds 0 violations, 0 `sorryAx` and 0 meta-scan hits. Manuscript: `proofs/manuscript/s6.tex` v6.1
(lines 238–260, 390–407, 443–460, 620–677, 759–812), `s5.tex:227` (ε_ch) and `s5.tex:360` (ε_K := ε_ch).

These are TRIAGE §3 items 24–28. They are built on the locked HB Run model (`EG.HB.Run`, work/p2d/hb.md), which
they do not change. They import only `EG.Defs.HB.Run`, `EG.Defs.Components`, `EG.Defs.Objects`, `EG.Defs.Log` and
`EG.Defs.Constants`. They do **not** import the stage-1 layer (TRIAGE items 15–19), which did not exist when this
work started (see D-DES-1).

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Chain/Design.lean` | `EG.Defs.Chain.Design` | `Designation` (abbrev), `IsDesignation`, `classedPorts`, `classDeg` (d_{Y,l}(h)), `mY`, `dStar`, `alphaY`, `Bead`, `gammaL`, `IsGiant`, `cAggClasses`, `cAgg`, `cFresh` (c_x(Z)), `cPP` |
| `EG/Defs/Chain/Lending.lean` | `EG.Defs.Chain.Lending` | `StageData` (record), `lendBad`, `lendGoodAnc`, `Tj`, `lost`, `ret`, `qs` (Q*), `OZ`, `lostRound` (Lost_l), `XU`, `freshCentres`, `qsRound` |
| `EG/Defs/Chain/JSet.lean` | `EG.Defs.Chain.JSet` | `IsJparEdge`, `IsJhubEdge`, `IsJfrEdge`, `IsJlostEdge`, `Jpar`, `Jhub`, `Jfr`, `Jlost`, `jBound` (RHS of eqJbound), **`JPlusProps`** |
| `EG/Defs/Chain/JConsumer.lean` | `EG.Defs.Chain.JConsumer` | `JC1`, `JC2`, `JC3`, **`JConsumer`** |
| `EG/Defs/Chain/Constants.lean` | `EG.Defs.Chain.Constants` | `epsCONC`, `epsK`, `epsM` |
| `EG/Lib/Chain/Design.lean` | `EG.Lib.Chain.Design` | port/classed-port API, one pre-part per vertex outside D_l, designations, vanishing, port counting |
| `EG/Lib/Chain/Lending.lean` | `EG.Lib.Chain.Lending` | l ≤ 2 case, Z^0 = Ret ⊔ Q*, disjointness, lend-good facts, O_Z, \|Lost_l\|, (J3) role disjointness |
| `EG/Lib/Chain/JSet.lean` | `EG.Lib.Chain.JSet` | J ⊆ ⋃E_l(Z) ⊆ E(G), exclusivity of the types, uniqueness of centre and class, (J1) at every vertex, non-vacuity |
| `EG/Lib/Chain/JConsumer.lean` | `EG.Lib.Chain.JConsumer` | JC2 ⇒ JC3, `trivialConsumer`, `nonempty_jConsumer` |
| `EG/Lib/Chain/Constants.lean` | `EG.Lib.Chain.Constants` | `epsM_eq`, `epsCONC_nonneg`, `epsA_nonneg` (D ≥ 4) |
| `EGTest/Design.lean` | `EGTest.Design` | a 3-round run with a classed port; designation; lending in three stage-data scenarios; J-interface and consumer tests; constants |

All names are in the namespace `EG.Chain`. Size: Defs 554 lines, Lib 1013 lines, tests 422 lines.

Root imports for the orchestrator to add (I did not edit `EG.lean` or `EGTest.lean`):
- to `EG`: `EG.Defs.Chain.Design`, `EG.Defs.Chain.Lending`, `EG.Defs.Chain.JSet`, `EG.Defs.Chain.JConsumer`,
  `EG.Defs.Chain.Constants`, `EG.Lib.Chain.Design`, `EG.Lib.Chain.Lending`, `EG.Lib.Chain.JSet`,
  `EG.Lib.Chain.JConsumer`, `EG.Lib.Chain.Constants`;
- to `EGTest`: `EGTest.Design` (it imports `EGTest.HB`, whose `StandaloneTest` example it extends).

## Definitions, with the manuscript text

Common arguments: `run : EG.HB.Run V`, `G : FGraph V`, `δ : Designation V`, `S : StageData V`, a round `l : ℕ`, a
pre-part address `a : Addr` (the pre-part Z), an ancestor `Y : PartId`. Argument order: `run G δ S` then the
indices, e.g. `classDeg run G δ Y l h`, `lost run G δ S l a`, `JPlusProps run G δ S l J`.

### Design.lean (s6:defDesign)

> "A *designation* δ assigns, for every round l≥3, to every standalone pre-part Z∈Std_l and every classed port
> u∈Q_Z an ancestor Y(u)∈anc_l(u), the *class* of u. Here δ is any deterministic function of the run."

- **`Designation V := ℕ → V → PartId`**; **`IsDesignation run G δ := ∀ l ≥ 3, ∀ a ∈ Std_l, ∀ u ∈ Q_a, δ l u ∈ anc_l(u)`**.
  δ is round-indexed (DES-CLASS-DEPENDS-ON-ROUND), total, constrained only at classed ports (DES-DELTA-TOTAL), and a
  parameter quantified before any law (DES-DETERMINISTIC).
- **`classedPorts l := ⋃_{a ∈ Std_l} Q_a`** ("a classed port of round l").
- **`classDeg Y l h := #⋃_{a ∈ Std_l} {e ∈ E_l(a) : ∃ u ∈ Q_a, e = hu ∧ δ l u = Y}`** — "d_{Y,l}(h):=#{hu∈E_l(Z): Z∈Std_l,
  u∈Q_Z, Y(u)=Y}". **Edges are counted, literally** (the blueprint counted ports). The port form is the Lib lemma
  `classDeg_eq_card_ports` (u ↦ hu is a bijection at fixed h).
- **`mY Y l := G.verts.sup (classDeg Y l)`** — "m_{Y,l}:=max_h d_{Y,l}(h), the maximum over all vertices h of G".
- **`dStar Y l := #{u ∈ classedPorts l : δ l u = Y ∧ u ∈ Dup*_{Y.1}}`** — "d*_{Y,l}:=#{u: u a classed port of round
  l, Y(u)=Y, u∈Dup*_r}".
- **`alphaY Y l := sup_{x ∈ S_Y} #{u ∈ V(Y) \ Dup*_{Y.1} : ∃ a ∈ Std_l, u ∈ Q_a ∧ δ l u = Y ∧ xu ∈ E_l(a)}`** — "for light
  Y, α_{Y,l}:=max_{x∈S_Y}#{u∈Y∖Dup*_r: …, xu∈E_l(Z_u)}, with α_{Y,l}:=0 if S_Y=∅". `Finset.sup ∅ = 0`. Total;
  read only for light Y (DES-ALPHA-LIGHT-ONLY). Z_u is written `∃ a ∈ Std_l, u ∈ Q_a ∧ …` (DES-UNIQUE-Z;
  uniqueness is `classed_disjoint`).
- **`Bead Y l := ⋃_{a ∈ Std_l} {e ∈ E_l(a) : ∃ h u, e = hu ∧ u ∈ Q_a ∧ δ l u = Y ∧ (h ∉ Q_a ∨ δ l h ≠ Y)}`** — literal,
  including the vacuous clause (DES-BEAD-CLAUSE-VACUOUS).
- **`gammaL l := ⌊P_{l−2}/M_l⌋₊`** (= `P_{l−2} / M_l` in ℕ, `gammaL_eq_div`); **`IsGiant Y l := ∃ C ∈ edgeComps (Bead Y l),
  2γ_l < |compEdges (Bead Y l) C|`** — "the pair (Y,l) is giant iff some connected component of Bead_{Y,l} has more
  than 2γ_l edges" (components from the locked `EG.Defs.Components`).
- **`cAggClasses h l := {δ l u : u ∈ Q_a, a ∈ Std_l, hu ∈ E_l(a)}`, `cAgg h l := #cAggClasses h l`** — "c^agg_{h,l}:=#{Y:
  d_{Y,l}(h)≥1}". The set is exactly `{Y : d_{Y,l}(h) ≥ 1}` (`mem_cAggClasses_iff`), and needs no range for Y.
- **`cFresh l a x := #{δ l u : u ∈ Q_a, xu ∈ E_l(a)}`**, **`cPP l a u := #{δ l v : v ∈ Q_a, uv ∈ E_l(a)}`** — literal.

### Lending.lean (s6:defLending)

- **`structure StageData V`** (fields `colA colB demoted : PartId → Prop`, `lab : PartId → ℕ → V → Option ℕ`,
  `own : PartId → Finset (Sym2 V)`, `ljs : PartId → ℕ → ℕ → Finset (Sym2 V)`, `ljv : PartId → ℕ → Finset (Sym2 V)`,
  `dem lp : ℕ`). See D-DES-1.
- **`lendBad Y := (isLight Y ∧ S.demoted Y) ∨ ¬ S.colA Y ∨ ¬ S.colB Y`** — "An ancestor Y is *lend-bad* iff Y is a demoted
  light part, or an event of Lemma COL(a) fails for Y, or an event of Lemma COL(b) fails for Y. Otherwise lend-good."
- **`lendGoodAnc l := {Y ∈ ancestors : Y.1 + 2 ≤ l ∧ ¬ lendBad Y}`** — "Y a lend-good ancestor of a round ≤ l−2" (JC1,
  JS-LC).
- **`Tj Y l j := {y ∈ V(Y) : S.lab Y l y = some j}`** — T_j(Y,l) of s3:defCOL(iv), as read in "u∉⋃_jT_j(Y(u),l)".
- **`lost l a := if 3 ≤ l then {u ∈ Q_a : lendBad (δ l u) ∨ S.lab (δ l u) l u ≠ none} else ∅`** — "For l≥3 and Z∈Std_l …
  Lost_Z:={u∈Q_Z: Y(u) is lend-bad, or lab_{Y(u),l}(u)≠*}. … For l≤2 put Lost_Z:=∅".
- **`ret l a := A_a ∪ F_a ∪ lost l a`**, **`qs l a := Q_a \ lost l a`** — "Ret_Z:=A_Z∪F_Z∪Lost_Z … Q*_Z:=Q_Z∖Lost_Z". The
  manuscript's l≤2 clause (Ret_Z := A_Z∪F_Z = Z^0, Q*_Z := ∅) is the same set (`ret_of_le_two`, `qs_of_le_two`).
- **`OZ l a := if lendBad (l,a) then X^0_a else FGraph.ofEdges Z^0_a (S.own (l,a))`** — "O_Z:=Own_Z if the ancestor Z is
  lend-good, and O_Z:=X^0_Z otherwise" (LEND-OZ-SPANNING: a graph on Z^0, `OZ_verts`).
- **`lostRound l := ⋃_{a∈Std_l} lost l a`** — "Lost_l:=⋃_{Z∈Std_l}Lost_Z".
- **`XU := 80·dem + 369·lp + Σ_{l∈[1,R]} (169 + M_l)·|Lost_l|`** ∈ ℕ — "X_U:=80 dem+369 lp+Σ_l(169+M_l)|Lost_l|"
  (LEND-XU-RANGE: l ∈ [1,R]; Lost_l = ∅ for l ≤ 2 and outside [1,R]).
- Role sets of a round (J3, s7): **`freshCentres l := ⋃_{a∈Std_l} F_a`**, **`qsRound l := ⋃_{a∈Std_l} Q*_a`**.

### JSet.lean (s6:lemJplus; eqJbound of s6:lemJSLC)

The four types, each "for some Z ∈ Std_l with the edge in E_l(Z)" (the lemma's "for Z∈Std_l"):
- `IsJparEdge l e := ∃ a ∈ Std_l, e ∈ E_l(a) ∧ ∃ u v, e = uv ∧ u,v ∈ Q*_a ∧ δ l u ≠ δ l v` — "a J^par-edge has both ends
  in Q*_Z, with different classes";
- `IsJhubEdge l h Y e := ∃ a ∈ Std_l, e ∈ E_l(a) ∧ ∃ u, e = hu ∧ h ∈ A_a ∧ u ∈ Q*_a ∧ δ l u = Y` — "a J^hub-edge is an
  edge hu with h∈A_Z⊆D_l and u∈Q*_Z"; "The class of a J^hub-… edge hu is Y(u)";
- `IsJfrEdge l x Y e` (x ∈ F_a) and `IsJlostEdge l v Y e` (v ∈ Lost_a), likewise.
- `Jpar/Jhub/Jfr/Jlost l J` are the corresponding filters of J (the four RoundInput sets of s7).
- `jBound l := Σ_{h∈D_l} c^agg_{h,l} + Σ_{a∈Std_l} (Σ_{x∈F_a} c_x + (M_l − 1)|Lost_a| + ½ Σ_{u∈Q_a} c_pp(u))` ∈ ℝ — the right
  side of (s6:eqJbound), for the JS-LC Spec (blueprint JSLC-EQJBOUND keeps the conjunct).

**`structure JPlusProps run G δ S l J : Prop`** — fields:

| field | manuscript |
|---|---|
| `types : ∀ e ∈ J, IsJparEdge ∨ (∃ h Y, IsJhubEdge) ∨ (∃ x Y, IsJfrEdge) ∨ (∃ v Y, IsJlostEdge)` | "J_l=J^lost⊔J^hub⊔J^fr⊔J^par" and (i) exhaustive |
| `J1hub : ∀ h ∈ D_l, ∀ Y, #(J.filter (IsJhubEdge l h Y)) ≤ 1` | (J1) "at most one J^hub-edge of class Y at h, **aggregated over all parts of round l**" |
| `J1fr : ∀ x ∈ freshCentres l, ∀ Y, #(J.filter (IsJfrEdge l x Y)) ≤ 1` | (J1) fresh centres |
| `J1lost : ∀ v ∈ lostRound l, ∀ Y, #(J.filter (IsJlostEdge l v Y)) ≤ 1` | (J1) "(The same holds at lost centres.)" |
| `J2end : ∀ a ∈ Std_l, ∀ e ∈ J, e ∈ E_l(a) → ∃ u ∈ Q*_a, u ∈ e` | (J2) "Every J-edge lying in E_l(Z) has an end in Q*_Z" |
| `J2cap : ∀ a ∈ Std_l, ∀ v, #{e ∈ J : e ∈ E_l(a) ∧ v ∈ e} ≤ M_l − 1` | (J2) "For every Z and every vertex, at most M_l−1 J-edges at that vertex lie in E_l(Z)" |
| `J2out : ∀ v ∉ D_l, degE J v ≤ M_l − 1` | (J2) "In particular a port or a fresh centre (a vertex outside D_l) carries at most M_l−1 J-edges of round l" |
| `J2card : |J| ≤ n (M_l − 1)` | (J2) "Also \|J_l\|≤n(M_l−1)" (the vestigial ≤ 1.37n(M_l−1) is implied) |
| `freshCap : ∀ x ∈ freshCentres l, #{e ∈ J : ∃ Y, IsJfrEdge l x Y e} ≤ M_l − 1` | (ii) "A fresh centre carries at most M_l−1 J^fr-edges" |

All filters run over the whole of `J`: every (J1) is **aggregated** (TRIAGE §1b MULT-J1, §2.9); the refutation target
of probe P-2 ("two J^hub edges of one class at one hub in one round") is exactly `¬ J1hub`.

Not fields (J-independent, TRIAGE §2.9, blueprint JPLUS-J3-III-IV/JPLUS-V-PROB): (J3) and the exclusive half of (i)
are Lib lemmas **for every run** (below); (iii) is s2:propStructure(iii) (a run Spec); (iv) is
`IsDesignation.mem_ancVerts`; (v) is a stage-1 law lemma. The "consists exactly of the Step-2 deletions / every
choice / Steps 3–8 delete nothing" clause is about the proof of JS-LC and is used by nothing downstream (checked
by blueprint s6b against every s7 citation); not encoded.

### JConsumer.lean (s6:defJconsumer)

- `JC1 l L := L ⊆ ⋃_{Y ∈ lendGoodAnc l} S.ljv Y l`; `JC2 J L Ob := IsDecomp (J ∪ L) Ob`; `JC3 J L Ob := ∀ o ∈ Ob, ∀ e ∈
  o.edges, e ∈ J ∪ L`.
- **`structure JConsumer run G δ S`**: `out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)` (`(l, J_l) ↦ (Obj_l,
  LentJV_l)`), `jc1`, `jc2 : ∀ l J, 3 ≤ l → l ≤ R → JPlusProps run G δ S l J → JC1/JC2 …`.

### Constants.lean

- `epsCONC D := 2^{σ+15}·log*D/log D + 200ε·log*D/(C'·log log D) + 4(2 log*D + 2)/(log D)^{1/2}` (s6:thmCONCL(iv), also
  s1:condG4); the parse is pinned by an `rfl` test with all parentheses explicit.
- `epsK D := 614/D + log(2A·log(A·log log D))/(371 (log log D)^2)` (s5:lemKRED "ε_K(D_*) := ε_ch(D_*)", s5:lemParent(ii)).
- `epsM D := epsK D + 169·ε_A(D) + 252/D` (s6:thmMIXC(c)), with the locked `EG.HB.epsA`.

## Decisions

- **D-DES-1 (stage data as an explicit record).** s6:defLending reads a stage-1 outcome only through: the COL(a) and
  COL(b) events of each ancestor, the demotion status, the JS labels, the classes Own_Y, LJS_{Y,l,j}, LJV_{Y,l}, and
  dem, lp. These are the fields of `StageData`; every s6 Def (and `JPlusProps`, `JConsumer`) takes a `StageData`.
  - Why: the stage-1 layer (TRIAGE items 15–19) was not written, and the whole s6/s7 interface should not depend on
    the concrete stage-1 sample space. Probe P-2 can then prove JS-LC/J⁺ against the record, with the stage-1 facts it
    uses (e.g. "colB Y → LJS_{Y,l,j} path connected through T_j") as hypotheses discharged by the instantiation.
  - No loss: the record has **no axioms**, so a statement proved for all `S` holds for the instantiated one; the
    faithful combination (the disjunction of lend-bad, the lost condition, O_Z, X_U) is in the locked Defs here.
  - **Instantiation contract** (to be written once, in a Defs file after `EG/Defs/Light/Stages.lean`, e.g.
    `EG/Defs/Chain/StageInst.lean`, and reviewed with this note): for a stage-1 outcome `ω : EG.Stage1.Outcome G run`,
    `colA Y := COLa (ω.cOutAt Y)`, `colB Y := COLb (ω.cOutAt Y)` (the in-progress `EG/Defs/Stage1/COL.lean` defines
    `EG.Stage1.COLa`, `COLb` on `COLOut G run Y`), `demoted Y :=` the s5:defStages demotion, `lab Y l y := ω`'s JS label
    at the site `(l, y)` of `Y` and `none` off `jsSites G run Y`, `own Y := (Own (ω.colAt Y)).edges`,
    `ljs Y l j := (LJS (ω.colAt Y) l j).edges`, `ljv Y l := (LJV (ω.colAt Y) l).edges`, `dem`, `lp` of s5:defStages.
    With this, `Chain.Tj` equals `Stage1.Tj` of the JS labels (both filter V(Y) by label `= j`).
  - Checked against the in-progress Stage1 files (13:30 UTC): their JS labels are `Option ℕ` (none = `*`), classes are
    `FGraph`s whose `.edges` are the edge sets used here. Nothing here depends on their unreviewed content.
- **D-DES-2 (designation).** `Designation V := ℕ → V → PartId`, `IsDesignation` only at classed ports of standalone
  pre-parts of rounds ≥ 3 (TRIAGE §2.9). Existence: `exists_isDesignation` (choice from anc_l(u) ≠ ∅).
- **D-DES-3 (class data literal).** Edge counts where the text counts edges (`classDeg`); class-set images where it
  counts classes (`cAgg`, `cFresh`, `cPP`); the image form of c^agg needs no index range for Y and equals
  `{Y : d_{Y,l}(h) ≥ 1}`. Z_u is never a function (`∃ a ∈ Std_l, u ∈ Q_a ∧ …`).
- **D-DES-4 (vanishing ranges).** No guards beyond the HB model's: for l ≤ 2 classed ports are empty (`anc_l = ∅`),
  for l ∉ [1,R] `Std_l = ∅` (guarded run model); all quantities vanish there (Lib `*_of_le_two`, `*_of_not_isRound`,
  `classDeg_eq_zero_of_not_anc` for pairs (Y,l) with r(Y)+2 > l on a designation — the sum ranges of CONC/CONC-L).
  γ_l reads `P (l − 2)` (ℕ-subtraction), meaningful for l ≥ 3.
- **D-DES-5 (lost guard).** `lost` carries the literal `3 ≤ l` guard; `ret`, `qs` are uniform and their l ≤ 2 values
  are lemmas (blueprint LEND-L2-CASE).
- **D-DES-6 (X_U in ℕ, range [1,R]).** All summands are natural numbers; statements cast.
- **D-DES-7 (JPlusProps content).** The fields are exactly (i)-exhaustive, (J1) ×3 aggregated, (J2) ×4, (ii). Each (J1)
  is quantified over the literal centre set (D_l, fresh centres, lost centres); the unrestricted forms are
  `JPlusProps.J1hub_all`/`J1fr_all`/`J1lost_all`. (J3), exclusivity, J ⊆ E(G) are J-independent Lib lemmas, so the
  JS-LC proof never has to reprove them.
- **D-DES-8 (JConsumer).** Out is a function of (l, J) in a fixed context (TRIAGE §2.9, blueprint JCONS-TYPE); JC1/JC2
  only for 3 ≤ l ≤ R and `JPlusProps` inputs (JCONS-CONDITIONAL); JC2 is `IsDecomp (J ∪ LentJV) Obj` (the predicate
  s7:lemLift(iv) must produce); "of G" is implied by J ⊆ E(G) (`JPlusProps.subset_edges`) and LJV ⊆ E(H_Y) ⊆ E(G)
  (a stage-1 fact of the instantiation); JC3 is a lemma (JCONS-JC3).
- **D-DES-9 (ε_K written out).** `epsK` transcribes s5:lemParent(ii)'s ε_ch, because MIX-C names ε_K and the s5 Defs
  (`EG/Defs/Light/Constants.lean`) do not exist yet. When they do, `epsK = epsChain` must be an `rfl` Lib lemma.

## Interface map: JPlusProps / Lending → s7 `RoundInput.Valid` (blueprint s7a lean_shape)

For the instantiation lemma `RoundInput.ofPast_valid` (reviewed jointly, TRIAGE §3 gate "items 26, 27, 31"):

| RoundInput.Valid field | source here |
|---|---|
| `roles` (hubs, fresh, ports, lost pairwise disjoint) | `disjoint_D_freshCentres`, `disjoint_D_qsRound`, `disjoint_D_lostRound`, `disjoint_freshCentres_qsRound`, `disjoint_freshCentres_lostRound`, `disjoint_qsRound_lostRound` (every run) with hubs := D_l, fresh := `freshCentres`, ports := `qsRound`, lost := `lostRound` |
| `typed` (endpoints of Jlost/Jhub/Jfr/Jpar; classes pairwise disjoint; all ⊆ E(G)) | `Jlost`…`Jpar` defs + `types` + `JPlusProps.union_types`, the `*.not_is*Edge` lemmas, `JPlusProps.subset_edges` |
| `J1` (≤ 1 Jhub edge per (hub, class)) | `J1hub` / `J1hub_all` (+ `IsJhubEdge.unique`) |
| `J2` (∀ v ∉ hubs, degE J v ≤ M − 1) | `J2out` (verbatim) |
| `J2tot` | `J2card` (verbatim) |
| `cls_round`, `cls_mem` | `IsDesignation.one_le_round`, `round_add_two_le`, `mem_ancVerts` |
| `lendGood_ports` | `not_lendBad_of_mem_qs`, `mem_lendGoodAnc_of_mem_qs` |
| `ljv_in`, `ljv_disj`, `ljv_J` | stage-1 facts (LJV ⊆ E(H_Y)) + s2:propStructure(iii) + `JPlusProps.subset_E` |
| `good_cand`, `M_ge`, `Hcd_ge`, `pool_sub` | s7:lemCand, Γ (not s6) |

MIX-C Option B′ (TRIAGE §2.9) reads `JPlusProps run G δ S l (Js l)` and `JConsumer run G δ S` exactly as defined here.

## API (`EG/Lib/Chain/*`)

- **Design:** `mem_ports_iff`, `mem_fresh_iff`, `mem_classed_iff`, `mem_hubs_iff`, `classed_subset_ports`, `fresh_subset_ports`,
  `ports_subset_Z0`, `classed_subset_Z0`, `hubs_subset_D`, `not_mem_D_of_mem_ports`, `disjoint_fresh_classed`,
  `classed_eq_empty_of_le_two`, `anc_ne_empty_of_mem_classed`, `mu_eq_card`, `eq_of_mem_Z0_of_notMem_D` (a vertex outside
  D_l lies in at most one pre-part), `Std_subset_prePartAddrs`, `ports_disjoint`, `classed_disjoint`, `eq_of_mem_classed`,
  `E_disjoint`, `eq_of_mem_E`, `E_subset_edges`, `exists_isDesignation`, `IsDesignation.{mem_anc, mem_ancVerts,
  round_add_two_le, mem_ancestors, one_le_round}`, `mem_classedPorts`, vanishing (`classedPorts_/classDeg_/mY_/dStar_…
  _eq_zero_of_le_two` and `_of_not_isRound`, `cAgg_eq_zero_of_le_two`, `Bead_eq_empty_of_le_two`,
  `classDeg_eq_zero_of_not_anc`, `mY_eq_zero_of_not_anc`), `classDeg_le_mY`, `classDeg_eq_card_ports`,
  `mem_cAggClasses_iff`, `gammaL_eq_div`, `Bead_subset`, `biUnion_eq_empty_of`.
- **Lending:** `lost_of_le_two`, `mem_lost_iff`, `lost_subset_classed`, `qs_subset_classed`, `mem_qs_iff'`, `mem_qs_iff`,
  `qs_of_le_two`, `ret_of_le_two`, `three_le_of_mem_qs`, `not_lendBad_of_mem_qs`, `lab_eq_none_of_mem_qs`,
  `notMem_Tj_of_mem_qs`, `mem_lendGoodAnc_of_mem_qs`, `ret_union_qs`, `disjoint_ret_qs`, `disjoint_hubs_{ports,fresh,lost}`,
  `disjoint_fresh_lost`, `disjoint_lost_qs`, `OZ_of_lendBad`, `OZ_of_not_lendBad`, `OZ_verts`, `mem_lostRound`,
  `mem_freshCentres`, `mem_qsRound`, `lostRound_of_le_two`, `qsRound_of_le_two`, `card_lostRound`, `eq_of_mem_ports`, the six
  role-disjointness lemmas.
- **JSet:** `disjoint_hubs_qs`, `disjoint_fresh_qs`, `Is*Edge.exists_mem_E`, `JPlusProps.{exists_mem_E, subset_E,
  subset_edges, not_isDiag, eq_empty_of_le_two, union_types, J1hub_all, J1fr_all, J1lost_all}`, `centre_eq_of_eq`, six
  exclusivity lemmas, `Is{Jhub,Jfr,Jlost}Edge.unique`, `IsJhubEdge.mem_D`, `IsJfrEdge.mem_freshCentres`,
  `IsJlostEdge.mem_lostRound`, `jBound_of_le_two`, `jPlusProps_empty`.
- **JConsumer:** `JC3_of_JC2`, `JConsumer.jc3`, `flatMap_edges_map_edge`, `trivialConsumer`, `nonempty_jConsumer`.
- **Constants:** `epsM_eq`, `two_le_logb_of_four_le`, `one_le_logb_logb_of_four_le`, `epsA_nonneg`, `epsCONC_nonneg`.

## Tests (`EGTest/Design.lean`)

- **A run with a classed port** (not valid; definitions only): `run3 = ⟨[cA, cA, cA]⟩` on `G5` of
  `EGTest.HB.StandaloneTest`. Round 1 assigns all edges, so `G_2 = G_3 = Gz` (edgeless); on `Gz` the same choices give the
  same pre-parts (P = 0), `D_3 = {0,1}`, `[true]` standalone. `anc_3(2) ∋ (1,[true])`, so **`Q_{[true]} = {2}` at
  round 3** (`classed3_t`).
- A designation `δ3` (checked `IsDesignation` over all three pre-parts of round 3), `u ∈ V(Y(u))`, `r(Y(u)) + 2 ≤ l`,
  `2 ∈ classedPorts 3`, `d* = 0` (classed ports avoid D_3 = Dup*_1 = {0,1}), `d_{Y,3} = 0`, `Bead = ∅`, not giant,
  `m = 0` for l ≤ 2.
- Lending: `Sgood` (all good, labels `*`): `Lost = ∅`, `Q* = {2}`, `Ret = {0,1}`, `Y(2)` lend-good, `X_U = 80·7 + 369·5`;
  `Slab` (label 0 ≠ `*`): `Lost = {2}`, `Q* = ∅`, `Ret = Z^0`; `Sbad` (COL(b) fails for `(1,[true])`): `Lost = {2}`;
  `O_Z = X^0_Z` for a lend-bad Z and `Own_Z` otherwise; `l ≤ 2` values.
- J-interface: `∅` satisfies `JPlusProps`; **negative**: `{02}` does not (no E_3(Z) contains it); at `l ≤ 2` only `∅`;
  `jBound = 0` at l = 1; the trivial consumer and `Nonempty JConsumer`.
- Constants: `epsM_eq`, `ε_CONC(4) ≥ 0`, and `rfl` tests fixing the parse of `ε_CONC` and `ε_K`.

## Notes for Spec authors (probe P-2, s6/s7 Specs)

- Quantify `∀ δ, IsDesignation run G δ → …` before any law; for stage-1 statements use the instantiated
  `StageData` of an outcome ω (D-DES-1).
- The JS-LC Spec should state: `J ⊆ ⋃_Z B_Z`, `LentJS ⊆ ⋃_{Y ∈ lendGoodAnc l} ⋃_{j < KJS l} S.ljs Y l j` (KJS from the
  stage-1 layer), the decomposition, the cost `126 n/M_l + 1.5 Σ_{Y : IsGiant Y l} mY Y l` (sum over `run.ancestors G`),
  `J.card ≤ jBound l` (optional conjunct), and `JPlusProps run G δ S l J`.
- Sums "over (Y,l)" (CONC, CONC-L, MIX-C): `Σ_{l∈[1,R]} Σ_{Y ∈ ancestors}`; `mY_eq_zero_of_not_anc` removes the rest.
- `alphaY` is meaningful only for light Y; `cFresh`, `cPP` only at fresh/classed ports of standalone parts.

## Manuscript issues

None new. T0 readings recorded here (no manuscript change needed): X_U sums over l ∈ [1,R]; JC2's "of G" follows from
the union; (J1) at fresh/lost centres stated aggregated (equivalent, those centres lie in one part); the vestigial
factor 1.37 in (J2); the J⁺ "every choice / Steps 3–8" clause is not encoded (unused downstream).

## Fix round 1 (review `work/p2d/design.review1.md`)

Status after the fix: all touched and new files compile with 0 errors, 0 warnings and 0 `sorry`
(`scripts/check.sh` on each; `lake build EGTest.StageInst` builds everything below). `python3 -I
scripts/lint.py`: 0 findings. `python3 -I scripts/lock.py check`: 0 violations (new constants
PENDING). Axiom scan `--prefix EG EG.Lib.Chain.StageInst EG.Lib.Chain.JSet`: 2151 constants, 0
`sorryAx`, 0 violations. **No existing definition was changed**: the five Defs files of this note are
byte-identical; all additions are new files or new Lib lemmas.

New files (root imports for the orchestrator, not edited by me):
- to `EG`: `EG.Defs.Chain.StageInst`, `EG.Lib.Chain.StageInst`;
- to `EGTest`: `EGTest.StageInst`.

| File | Contents |
|---|---|
| `EG/Defs/Chain/StageInst.lean` | `StageData.ofOutcome ω demoted dem lp`, **`StageData.Coherent run G S`** |
| `EG/Lib/Chain/StageInst.lean` | `ofOutcome_*` (rfl), `Tj_ofOutcome`, `restrictEdges_edges_self`, `LJS_restrict`/`LJV_restrict`/`lentClass_restrict`/`Own_restrict`, `js_mem_supp_jsLaw`, `mem_lentIdx_of_mem_lentClass`, `lt_KJS_of_labAt`, **`coherent_ofOutcome`**, `exists_coherent`, `StageData.Coherent.{Tj_eq_empty, ljv_subset_edges, ljs_subset_edges, ljv_eq_empty_of_lt}` |
| `EG/Lib/Chain/JSet.lean` (additions) | `IsJhubEdge.one_le_classDeg`, `IsJhubEdge.mem_cAggClasses`, `IsJhubEdge.one_le_cAgg`, `IsJfrEdge.one_le_cFresh`, `JPlusProps.J1hub_ports`, `JPlusProps.degE_types_le` |
| `EGTest/StageInst.lean` | coherence tests on `run3`, instantiation tests (abstract run), positive J-lemma tests |

### MAJOR-1 (valid; fixed additively)

Verified: `StageData` has no axioms and there was no named predicate for the stage-1 facts, and no
map `ω ↦ S`; JS-LC's hypotheses, s6:lemLost (a law statement over ω) and the s7 Specs over
`ω ∈ supp` could not be stated without an inline hypothesis bundle.

- **`StageData.ofOutcome {G run} (ω : Stage1.Outcome G run) (demoted : PartId → Prop) (dem lp : ℕ)`**
  (D-DES-1 contract, now a definition): `colA Y := Stage1.COLa G run Y (ω.cOutAt Y)`,
  `colB Y := Stage1.COLb G run Y (ω.cOutAt Y)`, `lab := ω.labAt`, `own Y := (Own … (ω.colAt Y)).edges`,
  `ljs Y l j := (LJS … (ω.colAt Y) l j).edges`, `ljv Y l := (LJV … (ω.colAt Y) l).edges`. The s5 status
  data are parameters until `EG/Defs/Light/Stages.lean` exists (gating item G-S5-1 below).
- **`StageData.Coherent run G S : Prop`**, fields (each quotes s3:defCOL / s3:lemCOL):
  - `colB_conn`: `S.colB Y → ∀ l ∈ Stage1.lateRounds run Y.1, ∀ j < Stage1.KJS G run l,
    (H_Y.restrictEdges (S.ljs Y l j)).IsPathConnected (2^12 * run.LY G Y ^ 4) (Stage1.tJS G run l) (Tj run G S Y l j)`
    — exactly the `Stage1.COLb` form; "the class as a graph on V(Y)" is `H_Y.restrictEdges`, which *is*
    `Stage1.LJS` on the instantiation (`LJS_restrict`);
  - `colA_own`, `colA_ljs`, `colA_ljv`: the COL(a) conjuncts for `Own_Y` and the JS/JV-lent classes
    (TPV on `O_Z = Own_Z`, s7's LJV expansion);
  - `own_sub`, `ljs_sub`, `ljv_sub` (⊆ `E(H_Y)`);
  - `ljs_disj` (distinct `(l,j)`), `ljv_disj`, `ljs_ljv_disj`, `own_ljs_disj`, `own_ljv_disj`
    (classes of one ancestor pairwise disjoint; distinct ancestors are disjoint by s2:propStructure(iii),
    a run fact, not repeated);
  - `ljs_eq_empty`, `ljv_eq_empty` (no JS class outside `l ∈ [r+2,R]`, `j < K^JS_l`; no JV class outside
    `l ∈ [r+2,R]`), `lab_dom` (a label `≠ *` sits at a site), `lab_lt` (label value `< K^JS_l`).
  All fields except `ljs_eq_empty`, `ljv_eq_empty`, `lab_lt` hold for **every** outcome; those three
  hold on the support.
- **`coherent_ofOutcome (hω : ω ∈ (Stage1.law G run).supp) d dem lp : (ofOutcome ω d dem lp).Coherent run G`**
  (proved), and `exists_coherent` (non-vacuity for every run).
- Tests: `S0` (all COL events fail, no classes) is coherent on `run3`; `Slab` is not (`lab_dom`); a JV
  class at round 0 is not (`ljv_eq_empty`); an own class with the edge `04 ∉ E(H_{(1,[true])})` is not
  (`own_sub`); for an abstract run, `colB_conn` of the instantiated record is literally `Stage1.COLb`'s
  path connectivity through `Stage1.Tj`.
- **For Spec authors (not done here: Specs are out of scope):** state JS-LC (P-2) as
  `∀ S, S.Coherent run G → …` and transfer to `ω ∈ supp` with `coherent_ofOutcome`; s6:lemLost and the
  s7 Specs quantify ω and use `StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)` with the s5 Defs.
  These additions are part of the joint review of TRIAGE items 26, 27, 31.

### MINOR-1 (valid; fixed by Lib lemmas; concrete round deferred)

Verified: in `run3`, `E_3 = ∅`, so the class data and J-types were only tested at 0/∅/false. Added the
positive Lib lemmas `IsJhubEdge.one_le_classDeg`, `IsJhubEdge.mem_cAggClasses`, `IsJhubEdge.one_le_cAgg`,
`IsJfrEdge.one_le_cFresh` (none of them provable for a constantly-0 definition) and the s7 shapes
`JPlusProps.J1hub_ports` (RoundInput J1) and `JPlusProps.degE_types_le` (RoundInput J2), with tests. A
concrete round with `E_l(Z) ≠ ∅` and a nonempty `J` satisfying `JPlusProps` was **not** built: it needs a
run in which an edge `hu` (`h ∈ D_3`, `u ∈ Q_Z`) survives rounds 1 and 2 on `G5`, i.e. new pre-part
computations for two more graphs (the `EGTest.HB` example for one graph is ~400 lines). Left for the
integrator to request if the Lib lemmas are judged insufficient.

### MINOR-2 (valid; fixed)

`Tj_ofOutcome : Tj run G (ofOutcome ω d dem lp) Y l j = Stage1.Tj G run Y (ω.jsAt Y) l j` in Lib.

### MINOR-3 (valid hazard; recorded as gating item, no change possible in these files)

**G-S5-1 (gating for `EG/Defs/Light/Constants.lean` and `EG/Defs/Light/Stages.lean`):**
- `epsChain` must be *defined* as `EG.Chain.epsK` (import `EG.Defs.Chain.Constants`), not retyped, so
  that no second locked copy of ε_ch exists; if the s5 author prefers the formula in the s5 file, then
  `EG.Chain.epsK` must be re-reviewed together with it and an `rfl` lemma `epsChain = epsK` added
  **before** either is locked.
- The s5 layer instantiates the parameters of `StageData.ofOutcome` (`demoted`, `dem`, `lp` as functions
  of ω), without changing `ofOutcome`.

### MINOR-4 (valid, s7 joint-review note)

- `ljv_J` for rounds `l < r(Y)+2`: now available on the support through `Coherent.ljv_eq_empty` /
  `StageData.Coherent.ljv_eq_empty_of_lt` (`LJV_{Y,l} = ∅` there), so `RoundInput.ofPast` can set
  `I.ljv Y := S.ljv Y l` with a coherent `S` and needs no range guard. (Setting the guard in `ofPast` is
  equally fine.) For `r(Y)+2 ≤ l`: `ljv_sub` + s2:propStructure(iii) (`E(H_Y) ∩ E_l(Z) = ∅`).
- `RoundInput.cls : V → A` needs `A` nonempty (e.g. `A := ↥(run.ancestors G)` with a default, or
  `Option`): an s7 Defs item (TRIAGE item 31), recorded here for the joint review.

### COSMETIC-1 (valid; no change)

`J2end` is implied by `types` + `E_disjoint` (every run) and `freshCap` by `J2out` (fresh centres lie
outside `D_l`); both are kept as literal sentences of s6:lemJplus. Recorded here only (the locked-candidate
docstrings are unchanged).

### COSMETIC-2 (valid; kept)

`cAgg h l` vs `cFresh l a x` / `cPP l a u`: kept. The order follows the manuscript's notation
(`c^agg_{h,l}`: centre then round; `c_x(Z)`, `c_pp(u)` with `Z ∈ Std_l`: part (round, address) then vertex),
and renaming now would touch Lib and tests for no semantic gain.

## Fix round 2 (review `work/p2d/design.review2.md`)

Status after the fix: `lake build EGTest.StageInst` (builds all s6 Lib modules and both tests) and
`lake build EG.Lib.Chain.JConsumer EG.Lib.Chain.Constants` succeed with 0 errors, 0 warnings, 0 `sorry`.
`python3 -I scripts/lint.py`: 0 findings. `python3 scripts/lock.py check`: 419 locked constants, 0
violations, 216 pending. Axiom scan `--prefix EG EG.Lib.Chain.StageInst EG.Lib.Chain.JSet
EG.Lib.Chain.Design`: 2239 constants, 0 `sorryAx`, 0 violations. **No Defs file was touched**: the six
`EG/Defs/Chain/{Design,Lending,JSet,JConsumer,Constants,StageInst}.lean` are byte-identical to round 2's
review; every change is a new Lib lemma, a new test, or a note.

### MINOR-A (valid; cannot be closed here; recorded as a gate note)
`EG/Defs/Quot/Round.lean` (item 31) still does not exist, so the s7 leg of the gate 26 ↔ 27 ↔ 31 is open.
Recorded as a sub-bullet of TRIAGE §3 item 31: `ofPast` uses `hubs := run.D G l`, `fresh := freshCentres`,
`ports := qsRound`, `lost := lostRound`, `cls := δ l` (nonempty ancestor type), `ljv Y := S.ljv Y l`,
`lendGood := ¬ lendBad`; every `Valid` field is discharged by the lemmas of the "Interface map" above plus
this round's glue; the s7 Specs carry `S.Coherent run G` (or `ω ∈ supp` via `coherent_ofOutcome`).
This round adds the unconditional forms that `ofPast_valid` needs:
`StageData.Coherent.ljv_subset_graph_edges` (`ljv_in`, JC2 "of G"), `ljs_subset_graph_edges`,
`own_subset_graph_edges`. No change to the s6 Defs is expected.

### MINOR-B (valid; binding note added, no s6 file changes)
Verified: blueprint_s5 (line 31 and the `lean_shape` of s5:lemParent) retyped the ε_ch formula as
`EG.epsChain`. Fixed in the two notes the s5 author reads:
- TRIAGE §3 item 20 now carries **G-S5-1**: `noncomputable def epsChain (D : ℝ) : ℝ := EG.Chain.epsK D`
  (import `EG.Defs.Chain.Constants`), never a second literal copy; and for item 19 the types
  `demoted ω run G : PartId → Prop`, `dem ω run G`, `lp ω run G : ℕ`, so the record is
  `StageData.ofOutcome ω (demoted ω run G) (dem ω run G) (lp ω run G)` with no cast.
- blueprint_s5: line 31 marks the formula as "define it as `EG.Chain.epsK D`", and the `lean_shape` def
  is replaced by `noncomputable def epsChain (D : ℝ) : ℝ := EG.Chain.epsK D` with the formula as a comment.
The docstring of `EG.Chain.epsK` (Defs, pending lock) still says "`epsK D = epsChain D` must be a `rfl`
Lib lemma"; it stays true under the binding recommendation (`rfl` by definition), so the Defs file was not
touched.

### MINOR-C (valid; recorded as a lock gate)
Added to TRIAGE §3 "Lock gates": `EG/Defs/Chain/StageInst.lean` is locked only after items 15–18; a change
to `Outcome.labAt`, `COLa`/`COLb`, `Own`/`LJS`/`LJV`, `jsSites`, `lateRounds`, `KJS`, `tJS` forces a
re-review of `ofOutcome`/`Coherent`. The other five s6 Defs files do not import the stage-1 layer and can be
locked now.

### MINOR-D (valid; strengthened by abstract positive lemmas; concrete run still deferred)
A concrete three-graph run with `E_3(Z) ≠ ∅` is still not built (same reason as fix round 1; the reviewer
agrees with deferring it to P-2's test suite). What was only a scratch check or untested is now Lib + test:
- `IsJhubEdge.jPlusProps_singleton` (Check A): a one-edge `J^hub` set satisfies all nine `JPlusProps`
  fields when `M_l ≥ 2`, so `JPlusProps` is not an `∅`-only predicate;
- `IsJhubEdge.mem_Bead` (a `J^hub`-edge of class `Y` is in `Bead_{Y,l}`),
  `isGiant_of_mem_Bead_of_gammaL_eq_zero` and `IsJhubEdge.isGiant_of_gammaL_eq_zero` (`IsGiant` holds
  when `γ_l = 0` and the bead set has a non-loop edge), `one_le_alphaY` (a guest adjacent in `E_l(Z)` to a
  classed port of class `Y` outside `Dup*_r` gives `α_{Y,l} ≥ 1`). None of these is provable for a
  constantly-`∅`/`False`/`0` `Bead`/`IsGiant`/`alphaY`.
- `Tj_disjoint` (Check F, JS-LC Step 7) in `EG/Lib/Chain/Lending.lean`.
Tests: `EGTest/StageInst.lean`, section `Abstract`.

### COSMETIC-A (valid; fixed)
TRIAGE §2.9 now reads "Class degrees count edges of `E_l(Z)` at `h` (the literal text of s6:defDesign;
D-DES-3), with the equivalence lemma `classDeg_eq_card_ports` to port counting", matching the Defs.

### COSMETIC-B (valid; fixed)
`EG/Lib/Chain/StageInst.lean`: `ancGraph_le run G Y : run.ancGraph G Y ≤ G` (from `partGraph_le_X0`,
`X0_le_graph`, `graph_le_of_le`, `graph_zero`), `ancGraph_edges_subset_edges`, and the hypothesis-free
`StageData.Coherent.{ljv,ljs,own}_subset_graph_edges`. The hypothesised versions are kept (unchanged API).

### COSMETIC-C (valid; fixed)
`OZ_eq_restrictEdges (hS : S.Coherent run G) (hstd : ¬ run.isLight G l a) (hgood : ¬ lendBad run G S (l,a)) :
OZ run G S l a = (run.ancGraph G (l,a)).restrictEdges (S.own (l,a))` (the reviewer's Check B proof) in
`EG/Lib/Chain/StageInst.lean`, with a test.

### COSMETIC-D (valid; not mine to fix)
`EG.lean`/`EGTest.lean` are root files, which this task may not edit. The orchestrator should add:
- to `EG`: `EG.Defs.Chain.{Design,Lending,JSet,JConsumer,Constants,StageInst}`,
  `EG.Lib.Chain.{Design,Lending,JSet,JConsumer,Constants,StageInst}`;
- to `EGTest`: `EGTest.Design`, `EGTest.StageInst`.
`EG.Lib.Chain.Design` now also imports `EG.Lib.Found.Components` (already in the tree).
