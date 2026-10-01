module

public import EG.Defs.Chain.Design

/-!
# Lending statuses, lost ports, retirement sets, `O_Z` and `X_U` (manuscript s6:defLending)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Definition [s6:defLending] ("stage-2 lending statuses, retirement sets and the
functional `X_U`"), quoted in the docstrings below. Design note: `formal/work/p2d/design.md`.
Namespace `EG.Chain`.

**The stage data are a parameter (decision D-DES-1 of the design note).** The definition reads
"a valid run, a designation `δ` and a stage-1 outcome: the colourings and JS labels of
Definition s3:defCOL, and the zones of Definition s5:defZones", through exactly these objects:
* whether all events of Lemma s3:lemCOL(a), resp. (b), hold for an ancestor `Y`;
* whether a light part `Y` is demoted (s5:defStages);
* the JS labels `lab_{Y,l}(y) ∈ {*} ∪ [0, K^JS_l)` (s3:defCOL(iv); `*` is `none`);
* the classes `Own_Y`, `LJS_{Y,l,j}`, `LJV_{Y,l}` (s3:defCOL(i),(ii)), as edge sets;
* the numbers `dem`, `lp` (s5:defStages).

These are bundled as the record `EG.Chain.StageData V`, and every definition of this file (and of
`EG.Chain.JPlusProps`, `EG.Chain.JConsumer`) is a function of the run, the designation and such a
record. The stage-1 layer (`EG/Defs/Stage1/**`, `EG/Defs/Light/**`, TRIAGE §3 items 15–19, not yet
written) instantiates the record from a stage-1 outcome `ω`; the instantiation is where the
meaning of the fields is fixed and reviewed (its contract is the docstring of each field). This
keeps the s6 interfaces independent of the concrete stage-1 sample space, so that probe P-2
(routing engine → JS-LC → J⁺) can be proved against them, and it adds no hypothesis: the record
has no axioms, so every statement proved "for every stage data" holds in particular for the
instantiated one.

Other encoding decisions (blueprint s6b notes LEND-*):
* `Lost_Z` is defined uniformly with the guard `3 ≤ l` (for `l ≤ 2` the manuscript's separate
  clause `Lost_Z := ∅, Ret_Z := A_Z ∪ F_Z = Z^0, Q*_Z := ∅` is then a Lib lemma:
  `EG.Chain.lost_of_le_two`, `qs_of_le_two`, `ret_of_le_two`);
* `O_Z` is a graph **on `Z^0`** (spanning): `Own_Z` is turned into a graph by
  `FGraph.ofEdges (Z^0) (Own_Z)`;
* `X_U` sums over the rounds `l ∈ [1, R]` (`Lost_l = ∅` outside `[3, R]`) and is a natural number.
-/

@[expose] public section

namespace EG.Chain

open EG.HB

/-- The stage-1 outcome together with its stage-2 statuses, **as read by s6** (s6:defLending,
s6:lemJSLC, s6:defJconsumer: "a stage-1 outcome with its stage-2 data"). A plain record without
axioms; the stage-1 layer instantiates it from a stage-1 outcome (see the module docstring). The
docstring of each field is the contract of that instantiation. -/
structure StageData (V : Type*) where
  /-- [s3:lemCOL] (a) every event of Lemma COL(a) holds for the ancestor `Y` (the expander
  properties of `Own_Y`, `Lend_Y`, of every lent class and, for light `Y`, of every own class). -/
  colA : PartId → Prop
  /-- [s3:lemCOL] (b) every event of Lemma COL(b) holds for the ancestor `Y` (every
  `LJS_{Y,l,j}` is `(2^{12} L_Y^4, t^JS_l)`-path connected through `T_j(Y,l)`). -/
  colB : PartId → Prop
  /-- [s5:defStages] the light part `Y` is *demoted* (read only for light parts). -/
  demoted : PartId → Prop
  /-- [s3:defCOL] (iv) the JS label `lab_{Y,l}(y) ∈ {*} ∪ [0, K^JS_l)` of the vertex `y` of the
  ancestor `Y` for round `l` (`r(Y) + 2 ≤ l ≤ R`, `y ∈ V(Y)`); `none` is the label `*`. -/
  lab : PartId → ℕ → V → Option ℕ
  /-- [s3:defCOL] (i) the own class `Own_Y` of the ancestor `Y` (an edge set, `⊆ E(H_Y)`). -/
  own : PartId → Finset (Sym2 V)
  /-- [s3:defCOL] (ii) the JS-lent class `LJS_{Y,l,j}` (an edge set, `⊆ Lend_Y`). -/
  ljs : PartId → ℕ → ℕ → Finset (Sym2 V)
  /-- [s3:defCOL] (ii) the JV-lent class `LJV_{Y,l}` (an edge set, `⊆ Lend_Y`). -/
  ljv : PartId → ℕ → Finset (Sym2 V)
  /-- [s5:defStages] `dem = Σ_{Y demoted} |Y|`. -/
  dem : ℕ
  /-- [s5:defStages] `lp = Σ_{Y ∈ Bad} |Y| (R − r(Y))`. -/
  lp : ℕ

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-- [s6:defLending] "An ancestor `Y` is *lend-bad* iff `Y` is a demoted light part (Definition
s5:defStages), or an event of Lemma s3:lemCOL(a) fails for `Y`, or an event of Lemma s3:lemCOL(b)
fails for `Y`. Otherwise `Y` is *lend-good*." -/
def lendBad (Y : PartId) : Prop :=
  (run.isLight G Y.1 Y.2 ∧ S.demoted Y) ∨ ¬ S.colA Y ∨ ¬ S.colB Y

open Classical in
/-- [s6:defLending], [s6:defJconsumer] (JC1), [s6:lemJSLC]: "`Y` a lend-good ancestor of a round
`≤ l − 2`" (written `r(Y) + 2 ≤ l`, TRIAGE §2.1). -/
noncomputable def lendGoodAnc (l : ℕ) : Finset PartId :=
  (run.ancestors G).filter (fun Y => Y.1 + 2 ≤ l ∧ ¬ lendBad run G S Y)

/-- [s3:defCOL] (iv) "`T_j(Y,l) := {y ∈ V(Y) : lab_{Y,l}(y) = j}`", the junction set of label
`j` of the ancestor `Y` for round `l` (as read in s6:defLending: "`u ∉ ⋃_j T_j(Y(u), l)`"). -/
noncomputable def Tj (Y : PartId) (l j : ℕ) : Finset V :=
  (run.ancVerts G Y).filter (fun y => S.lab Y l y = some j)

open Classical in
/-- [s6:defLending] "For `l ≥ 3` and `Z ∈ Std_l`, the set of *lost* ports is
`Lost_Z := {u ∈ Q_Z : Y(u) is lend-bad, or lab_{Y(u),l}(u) ≠ *}`. … For `l ≤ 2` put
`Lost_Z := ∅`." (The pre-part `Z` is its address `a`; `Y(u) = δ l u`.) -/
noncomputable def lost (l : ℕ) (a : Addr) : Finset V :=
  if 3 ≤ l then
    (run.classed G l a).filter (fun u => lendBad run G S (δ l u) ∨ S.lab (δ l u) l u ≠ none)
  else ∅

/-- [s6:defLending] "Put `Ret_Z := A_Z ∪ F_Z ∪ Lost_Z` (the *retirement set* of `Z` for Lemma
s4:lemTPV) … For `l ≤ 2` put … `Ret_Z := A_Z ∪ F_Z = Z^0`" (the second clause is the case
`Lost_Z = ∅` of the first: `EG.Chain.ret_of_le_two`). -/
noncomputable def ret (l : ℕ) (a : Addr) : Finset V :=
  run.hubs G l a ∪ run.fresh G l a ∪ lost run G δ S l a

/-- [s6:defLending] "`Q*_Z := Q_Z \ Lost_Z`. … For `l ≤ 2` put … `Q*_Z := ∅`" (for `l ≤ 2`,
`Q_Z = ∅` since `anc_l = ∅`, so the two clauses agree: `EG.Chain.qs_of_le_two`). The *classed
non-lost ports* of `Z`. -/
noncomputable def qs (l : ℕ) (a : Addr) : Finset V :=
  run.classed G l a \ lost run G δ S l a

open Classical in
/-- [s6:defLending] "`O_Z := Own_Z` if the ancestor `Z` is lend-good, and `O_Z := X^0_Z`
otherwise." `Own_Z` is taken as a graph on `Z^0` (spanning, as Lemma s4:lemTPV needs). For a
standalone `Z ∈ Std_l` the ancestor is `(l, a)`. -/
noncomputable def OZ (l : ℕ) (a : Addr) : FGraph V :=
  if lendBad run G S (l, a) then run.X0 G l a else FGraph.ofEdges (run.Z0 G l a) (S.own (l, a))

/-- [s6:defLending] "`Lost_l := ⋃_{Z ∈ Std_l} Lost_Z`". -/
noncomputable def lostRound (l : ℕ) : Finset V :=
  (run.Std G l).biUnion (lost run G δ S l)

/-- [s6:defLending] "`X_U := 80 dem + 369 lp + Σ_l (169 + M_l) |Lost_l|`, with `dem` and `lp` as in
Definition s5:defStages." The sum is over the rounds `l ∈ [1, R]` (`Lost_l = ∅` for `l ≤ 2`); a
natural number. -/
noncomputable def XU : ℕ :=
  80 * S.dem + 369 * S.lp +
    ∑ l ∈ Finset.Icc 1 run.R, (169 + run.M G l) * (lostRound run G δ S l).card

/-! ### Role sets of a round (s6:lemJplus (J3), s7:consRound) -/

/-- The fresh centres of round `l`: `⋃_{Z ∈ Std_l} F_Z` ([s6:lemJplus] (J3) "`⋃_Z F_Z` (fresh
centres)"). -/
noncomputable def freshCentres (l : ℕ) : Finset V :=
  (run.Std G l).biUnion (run.fresh G l)

/-- The classed non-lost ports of round `l`: `⋃_{Z ∈ Std_l} Q*_Z` ([s6:lemJplus] (J3)
"`⋃_Z Q*_Z` (classed non-lost ports)"; the *ports* of s7). -/
noncomputable def qsRound (l : ℕ) : Finset V :=
  (run.Std G l).biUnion (qs run G δ S l)

end EG.Chain
