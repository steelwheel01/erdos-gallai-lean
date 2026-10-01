module

public import EG.Defs.Stage1.Law
public import EG.Defs.PathDecomp
public import EG.Defs.Link.HBFamily
public import EG.Defs.Vortex.PVData

/-!
# Stage-2 statuses of light parts, the child data and the arc hypotheses (manuscript s5:defStages)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s5.tex`, Definition [s5:defStages], and the data named in Lemma [s5:lemChild]
and Lemma [s5:lemParent]. Design note: `formal/work/p2d/light.md`. Namespace `EG.Light`;
TRIAGE §3 item 19.

Manuscript text ([s5:defStages], opening): "Fix an outcome of the stage-1 data (the colourings and
labels of Definition [s3:defCOL] and the choices and sublabels of Definition [s5:defZones]). Let
`Y` be a light part of round `r`. Then `H_Y = X_Y` is a `(2^{-6}, s_r/2)`-expander on `Y` …. Put
`vm_Y := ⌈L_Y^6⌉` and `vb_Y := ⌈2^7 L_Y^2 vm_Y⌉`. … So Lemma [s3:lemHB], applied to `X_Y` with
`ε' = 2^{-6}` and `m = vm_Y` (then `b = vb_Y`), provides sets `A_Y(w) ⊆ N_{X_Y}(w)`, `w ∈ Y`, with
`|A_Y(w)| = vm_Y` such that every vertex lies in at most `vb_Y` of them. We fix one such family by
a fixed rule; it depends only on the run. Let `M_Y` denote the own colour class `M` of `Y`."

Data model (on the locked HB `Run` and the Stage-1 layer, `formal/work/p2d/{hb,stage1}.md`):
* a light part is a `PartId = (r, a)` in `run.lightParts G`, with `V(Y) = run.ancVerts G Y`,
  `H_Y = X_Y = run.X G Y.1 Y.2` (`= run.ancGraph G Y` for light `Y`), `L_Y = run.LY G Y`;
* a stage-1 outcome is `ω : EG.Stage1.Outcome G run`; every status is a function of `ω` (the
  manuscript's "deterministic functions of the stage-1 outcome" is definitional). The functions of
  `ω` take `G run` **implicitly** (they are determined by the type of `ω`): `demoted ω Y`,
  `dem ω`, `lp ω`, `Rt ω Z`, …; the functions of the run alone take `G run` explicitly, first
  (`vm G run Y`, `AY G run Y`, `Jbar G run l`; Stage-1 convention D-S1-1);
* the colouring of `Y` is read as `ω.colAt Y`, its lending data as `ω.cOutAt Y`, the zone labels
  as `ω.zone` (`EG.Stage1.Outcome`);
* "COL(a) fails" is `¬ EG.Stage1.COLa G run Y (ω.cOutAt Y)` (for light `Y` this is literally the
  list of [s5:defStages]: `EG.Stage1.COLa_iff_of_isLight`); "parent-bad" is the failure of the
  event `EG.Stage1.COLc` of [s3:lemCOL] (c) for the family of the zones of `Y` (for light `Y` its
  index set `I^U(Y)` is exactly the set of triples `(l, c, σ)` of [s5:defStages]);
* the statuses are total: they are defined for every `Y : PartId` and every outcome; they are
  meaningful for light parts and outcomes of positive weight (`ω ∈ (Stage1.law G run).supp`),
  which the statements assume (blueprint STAGES-STAGE1-SUPPORT).

`A_Y` exists only under hypotheses (Γ and validity; Lemma [s3:lemHB]); the definition is total by
`Classical.epsilon` of the property `EG.IsHBFamily` (`EG/Defs/Link/HBFamily.lean`, shared with the
s3 and s4 statements; blueprint STAGES-AY-CHOICE). Its property under the hypotheses is a Spec
(StagesHBStatement).

The child data `childData ω Z` is a value of the canonical Lemma-PV record `EG.Vortex.PVData`
(`EG/Defs/Vortex/PVData.lean`, TRIAGE §2.8 PV-DATA-RECORD).

The arcs of [s5:lemChild] are only asserted to exist; the parent side takes **any** arc systems
with the child-side properties (`ArcHyp`, blueprint PAR-ARCS-INPUT). Lemma [s5:lemChild] (b)–(d)
for one part is the per-part predicate `ArcSys` (with the `H_0` condition `H0Adm`), which both the
lemChild Spec and `ArcHyp` use.
-/

@[expose] public section

namespace EG.Light

open EG.HB EG.Stage1

variable {V : Type*} [DecidableEq V]

/-! ### Lemma-HB families and the fixed sets `A_Y` -/

/- The predicate `IsHBFamily X m b A` of Lemma [s3:lemHB] is `EG.IsHBFamily`
(`EG/Defs/Link/HBFamily.lean`), shared with the s3 and s4 statements (fix round 1, MINOR-3). -/

variable (G : FGraph V) (run : Run V)

/-- [s5:defStages] "Put `vm_Y := ⌈L_Y^6⌉`": written as the Lemma-PV parameter
`EG.Vortex.pvM |V(Y)| = ⌈(log₂|V(Y)|)^6⌉₊` (the same term, `vm_eq` is `rfl`), so that the sets
`A_Y` have exactly the size that [s4:lemPV] requires ([s5:lemChild] "so `vm = ⌈L_Z^6⌉`"). -/
noncomputable def vm (Y : PartId) : ℕ := Vortex.pvM (run.ancVerts G Y).card

/-- [s5:defStages] "and `vb_Y := ⌈2^7 L_Y^2 vm_Y⌉`": written as `EG.Vortex.pvB |V(Y)|`
`= ⌈2^7 (log₂|V(Y)|)^2 · pvM |V(Y)|⌉₊` (the same term, `vb_eq` is `rfl`). -/
noncomputable def vb (Y : PartId) : ℕ := Vortex.pvB (run.ancVerts G Y).card

/-- [s5:defStages] "Lemma [s3:lemHB], applied to `X_Y` with `ε' = 2^{-6}` and `m = vm_Y` (then
`b = vb_Y`), provides sets `A_Y(w) ⊆ N_{X_Y}(w)`, `w ∈ Y`, with `|A_Y(w)| = vm_Y` such that every
vertex lies in at most `vb_Y` of them. We fix one such family by a fixed rule; it depends only on
the run." The fixed rule is `Classical.epsilon` of `IsHBFamily (X_Y) vm_Y vb_Y` (an arbitrary
family if none exists; under Γ and validity one exists, a Spec). -/
noncomputable def AY (Y : PartId) : V → Finset V :=
  Classical.epsilon fun A : V → Finset V => IsHBFamily (run.X G Y.1 Y.2) (vm G run Y) (vb G run Y) A

/-! ### Statuses of a light part -/

variable {G run}

/-- [s5:defStages] "(E1) holds for `Y` if for every round `l` with `r ≤ l ≤ R` and every `w ∈ Y`:
`#{u ∈ A_Y(w) : wu ∈ M_Y and u carries no round-l zone} ≥ L_Y^5/8`." Here `M_Y` is the own class
`M` of the colouring of `Y` (`EG.Stage1.ownM`), and "`u` carries no round-`l` zone" is
`zonePhase ω.zone l u = none` ([s5:defZones]). -/
def E1 (ω : Outcome G run) (Y : PartId) : Prop :=
  ∀ l ∈ Finset.Icc Y.1 run.R, ∀ w ∈ run.ancVerts G Y,
    run.LY G Y ^ 5 / 8 ≤
      (((AY G run Y w).filter fun u =>
          s(w, u) ∈ (ownM G run Y (ω.colAt Y)).edges ∧ zonePhase ω.zone l u = none).card : ℝ)

/-- [s5:defStages] "`Y` is *demoted* if (E1) fails for `Y` or a COL(a) event fails for `Y`, that
is, if one of `Own_Y`, `Lend_Y` is not a `(2^{-6}, s_r/8)`-expander on `Y`, or some lent class of
`Y` is not a `(2^{-6}, s_lent)`-expander on `Y` with `s_lent := s_r/(16 k_lend(Y))`, or some own
class of `Y` is not a `(2^{-6}, s_own)`-expander on `Y` with `s_own := s_r/(16 k_own)` (Lemma
[s3:lemCOL] (a) with `ε_Y = 2^{-6}`, `s_Y = s_r/2`)." The COL(a) events are
`EG.Stage1.COLa G run Y (ω.cOutAt Y)`; for light `Y` they unfold to exactly this list
(`EG.Stage1.COLa_iff_of_isLight`). Total (no light guard; read only for light parts, TRIAGE
item 20). -/
def demoted (ω : Outcome G run) (Y : PartId) : Prop :=
  ¬ E1 ω Y ∨ ¬ COLa G run Y (ω.cOutAt Y)

/-- [s5:defStages] "`Y` is *parent-bad* if for some `(l,c,σ)` with `r+2 ≤ l ≤ R`, `c ∈ [4]`,
`σ ∈ [T^sl_Y]`, the class `LU_{Y,l,c,σ}` is not `(2^{12} L_Y^4, t_Y)`-path connected through
`Zone_{Y,l,c,σ}` (in the multiset sense of Cited result [s1:citDef7]), where `t_Y = ⌈λ_r^{1.6}⌉`
is the U-multiplicity parameter of Definition [s3:defCOL]. If `r ≥ R-1`, the family `I^U` of `Y`
is empty …, so `Y` has no sublabels and no zones and is never parent-bad."
Written as the failure of the event (c) of Lemma [s3:lemCOL] (`EG.Stage1.COLc`, with `t_Y =
EG.Stage1.tY`) for the family `V_{l,c,σ} := Zone_{Y,l,c,σ}` ([s5:lemE1] (c)); for light `Y` its
index set `I^U(Y)` is exactly the set of triples above (`EG.Stage1.mem_IU`). -/
def parentBad (ω : Outcome G run) (Y : PartId) : Prop :=
  ¬ COLc G run Y (ω.cOutAt Y) (fun i => Zone G run ω.zone Y i)

/-- [s5:defStages] "A *good parent* is a light part that is neither demoted nor parent-bad." -/
def goodParent (ω : Outcome G run) (Y : PartId) : Prop :=
  Y ∈ run.lightParts G ∧ ¬ demoted ω Y ∧ ¬ parentBad ω Y

open Classical in
/-- [s5:defStages] "`Bad := {demoted light parts} ∪ {parent-bad light parts}`". -/
noncomputable def Bad (ω : Outcome G run) : Finset PartId :=
  (run.lightParts G).filter fun Y => demoted ω Y ∨ parentBad ω Y

open Classical in
/-- The good parents of rounds `≤ l - 2` (written `r(Y) + 2 ≤ l`, TRIAGE §2.1): the parents
available to the light parts of round `l` ([s5:defStages] `Rt(Z)`; the nodes of the quotient
multigraphs of [s5:lemParent] Step 2). Empty for `l ≤ 2`. -/
noncomputable def goodParents (ω : Outcome G run) (l : ℕ) : Finset PartId :=
  (run.lightParts G).filter fun Y => goodParent ω Y ∧ Y.1 + 2 ≤ l

open Classical in
/-- [s5:defStages] "For a non-demoted light part `Z` of round `l` put
`Rt(Z) := Z ∩ ⋃{Y : Y a good parent of round ≤ l-2}`" (defined for every `Z : PartId`, with
`l = Z.1`). -/
noncomputable def Rt (ω : Outcome G run) (Z : PartId) : Finset V :=
  (run.ancVerts G Z).filter fun v => ∃ Y ∈ goodParents ω Z.1, v ∈ run.ancVerts G Y

/-- [s5:defStages] "`Pl(Z) := Z \ Rt(Z)`". -/
noncomputable def Pl (ω : Outcome G run) (Z : PartId) : Finset V :=
  run.ancVerts G Z \ Rt ω Z

open Classical in
/-- [s5:defStages] "give every `v ∈ Rt(Z)` the fixed parent `par(v)`, the good parent of the
smallest round `≤ l-2` that contains `v`. (It is unique: `v` lies in at most one light part per
round …) … `par(v)` depends only on `v` and on the round `l` of the part in which it is used."
`parU ω l v` is `some Y` for a good parent `Y ∋ v` of round `≤ l - 2` of smallest round (chosen by
`Classical.epsilon`; unique under s2:propStructure(iv), a Spec), and `none` if `v` lies in no good
parent of round `≤ l - 2`, i.e. `v ∉ Rt(Z)` for `v ∈ Z` of round `l`. -/
noncomputable def parU (ω : Outcome G run) (l : ℕ) (v : V) : Option PartId :=
  if ((goodParents ω l).filter fun Y => v ∈ run.ancVerts G Y).Nonempty then
    some (Classical.epsilon fun Y : PartId => Y ∈ goodParents ω l ∧ v ∈ run.ancVerts G Y ∧
      ∀ Y' ∈ goodParents ω l, v ∈ run.ancVerts G Y' → Y.1 ≤ Y'.1)
  else none

open Classical in
/-- [s5:defStages] "`dem := Σ_{Y demoted} |Y|`" (over the demoted light parts). -/
noncomputable def dem (ω : Outcome G run) : ℕ :=
  ∑ Y ∈ (run.lightParts G).filter (fun Y => demoted ω Y), (run.ancVerts G Y).card

/-- [s5:defStages] "`lp := Σ_{Y ∈ Bad} |Y| (R - r(Y))`" (`r(Y) ≤ R` for every light part, so the
natural subtraction is exact). -/
noncomputable def lp (ω : Outcome G run) : ℕ :=
  ∑ Y ∈ Bad ω, (run.ancVerts G Y).card * (run.R - Y.1)

/-! ### The data of Lemma PV for a light part ([s5:lemChild]) -/

/-- [s5:lemChild] "Fix a stage-1 outcome and a non-demoted light part `Z` of round `l`. Apply
Lemma [s4:lemPV] to the vertex set `Z` with the following data:
* `O := H_Z = X_Z`, and the sets `A(w) := A_Z(w)` of Definition [s5:defStages] (so
  `vm = ⌈L_Z^6⌉`, `vb = ⌈2^7 L_Z^2 vm⌉`);
* as own classes, the classes `R_{j,c}` (`0 ≤ j < J_Z`, `c ∈ [4]`) and `M = M_Z` of the colouring
  of `Own_Z` in Definition [s3:defCOL] (iii);
* `Rt := Rt(Z)` and `Pl := Pl(Z)` (Definition [s5:defStages]);
* `ext(v) := c` if `v` carries a round-`l` zone and `c` is its phase, and `ext(v) := *` if `v`
  carries no round-`l` zone."
With the expansion parameters of its proof: "`O = X_Z` is a spanning `(2^{-6}, s_l/2)`-expander on
`Z`" and "every own class is a spanning `(2^{-6}, s')`-expander on `Z` with `s' := s_l/(16 k_own)`".
The record is the canonical Lemma-PV data record `EG.Vortex.PVData` (TRIAGE §2.8 PV-DATA-RECORD).
Its own classes are indexed by `Fin (pvJ |Z|) × Fin 4` with `Z` the vertex-set field; here
`|Z| = |V(Z)|` and `J_Z = EG.Vortex.pvJ |V(Z)|` (`EG.Stage1.JY`) definitionally, so the classes
`R_{j,c}` of the colouring are passed with no cast (TRIAGE §2.7 PV-OWNCLASS-INDEX). -/
noncomputable def childData (ω : Outcome G run) (Z : PartId) : Vortex.PVData V where
  Z := run.ancVerts G Z
  O := run.X G Z.1 Z.2
  sO := (run.s G Z.1 : ℝ) / 2
  A := AY G run Z
  R p := ownR G run Z (ω.colAt Z) p.1 p.2
  M := ownM G run Z (ω.colAt Z)
  sOwn := (run.s G Z.1 : ℝ) / (16 * kown G run Z)
  Rt := Rt ω Z
  Pl := Pl ω Z
  ext v := zonePhase ω.zone Z.1 v

/-! ### Arcs, U-bundles and the child-side hypotheses of the parent side ([s5:lemParent]) -/

/-- An arc of a light part ([s5:lemChild] (b)): a path, as a vertex list, with its phase
`c ∈ [4]` (`Fin 4`). -/
abbrev Arc (V : Type*) : Type _ := List V × Fin 4

/-- The edge set of a family of arcs ("`H^arc(Z)` is the edge set of a family of … paths"). -/
def arcEdges (as : List (Arc V)) : Finset (Sym2 V) :=
  (as.flatMap fun a => walkEdges a.1).toFinset

open Classical in
/-- The non-demoted light parts of round `l` (the parts `Z` of [s5:lemChild] and [s5:lemParent]:
"the letter `Z` ranges over the non-demoted light parts of round `l`"). -/
noncomputable def childParts (ω : Outcome G run) (l : ℕ) : Finset PartId :=
  (run.lightParts G).filter fun Z => Z.1 = l ∧ ¬ demoted ω Z

/-- [s5:lemParent] the hypothesis on the edge set `H_0(Z)` of a non-demoted light part `Z` of
round `l = Z.1`: "an edge set `H_0(Z)` with `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`" (the same condition is the
hypothesis "for *every* edge set `H_0(Z)` with `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`" of [s5:lemChild]).
Per part, so that the lemChild Spec and `ArcHyp` share one copy (fix round 1, MINOR-1). -/
def H0Adm (ω : Outcome G run) (Z : PartId) (H0 : Finset (Sym2 V)) : Prop :=
  (Own G run Z (ω.colAt Z)).edges ⊆ H0 ∧ H0 ⊆ run.E G Z.1 Z.2

/-- [s5:lemChild] (b)–(d), for one non-demoted light part `Z` of round `l = Z.1`, an edge set
`H_0 = H_0(Z)` and a list `as` of arcs (a path as a vertex list, with its phase):
* (b) "`H^arc(Z)` is the edge set of a family of pairwise edge-disjoint paths (the *arcs* of
  `Z`), each with at least one edge and both ends in `Rt(Z)`, and each carrying a phase
  `c ∈ [4]`, such that every vertex of a phase-`c` arc, ends included, lies in no round-`l`
  phase-`c` zone": the concatenated edge lists are duplicate-free (pairwise edge-disjoint paths,
  as `Sym2`, so also across orientations); each arc is a path in `H_0` (as
  `H^arc(Z) ⊆ H_0(Z)`, the partition `H_0(Z) = H^obj(Z) ⊔ H^arc(Z)`) with `≥ 1` edge and both
  ends in `Rt(Z)`; "no round-`l` phase-`c` zone" is `x ∉ Zone_{Y,l,c,σ}` for all `Y`, `σ`;
* (c) "`Z` has at most `14(J_Z+1)|Z|` arcs, and every vertex `x` is an end of at most
  `deg_{H_0(Z)}(x) ≤ |Z|-1` arcs of `Z`";
* (d) "if `Rt(Z) = ∅`, in particular if `l ≤ 2`, then `Z` has no arcs".
Two clauses are **redundant and kept for literalness** (a Spec author must not drop one of them in
one place only; the lemChild Spec concludes this predicate verbatim): (d) follows from "both ends
in `Rt(Z)`" (every arc is a nonempty list, so `Rt(Z) = ∅` leaves no arc), and the bound
`pathEndCount ≤ |Z| - 1` follows from `pathEndCount ≤ deg_{H_0}` together with
`H_0 ⊆ E_l(Z) ⊆ V(Z).sym2` (loopless edges, `H0Adm`), which gives `deg_{H_0}(x) ≤ |Z| - 1`.
The pure (b)–(d) content (no hypothesis on `H_0`): `H0Adm` is separate. The lemChild Spec
concludes `ArcSys ω Z H0 as` for the arcs it produces; the parent side takes any `ArcSys`
families (`ArcHyp`, blueprint PAR-ARCS-INPUT). -/
def ArcSys (ω : Outcome G run) (Z : PartId) (H0 : Finset (Sym2 V)) (as : List (Arc V)) : Prop :=
  (as.flatMap fun a => walkEdges a.1).Nodup ∧
    (∀ a ∈ as, IsPathIn H0 a.1 ∧ 1 ≤ pathLength a.1 ∧
      (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ Rt ω Z) ∧
      ∀ x ∈ a.1, ∀ (Y : PartId) (σ : ℕ), x ∉ Zone G run ω.zone Y (LentTag.U Z.1 a.2 σ)) ∧
    as.length ≤ 14 * (JY G run Z + 1) * (run.ancVerts G Z).card ∧
    (∀ x, pathEndCount (as.map Prod.fst) x ≤ degE H0 x ∧
      pathEndCount (as.map Prod.fst) x ≤ (run.ancVerts G Z).card - 1) ∧
    (Rt ω Z = ∅ → as = [])

/-- The child-side properties of the arcs of the round-`l` parts, as the parent side uses them
([s5:lemParent] "Fix a round `l` … and, for every non-demoted light part `Z` of round `l`, an edge
set `H_0(Z)` with `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`; the arcs of `Z` are those given by Lemma
[s5:lemChild] for this `H_0(Z)`"): for every non-demoted light part `Z` of round `l`, `H_0(Z)`
satisfies `H0Adm` and the arcs of `Z` satisfy [s5:lemChild] (b)–(d) (`ArcSys`; since `Z.1 = l`,
the round of the zones and of `E_l(Z)` is `l`). Any arc systems with these properties are
admissible (blueprint PAR-ARCS-INPUT); the arcs of the other parts are not read. -/
def ArcHyp (ω : Outcome G run) (l : ℕ) (H0 : PartId → Finset (Sym2 V))
    (arcs : PartId → List (Arc V)) : Prop :=
  ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z) ∧ ArcSys ω Z (H0 Z) (arcs Z)

/-- [s5:lemParent] "For `c ∈ [4]` the *U-bundle* `B_{l,c}` is the set of all phase-`c` arcs of all
non-demoted light parts of round `l`; `E(B_{l,c})` denotes the union of their edge sets." -/
noncomputable def bundleEdges (ω : Outcome G run) (l : ℕ) (arcs : PartId → List (Arc V))
    (c : Fin 4) : Finset (Sym2 V) :=
  (childParts ω l).biUnion fun Z => arcEdges ((arcs Z).filter fun a => a.2 = c)

/-- [s5:lemParent] (i) "`LentU_{l,c} ⊆ ⋃_Y ⋃_{σ ∈ [T^sl_Y]} LU_{Y,l,c,σ}`, the union over the good
parents `Y` of rounds `≤ l-2`" (the U-lent edges available to the bundle `B_{l,c}`; `σ` is
`0`-based). -/
noncomputable def lentUAvail (ω : Outcome G run) (l : ℕ) (c : Fin 4) : Finset (Sym2 V) :=
  (goodParents ω l).biUnion fun Y =>
    (Finset.range (Tslot G run Y)).biUnion fun σ => (LU G run Y (ω.colAt Y) l c σ).edges

/-- [s5:lemParent] (i) "a *connector*, a path in `LU_{Y,l,c,σ}` all of whose interior vertices lie
in `Zone_{Y,l,c,σ}`". -/
def IsConnector (ω : Outcome G run) (l : ℕ) (c : Fin 4) (Y : PartId) (σ : ℕ) (p : List V) : Prop :=
  IsPathIn (LU G run Y (ω.colAt Y) l c σ).edges p ∧
    IsThrough (Zone G run ω.zone Y (LentTag.U l c σ)) p

variable (G run)

open Classical in
/-- [s5:lemParent] (preamble) "For a round `l ≥ 3` put `J̄_l := max{J_Z : Z a light part of round
l}` (and `J̄_l := 0` if there is none)" (a `Finset.sup` in `ℕ`, which is `0` on the empty set). -/
noncomputable def Jbar (l : ℕ) : ℕ :=
  ((run.lightParts G).filter fun Z => Z.1 = l).sup (JY G run)

end EG.Light
