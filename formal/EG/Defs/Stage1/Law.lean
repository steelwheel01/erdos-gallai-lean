module

public import EG.Defs.Stage1.COL
public import EG.Defs.Stage1.Zones
public import EG.Defs.Stage1.Pool

/-!
# The stage-1 law: one joint distribution of (1a)–(1d) (manuscript s7:defSchedule, stage 1)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`, Definition [s7:defSchedule]: "*Stage 1* consists of four mutually
independent families: (1a) the COL-JV colourings of Definition [s3:defCOL] (i)–(iii); (1b) the
vertex choices and sublabels of Definition [s5:defZones]; (1c) the JS labels of Definition
[s3:defCOL] (iv); (1d) the pool labels of Definition [s7:defPool]." With [s3:defCOL]: "The data of
distinct ancestors are independent. … every edge `e` of `H_Y` carries three independent uniform
random variables …, and the labels of (iv) are independent of all edge variables", [s5:defZones]
"Independently for every vertex `v` of `G`, and independently of all other stage-1 data", and
[s7:defPool] "Every vertex `v` of `G` independently draws a pool label … independent of all other
stage-1 data".

Design note: `formal/work/p2d/stage1.md`. TRIAGE §2.7 (binding): "One record
`EG.Stage1.Outcome G run` with four named projections, one law `EG.Stage1.law G run`, and marginal
and independence lemmas (`IndepFun` of projections)".

Construction. All stage-1 variables are coordinates of one finite product:
* the coordinate set `Coord G run` is the disjoint union of the edges `(Y, e)` of the ancestors
  (`e ∈ E(H_Y)`, component (1a)), the vertices of `G` (1b), the JS sites `(Y, (l, y))` of the
  ancestors (1c), and the vertices of `G` again (1d);
* coordinate `c` takes values in `CoordVal G run c` and has law `coordLaw G run c` (`edgeLaw`,
  `zoneLabelLaw`, `jsLabelLaw`, `poolLabelLaw`);
* `law G run` is the image of `FinDist.pi (coordLaw G run)` under the bijection `Outcome.ofCoords`
  onto the record `Outcome G run`, whose fields are the four components: `col` (1a), `zone` (1b),
  `js` (1c), `pool` (1d).
Every independence statement of the manuscript about stage 1 is then independence of functions
of disjoint sets of coordinates (API: `EG.Lib.Stage1.Law`), and every marginal is a product law.

Ancestors are the elements of `run.ancestors G` (a `Finset PartId`); the fields `col`, `js` are
indexed by the subtype. `Outcome.colAt`/`jsAt`/`cOutAt` read them at any `Y : PartId` (with a junk
value off the ancestors), so that the events `COLa … COLg` of `EG.Stage1` apply to a stage-1
outcome as `COLa G run Y (ω.cOutAt Y)`.
-/

@[expose] public section

namespace EG.Stage1

open EG.HB

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- The coordinates of the stage-1 product: edges `(Y, e)` of the ancestors (1a), vertices (1b),
JS sites `(Y, (l, y))` of the ancestors (1c), vertices (1d). -/
abbrev Coord : Type _ :=
  (Σ Y : ↥(run.ancestors G), ↥(run.ancGraph G Y).edges) ⊕
    (↥G.verts ⊕ ((Σ Y : ↥(run.ancestors G), ↥(jsSites G run Y)) ⊕ ↥G.verts))

/-- The value type of a coordinate: an edge label triple, a zone label, a JS label, or a pool
label. -/
abbrev CoordVal : Coord G run → Type :=
  Sum.elim (fun p => EdgeLabel G run p.1)
    (Sum.elim (fun _ => Option ZIdx) (Sum.elim (fun _ => Option ℕ) (fun _ => Option (ℕ × ℕ))))

/-- The law of each coordinate: `edgeLaw` for an edge of `H_Y` ([s3:defCOL] (i)–(iii)),
`zoneLabelLaw` for the zone label of a vertex ([s5:defZones]), `jsLabelLaw G run l` for the JS
label at a site `(l, y)` ([s3:defCOL] (iv)), `poolLabelLaw` for the pool label of a vertex
([s7:defPool]). -/
noncomputable def coordLaw : (c : Coord G run) → FinDist (CoordVal G run c)
  | .inl p => edgeLaw G run p.1
  | .inr (.inl v) => zoneLabelLaw G run v
  | .inr (.inr (.inl p)) => jsLabelLaw G run p.2.1.1
  | .inr (.inr (.inr _)) => poolLabelLaw G run

/-- [s7:defSchedule] a stage-1 outcome, with the four families as named fields:
(1a) `col`, the COL-JV colouring of every ancestor; (1b) `zone`, the zone label (choice and
sublabel) of every vertex; (1c) `js`, the JS labels of every ancestor; (1d) `pool`, the pool
label of every vertex. -/
structure Outcome where
  /-- (1a) the COL-JV colourings [s3:defCOL] (i)–(iii), one per ancestor. -/
  col : (Y : ↥(run.ancestors G)) → Colouring G run Y
  /-- (1b) the vertex choices and sublabels [s5:defZones]. -/
  zone : ↥G.verts → Option ZIdx
  /-- (1c) the JS labels [s3:defCOL] (iv), one family per ancestor. -/
  js : (Y : ↥(run.ancestors G)) → JSLabels G run Y
  /-- (1d) the pool labels [s7:defPool]. -/
  pool : ↥G.verts → Option (ℕ × ℕ)

variable {G run}

/-- The stage-1 outcome with the given coordinates. -/
def Outcome.ofCoords (f : (c : Coord G run) → CoordVal G run c) : Outcome G run where
  col Y e := f (.inl ⟨Y, e⟩)
  zone v := f (.inr (.inl v))
  js Y s := f (.inr (.inr (.inl ⟨Y, s⟩)))
  pool v := f (.inr (.inr (.inr v)))

/-- The coordinates of a stage-1 outcome (inverse of `Outcome.ofCoords`). -/
def Outcome.toCoords (ω : Outcome G run) : (c : Coord G run) → CoordVal G run c
  | .inl p => ω.col p.1 p.2
  | .inr (.inl v) => ω.zone v
  | .inr (.inr (.inl p)) => ω.js p.1 p.2
  | .inr (.inr (.inr v)) => ω.pool v

/-- The stage-1 lending data of the ancestor `Y ∈ run.ancestors G` ([s3:defCOL] (i)–(iv)): its
colouring and its JS labels. -/
def Outcome.cOut (ω : Outcome G run) (Y : ↥(run.ancestors G)) : COLOut G run Y :=
  (ω.col Y, ω.js Y)

/-- The colouring of `Y : PartId` in `ω` (the field `col` at an ancestor; the junk colouring
`(false, none, 0)` on every edge if `Y` is not an ancestor). -/
noncomputable def Outcome.colAt (ω : Outcome G run) (Y : PartId) : Colouring G run Y :=
  if h : Y ∈ run.ancestors G then ω.col ⟨Y, h⟩ else fun _ => (false, none, 0)

/-- The JS labels of `Y : PartId` in `ω` (the field `js` at an ancestor; all `∗` otherwise). -/
noncomputable def Outcome.jsAt (ω : Outcome G run) (Y : PartId) : JSLabels G run Y :=
  if h : Y ∈ run.ancestors G then ω.js ⟨Y, h⟩ else fun _ => none

/-- The stage-1 lending data of `Y : PartId` in `ω` (`= ω.cOut ⟨Y, h⟩` for an ancestor). -/
noncomputable def Outcome.cOutAt (ω : Outcome G run) (Y : PartId) : COLOut G run Y :=
  (ω.colAt Y, ω.jsAt Y)

/-- [s3:defCOL] (iv) the JS label `lab_{Y,l}(y)` in `ω` (`none` = `∗`; also `none` off the sites
`r(Y) + 2 ≤ l ≤ R`, `y ∈ V(Y)`, and off the ancestors). -/
noncomputable def Outcome.labAt (ω : Outcome G run) (Y : PartId) (l : ℕ) (y : V) : Option ℕ :=
  if h : (l, y) ∈ jsSites G run Y then ω.jsAt Y ⟨(l, y), h⟩ else none

variable (G run)

/-- [s7:defSchedule] the law of stage 1: the four families (1a)–(1d) are mutually independent,
and within each family the variables are independent (per edge of every `H_Y`, per vertex, per JS
site, per vertex), each with its law `coordLaw` ([s3:defCOL], [s5:defZones], [s7:defPool]). -/
noncomputable def law : FinDist (Outcome G run) :=
  (FinDist.pi (coordLaw G run)).map Outcome.ofCoords

end EG.Stage1
