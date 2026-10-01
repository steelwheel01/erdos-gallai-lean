module

public import EG.Defs.Quot.Round
public import EG.Defs.Chain.JConsumer

/-!
# Statement of Lemma JV-L, the lift (manuscript s7:lemLift) — probe P-1

Statement file (`EG/Spec/**`), unit P1 (probe P-1). Design note: `formal/work/p2b/P1.md`. Proof
(stage 2): `EG/Proof/Quot/Lift.lean`. **Refutation target of probe P-1** (TRIAGE §4, s7 "What is
not established"): a lifted cycle repeating a vertex. It is excluded by part (ii) below, whose
conclusion `(Obj.cycle c).WF` contains `c.Nodup`.

Manuscript v6.1, `s7.tex`, Lemma [s7:lemLift] (Lemma JV-L: the lift):
"Let `3 ≤ l ≤ R`, fix any past, any `ξ_l`, and let `Live` be the set of live vertices of round `l`.
(i) `Live ∩ Pool_l = ∅`. Every port carries at most one PAR object of each PAR colour and at most
one coloured hub item of each HUB colour. Hence, although ports are not vertices of `Q_l`, at most
one edge of each sub-layer is an object or item with an end at a given port. Every fresh centre is
the middle of at most one cherry of each PAR colour. Hubs, fresh centres and ports are pairwise
disjoint.
(ii) For *every* decomposition `Dec` of `E(Q_l)` into cycles and single edges, the lift of each
cycle of `Dec` (Construction s7:consRound(h)) is a cycle of `G`, and the lift of each single edge
of `Dec` consists of one or two single edges of `G`. The lifts of distinct members of `Dec` are
pairwise edge-disjoint. Hence the lift of `Dec` consists of at most `2|Dec|` pairwise
edge-disjoint objects of `G`.
(iii) Every item is either paid or lies in exactly one edge of `Q_l`. Every junction edge `uw` is
the junction edge of at most one item-end, and that end is at `u`, never at `w`. The edge `uw` lies
in exactly one lent class, namely `LJV_{Y(u),l}`, where `Y(u)` is a lend-good ancestor of round at
most `l−2`; the only consumer of this class is the round-`l` step. Junction edges lie in `E_r(Y)`
for ancestors `Y` of rounds `r ≤ l−2`, items lie in `E_l(Z)` for `Z ∈ Std_l`, and these edge sets
are disjoint.
(iv) Consequently the round step of Construction s7:consRound, applied at every round
`3 ≤ l ≤ R`, is a J-consumer: `Obj_l` and `LentJV_l` satisfy (JC1)–(JC3) of Definition
s6:defJconsumer. The objects of `Obj_l` other than paid single edges number at most
`2|Dec_l| = 2f(Q_l)`."

Formal reading (TRIAGE §2.9, §2.10; blueprint s7a LIFT-*).
* Round level: every valid past `I`, every valid choice `R` of the fixed rules, every `ξ`.
  `Live = I.liveVerts`, `Pool_l = I.pool`; PAR objects `R.parObjs`, coloured hub items
  `R.colouredHub ξ.1`; the layer edges `R.layerEdges ξ` (unpaid PAR objects and coloured hub
  items), each in the sub-layer `(kind, κ, rank)` (`layerSubLayer`).
* (ii) "a decomposition of `E(Q_l)` into cycles and single edges" is
  `IsDecomp ((R.Q ξ).edges : Set _) Dec` (objects well formed, each edge of `Q_l` exactly once).
  The lift of a member `c` is `R.liftObj ξ c` (Defs; for a cycle it is the one closed walk of
  Construction (h)). "is a cycle of `G`" is `(Obj.cycle c').WF` (at least three pairwise distinct
  vertices) with all its edges in `E(G)`; "one or two single edges of `G`" likewise.
  "pairwise edge-disjoint objects" is `Nodup` of the concatenated edge lists of all lifted objects
  (this also says that each lifted object repeats no edge).
* (iii) "the item `e` lies in the edge `q` of `Q_l`" (`ItemInQEdge`): `e` is a J-edge of a layer
  edge whose `Q_l`-edge (in its rank sub-layer) is `q`. "paid" = in `R.paidEdges ξ` (paid in (a),
  (b), (d) or (e3)). An *item-end* with a junction edge is an end of a coloured hub item or of an
  unpaid PAR object (`juncEnds`); its junction edge is `s(port, junction)`. "exactly one lent
  class, namely `LJV_{Y(u),l}`" is stated among the classes `LJV_{Y,l}` of the ancestors `Y` of the
  past (the only lent classes the round step reads); "the only consumer of this class is the
  round-`l` step" is a property of the whole assembly (s3:defCOL (g), s6:lemLent) and is not a
  proposition about one round (blueprint LIFT-COLG-META): it is not formalized here. "Junction
  edges … items … are disjoint" is `Disjoint (R.junctionEdges ξ) I.J` (the round step reads
  `E_r(Y)` and `E_l(Z)` only through `LJV_{Y,l} ⊆ E(H_Y) ⊆ E_r(Y)` and `J_l`).
* (iv), round level: (JC1) in the form of the past (`LentJV_l ⊆ ⋃ LJV_{Y,l}` over the lend-good
  ancestors `Y` of rounds `≤ l − 2`), (JC2) = `EG.Chain.JC2 I.J (R.lentJV ξ) (R.objs ξ)` (it
  implies (JC3), `EG.Chain.JC3`), and the count `|⋃ lifts of Dec_l| ≤ 2f(Q_l)`; `R.objs ξ` is the
  list of the paid single edges followed by the lifts of `Dec_l = R.dec ξ`.
* (iv), run level (`LiftJConsumerRunStatement`): the J-consumer of s7 is
  `roundOut run G δ S π` (one chosen valid rule, the chosen `ξ_l`, TRIAGE §2.10 JV-SAME-Q); (JC1)
  and (JC2) are the predicates `EG.Chain.JC1`, `EG.Chain.JC2` of the J-consumer interface, for
  `3 ≤ l ≤ R` and every `J` with `JPlusProps`, as in `EG.Chain.JConsumer`. J⁺ and the other
  properties of the past enter as the hypothesis `(RoundInput.ofPast run G δ S π l J).Valid`
  (probe P-1 assumes J⁺; `ofPast_valid` is deferred, TRIAGE §4 row P-1).
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

section helpers

variable {V : Type*} [DecidableEq V]

/-- The layer edge `e` has an end at the port `u`: a PAR object with an end at `u`, or a hub item
`(h, u)` ([s7:lemLift] (i) "an object or item with an end at a given port"). -/
def layerHasPortEnd : LayerEdge V → V → Prop
  | .inl o, u => ∃ b, o.endAt b = u
  | .inr it, u => it.2 = u

/-- The J-edges of a layer edge: the one or two J-edges of a PAR object, or the edge `hu` of a hub
item `(h, u)`. -/
def layerItems : LayerEdge V → List (Sym2 V)
  | .inl o => o.edgeList
  | .inr it => [s(it.1, it.2)]

/-- The sub-layer `(kind, κ, ι)` of a layer edge (kind `false` = PAR, `true` = HUB; its colour
`κ`; its rank `ι`), or `none` if it has no colour ([s7:consRound] (g)). -/
noncomputable def layerSubLayer {I : RoundInput V} (R : Rules I) (ξ : Xi I.G I.M) :
    LayerEdge V → Option (Bool × ℕ × ℕ)
  | .inl o => (R.parColour o).map (fun κ => (false, κ, R.rank ξ (.inl o)))
  | .inr it => (R.hubColour ξ.1 it).map (fun κ => (true, κ, R.rank ξ (.inr it)))

/-- [s7:lemLift] (iii) "the item `e` lies in the edge `q` of `Q_l`": `e` is a J-edge of a layer
edge whose edge of `Q_l` (in the sub-layer of its rank) is `q`. -/
def ItemInQEdge {I : RoundInput V} (R : Rules I) (ξ : Xi I.G I.M) (e : Sym2 V)
    (q : Sym2 (QVert V)) : Prop :=
  ∃ le ∈ R.layerEdges ξ, R.qEdge ξ (R.rank ξ le) le = some q ∧ e ∈ layerItems le

/-- The item-ends that receive junctions ([s7:consRound] (e): "Every end of a coloured hub item or
of an unpaid PAR object now has a junction `w` … The edge `uw` is the *junction edge* of that
end"): the ends of the coloured hub items and of the unpaid PAR objects. -/
noncomputable def juncEnds {I : RoundInput V} (R : Rules I) (ξ : Xi I.G I.M) : Finset (REnd V) :=
  (R.colouredHub ξ.1).image (fun it => REnd.hub it.1 it.2) ∪
    (R.unpaidPar ξ).biUnion (fun o => (Finset.univ : Finset Bool).image (REnd.par o))

end helpers

/-- [s7:lemLift] (i) "`Live ∩ Pool_l = ∅`. Every port carries at most one PAR object of each PAR
colour and at most one coloured hub item of each HUB colour. Hence, although ports are not vertices
of `Q_l`, at most one edge of each sub-layer is an object or item with an end at a given port. Every
fresh centre is the middle of at most one cherry of each PAR colour. Hubs, fresh centres and ports
are pairwise disjoint." -/
def LiftRolesStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ ξ : Xi I.G I.M,
      Disjoint I.liveVerts I.pool ∧
      -- (2), (5) quantify over every vertex `u` / `x`, not only over ports / fresh centres:
      -- stronger than the TeX and still true, since only ports are ends and only fresh centres
      -- are middles of PAR objects (second review of P1, cosmetic C2)
      (∀ (u : V) (κ : ℕ),
          (R.parObjs.filter (fun o => (∃ b, o.endAt b = u) ∧ R.parColour o = some κ)).card ≤ 1) ∧
      (∀ (u : V) (κ : ℕ),
          ((R.colouredHub ξ.1).filter (fun it => it.2 = u ∧ R.hubColour ξ.1 it = some κ)).card
            ≤ 1) ∧
      -- (4): the hypothesis `(layerSubLayer R ξ e).isSome` is redundant, not a weakening: for a
      -- coloured hub item it holds by definition (`colouredHub` = items with an SDR, `hubColour`
      -- is then `some`), and for an unpaid PAR object under `I.Valid`, `R.Valid` it follows from
      -- `WellDefParStatement` (2) (every PAR object gets a colour). Stage-2 users discharge it that
      -- way (both checked in the scratch file of fix round 2, work/p2b/P1.md; review 2, C1)
      (∀ (u : V), ∀ e ∈ R.layerEdges ξ, ∀ e' ∈ R.layerEdges ξ,
          layerHasPortEnd e u → layerHasPortEnd e' u →
          (layerSubLayer R ξ e).isSome → layerSubLayer R ξ e = layerSubLayer R ξ e' → e = e') ∧
      (∀ (x : V) (κ : ℕ),
          (R.parObjs.filter (fun o => o.middle = some x ∧ R.parColour o = some κ)).card ≤ 1) ∧
      Disjoint I.hubs I.fresh ∧ Disjoint I.hubs I.ports ∧ Disjoint I.fresh I.ports

/-- [s7:lemLift] (ii) "For *every* decomposition `Dec` of `E(Q_l)` into cycles and single edges,
the lift of each cycle of `Dec` is a cycle of `G`, and the lift of each single edge of `Dec`
consists of one or two single edges of `G`. The lifts of distinct members of `Dec` are pairwise
edge-disjoint. Hence the lift of `Dec` consists of at most `2|Dec|` pairwise edge-disjoint objects
of `G`." (Refutation target of probe P-1: `(Obj.cycle c).WF` excludes a lifted cycle repeating a
vertex.) -/
def LiftDecompStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (Dec : List (Obj (QVert V))),
      IsDecomp ((R.Q ξ).edges : Set (Sym2 (QVert V))) Dec →
      (∀ c ∈ Dec, c.isEdge = false →
          ∃ c' : List V, R.liftObj ξ c = [Obj.cycle c'] ∧ (Obj.cycle c').WF ∧
            ∀ e ∈ cycleEdges c', e ∈ I.G.edges) ∧
      (∀ c ∈ Dec, c.isEdge = true →
          1 ≤ (R.liftObj ξ c).length ∧ (R.liftObj ξ c).length ≤ 2 ∧
          ∀ o ∈ R.liftObj ξ c, o.isEdge = true ∧ o.WF ∧ ∀ e ∈ o.edges, e ∈ I.G.edges) ∧
      ((Dec.flatMap (R.liftObj ξ)).flatMap Obj.edges).Nodup ∧
      (Dec.flatMap (R.liftObj ξ)).length ≤ 2 * Dec.length

/-- [s7:lemLift] (iii) "Every item is either paid or lies in exactly one edge of `Q_l`. Every
junction edge `uw` is the junction edge of at most one item-end, and that end is at `u`, never at
`w`. The edge `uw` lies in exactly one lent class, namely `LJV_{Y(u),l}`, where `Y(u)` is a
lend-good ancestor of round at most `l−2` […]. Junction edges lie in `E_r(Y)` for ancestors `Y` of
rounds `r ≤ l−2`, items lie in `E_l(Z)` for `Z ∈ Std_l`, and these edge sets are disjoint."
Scope (T0, see the module docstring and work/p2b/P1.md §6): "exactly one lent class" is checked
only among the classes `LJV_{Y,l}` of round `l` of the ancestors `Y ∈ I.ancs` of the past (the
classes the round step reads); exclusivity against the other lent classes (`Own`, `LJS`, `LU`, and
the classes of other rounds) is a property of the stage data (one COL label per edge,
s3:defCOL) and is not stated here. The clause "the only consumer of this class is the round-`l`
step" (COL(g)) is not formalized here either. The memberships `E_r(Y)` / `E_l(Z)` are rendered by
their consequence used in (iv): no junction edge is a J-edge. -/
def LiftAccountingStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ ξ : Xi I.G I.M,
      -- every item is paid, or lies in exactly one edge of `Q_l` (and not both)
      (∀ e ∈ I.items,
          (e ∈ R.paidEdges ξ ∧ ∀ q ∈ (R.Q ξ).edges, ¬ ItemInQEdge R ξ e q) ∨
          (e ∉ R.paidEdges ξ ∧ ∃! q, q ∈ (R.Q ξ).edges ∧ ItemInQEdge R ξ e q)) ∧
      -- a junction edge is the junction edge of at most one item-end
      (∀ en ∈ juncEnds R ξ, ∀ en' ∈ juncEnds R ξ, ∀ w w' : V,
          R.junction ξ en = some w → R.junction ξ en' = some w' →
          s(en.port, w) = s(en'.port, w') → en = en') ∧
      -- that end is at the port `u`, never at the junction `w` (a pooled vertex)
      (∀ en ∈ juncEnds R ξ, ∀ w : V, R.junction ξ en = some w →
          en.port ∈ I.ports ∧ en.port ∉ I.pool ∧ w ∈ I.pool) ∧
      -- `uw` lies in exactly one class `LJV_{Y,l}`, namely `Y = Y(u)`, lend-good, of round `≤ l−2`
      (∀ en ∈ juncEnds R ξ, ∀ w : V, R.junction ξ en = some w →
          I.cls en.port ∈ I.ancs ∧ s(en.port, w) ∈ I.ljv (I.cls en.port) ∧
          (∀ Y ∈ I.ancs, s(en.port, w) ∈ I.ljv Y → Y = I.cls en.port) ∧
          I.lendGood (I.cls en.port) ∧ (I.cls en.port).1 + 2 ≤ I.l) ∧
      -- junction edges and J-edges are disjoint
      Disjoint (R.junctionEdges ξ) I.J

/-- [s7:lemLift] (iv), round level: "`Obj_l` and `LentJV_l` satisfy (JC1)–(JC3) of Definition
s6:defJconsumer. The objects of `Obj_l` other than paid single edges number at most
`2|Dec_l| = 2f(Q_l)`." (For every `ξ`; (JC1) in the form of the past: `LentJV_l` lies in the classes
`LJV_{Y,l}` of the lend-good ancestors `Y` of rounds `≤ l − 2`; (JC2), which implies (JC3), is
`EG.Chain.JC2`.) -/
def LiftJConsumerStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ ξ : Xi I.G I.M,
      (∀ e ∈ R.lentJV ξ, ∃ Y ∈ I.ancs, Y.1 + 2 ≤ I.l ∧ I.lendGood Y ∧ e ∈ I.ljv Y) ∧
      Chain.JC2 I.J (R.lentJV ξ) (R.objs ξ) ∧
      ((R.dec ξ).flatMap (R.liftObj ξ)).length ≤ 2 * fnum (R.Q ξ).edges

/-- [s7:lemLift] (iv), run level: "Consequently the round step of Construction s7:consRound,
applied at every round `3 ≤ l ≤ R`, is a J-consumer: `Obj_l` and `LentJV_l` satisfy (JC1)–(JC3) of
Definition s6:defJconsumer. The objects of `Obj_l` other than paid single edges number at most
`2|Dec_l| = 2f(Q_l)`." The J-consumer is `roundOut run G δ S π` (Defs), its quotient
`roundQuotient run G δ S π l J`; the obligations are those of the fields `jc1`, `jc2` of
`EG.Chain.JConsumer` (for `3 ≤ l ≤ R` and `J` with `JPlusProps`), under the J⁺ hypothesis
`(RoundInput.ofPast run G δ S π l J).Valid`.
**Conditional statement** (fix round 1, review issue M1): that hypothesis bundles s6:lemJplus,
s7:lemCand (iv) and s2:propStructure (iii); its discharge, `ofPast_valid`, is an open obligation of
the joint s6/s7 unit (work/p2b/P1.md §3, §6, OBL-P1-1) that no Spec states yet, and the hypotheses of
this statement have not been shown satisfiable for `3 ≤ l ≤ R` (P1.md H4). This is the TeX's claim
"the round step … is a J-consumer" only modulo `ofPast_valid`. -/
def LiftJConsumerRunStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (run : HB.Run V) (G : FGraph V) (δ : Chain.Designation V)
    (S : Chain.StageData V) (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V)),
    3 ≤ l → l ≤ run.R → Chain.JPlusProps run G δ S l J →
    (RoundInput.ofPast run G δ S π l J).Valid →
      Chain.JC1 run G S l (roundOut run G δ S π l J).2 ∧
      Chain.JC2 J (roundOut run G δ S π l J).2 (roundOut run G δ S π l J).1 ∧
      (((RoundInput.ofPast run G δ S π l J).chosenRules.dec
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen).flatMap
        ((RoundInput.ofPast run G δ S π l J).chosenRules.liftObj
          (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen)).length ≤
        2 * fnum (roundQuotient run G δ S π l J).edges

end EG.Spec
