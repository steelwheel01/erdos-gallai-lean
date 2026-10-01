module

public import EG.Defs.Probe.P4B.Trail
public import EG.Defs.Objects
public import EG.Defs.Walk

/-!
# Statements of the combinatorial steps of Lemma parent side (manuscript s5:lemParent, Steps 1–8)

Statement file (`EG/Spec/**`) of probe unit P4B (probe P-4, part 2): the step nodes "quotient
multigraph, T-join, Euler, trail surgery, slots, multiplicity" of TRIAGE §4 row P-4, stated
abstractly (no run, no stage-1 outcome): arcs are edge indices `ι` with their two ends
`ends : ι → V × V`, the parent map is any `par : V → β`. The run-level nodes (the multiplicity
`M_l - 1 ≤ t_Y`, the end count of a U-bundle, `η` halving, the parent-bad probability) are in
`EG/Spec/Light/ParentRun.lean`; the lemma itself is the s5 unit's `EG.Spec.LemParentStatement`
(`EG/Spec/Light/Parent.lean`). Design note `formal/work/p2b/P4B.md`; Defs
`EG/Defs/Probe/P4B/Trail.lean` (`EG.MTrail`).

Manuscript v6.1, `s5.tex`, proof of Lemma [s5:lemParent] (quoted per statement below).

Formal reading (common):
* the arcs of one class: a finite set `A : Finset ι`; the arc `a` has ends `(ends a).1`,
  `(ends a).2` (first and last vertex of its path);
* the quotient multigraph `UQ_{l,c,i}` of Step 2: edge set `A`, endpoint map `qEnds par ends`
  (`e_a` joins `par(v)`, `par(v')`; a loop if they are equal), node set any finset `Nd ⊇` the parents
  of the arc ends ("the good parents of rounds `≤ l−2`", at most `ν_l` of them);
* a closed trail of Step 3 is `IsClosedTrail (qEnds par ends) W` for a list `W` of oriented arcs;
  its transitions are `transitions ends W` (pairs `(v_j^+, v_{j+1}^-)` of vertices), their nodes
  `par t.1`; `vis par ends W Y` counts the transitions at `Y`; `trailEdges Ws` lists the arcs of a
  list of trails.
-/

@[expose] public section

namespace EG.Spec

open EG.MTrail

universe u v w

/-- [s5:lemParent] Steps 2–3 (quotient multigraph, `T`-join, Euler trails), for one class: "let
`UQ_{l,c,i}` be the multigraph (loops allowed) whose vertices are the good parents of rounds
`≤ l−2`, with one edge `e_a` joining `par(v)` and `par(v')` for each arc `a ∈ 𝒜_i` with ends
`v, v'` … Fix a spanning forest `𝓕_i` of `UQ_{l,c,i}` … there is a set `𝒯_i ⊆ E(𝓕_i)` in which
every vertex has odd degree iff it lies in `Odd_i`. Then all degrees of `UQ_{l,c,i} − 𝒯_i` are
even, and `|𝒯_i| ≤ |E(𝓕_i)| ≤ ν_l − 1`. … Every component of `UQ_{l,c,i} − 𝒯_i` that has an edge
… has a closed Euler trail … This gives at most `ν_l` closed trails for class `i`, which together
use every edge of `UQ_{l,c,i} − 𝒯_i` exactly once": for arcs `A` whose ends have parents in the
node set `Nd`, there are a set `T ⊆ A` of at most `|Nd| − 1` arcs (output as single edges) and at
most `|Nd|` closed trails of the quotient multigraph that use every arc of `A \ T` exactly once and
no other arc. -/
def ArcClassEulerStatement : Prop :=
  ∀ (V : Type u) (β : Type v) (ι : Type w) [DecidableEq V] [DecidableEq β] [DecidableEq ι]
    (A : Finset ι) (ends : ι → V × V) (par : V → β) (Nd : Finset β),
    (∀ a ∈ A, par (ends a).1 ∈ Nd ∧ par (ends a).2 ∈ Nd) →
    ∃ (T : Finset ι) (Ws : List (List (ι × Bool))),
      T ⊆ A ∧ T.card ≤ Nd.card - 1 ∧ Ws.length ≤ Nd.card ∧
      (∀ W ∈ Ws, IsClosedTrail (qEnds par ends) W) ∧
      (trailEdges Ws).Nodup ∧
      ∀ a, a ∈ trailEdges Ws ↔ a ∈ A ∧ a ∉ T

/-- [s5:lemParent] Claim (transitions): "In every closed trail of this kind, every transition
consists of two distinct vertices of its node `Y`." Proof: "Both vertices have parent `Y` …
If `k ≥ 2`, then `a_j ≠ a_{j+1}` are distinct arcs of one class, which are vertex-disjoint
(Step 1), so `v_j^+ ≠ v_{j+1}^-`. If `k = 1`, the transition is `(v_1^+, v_1^-)`, the two ends of
one arc, which are distinct by (F-d)." Stated for a closed trail of the quotient multigraph whose
arcs have two distinct ends and pairwise disjoint end sets (arcs of one class are vertex-disjoint,
so in particular their ends are). -/
def TransitionClaimStatement : Prop :=
  ∀ (V : Type u) (β : Type v) (ι : Type w) [DecidableEq V] [DecidableEq β] [DecidableEq ι]
    (ends : ι → V × V) (par : V → β) (W : List (ι × Bool)),
    IsClosedTrail (qEnds par ends) W →
    (∀ p ∈ W, (ends p.1).1 ≠ (ends p.1).2) →
    (∀ p ∈ W, ∀ q ∈ W, p.1 ≠ q.1 →
      ∀ x, (x = (ends p.1).1 ∨ x = (ends p.1).2) → x ≠ (ends q.1).1 ∧ x ≠ (ends q.1).2) →
    ∀ t ∈ transitions ends W, t.1 ≠ t.2 ∧ par t.1 = par t.2

/-- [s5:lemParent] Step 4 (visit capping): "If `vis_Y(𝒲) > T^sl_Y`, *split* `𝒲` at `Y` … Group
consecutive segments into `⌈vis/T^sl_Y⌉` blocks of at most `T^sl_Y` segments. A block
`(a_p, …, a_q)` is again a closed trail of the same kind … So a split at `Y` replaces `𝒲` by
`⌈vis/T^sl_Y⌉ ≤ 1 + vis/T^sl_Y` closed trails, partitions the arcs of `𝒲` among them, leaves every
transition at every other node unchanged … Process the nodes `Y` one after another … at the end
every trail `𝒲` satisfies `vis_Y(𝒲) ≤ T^sl_Y` for every `Y`. When `Y` is processed, the number of
new trails is at most `Σ_𝒲 vis_Y(𝒲)/T^sl_Y` … and `Σ_𝒲 vis_Y(𝒲)` … is not changed by any
split. Call it `tr_{c,i,Y}`": for closed trails `Ws` (pairwise arc-disjoint) and capacities
`cap Y ≥ 1` at the nodes of their transitions, there are closed trails `Ws'` with the same arcs
(each final trail uses arcs of one initial trail, with their orientation), at most `cap Y`
transitions at every node `Y`, and at most `|Ws| + Σ_Y tr_Y / cap Y` of them, the sum over the
nodes of the transitions of `Ws`. -/
def VisitCapStatement : Prop :=
  ∀ (V : Type u) (β : Type v) (ι : Type w) [DecidableEq V] [DecidableEq β] [DecidableEq ι]
    (ends : ι → V × V) (par : V → β) (cap : β → ℕ) (Ws : List (List (ι × Bool))),
    (∀ W ∈ Ws, IsClosedTrail (qEnds par ends) W) → (trailEdges Ws).Nodup →
    (∀ W ∈ Ws, ∀ t ∈ transitions ends W, 1 ≤ cap (par t.1)) →
    ∃ Ws' : List (List (ι × Bool)),
      (∀ W' ∈ Ws', IsClosedTrail (qEnds par ends) W') ∧
      (trailEdges Ws').Perm (trailEdges Ws) ∧
      (∀ W' ∈ Ws', ∃ W ∈ Ws, ∀ p ∈ W', p ∈ W) ∧
      (∀ W' ∈ Ws', ∀ Y : β, vis par ends W' Y ≤ cap Y) ∧
      (Ws'.length : ℝ) ≤ (Ws.length : ℝ) +
        ∑ Y ∈ ((Ws.flatMap (transitions ends)).map fun t => par t.1).toFinset,
          (((Ws.flatMap (transitions ends)).countP fun t => par t.1 = Y : ℕ) : ℝ) / (cap Y : ℝ)

/-- [s5:lemParent] Step 5, first two bullets (the multiplicity count; refutation target of P-4):
"*Each arc end lies in at most one transition.* … every end of every arc of a trail lies in
exactly one transition of that trail. … Hence every arc end lies in at most one transition over all
final trails of all classes. *Counting.* By the transition claim, `v` is at most one of the two
vertices of any pair, and each occurrence of `v` in a pair is an arc end at `v` … By the first
bullet, distinct occurrences are distinct arc ends, and an arc has at most one end equal to `v`,
since its two ends are distinct (F-d). So the number of pairs … containing `v`, counted with
multiplicity, is at most the number of arcs … having `v` as an end": for closed trails `Ws` of the
quotient multigraph, pairwise arc-disjoint, whose arcs have two distinct ends, the number of
transitions (over all trails, with multiplicity) containing a vertex `v` is at most the number of
arcs of the trails having `v` as an end. -/
def TransitionCountStatement : Prop :=
  ∀ (V : Type u) (β : Type v) (ι : Type w) [DecidableEq V] [DecidableEq β] [DecidableEq ι]
    (ends : ι → V × V) (par : V → β) (Ws : List (List (ι × Bool))),
    (∀ W ∈ Ws, IsClosedTrail (qEnds par ends) W) → (trailEdges Ws).Nodup →
    (∀ a ∈ trailEdges Ws, (ends a).1 ≠ (ends a).2) →
    ∀ v : V,
      (Ws.flatMap (transitions ends)).countP (fun t => t.1 = v ∨ t.2 = v) ≤
        ((trailEdges Ws).toFinset.filter fun a => (ends a).1 = v ∨ (ends a).2 = v).card

/-- [s5:lemParent] Step 7, Claim (cycles): "Let `𝒲 = (a_1, …, a_k)` be a final trail, and let
`𝒞_j` be the connector of its transition `(v_j^+, v_{j+1}^-)` … Let `C(𝒲)` be the closed walk that
traverses `a_1` from `v_1^-` to `v_1^+`, then `𝒞_1` from `v_1^+` to `v_2^-`, then `a_2`, then
`𝒞_2`, and so on, and returns to `v_1^-` along `𝒞_k`. `C(𝒲)` is a cycle of `G` of length at least
`3`." Proof inputs: "(1) The arcs `a_1, …, a_k` are paths with pairwise disjoint vertex sets …
(2) … no interior vertex of a connector lies on an arc of `𝒲`. (3) For `j ≠ j'` the interiors of
`𝒞_j` and `𝒞_{j'}` are disjoint … (4) Each `𝒞_j` is a path from `v_j^+` to `v_{j+1}^-`, and these
two vertices are distinct … Suppose it had exactly two [edges]. Then `k = 1`, `a_1` is the single
edge `v_1^-v_1^+` and `𝒞_1` is the single edge `v_1^+v_1^-`. As `G` is simple, these are the same
edge. But … these edge sets are disjoint (F-c)." Stated for the list `segs` of pairs
(arc traversed in trail order, its connector): the arcs and connectors are paths with `≥ 1` edge,
connector `j` runs from the last vertex of arc `j` to the first vertex of arc `j+1` (cyclically),
the arcs are pairwise vertex-disjoint, the connector interiors are pairwise disjoint and avoid all
arcs, and no arc edge is a connector edge; then the closed walk `a_1 𝒞_1° a_2 𝒞_2° ⋯ a_k 𝒞_k°`
(`°` = interior) is a cycle (no repeated vertex, `≥ 3` vertices) whose edges are exactly the arc
edges and the connector edges. -/
def ConnectorCycleStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (segs : List (List V × List V)),
    segs ≠ [] →
    (∀ s ∈ segs, s.1.Nodup ∧ 2 ≤ s.1.length ∧ s.2.Nodup ∧ 2 ≤ s.2.length) →
    (∀ p ∈ List.zip segs (segs.rotate 1),
      p.1.2.head? = p.1.1.getLast? ∧ p.1.2.getLast? = p.2.1.head?) →
    (segs.flatMap Prod.fst).Nodup →
    (segs.flatMap fun s => interior s.2).Nodup →
    (∀ s ∈ segs, ∀ s' ∈ segs, ∀ x ∈ interior s.2, x ∉ s'.1) →
    (segs.flatMap fun s => walkEdges s.1).Disjoint (segs.flatMap fun s => walkEdges s.2) →
    (Obj.cycle (segs.flatMap fun s => s.1 ++ interior s.2)).WF ∧
      (cycleEdges (segs.flatMap fun s => s.1 ++ interior s.2)).Perm
        (segs.flatMap fun s => walkEdges s.1 ++ walkEdges s.2)

end EG.Spec
