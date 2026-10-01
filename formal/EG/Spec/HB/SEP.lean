module

public import EG.Defs.HB.SplitTree

/-!
# Statement of Lemma SEP (manuscript s2:lemSEP)

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). Design note
`formal/work/p2b/P3A.md`. Definitions: `EG/Defs/HB/SplitTree.lean` (locked).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemSEP]:
"A *split recursion* on a graph `H_0` is a finite rooted binary tree whose nodes `ν` carry graphs
`H_ν`, with `H_ν = H_0` at the root, such that at every non-leaf node `ν` there are disjoint sets
`U'_ν, N''_ν ⊆ V(H_ν)` for which the two children `ν_1, ν_2` of `ν` carry
`H_{ν_1} = H_ν[U'_ν ∪ N''_ν]`, `H_{ν_2} = H_ν[V(H_ν) \ U'_ν] - E(H_ν[N''_ν])`, and the *deleted
set* at `ν` is `F''_ν := E_{H_ν}(U'_ν, V(H_ν) \ (U'_ν ∪ N''_ν))`. … We write `|ν| := |H_ν|`, say
that a vertex `v` *lies in* `ν` if `v ∈ V(H_ν)`, and call the leaf nodes *leaves* (distinct leaf
nodes are distinct leaves even if their vertex sets coincide). A *deleted edge* is an edge of some
`F''_ν`. Let `Dup` be the set of vertices lying in at least two leaves. Then: (0) … (i) … (ii) …
(iii) …" (each item is quoted at its statement).

Formal reading (Defs of `EG.HB.STree`).
* A split recursion on `H` is a tree `t : STree V` with `t.WF H`; the graph at the node with
  address `a` is `t.graphAtD H a`; the children of `a` are `a ++ [false]` (`ν_1`) and
  `a ++ [true]` (`ν_2`); `U'_a = t.labelU a`, `N''_a = t.labelN a`, `F''_a = t.delAt H a`.
* Leaves are leaf *addresses* (`t.leafAddrs`), so distinct leaves with equal vertex sets are
  distinct; `Dup = t.dup H`; the deleted edges are `t.deleted H`; the total leaf size is
  `t.leafMass H`.
* "Ancestor" is "prefix" (`List.IsPrefix`, notation `a <+: b`); a node is an ancestor of itself
  ("`Leaf_u` included"); "below `ν`" means "with address extending `ν`".
* (0') (`SEPMonoStatement`) is the monotonicity "vertex sets shrink downwards" used in the proofs
  of (i), (ii) and by later lemmas without citation (blueprint SEP-MONO-IMPLICIT).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemSEP] (0) "at every non-leaf `ν`, `E(H_ν) = E(H_{ν_1}) ⊔ E(H_{ν_2}) ⊔ F''_ν`; a vertex
of `U'_ν` lies only in `ν_1`, a vertex of `N''_ν` lies in both children, every other vertex of
`ν` lies only in `ν_2`, and `|ν_1| + |ν_2| = |ν| + |N''_ν|`. Every vertex of a node lies in at
least one leaf below it, and the total size of the leaves is `|H_0| + Σ_ν |N''_ν|`, the sum over
the non-leaf nodes." -/
def SEP0Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V), t.WF H →
    (∀ a ∈ t.internalAddrs,
      Disjoint (t.graphAtD H (a ++ [false])).edges (t.graphAtD H (a ++ [true])).edges ∧
      Disjoint (t.graphAtD H (a ++ [false])).edges (t.delAt H a) ∧
      Disjoint (t.graphAtD H (a ++ [true])).edges (t.delAt H a) ∧
      (t.graphAtD H (a ++ [false])).edges ∪ (t.graphAtD H (a ++ [true])).edges ∪ t.delAt H a =
        (t.graphAtD H a).edges ∧
      (∀ v ∈ t.labelU a, v ∈ (t.graphAtD H (a ++ [false])).verts ∧
        v ∉ (t.graphAtD H (a ++ [true])).verts) ∧
      (∀ v ∈ t.labelN a, v ∈ (t.graphAtD H (a ++ [false])).verts ∧
        v ∈ (t.graphAtD H (a ++ [true])).verts) ∧
      (∀ v ∈ (t.graphAtD H a).verts \ (t.labelU a ∪ t.labelN a),
        v ∉ (t.graphAtD H (a ++ [false])).verts ∧ v ∈ (t.graphAtD H (a ++ [true])).verts) ∧
      (t.graphAtD H (a ++ [false])).card + (t.graphAtD H (a ++ [true])).card =
        (t.graphAtD H a).card + (t.labelN a).card) ∧
    (∀ a ∈ t.nodeAddrs, ∀ v ∈ (t.graphAtD H a).verts,
      ∃ b ∈ t.leafAddrs, a <+: b ∧ v ∈ (t.graphAtD H b).verts) ∧
    t.leafMass H = H.card + ∑ a ∈ t.internalAddrs, (t.labelN a).card

/-- [s2:lemSEP] (0'), implicit in the proofs of (i)–(iii) ("Every edge of a child is an edge of
its parent", "vertex sets shrink downwards"): the graph of a node is a subgraph of the graph of
each of its ancestors; in particular every node graph is a subgraph of `H_0`. (No hypothesis
`t.WF H` is needed.) -/
def SEPMonoStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V) (a b : Addr),
    b ∈ t.nodeAddrs → a <+: b → t.graphAtD H b ≤ t.graphAtD H a

/-- [s2:lemSEP] (i) "every edge `xy` of `H_0` either lies in exactly one leaf, which contains `x`
and `y`, or is deleted at exactly one node `ν`. In the second case `x` and `y` lie in `ν` and go
to different children of `ν`, each to only one child, and `ν` is the first node on the path of
nodes having `xy` as an edge at which this happens."

Formal reading. "Either … or …, exactly one" is the count
`#{leaves L : e ∈ E(H_L)} + #{non-leaf ν : e ∈ F''_ν} = 1`. In the second case: `e = xy` with
`x ∈ U'_ν` and `y ∈ V(H_ν) \ (U'_ν ∪ N''_ν)` (so `x, y` lie in `ν`); `x` lies in `ν_1` and not in
`ν_2`, `y` in `ν_2` and not in `ν_1`; `e` is an edge of every ancestor of `ν` (`ν` included) and of
neither child ("the first node … at which this happens"; blueprint SEP-I-FIRST-NODE). -/
def SEPiStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V), t.WF H →
    ∀ e ∈ H.edges,
      (t.leafAddrs.filter (fun L => e ∈ (t.graphAtD H L).edges)).card +
          (t.internalAddrs.filter (fun a => e ∈ t.delAt H a)).card = 1 ∧
      (∀ L ∈ t.leafAddrs, e ∈ (t.graphAtD H L).edges → ∀ x ∈ e, x ∈ (t.graphAtD H L).verts) ∧
      (∀ a ∈ t.internalAddrs, e ∈ t.delAt H a →
        (∀ b : Addr, b <+: a → e ∈ (t.graphAtD H b).edges) ∧
        e ∉ (t.graphAtD H (a ++ [false])).edges ∧ e ∉ (t.graphAtD H (a ++ [true])).edges ∧
        ∃ x y : V, e = s(x, y) ∧ x ∈ t.labelU a ∧
          y ∈ (t.graphAtD H a).verts \ (t.labelU a ∪ t.labelN a) ∧
          x ∈ (t.graphAtD H (a ++ [false])).verts ∧ x ∉ (t.graphAtD H (a ++ [true])).verts ∧
          y ∉ (t.graphAtD H (a ++ [false])).verts ∧ y ∈ (t.graphAtD H (a ++ [true])).verts)

/-- [s2:lemSEP] (ii) "if `u ∉ Dup` and `u ∈ V(H_0)`, then the nodes in which `u` lies are exactly
the ancestors of the unique leaf `Leaf_u` containing `u` (`Leaf_u` included), and `u ∉ N''_ν` at
every node `ν` on that path." -/
def SEPiiStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V), t.WF H →
    ∀ u ∈ H.verts, u ∉ t.dup H →
      ∃ L ∈ t.leafAddrs, u ∈ (t.graphAtD H L).verts ∧
        (∀ L' ∈ t.leafAddrs, u ∈ (t.graphAtD H L').verts → L' = L) ∧
        (∀ a ∈ t.nodeAddrs, u ∈ (t.graphAtD H a).verts ↔ a <+: L) ∧
        (∀ a ∈ t.internalAddrs, a <+: L → u ∉ t.labelN a)

/-- [s2:lemSEP] (iii) "if `u ∉ Dup`, `u, h ∈ V(H_0)`, `h ∉ V(Leaf_u)`, and `ν^*` is the deepest
ancestor of `Leaf_u` in which `h` lies, then every deleted edge `hu'` with
`u' ∈ V(Leaf_u) \ Dup` is deleted at `ν^*`."

Formal reading. `Leaf_u` is a leaf `L` containing `u` (unique by (ii)); "`ν^*` is the deepest
ancestor of `L` in which `h` lies" is: `ν^* <+: L`, `h ∈ V(H_{ν^*})`, and every prefix `b` of `L`
with `h ∈ V(H_b)` is at most as long as `ν^*` (blueprint SEP-III-DEEPEST). -/
def SEPiiiStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V), t.WF H →
    ∀ (u h : V), ∀ L ∈ t.leafAddrs, u ∈ H.verts → u ∉ t.dup H → u ∈ (t.graphAtD H L).verts →
      h ∈ H.verts → h ∉ (t.graphAtD H L).verts →
      ∀ νs : Addr, νs <+: L → h ∈ (t.graphAtD H νs).verts →
        (∀ b : Addr, b <+: L → h ∈ (t.graphAtD H b).verts → b.length ≤ νs.length) →
        ∀ u' ∈ (t.graphAtD H L).verts \ t.dup H, s(h, u') ∈ t.deleted H →
          s(h, u') ∈ t.delAt H νs

end EG.Spec
