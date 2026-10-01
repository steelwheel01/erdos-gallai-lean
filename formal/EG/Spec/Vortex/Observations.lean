module

public import EG.Defs.PathDecomp
public import EG.Defs.Graph

/-!
# Statements of the shared vortex observations (S), (E), (C) (manuscript s4, §"Conventions and
elementary observations")

Statement file (`EG/Spec/**`) of probe unit P4A (probe P-4, part 1): probe nodes (the vortex step
engine: trails, ends, closing). Design note `formal/work/p2b/P4A.md`. Proofs (stage 2):
`EG/Proof/Vortex/Observations.lean`.

Manuscript v6.1, `s4.tex`: "The three proofs below share five elementary observations. They are
recorded here once, with tags, and proved in full; they are parts of the proofs of Lemma TPV,
Lemma PV and Theorem VX⁺ below, not separate statements." Three of them are stated here: (S)
`s4:eqSplit`, (E) `s4:eqEnds`, (C) `s4:eqClose`. (MC) and (B) are probabilistic and are not used
by the deterministic part of Lemma PV that this unit probes.

Formal reading.
* A walk `x_0 x_1 ⋯ x_q` is its vertex list `T` (`T ≠ []`, `q = T.length - 1`), its edges are
  `EG.walkEdges T`; "a trail (a walk with pairwise distinct edges) in a simple graph" is
  `(walkEdges T).Nodup` together with "no edge of `T` is a loop" (the only use of simplicity in
  the proof: `i' - i = 1` "would be a loop").
* `rep(T) := (q+1) - |{x_0, …, x_q}|` is `T.length - T.toFinset.card` (natural subtraction; the
  right side is `≤` the left side).
* A cycle is a vertex list `c` with `(EG.Obj.cycle c).WF` (no repeated vertex, `≥ 3` vertices),
  its edges `EG.cycleEdges c`; a path is a vertex list without repeated vertex and with at least
  two vertices, its edges `EG.walkEdges`. "`E(T)` is the disjoint union of the edge sets of the
  pieces" is a `List.Perm` between the concatenated edge lists of the pieces and `walkEdges T`
  (as `walkEdges T` has no duplicate, this is disjointness plus equality of the unions).
* "at most one path": an `Option (List V)`.
* (E): a decomposition of an edge set `F` into non-trivial paths is `EG.IsPathDecomp ↑F P`;
  "the number of paths of `𝒫` having `v` as an end" is `EG.pathEndCount P v`; `deg_F(v)` is
  `EG.degE F v`.
* (C): "`Q'` an `x–y` path" is a vertex list without repeated vertex from `x` to `y`; "whose inner
  vertices avoid `V(Q)`" is `∀ v ∈ interior Q', v ∉ Q`; "`Q ∪ Q'` is a cycle" is the vertex list
  `Q ++ (interior Q').reverse` (go along `Q` from `x` to `y`, then back along `Q'`), a well-formed
  cycle whose edges are those of `Q` and of `Q'`.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s4:eqSplit] (S) "Let `T = x_0x_1⋯x_q` (`q ≥ 0`) be a trail (a walk with pairwise distinct
edges) in a simple graph and put `rep(T) := (q+1) - |{x_0,…,x_q}|`. Then `E(T)` is the disjoint
union of the edge sets of at most `rep(T)` cycles, each of length at least `3`, and of at most
one path; the path is present if and only if `x_0 ≠ x_q`, and then its ends are `x_0` and `x_q`.
Every vertex of every piece is a vertex of `T`." -/
def TrailSplitStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (T : List V),
    T ≠ [] → (walkEdges T).Nodup → (∀ e ∈ walkEdges T, ¬ e.IsDiag) →
    ∃ (C : List (List V)) (p : Option (List V)),
      (∀ c ∈ C, (Obj.cycle c).WF) ∧ C.length ≤ T.length - T.toFinset.card ∧
      List.Perm (C.flatMap cycleEdges ++ (p.map walkEdges).getD []) (walkEdges T) ∧
      (p.isSome ↔ T.head? ≠ T.getLast?) ∧
      (∀ q ∈ p, q.Nodup ∧ 2 ≤ q.length ∧ q.head? = T.head? ∧ q.getLast? = T.getLast?) ∧
      (∀ c ∈ C, ∀ x ∈ c, x ∈ T) ∧ (∀ q ∈ p, ∀ x ∈ q, x ∈ T)

/-- [s4:eqSplit] (S), last sentence: "In particular, if the inner vertices `x_1,…,x_{q-1}` are
pairwise distinct, then `rep(T) ≤ 2`" (the rest of the sentence, "`T` splits into at most two
cycles and at most one path", is then `TrailSplitStatement`). The inner vertices are
`EG.interior T`. The proof uses only the counting `|{x_0,…,x_q}| ≥ q - 1`, so no trail hypothesis
is needed. -/
def TrailRepInnerStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (T : List V),
    (interior T).Nodup → T.length - T.toFinset.card ≤ 2

/-- [s4:eqEnds] (E), first sentence: "Let `𝒫` be a decomposition of an edge set `F` into
(non-trivial) paths. For every vertex `v` the number of paths of `𝒫` having `v` as an end is
congruent to `deg_F(v)` modulo `2`." -/
def PathEndsParityStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (F : Finset (Sym2 V)) (P : List (List V)),
    IsPathDecomp (F : Set (Sym2 V)) P → ∀ v : V, pathEndCount P v % 2 = degE F v % 2

/-- [s4:eqEnds] (E), second sentence: "If every vertex is an end of at most two paths of `𝒫` and
all edges of `F` have both ends in a set `W`, then `|𝒫| ≤ |W|`." (Also the "Consequence used in
this manuscript" of [s1:citCor22].) -/
def PathEndsCountStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (F : Finset (Sym2 V)) (P : List (List V)) (W : Finset V),
    IsPathDecomp (F : Set (Sym2 V)) P → (∀ v : V, pathEndCount P v ≤ 2) →
    (∀ e ∈ F, ∀ v ∈ e, v ∈ W) → P.length ≤ W.card

/-- [s4:eqClose] (C) "Let `Q` be a path of length at least `2` with ends `x ≠ y`, and let `Q'` be
an `x–y` path whose inner vertices avoid `V(Q)` and which shares no edge with `Q`. Then `Q ∪ Q'`
is a cycle of length at least `3`." The cycle is the vertex list `Q ++ (interior Q').reverse`; its
edges are the edges of `Q` and of `Q'`. -/
def ClosingStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (Q Q' : List V) (x y : V),
    Q.Nodup → 2 ≤ pathLength Q → Q.head? = some x → Q.getLast? = some y →
    Q'.Nodup → Q'.head? = some x → Q'.getLast? = some y →
    (∀ v ∈ interior Q', v ∉ Q) → (walkEdges Q).Disjoint (walkEdges Q') →
    (Obj.cycle (Q ++ (interior Q').reverse)).WF ∧
      List.Perm (cycleEdges (Q ++ (interior Q').reverse)) (walkEdges Q ++ walkEdges Q')

end EG.Spec
