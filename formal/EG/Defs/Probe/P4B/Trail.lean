module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import EG.Defs.Log
public import EG.Defs.Constants

/-!
# Multigraphs, closed trails of oriented arcs, and the function `η` of s5:lemParent

NEW DEFS FILE of probe unit P4B (probe P-4, part 2). No locked Defs file provides these notions
(blueprint s5 PAR-MGRAPH-EULER: "EG.MGraph … do not exist … Alternative that avoids a multigraph
TYPE: state T-join and Euler for 'finite index set I with an endpoint map' directly"; TRIAGE §4
row P-4 "Lib: Multigraph/T-join/Euler"). Design note `formal/work/p2b/P4B.md`.

Manuscript v6.1:
* [s1:citEuler] (b) "A connected graph (or multigraph) in which every vertex has even degree has a
  closed trail using every edge exactly once."
* [s5:lemParent] Step 2: "let `UQ_{l,c,i}` be the multigraph (loops allowed) whose vertices are
  the good parents of rounds `≤ l-2`, with one edge `e_a` joining `par(v)` and `par(v')` for each
  arc `a ∈ 𝒜_i` with ends `v, v'` (a loop if `par(v) = par(v')`)"; Step 3: "a loop adds `2` to
  the degree"; "We record a closed trail `𝒲` as a cyclic sequence `(a_1, …, a_k)`, `k ≥ 1`, … of
  distinct arcs of one class, each with an orientation: `a_j` is traversed from its end `v_j^-` to
  its end `v_j^+`, and `par(v_j^+) = par(v_{j+1}^-)` for all `j` (indices modulo `k`). The
  *transition* at position `j` is the pair `(v_j^+, v_{j+1}^-)`, and its *node* is `par(v_j^+)`."
  Step 4: "let `vis_Y(𝒲)` be the number of transitions of `𝒲` at `Y`".
* [s5:lemParent] Step 9: "`η(x) := log₂(2A log₂(A log₂ x)) / (log₂ x)^2` (`x ≥ log₂ D_*`)".

Encoding (namespace `EG.MTrail`):
* a multigraph is a finite set `E : Finset ι` of edge indices with an endpoint map
  `ends : ι → N × N` (an arbitrary orientation of each edge; loops `(x, x)` and parallel edges
  allowed);
* an *oriented edge* is `(e, b) : ι × Bool`, traversed from `oSrc` to `oTgt` (`b = true`: from
  `(ends e).1` to `(ends e).2`);
* a closed trail is a nonempty list of oriented edges with pairwise distinct edges such that each
  edge ends where the next one (cyclically) starts; its *transitions* are the pairs
  `(oTgt W[j], oSrc W[j+1 mod k])` (`transitions`);
* for arcs (paths with first/last vertex `ends a`) and the parent map `par : V → β`, the quotient
  multigraph has the endpoint map `qEnds par ends`; a closed trail of oriented arcs in the sense of
  Step 3 is `IsClosedTrail (qEnds par ends) W`, and its transitions (pairs of vertices of `V`) are
  `transitions ends W`, with node `par t.1` (`= par t.2`).
-/

@[expose] public section

namespace EG.MTrail

variable {ι N β : Type*}

/-- The start vertex of the oriented edge `(e, b)` (`b = true`: `(ends e).1`). -/
def oSrc (ends : ι → N × N) (p : ι × Bool) : N := if p.2 then (ends p.1).1 else (ends p.1).2

/-- The end vertex of the oriented edge `(e, b)` (`b = true`: `(ends e).2`). -/
def oTgt (ends : ι → N × N) (p : ι × Bool) : N := if p.2 then (ends p.1).2 else (ends p.1).1

/-- [s5:lemParent] Step 3 "The *transition* at position `j` is the pair `(v_j^+, v_{j+1}^-)`"
(indices modulo `k`): the list of the `k` transitions of the cyclic sequence `W`. -/
def transitions (ends : ι → N × N) (W : List (ι × Bool)) : List (N × N) :=
  List.zipWith (fun p q => (oTgt ends p, oSrc ends q)) W (W.rotate 1)

/-- A closed trail of the multigraph with endpoint map `ends` ([s1:citEuler] (b); [s5:lemParent]
Step 3 "a cyclic sequence `(a_1, …, a_k)`, `k ≥ 1`, … of distinct arcs …, each with an
orientation"): a nonempty list of oriented edges, pairwise distinct as edges, each ending where
the next one (cyclically) starts. -/
def IsClosedTrail (ends : ι → N × N) (W : List (ι × Bool)) : Prop :=
  W ≠ [] ∧ (W.map Prod.fst).Nodup ∧ ∀ t ∈ transitions ends W, t.1 = t.2

/-- [s5:lemParent] Step 2: the endpoint map of the quotient multigraph: the edge `e_a` of the
arc `a` with ends `ends a` joins `par (ends a).1` and `par (ends a).2`. -/
def qEnds (par : N → β) (ends : ι → N × N) : ι → β × β :=
  fun i => (par (ends i).1, par (ends i).2)

/-- [s5:lemParent] Step 4 "`vis_Y(𝒲)`, the number of transitions of `𝒲` at `Y`" (the node of a
transition `t` is `par t.1`). -/
def vis [DecidableEq β] (par : N → β) (ends : ι → N × N) (W : List (ι × Bool)) (Y : β) : ℕ :=
  (transitions ends W).countP fun t => par t.1 = Y

/-- The edges (arcs) used by a list of trails, in order. -/
def trailEdges (Ws : List (List (ι × Bool))) : List ι :=
  Ws.flatMap fun W => W.map Prod.fst

/-- [s5:lemParent] Step 3 "(a loop adds `2` to the degree)": the degree of `v` in the multigraph
`(E, ends)`, counting each end of each edge. -/
def mdeg [DecidableEq N] (E : Finset ι) (ends : ι → N × N) (v : N) : ℕ :=
  (E.filter fun e => (ends e).1 = v).card + (E.filter fun e => (ends e).2 = v).card

/-- The vertices of the multigraph `(E, ends)` that are ends of some edge. -/
def mVerts [DecidableEq N] (E : Finset ι) (ends : ι → N × N) : Finset N :=
  E.biUnion fun e => {(ends e).1, (ends e).2}

/-- The simple graph of the adjacencies of the multigraph `(E, ends)` (loops and multiplicities
dropped); connectivity of the multigraph is connectivity of this graph. -/
def mAdj (E : Finset ι) (ends : ι → N × N) : SimpleGraph N :=
  SimpleGraph.fromRel fun x y => ∃ e ∈ E, ends e = (x, y)

end EG.MTrail

namespace EG.Light

/-- [s5:lemParent] Step 9 "`η(x) := log₂(2A log₂(A log₂ x)) / (log₂ x)^2` (`x ≥ log₂ D_*`)"
(`A = 105`; the same nested logarithms as `EG.Chain.epsK`). -/
noncomputable def etaCh (x : ℝ) : ℝ :=
  Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * Real.logb 2 x)) / Real.logb 2 x ^ 2

end EG.Light
