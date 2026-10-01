module

public import EG.Defs.HB.Witness

/-!
# Split recursions: trees, addresses, node graphs, `Dup`, grafting, `τ`-runs
(manuscript s2:lemSEP, s2:lemThinCut, s2:lemOVgeneric, s2:lem14tau)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s2.tex`. Design note: `formal/work/p2d/hb.md`. Namespace `EG.HB`.

Data model (TRIAGE §2.2, blueprint s2a SEP-TREE-INFRA; PLAN §3 decision 5, choices only):
* a split recursion is stored as its *choices*: `EG.HB.STree V` (a binary tree labelled by `Finset V × Finset V`);
  `nil` is a leaf, `node (U', N'') t₁ t₂` is a non-leaf node with its two sets `U'_ν`, `N''_ν`
  and its first and second child. The node graphs are *computed* from the root graph `H₀` by the
  generic split `EG.HB.splitFst` / `EG.HB.splitSnd` (the forms of Lemma SEP), which is shared by
  both levels of the two-level recursion of a round;
* nodes are named by their **address** `EG.HB.Addr = List Bool` (the path from the root; `false`
  = first child `ν_1`, `true` = second child `ν_2`). "Distinct leaf nodes are distinct leaves
  even if their vertex sets coincide" ([s2:lemSEP]): leaves, pieces, pre-parts and ancestors are
  identified by addresses, never by vertex sets (blueprint SEP-LEAF-IDENTITY);
* `STree.nodeAddrs`, `leafAddrs`, `internalAddrs`; `labelAt` (the pair `(U'_ν, N''_ν)` of a
  non-leaf node), `labelU`, `labelN`; `graphAtD t H₀ a` (the graph `H_ν` at address `a`; total:
  an address that leaves the tree returns the graph of the last node on its path);
  `delAt` (`F''_ν`), `WF` (the condition "`U'_ν, N''_ν ⊆ V(H_ν)` disjoint"), `leafMass` (`S`),
  `dup` (`Dup`), `deleted` (the set of deleted edges), `DeltaGe` (`Δ_{≥M}`), `dupGe`
  (`dup_{≥M}(v)`), `EG.HB.cOV` (`c_OV`), `OVHyp` (the hypotheses of Lemma OV);
* `STree.graft t f` (the two-level recursion: attach `f a` at every leaf `a` of `t`; the grafted
  node at address `b` of `f a` has address `a ++ b`) and `STree.leafPrefix t a` (the leaf of `t`
  on the path to `a`: the piece above a node of the grafted tree);
* validity predicates: `StopsAt` ("a node is a leaf iff its graph has property `P`"),
  `IsS0Rec` (an `s = 0` recursion, [s2:lemOVgeneric]), `IsTauSplitTree` (every split is produced
  by the `τ`-rules, hypothesis of [s2:lemThinCut]), `IsTauRun` (a `τ`-run, [s2:lem14tau]).

Validity is never built into the tree type: every tree is finite by construction, and the
predicates above are hypotheses of the statements (blueprint HB-VALID-NO-TERMINATION).
-/

@[expose] public section

namespace EG.HB

/-- A node address in a split recursion: the path from the root, `false` = first child,
`true` = second child. Also the address of a pre-part in the two-level recursion of its round
(TRIAGE §2.1: `EG.HB.Addr := List Bool`). -/
abbrev Addr := List Bool

/-- [s2:lemSEP] "A *split recursion* on a graph `H_0` is a finite rooted binary tree whose nodes
`ν` carry graphs `H_ν`, with `H_ν = H_0` at the root, such that at every non-leaf node `ν` there
are disjoint sets `U'_ν, N''_ν ⊆ V(H_ν)` …": the choices of a split recursion. `nil` is a leaf;
`node (U', N'') t₁ t₂` is a non-leaf node carrying `(U'_ν, N''_ν)` with first child `t₁` and
second child `t₂`. The graphs are computed by `STree.graphAtD`; the side conditions are
`STree.WF`. (The same shape as Mathlib's `BinaryTree (Finset V × Finset V)`; a separate inductive
type so that generalized field notation `t.graphAtD`, `t.IsTauRun`, … works on every tree
expression, design note `hb.md` D-HB-2.) -/
inductive STree (V : Type*) where
  /-- A leaf. -/
  | nil : STree V
  /-- A non-leaf node carrying `(U'_ν, N''_ν)`, with its first and second child. -/
  | node (p : Finset V × Finset V) (l r : STree V) : STree V

instance {V : Type*} : Inhabited (STree V) := ⟨.nil⟩

namespace STree

variable {V : Type*}

/-- The pair `(U'_ν, N''_ν)` carried by the node at address `a`: `some` for a non-leaf node,
`none` for a leaf or an address outside the tree. -/
def labelAt : STree V → Addr → Option (Finset V × Finset V)
  | .nil, _ => none
  | .node p _ _, [] => some p
  | .node _ l _, false :: a => labelAt l a
  | .node _ _ r, true :: a => labelAt r a

/-- The subtree rooted at address `a` (`none` if `a` is not a node address). -/
def subtreeAt : STree V → Addr → Option (STree V)
  | t, [] => some t
  | .nil, _ :: _ => none
  | .node _ l _, false :: a => subtreeAt l a
  | .node _ _ r, true :: a => subtreeAt r a

/-- The addresses of all nodes of the tree. -/
def nodeAddrs : STree V → Finset Addr
  | .nil => {[]}
  | .node _ l r =>
      insert [] ((nodeAddrs l).image (List.cons false) ∪ (nodeAddrs r).image (List.cons true))

/-- [s2:lemSEP] "call the leaf nodes *leaves*": the addresses of the leaves. -/
def leafAddrs : STree V → Finset Addr
  | .nil => {[]}
  | .node _ l r => (leafAddrs l).image (List.cons false) ∪ (leafAddrs r).image (List.cons true)

/-- The addresses of the non-leaf nodes. -/
def internalAddrs : STree V → Finset Addr
  | .nil => ∅
  | .node _ l r =>
      insert [] ((internalAddrs l).image (List.cons false) ∪
        (internalAddrs r).image (List.cons true))

/-- `U'_ν` at address `a` (`∅` if `a` is not a non-leaf node). -/
def labelU (t : STree V) (a : Addr) : Finset V := ((t.labelAt a).map Prod.fst).getD ∅

/-- `N''_ν` at address `a` (`∅` if `a` is not a non-leaf node). -/
def labelN (t : STree V) (a : Addr) : Finset V := ((t.labelAt a).map Prod.snd).getD ∅

variable [DecidableEq V]

/-- [s2:lemSEP] "nodes `ν` carry graphs `H_ν`, with `H_ν = H_0` at the root, … the two children
`ν_1, ν_2` of `ν` carry `H_{ν_1} = H_ν[U'_ν ∪ N''_ν]`,
`H_{ν_2} = H_ν[V(H_ν) \ U'_ν] - E(H_ν[N''_ν])`": the graph `H_a` at address `a`, computed from
the root graph `H₀` by `splitFst` / `splitSnd` along `a`. Total: when `a` leaves the tree (it
continues below a leaf), the graph of the leaf on its path is returned. -/
def graphAtD : STree V → FGraph V → Addr → FGraph V
  | .nil, H, _ => H
  | .node _ _ _, H, [] => H
  | .node p l _, H, false :: a => graphAtD l (splitFst H p.1 p.2) a
  | .node p _ r, H, true :: a => graphAtD r (splitSnd H p.1 p.2) a

/-- [s2:lemSEP] "the *deleted set* at `ν` is `F''_ν := E_{H_ν}(U'_ν, V(H_ν) \ (U'_ν ∪ N''_ν))`"
(empty at a leaf, where `U'_ν = N''_ν = ∅` by convention). -/
def delAt (t : STree V) (H : FGraph V) (a : Addr) : Finset (Sym2 V) :=
  splitDel (t.graphAtD H a) (t.labelU a) (t.labelN a)

/-- [s2:lemSEP] "… at every non-leaf node `ν` there are disjoint sets
`U'_ν, N''_ν ⊆ V(H_ν)`": the tree `t` is a split recursion on `H₀`. -/
def WF (t : STree V) (H : FGraph V) : Prop :=
  ∀ a ∈ t.internalAddrs, t.labelU a ⊆ (t.graphAtD H a).verts ∧
    t.labelN a ⊆ (t.graphAtD H a).verts ∧ Disjoint (t.labelU a) (t.labelN a)

/-- [s2:lemSEP] (0) "the total size of the leaves", `S = Σ_{leaves L} |L|` ([s2:lemOVgeneric]
"Let `S` be the total size of the leaves"): the sum over leaf addresses (leaves with equal vertex
sets are counted separately). -/
def leafMass (t : STree V) (H : FGraph V) : ℕ :=
  ∑ a ∈ t.leafAddrs, (t.graphAtD H a).card

/-- [s2:lemSEP] "Let `Dup` be the set of vertices lying in at least two leaves": the vertices
`v` for which at least two leaf *addresses* `a` have `v ∈ V(H_a)`. (Every node graph has its
vertices in `V(H₀)`, since `induce` intersects with the vertex set, so filtering `V(H₀)` loses
nothing.) -/
def dup (t : STree V) (H : FGraph V) : Finset V :=
  H.verts.filter (fun v => 2 ≤ (t.leafAddrs.filter (fun a => v ∈ (t.graphAtD H a).verts)).card)

/-- [s2:lemSEP] "A *deleted edge* is an edge of some `F''_ν`": the union of the deleted sets of
the non-leaf nodes. -/
def deleted (t : STree V) (H : FGraph V) : Finset (Sym2 V) :=
  t.internalAddrs.biUnion (fun a => t.delAt H a)

/-- [s2:lemOVgeneric] "For `M ≥ 2` let `Δ_{≥M} := Σ_ν |N''_ν|`, the sum over the non-leaf nodes
`ν` with `|ν| ≥ M`". `M` is real (it is `P_r ∈ ℕ` or `2` in the applications); defined for every
real `M`. -/
noncomputable def DeltaGe (t : STree V) (H : FGraph V) (M : ℝ) : ℕ :=
  ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)), (t.labelN a).card

/-- [s2:lemOVgeneric] "for a vertex `v` let `dup_{≥M}(v)` be the number of non-leaf nodes `ν`
with `|ν| ≥ M` and `v ∈ N''_ν`". -/
noncomputable def dupGe (t : STree V) (H : FGraph V) (M : ℝ) (v : V) : ℕ :=
  (t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ) ∧ v ∈ t.labelN a)).card

/-- [s2:lemOVgeneric] "Consider a split recursion (Lemma SEP) on a root graph with `n_0 ≥ 1`
vertices such that at every non-leaf node `ν`, with `m := |ν|`,
`m ≥ 2, |ν_1| ≤ (3/4)m, |N''_ν| ≤ c ε |U'_ν| / log² m`": the hypotheses of Lemma OV (the
split-recursion condition is `WF`; `n_0 ≥ 1` is not included, it is not needed, blueprint
OV-N0-POS). `ν_1` is the node at address `a ++ [false]`. -/
def OVHyp (ε c : ℝ) (t : STree V) (H : FGraph V) : Prop :=
  t.WF H ∧ ∀ a ∈ t.internalAddrs, 2 ≤ (t.graphAtD H a).card ∧
    ((t.graphAtD H (a ++ [false])).card : ℝ) ≤ 3 / 4 * ((t.graphAtD H a).card : ℝ) ∧
    ((t.labelN a).card : ℝ) ≤ c * ε * (t.labelU a).card / Real.logb 2 (t.graphAtD H a).card ^ 2

/-! ### Grafting (the two-level recursion, [s2:defHBtp] (R3)) -/

/-- [s2:defHBtp] (R3) "The *two-level recursion* of round `l` is the split recursion obtained
from the `s = 0` recursion by attaching, at every piece `𝒫` with `|𝒫| ≥ P_l`, the tree of its
`τ`-run": `t.graft f` replaces the leaf of `t` at address `a` by the tree `f a`. A node at
address `b` of `f a` gets the address `a ++ b`. (The labels of `f a` are used unchanged; the
graphs of the grafted tree below `a` are those of `f a` rooted at the leaf graph of `t` at `a`,
a lemma.) -/
def graft : STree V → (Addr → STree V) → STree V
  | .nil, f => f []
  | .node p l r, f =>
      .node p (graft l (fun a => f (false :: a))) (graft r (fun a => f (true :: a)))

/-- The address of the leaf of `t` on the path `a` (the longest prefix of `a` that is a node of
`t`, when that node is a leaf). For a node `a ++ b` of `t.graft f` below the leaf `a` of `t`,
`t.leafPrefix (a ++ b) = a`: the piece above a node of the two-level recursion. (Junk when `a`
ends at a non-leaf node of `t`.) -/
def leafPrefix : STree V → Addr → Addr
  | .nil, _ => []
  | .node _ _ _, [] => []
  | .node _ l _, false :: a => false :: leafPrefix l a
  | .node _ _ r, true :: a => true :: leafPrefix r a

/-! ### Validity predicates -/

/-- "a node is a leaf iff its graph has property `P`" ([s2:defHBtp] (R3): "a node is a leaf iff
its graph is an `(ε,0)`-expander"; [s2:lem14tau]: "stops if `H` is an `(ε,s)`-expander (the node
is then a leaf)"). -/
def StopsAt (t : STree V) (H : FGraph V) (P : FGraph V → Prop) : Prop :=
  ∀ a ∈ t.nodeAddrs, (a ∈ t.leafAddrs ↔ P (t.graphAtD H a))

/-- [s2:lemOVgeneric] "Call a split recursion an *`s = 0` recursion* if at every non-leaf node `ν`
there is a witness `(U_ν, F_ν)` at `H_ν` with parameter `s = 0` (Definition [s2:defWitness]) and
`U'_ν = U_ν`, `N''_ν = Nbr_{H_ν}(U_ν)`." The witness parameter `ε` is an argument (s2 uses
`ε = 2^{-5}`). The stopping rule of (R3) is not part of this predicate (`StopsAt`). -/
def IsS0Rec (ε : ℝ) (t : STree V) (H : FGraph V) : Prop :=
  t.WF H ∧ ∀ a ∈ t.internalAddrs, ∃ (U : Finset V) (F : Finset (Sym2 V)),
    IsWitness (t.graphAtD H a) ε 0 U F ∧
      t.labelAt a = some (U, (t.graphAtD H a).nbrSet U)

/-- [s2:lemThinCut] "consider a split recursion (Lemma SEP) in which every split is produced by
the `τ`-rules at threshold `τ`: at each non-leaf node `ν` there are `s_ν < τ` and a witness at
`H_ν` (with parameter `s_ν`) whose `τ`-rules (Definition [s2:defTauRules]) give `U'_ν` and
`N''_ν`." The witness `(U,F)` enters through `N = Nbr_{H_ν - F}(U)` (`witN`). -/
def IsTauSplitTree (ε τ : ℝ) (t : STree V) (H : FGraph V) : Prop :=
  t.WF H ∧ ∀ a ∈ t.internalAddrs, ∃ (s : ℝ) (U : Finset V) (F : Finset (Sym2 V)), s < τ ∧
    IsWitness (t.graphAtD H a) ε s U F ∧
      t.labelAt a = some (tauU1 (t.graphAtD H a) U (witN (t.graphAtD H a) U F) τ,
        tauN2 (t.graphAtD H a) U (witN (t.graphAtD H a) U F) τ)

/-- [s2:lem14tau] "The *`τ`-run* of `H_0` (with parameters `s, τ`) is the recursion that, at a
node `H`, stops if `H` is an `(ε,s)`-expander (the node is then a leaf), and otherwise picks any
witness `(U,F)` at `H` with parameter `s` (Definition [s2:defWitness]) and splits `H` by the
`τ`-rules at threshold `τ` (Definition [s2:defTauRules])."

Formal reading ("for every choice of witnesses" = every tree satisfying this predicate):
`t` is a split recursion on `H₀` (`WF`); a node is a leaf iff its graph is an `(ε,s)`-expander
(both directions, blueprint HB-STOPRULE); at every non-leaf node the label is the pair
`(U', N'')` of the `τ`-rules for some witness with parameter `s`. The children are the generic
`splitFst`/`splitSnd` at `(U', N'')`, which are the manuscript's `G_1`, `G_2` by (eqSplit). The
hypotheses of the lemma (`s ≥ 1`, `τ ≥ 128 s log² n_0`) are not part of the predicate; `s` is a
natural number ("`s ≥ 1` an integer"). -/
def IsTauRun (ε : ℝ) (s : ℕ) (τ : ℝ) (t : STree V) (H : FGraph V) : Prop :=
  t.WF H ∧ t.StopsAt H (fun Q => Q.IsExpander ε s) ∧
    ∀ a ∈ t.internalAddrs, ∃ (U : Finset V) (F : Finset (Sym2 V)),
      IsWitness (t.graphAtD H a) ε s U F ∧
        t.labelAt a = some (tauU1 (t.graphAtD H a) U (witN (t.graphAtD H a) U F) τ,
          tauN2 (t.graphAtD H a) U (witN (t.graphAtD H a) U F) τ)

end STree

/-- [s2:lemOVgeneric] "put `c_OV := log₂(4/3)`". -/
noncomputable def cOV : ℝ := Real.logb 2 (4 / 3)

end EG.HB
