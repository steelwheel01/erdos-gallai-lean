module

public import EG.Defs.Expander
public import EG.Defs.Objects

/-!
# Statement of Bucić–Montgomery Lemma 25, explicit form (manuscript s1:citLem25)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Ext/BMLemma25.lean` proves it (at
present with `sorry`: the proof is a later task).

Manuscript, Cited result [s1:citLem25] ("[BM, Lemma 25], explicit form"):
"Let `ε ≥ 2^{-5}` and `m ≥ 2^{30}/ε²` (so `m ≥ 2^{40}` suffices at `ε = 2^{-5}`). Every
`m`-vertex `(ε,0)`-expander contains a cycle of length at least `ε² m / (18 log⁴ m)`."

Formal reading.
* "`m`-vertex `(ε,0)`-expander": `G : EG.FGraph V` with `m = |G| = G.card` and
  `G.IsExpander ε 0` (Definition 11, [s1:citDef11], `log = log₂`); `ε : ℝ`.
* "a cycle of length `ℓ`": a vertex list `c` that is a well-formed cycle object
  (`(EG.Obj.cycle c).WF`: no repeated vertex and at least three vertices, [s1:defObject]) all of
  whose edges `EG.cycleEdges c` (including the closing edge) are edges of `G`; its length is its
  number of edges, which is `c.length` (`cycleEdges c` has `c.length` entries). Its vertices are
  then vertices of `G` automatically (`FGraph.edge_verts`).
* `log⁴ m = (Real.logb 2 m)^4`; the bound is compared in `ℝ`.
* **Added hypothesis `2 ≤ m`.** The bound `ε² m / (18 log⁴ m)` is undefined for `m = 1`
  (`log 1 = 0`). Read literally in Lean (where `x / 0 = 0`), the statement without this
  hypothesis is false: for `ε = 2^{15}` one has `2^{30}/ε² = 1`, every one-vertex graph is an
  `(ε,0)`-expander (Definition 11 is vacuous, as no `U` has `1 ≤ |U| ≤ 2/3`), and a one-vertex
  graph contains no cycle. (`EG.bmLemma25_literal_false` in `EG/Proof/Ext/BMLemma25.lean` proves
  this.) For `m = 0` the hypothesis `m ≥ 2^{30}/ε²` already fails, and for `m ≥ 2` the bound is
  defined (`log m > 0`), so `m = 1` is the only degenerate case. The only use, [s2:lemCap] (ii),
  has `ε = 2^{-5}` and `m ≥ 2^{40}`. Class T0 (encoding) deviation (PLAN §7), entry
  **T0-cap-1** in `formal/work/p1b/cap.md` (for the central T0 record); proposed manuscript
  wording for [s1:citLem25]: "Let `ε ≥ 2^{-5}` and `m ≥ max(2, 2^{30}/ε²)`".
-/

@[expose] public section


namespace EG.Spec

universe u

/-- [s1:citLem25] "Let `ε ≥ 2^{-5}` and `m ≥ 2^{30}/ε²` (so `m ≥ 2^{40}` suffices at
`ε = 2^{-5}`). Every `m`-vertex `(ε,0)`-expander contains a cycle of length at least
`ε² m / (18 log⁴ m)`." Here `m = G.card`, `log = log₂`, a cycle is a well-formed cycle object with
all edges in `E(G)` and its length is `c.length`; the hypothesis `2 ≤ m` makes the bound defined
(see the module docstring). -/
def BMLemma25Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε : ℝ),
    (2 : ℝ) ^ (-5 : ℤ) ≤ ε → (2 : ℝ) ^ 30 / ε ^ 2 ≤ (G.card : ℝ) → 2 ≤ G.card →
    G.IsExpander ε 0 →
    ∃ c : List V, (EG.Obj.cycle c).WF ∧ (∀ e ∈ EG.cycleEdges c, e ∈ G.edges) ∧
      ε ^ 2 * (G.card : ℝ) / (18 * Real.logb 2 (G.card : ℝ) ^ 4) ≤ (c.length : ℝ)

end EG.Spec
