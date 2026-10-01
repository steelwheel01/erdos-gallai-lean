module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Fin

/-!
# Greedy longest-processing-time placement (manuscript s6:lemEQLPT)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Lemma [s6:lemEQLPT] (EQ-LPT): "Let `Φ_1 ≥ Φ_2 ≥ … ≥ Φ_m ≥ 0` be loads of `m`
items, and let `1 ≤ k ≤ m`. Place the items in the order `1, 2, …, m` into `k` initially empty
layers. Each item goes to a layer of currently minimum load, and to an empty layer whenever one
exists ("greedy longest-processing-time placement"). Then all `k` layers are non-empty, and the
final layer loads satisfy `max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`."

The placement rule is non-deterministic (ties are arbitrary). It is therefore a *relation*
`EG.Chain.IsGreedyLPT Φ σ` between the loads `Φ : Fin m → ℝ` and a placement
`σ : Fin m → Fin k` (item `i` goes to layer `σ i`); the lemma is about every placement satisfying
it (blueprint note EQ-GREEDY-RELATION). Items `1..m` and layers `1..k` are `Fin m`, `Fin k`
(0-based: `Φ_1` is `Φ 0`). Loads are real numbers, as in the manuscript (at every use they are
natural numbers; they are then cast).
-/

@[expose] public section

namespace EG.Chain

/-- [s6:lemEQLPT] The load of layer `j` just before item `i` is placed: `∑_{i' < i, σ(i') = j} Φ_{i'}`
(items are placed in the order `0, 1, …, m-1`). -/
def loadBefore {m k : ℕ} (Φ : Fin m → ℝ) (σ : Fin m → Fin k) (i : Fin m) (j : Fin k) : ℝ :=
  ∑ i' ∈ Finset.univ.filter (fun i' => i' < i ∧ σ i' = j), Φ i'

/-- [s6:lemEQLPT] Layer `j` is empty just before item `i` is placed: no earlier item went to `j`. -/
def EmptyBefore {m k : ℕ} (σ : Fin m → Fin k) (i : Fin m) (j : Fin k) : Prop :=
  ∀ i', i' < i → σ i' ≠ j

/-- [s6:lemEQLPT] "Place the items in the order `1, 2, …, m` into `k` initially empty layers.
Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists
("greedy longest-processing-time placement")."

`IsGreedyLPT Φ σ`: for every item `i`,
* (G1) the layer `σ i` has minimum load among all layers just before `i` is placed, and
* (G2) if some layer is empty just before `i` is placed, then `σ i` is such a layer. -/
def IsGreedyLPT {m k : ℕ} (Φ : Fin m → ℝ) (σ : Fin m → Fin k) : Prop :=
  ∀ i : Fin m,
    (∀ j : Fin k, loadBefore Φ σ i (σ i) ≤ loadBefore Φ σ i j) ∧
    ((∃ j : Fin k, EmptyBefore σ i j) → EmptyBefore σ i (σ i))

/-- [s6:lemEQLPT] "the final layer loads" `Φ^lay_j := ∑_{σ(i) = j} Φ_i`. -/
def layerLoad {m k : ℕ} (Φ : Fin m → ℝ) (σ : Fin m → Fin k) (j : Fin k) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => σ i = j), Φ i

end EG.Chain
