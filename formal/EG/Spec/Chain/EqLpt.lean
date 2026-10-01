module

public import EG.Defs.Chain.EqLpt
public import Mathlib.Order.Monotone.Defs

/-!
# Statement of Lemma EQ-LPT (manuscript s6:lemEQLPT)

Statement file of probe unit P2E (probe P-2, part 1; design note `formal/work/p2b/P2E.md`).

Manuscript v6.1, Lemma EQ-LPT [s6:lemEQLPT]:
"Let `Φ_1 ≥ Φ_2 ≥ … ≥ Φ_m ≥ 0` be loads of `m` items, and let `1 ≤ k ≤ m`. Place the items in
the order `1, 2, …, m` into `k` initially empty layers. Each item goes to a layer of currently
minimum load, and to an empty layer whenever one exists ("greedy longest-processing-time
placement"). Then all `k` layers are non-empty, and the final layer loads satisfy
`max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`."
Proof, first sentence: "An empty layer has load `0`, which is minimum. So the rule is
consistent, ..."

Formal reading (Defs `EG.Defs.Chain.EqLpt`, blueprint note EQ-GREEDY-RELATION):
* items and layers are `Fin m`, `Fin k` (0-based, `Φ_1` is `Φ ⟨0, _⟩`), loads are real;
* the placement rule is non-deterministic, so "greedy placement" is the relation
  `EG.Chain.IsGreedyLPT Φ σ`; `EqLptStatement` is the lemma for **every** greedy placement;
* `EqLptExistsStatement` is the consistency of the rule ("So the rule is consistent"): a greedy
  placement exists (JS-LC Step 4/5 "layer them by that lemma" needs it). It carries the lemma's
  hypotheses unchanged;
* "all `k` layers are non-empty" is surjectivity of `σ`; "`max_j − min_j ≤ Φ_1`" is
  `Φ^lay_j − Φ^lay_{j'} ≤ Φ_1` for all layers `j, j'` (equivalent since `k ≥ 1`).
-/

@[expose] public section

namespace EG.Spec

open EG.Chain

/-- [s6:lemEQLPT] (consistency of the rule, proof of the lemma) "Let `Φ_1 ≥ Φ_2 ≥ … ≥ Φ_m ≥ 0`
be loads of `m` items, and let `1 ≤ k ≤ m`. Place the items in the order `1, 2, …, m` into `k`
initially empty layers. Each item goes to a layer of currently minimum load, and to an empty
layer whenever one exists ... An empty layer has load `0`, which is minimum. So the rule is
consistent": a greedy placement exists. -/
def EqLptExistsStatement : Prop :=
  ∀ (m k : ℕ) (Φ : Fin m → ℝ), 1 ≤ k → k ≤ m → Antitone Φ → (∀ i, 0 ≤ Φ i) →
    ∃ σ : Fin m → Fin k, IsGreedyLPT Φ σ

/-- [s6:lemEQLPT] "Let `Φ_1 ≥ Φ_2 ≥ … ≥ Φ_m ≥ 0` be loads of `m` items, and let `1 ≤ k ≤ m`.
Place the items in the order `1, 2, …, m` into `k` initially empty layers. Each item goes to a
layer of currently minimum load, and to an empty layer whenever one exists ("greedy
longest-processing-time placement"). Then all `k` layers are non-empty, and the final layer
loads satisfy `max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`."

For every greedy placement `σ` (`IsGreedyLPT Φ σ`): `σ` is onto the `k` layers, and any two final
layer loads differ by at most `Φ_1 = Φ ⟨0, _⟩`. -/
def EqLptStatement : Prop :=
  ∀ (m k : ℕ) (Φ : Fin m → ℝ) (hk : 1 ≤ k) (hkm : k ≤ m), Antitone Φ → (∀ i, 0 ≤ Φ i) →
    ∀ σ : Fin m → Fin k, IsGreedyLPT Φ σ →
      Function.Surjective σ ∧
      ∀ j j' : Fin k, layerLoad Φ σ j - layerLoad Φ σ j' ≤ Φ ⟨0, by omega⟩

end EG.Spec
