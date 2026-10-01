module

public import EG.Defs.HB.SplitTree
public import EG.Defs.Constants

/-!
# Statement of the thin-cut lemma (manuscript s2:lemThinCut)

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). Design note
`formal/work/p2b/P3A.md`. Definitions: `EG/Defs/HB/SplitTree.lean` (locked).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemThinCut]:
"Let `τ > 0` and consider a split recursion (Lemma [s2:lemSEP]) in which every split is produced
by the `τ`-rules at threshold `τ`: at each non-leaf node `ν` there are `s_ν < τ` and a witness at
`H_ν` (with parameter `s_ν`) whose `τ`-rules (Definition [s2:defTauRules]) give `U'_ν` and
`N''_ν`. Then for every leaf `Leaf` and every vertex `h`,
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1`,
which is `τ - 1` when `τ` is an integer (as in all applications), and this number is `0` if
`h ∈ V(Leaf)`. Moreover, if `u ∉ Dup` then every edge at `u` is either deleted or an edge of the
unique leaf containing `u`."

Formal reading.
* The hypothesis on the recursion is `t.IsTauSplitTree epsC τ H` (the Def quotes it; `ε = 2^{-5}`
  is the witness parameter of s2).
* "the deleted edges `hu` with `u ∈ V(Leaf) \ Dup`" is the set of deleted edges `e` of the form
  `s(h, u)` with `u ∈ V(H_L) \ Dup`; the count is its cardinality. `⌈τ⌉ - 1` is computed in `ℤ`
  (`Int.ceil`). "which is `τ - 1` when `τ` is an integer" is the conjunct for `τ = k`, `k : ℕ`
  (then `k ≥ 1`, and `k - 1` is the natural-number difference).
* "every vertex `h`" ranges over all of `V` (blueprint THIN-H-ANY).
* "the unique leaf containing `u`": the leaf `L` with `u ∈ V(H_L)`, stated with its uniqueness.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemThinCut] (main part) "for every leaf `Leaf` and every vertex `h`,
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1`, which is `τ - 1` when `τ` is an integer (as
in all applications), and this number is `0` if `h ∈ V(Leaf)`." (Hypotheses: `τ > 0`, every
split produced by the `τ`-rules at threshold `τ`.) -/
def ThinCutStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V) (τ : ℝ), 0 < τ →
    t.IsTauSplitTree epsC τ H →
    ∀ L ∈ t.leafAddrs, ∀ h : V,
      (((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H, e = s(h, u))).card
          : ℤ) ≤ ⌈τ⌉ - 1 ∧
      (∀ k : ℕ, τ = k →
        ((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
          e = s(h, u))).card ≤ k - 1) ∧
      (h ∈ (t.graphAtD H L).verts →
        ((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
          e = s(h, u))).card = 0)

/-- [s2:lemThinCut] (Moreover) "if `u ∉ Dup` then every edge at `u` is either deleted or an edge
of the unique leaf containing `u`." (Same hypotheses as the lemma; `e` ranges over `E(H_0)`.) -/
def ThinCutEdgeStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V) (τ : ℝ), 0 < τ →
    t.IsTauSplitTree epsC τ H →
    ∀ u : V, u ∉ t.dup H → ∀ e ∈ H.edges, u ∈ e →
      e ∈ t.deleted H ∨
        ∃ L ∈ t.leafAddrs, u ∈ (t.graphAtD H L).verts ∧ e ∈ (t.graphAtD H L).edges ∧
          ∀ L' ∈ t.leafAddrs, u ∈ (t.graphAtD H L').verts → L' = L

end EG.Spec
