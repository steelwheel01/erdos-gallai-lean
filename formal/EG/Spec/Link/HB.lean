module

public import EG.Defs.Expander
public import EG.Defs.Link.HBFamily

/-!
# Statement of Lemma HB (candidate sets of bounded multiplicity; manuscript s3:lemHB)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3b (`formal/work/p2s/s3b.md`; blueprint
`formal/work/p2/blueprint_s3b.md`, node `s3:lemHB`). No proof here (blueprint: one application of
Mathlib's Hall theorem, `Finset.all_card_le_biUnion_card_iff_exists_injective`).

Manuscript v6.1, `s3.tex`, Lemma [s3:lemHB]:
"Let `X` be an `N`-vertex `(ε′,s)`-expander with `N ≥ 2` and `2^{-7} ≤ ε′ ≤ 1`, and put
`L := log N`. Let `m` be an integer with `1 ≤ m` and `2m ≤ s`, and put `b := ⌈2mL^2/ε′⌉`.
Thus `b = ⌈64L^2m⌉`, `⌈128L^2m⌉` or `⌈256L^2m⌉` at `ε′ = 2^{-5}`, `2^{-6}` or `2^{-7}`.
Then every vertex `w` has a set `A(w) ⊆ N_X(w)` with `|A(w)| = m`, such that every vertex of `X`
lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`."

Formal reading.
* `X : FGraph V`, `N = X.card`, `L = log₂ N`; `X.IsExpander ε' s` (s1:citDef11); `ε' s : ℝ`.
* "`m` an integer with `1 ≤ m`": `m : ℕ` with `1 ≤ m`; "`2m ≤ s`" is a real inequality.
* `b := ⌈2mL^2/ε′⌉` is `⌈2 m L^2 / ε'⌉₊` (the argument is positive, so this is the integer
  ceiling); the sentence "Thus `b = …`" only evaluates `b` and is not part of the statement.
* The conclusion is the shared predicate `EG.IsHBFamily X m b A` (`EG/Defs/Link/HBFamily.lean`,
  TRIAGE §2.8 HB-FAMILY), also read by the PV hypothesis (1) of s4:lemPV and by `A_Y` of
  s5:defStages: `A w ⊆ N_X(w) = X.nbrs w` and `|A w| = m` for `w ∈ V(X)`, and every vertex `u`
  lies in `A w` for at most `b` indices `w ∈ V(X)`. The family is a function `A : V → Finset V`
  (values outside `V(X)` are not read).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s3:lemHB] Lemma HB: "Let `X` be an `N`-vertex `(ε′,s)`-expander with `N ≥ 2` and
`2^{-7} ≤ ε′ ≤ 1`, and put `L := log N`. Let `m` be an integer with `1 ≤ m` and `2m ≤ s`, and put
`b := ⌈2mL^2/ε′⌉`. … Then every vertex `w` has a set `A(w) ⊆ N_X(w)` with `|A(w)| = m`, such that
every vertex of `X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`." -/
def HBStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (ε' s : ℝ) (m : ℕ),
    X.IsExpander ε' s → 2 ≤ X.card → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 →
    1 ≤ m → 2 * (m : ℝ) ≤ s →
    ∃ A : V → Finset V,
      IsHBFamily X m ⌈2 * (m : ℝ) * Real.logb 2 (X.card : ℝ) ^ 2 / ε'⌉₊ A

end EG.Spec
