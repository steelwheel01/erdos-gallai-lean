module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Statement of Haxell's condition for matchability (manuscript s1:citHaxell)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Ext/Haxell.lean` proves both
statements below (Haxell's alternating-tree argument, as written out in s1.tex after
[s1:citHaxell]).

Manuscript, Cited result [s1:citHaxell] ("Haxell's condition for matchability [Hax95]"):
"Let `q ≥ 1` be an integer, and let `𝓗` be a hypergraph (a set of subsets, called edges, of a
finite vertex set) whose vertex set is the disjoint union of two sets `𝓧` and `𝓨`, such that
every edge `e` satisfies `|e ∩ 𝓧| = 1` and `|e ∩ 𝓨| ≤ q`. Suppose that for every `𝓧' ⊆ 𝓧` and
every `Z ⊆ 𝓨` with `|Z| ≤ (2q-1)(|𝓧'|-1)` there is an edge `e` of `𝓗` with `e ∩ 𝓧 ⊆ 𝓧'` and
`e ∩ Z = ∅`. Then `𝓗` has an `𝓧`-saturating matching, i.e. a set of pairwise disjoint edges
such that every vertex of `𝓧` lies in one of them."

Two statements.
* `EG.Spec.HaxellStatedForm`: the stated form, literally (the bound `(2q-1)(|𝓧'|-1)` is compared
  in `ℤ`, so that for `𝓧' = ∅` it is negative and no `Z` qualifies, as the manuscript remarks).
* `EG.Spec.HaxellStatement` (**the locked form**, TRIAGE HAX-TRUTH / L9-HAXELL-FORM): the
  `q²`-form, in which the hypothesis is required only for nonempty `𝓧'` and for every `Z` with
  `|Z| < q²|𝓧'|`. This is exactly what the only application, the claim in the proof of
  [s3:lemL9rho], verifies ("The claim covers every `Z` with `|Z| < h²|I|`"). Relation: for
  nonempty `𝓧'`, `(2q-1)(|𝓧'|-1) < q²|𝓧'|` (as `q² - (2q-1) = (q-1)² ≥ 0`), so the hypothesis of
  the `q²`-form implies that of the stated form, and the stated form implies the `q²`-form
  (`EG.haxellStatement_of_statedForm`). Neither statement depends on the factor `2q-1` being
  checked against [Hax95]: both are proved in `EG/Proof/Ext/Haxell.lean`.

Formal reading.
* The vertex set is a type `α` with decidable equality; `𝓧`, `𝓨` are `X Y : Finset α` with
  `Disjoint X Y`; the hypergraph is `H : Finset (Finset α)` (a set of edges) with every edge a
  subset of `X ∪ Y` ("whose vertex set is the disjoint union of `𝓧` and `𝓨`").
* "`e ∩ Z = ∅`" is written `Disjoint e Z`.
* A matching is `M ⊆ H` whose edges are pairwise disjoint (`Set.PairwiseDisjoint id`);
  `𝓧`-saturating: every `a ∈ X` lies in some edge of `M`.
* `q : ℕ` with `1 ≤ q`. The universe of `α` is a parameter (TRIAGE §2.5).
-/

@[expose] public section


namespace EG.Spec

universe u

/-- [s1:citHaxell] The stated form: "Let `q ≥ 1` be an integer, and let `𝓗` be a hypergraph (a
set of subsets, called edges, of a finite vertex set) whose vertex set is the disjoint union of
two sets `𝓧` and `𝓨`, such that every edge `e` satisfies `|e ∩ 𝓧| = 1` and `|e ∩ 𝓨| ≤ q`.
Suppose that for every `𝓧' ⊆ 𝓧` and every `Z ⊆ 𝓨` with `|Z| ≤ (2q-1)(|𝓧'|-1)` there is an edge
`e` of `𝓗` with `e ∩ 𝓧 ⊆ 𝓧'` and `e ∩ Z = ∅`. Then `𝓗` has an `𝓧`-saturating matching, i.e. a
set of pairwise disjoint edges such that every vertex of `𝓧` lies in one of them." The bound is
compared in `ℤ` (negative for `𝓧' = ∅`). -/
def HaxellStatedForm : Prop :=
  ∀ (α : Type u) [DecidableEq α] (X Y : Finset α) (q : ℕ) (H : Finset (Finset α)),
    1 ≤ q → Disjoint X Y →
    (∀ e ∈ H, e ⊆ X ∪ Y) →
    (∀ e ∈ H, (e ∩ X).card = 1) →
    (∀ e ∈ H, (e ∩ Y).card ≤ q) →
    (∀ X' ⊆ X, ∀ Z ⊆ Y, (Z.card : ℤ) ≤ (2 * (q : ℤ) - 1) * ((X'.card : ℤ) - 1) →
      ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z) →
    ∃ M ⊆ H, (M : Set (Finset α)).PairwiseDisjoint id ∧ ∀ a ∈ X, ∃ e ∈ M, a ∈ e

/-- [s1:citHaxell] Haxell's condition for matchability, in the `q²`-form used by
[s3:lemL9rho] (the locked stage-α form): for `q ≥ 1` and a hypergraph `H` on `X ⊔ Y` whose
edges meet `X` in exactly one vertex and `Y` in at most `q` vertices, if for every nonempty
`X' ⊆ X` and every `Z ⊆ Y` with `|Z| < q²|X'|` there is an edge `e` with `e ∩ X ⊆ X'` and
`e ∩ Z = ∅`, then `H` has an `X`-saturating matching. It is a consequence of the stated form
`HaxellStatedForm` (see the module docstring). -/
def HaxellStatement : Prop :=
  ∀ (α : Type u) [DecidableEq α] (X Y : Finset α) (q : ℕ) (H : Finset (Finset α)),
    1 ≤ q → Disjoint X Y →
    (∀ e ∈ H, e ⊆ X ∪ Y) →
    (∀ e ∈ H, (e ∩ X).card = 1) →
    (∀ e ∈ H, (e ∩ Y).card ≤ q) →
    (∀ X' ⊆ X, X'.Nonempty → ∀ Z ⊆ Y, Z.card < q ^ 2 * X'.card →
      ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z) →
    ∃ M ⊆ H, (M : Set (Finset α)).PairwiseDisjoint id ∧ ∀ a ∈ X, ∃ e ∈ M, a ∈ e

end EG.Spec
