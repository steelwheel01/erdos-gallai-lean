# [haxell] Haxell's condition for matchability (s1:citHaxell)

Status: both files compile with 0 errors, 0 warnings and no `sorry`. `lake build EG.Proof.Ext.Haxell` succeeds.
`python3 scripts/lint.py` reports 0 findings. The axiom scan (`--prefix EG EG.Proof.Ext.Haxell`) covers 114 constants
and finds 0 `sorryAx` and 0 violations.

## Files
| File | Contents |
|---|---|
| `EG/Spec/Ext/Haxell.lean` (83 lines) | `EG.Spec.HaxellStatedForm` (the literal stated form, factor `2q-1`, bound compared in `ℤ`); `EG.Spec.HaxellStatement` (**the form to lock**: the `q²`-form) |
| `EG/Proof/Ext/Haxell.lean` (664 lines) | `EG.haxell_stated : HaxellStatedForm`, `EG.haxellStatement_of_statedForm`, `EG.haxell : HaxellStatement`, and the internal development in `EG.Haxell.*` |

The root files are not edited. The orchestrator must add the modules `EG.Spec.Ext.Haxell` and `EG.Proof.Ext.Haxell` to the roots.

## Statements (both universe-polymorphic, `α : Type u`, `[DecidableEq α]`)
Shared data: `X Y : Finset α`, `q : ℕ`, `H : Finset (Finset α)`, with `1 ≤ q`, `Disjoint X Y`, `∀ e ∈ H, e ⊆ X ∪ Y`,
`∀ e ∈ H, (e ∩ X).card = 1` and `∀ e ∈ H, (e ∩ Y).card ≤ q`.
Conclusion: `∃ M ⊆ H, (M : Set (Finset α)).PairwiseDisjoint id ∧ ∀ a ∈ X, ∃ e ∈ M, a ∈ e`.
- `HaxellStatedForm` has the hypothesis `∀ X' ⊆ X, ∀ Z ⊆ Y, (|Z| : ℤ) ≤ (2q-1)(|X'|-1) → ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z`.
  It uses `ℤ`, so `X' = ∅` is vacuous, as the manuscript remarks. This avoids the ℕ-subtraction trap HAX-NATSUB.
- `HaxellStatement` has the hypothesis `∀ X' ⊆ X, X'.Nonempty → ∀ Z ⊆ Y, |Z| < q²|X'| → ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z`.
  This is exactly what the claim in s3:lemL9rho supplies (with `q = h`, `X = [r]`, `Y = E(G)`).
- Relation: the stated form implies the `q²`-form (`EG.haxellStatement_of_statedForm`). For nonempty `X'`,
  `(2q-1)(|X'|-1) < q²|X'|`, because `q² - (2q-1) = (q-1)² ≥ 0`.
- Faithfulness: the vertex set is `X ⊔ Y`, so edges are subsets of `X ∪ Y`. "`e ∩ Z = ∅`" is written `Disjoint e Z`.
  A matching is a pairwise-disjoint subfamily. The hypothesis `e ⊆ X ∪ Y` is needed: without it, two edges could
  share a vertex outside `X ∪ Y`.

## Proof (follows "Proof of the stated form" in s1.tex; no gap found)
- **Induction on `|X|`** (`EG.Haxell.haxell_nat`, in ℕ with nonempty `X'`). Remove `a₀`, and restrict to the edges
  avoiding `a₀`. The induction hypothesis gives a good `M₀`.
- **Configurations** are the lists `[x_k, …, x₁]` (newest first). `𝓢_i` is not stored: it is computed as
  `S Y M x = {m ∈ M | (m ∩ x ∩ Y).Nonempty}`, which is (C2). `Xc`, `Zc` and `Valid` encode `𝓧^{(i)}`, `Z^{(i)}`, (C1) and
  `𝓢_i ≠ ∅`. "`a(x) ∈ 𝓧^{(i-1)}`" is written `x ∩ X ⊆ 𝓧^{(i-1)}`.
- **Counting** (`count`) has two parts:
  - `|Z| + (2q-1) ≤ (2q-1)|𝓧|` and `length + 1 ≤ |𝓧|`;
  - the key invariant `inv_J`: if `a(m) ∈ 𝓧^{(k)}` for `m ∈ M`, then `m ∩ Y ⊆ Z^{(k)}`. This gives the disjointness of
    the `𝓢_i` and the injectivity used in `|𝓧^{(k)}| - 1 = Σ|𝓢_i|`.

  `(*)` is `star`.
- **Swap step** (`swap`): strong induction on the configuration length. The recursion on `𝓢_i = {m}` is the
  manuscript's "repeat the swap step".
- **Termination.** The moves are not iterated. Instead, `augment` argues by contradiction:
  - Choose a good `M` and a configuration whose *key* is lexicographically maximal. The key is the signature, oldest
    first, with each entry `s` replaced by `|H| - s ∈ Fin (|H|+1)`.
  - A maximal key exists because keys have length ≤ `|X|` (`List.finite_length_le`, `Set.exists_max_image`).
  - Extending the configuration increases the key. The swap result `(s₁,…,s_{i-1},s_i-1)` has a key larger than every
    extension of `(s₁,…,s_i)`.

  This is the manuscript's `σ∞ <lex τ∞` order, reversed.

## Manuscript findings
- The written proof of the stated form is complete; each step is formalized as written.
- The factor `2q-1` is what the proof yields; the `[Hax95]` citation is no longer needed for this project.
  The TRIAGE item HAX-TRUTH can be closed: the stage-α hypothesis `HaxellStatement` is now a theorem (`EG.haxell`).
