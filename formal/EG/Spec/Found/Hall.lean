module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Function.Basic

/-!
# Statement of Hall's theorem (manuscript s1:citHall)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:citHall`). No proof here. The blueprint notes that
Mathlib proves it (`Finset.all_card_le_biUnion_card_iff_exists_injective`,
`Mathlib/Combinatorics/Hall/Basic.lean`), so this is not a trusted input; the statement records
the manuscript's wording for the consumers s3:lemHB, s7:lemWellDef (iii) and s7:consRound (f).

Manuscript v6.1, `s1.tex`, Cited result [s1:citHall] (Hall's theorem [Hal35]):
"Let `𝒥` be a finite set and, for every `a ∈ 𝒥`, let `𝒯(a)` be a finite set. If
`|⋃_{a ∈ 𝒥'} 𝒯(a)| ≥ |𝒥'|` for every `𝒥' ⊆ 𝒥`, then there is an injective map `χ` from `𝒥` to
`⋃_{a ∈ 𝒥} 𝒯(a)` with `χ(a) ∈ 𝒯(a)` for every `a ∈ 𝒥` (a system of distinct representatives)."

Formal reading.
* `𝒥 = J : Finset ι`, `𝒯 = T : ι → Finset α` (only its values on `J` matter);
  `⋃_{a ∈ 𝒥'} 𝒯(a) = J'.biUnion T`.
* "an injective map `χ` from `𝒥` to `⋃_{a ∈ 𝒥} 𝒯(a)` with `χ(a) ∈ 𝒯(a)`": an injective
  function `χ : ↥J → α` on the elements of `J` with `χ a ∈ T a` (then `χ` maps `J` into the
  union automatically). The domain is the subtype `↥J`, not `ι`: a function `ι → α` need not
  exist (for `J = ∅`, `α` empty and `ι` nonempty), so that form would be false.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s1:citHall] "Let `𝒥` be a finite set and, for every `a ∈ 𝒥`, let `𝒯(a)` be a finite set. If
`|⋃_{a ∈ 𝒥'} 𝒯(a)| ≥ |𝒥'|` for every `𝒥' ⊆ 𝒥`, then there is an injective map `χ` from `𝒥` to
`⋃_{a ∈ 𝒥} 𝒯(a)` with `χ(a) ∈ 𝒯(a)` for every `a ∈ 𝒥`." -/
def HallStatement : Prop :=
  ∀ (ι : Type u) (α : Type v) [DecidableEq α] (J : Finset ι) (T : ι → Finset α),
    (∀ J' ⊆ J, J'.card ≤ (J'.biUnion T).card) →
      ∃ χ : J → α, Function.Injective χ ∧ ∀ a : J, χ a ∈ T a

end EG.Spec
