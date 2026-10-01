module

public import EG.Defs.Chain.Cluster

/-!
# Statement of Lemma MED (manuscript s6:lemMED)

Statement file of probe unit P2E (probe P-2, part 1; design note `formal/work/p2b/P2E.md`).

Manuscript v6.1, Lemma MED [s6:lemMED]:
"Let `𝒦` be a parity-clean cluster and `≺` a linear order on `U_𝒦`.
(a) `MED(≺)` is an admissible orientation. There is a function `pot : A_𝒦 ∪ U_𝒦 → (0,1)` that
strictly increases along every arc of `MED(≺)`.
(b) For every admissible orientation of `𝒦`, in particular for `MED(≺)`, and every port `u`:
`|exc(u)| ≤ deg_{B_𝒦}(u)` and `exc(u) ≡ deg_{B_𝒦}(u) (mod 2)`. Moreover `∑_{u∈U_𝒦} exc(u) = 0`
and `Φ(𝒦) ≤ b(𝒦)`."

Formal reading (Defs `EG.Defs.Chain.Cluster`, design note `formal/work/p2d/chain.md`):
* the linear order `≺` on `U_𝒦` is a rank `rk : V → ℕ` injective on `U_𝒦` (`u ≺ v` iff
  `rk u < rk v`); every linear order of the finite set `U_𝒦` is of this form, and `medOrient rk`
  depends on `rk` only through these comparisons;
* `MedStatement` is (a), for the concrete median orientation `K.medOrient rk`;
* `MedExcStatement` is (b), for every admissible orientation `O` (not only `MED(≺)`); the
  lemma's standing hypothesis "parity-clean" is kept (it is implied by admissibility,
  `EG.Chain.Cluster.IsAdmissible.parityClean`, so this is no restriction);
* `exc(u) ∈ ℤ` is `EG.Chain.exc O u`; `Φ(𝒦)` is `K.load O ∈ ℕ` and `b(𝒦)` is the real number
  `K.beadCount`.
-/

@[expose] public section

namespace EG.Spec

open EG.Chain

universe u

/-- [s6:lemMED] (a) "Let `𝒦` be a parity-clean cluster and `≺` a linear order on `U_𝒦`.
(a) `MED(≺)` is an admissible orientation. There is a function `pot : A_𝒦 ∪ U_𝒦 → (0,1)` that
strictly increases along every arc of `MED(≺)`."

`≺` is given by `rk`, injective on the ports; `pot` is a real function whose values on
`V(𝒦) = A_𝒦 ∪ U_𝒦` lie in `(0,1)` (all arcs of `medOrient` have both ends in `V(𝒦)`). -/
def MedStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (K : Cluster V) (rk : V → ℕ),
    K.ParityClean → Set.InjOn rk (K.ports : Set V) →
      K.IsAdmissible (K.medOrient rk) ∧
      ∃ pot : V → ℝ, (∀ v ∈ K.verts, 0 < pot v ∧ pot v < 1) ∧
        ∀ a ∈ K.medOrient rk, pot a.1 < pot a.2

/-- [s6:lemMED] (b) "Let `𝒦` be a parity-clean cluster ... (b) For every admissible orientation
of `𝒦`, in particular for `MED(≺)`, and every port `u`: `|exc(u)| ≤ deg_{B_𝒦}(u)` and
`exc(u) ≡ deg_{B_𝒦}(u) (mod 2)`. Moreover `∑_{u∈U_𝒦} exc(u) = 0` and `Φ(𝒦) ≤ b(𝒦)`."

Congruence mod 2 in `ℤ` is `Even (exc(u) − deg(u))`. -/
def MedExcStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (K : Cluster V) (O : Finset (V × V)),
    K.ParityClean → K.IsAdmissible O →
      (∀ u ∈ K.ports, |exc O u| ≤ (degE K.beads u : ℤ) ∧ Even (exc O u - (degE K.beads u : ℤ))) ∧
      (∑ u ∈ K.ports, exc O u = 0) ∧
      ((K.load O : ℕ) : ℝ) ≤ K.beadCount

end EG.Spec
