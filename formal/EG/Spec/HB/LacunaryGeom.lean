module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Statement of Lemma "tower-lacunary sums", part (i) (manuscript s2:lemLacunary (i)) — declared
input of unit P3B

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). This statement is a DECLARED INPUT of
the probe: the tower sums of Theorems [s6:thmCONC] (iii) and [s6:thmCONCL] (iv) apply it ("By
(s6:eqTowerHalf) and Lemma [s2:lemLacunary](i), `Σ_r 𝖺(d_r) ≤ 2𝖺(d_R)`"); the stub is
`EG.lacunaryGeom` in `EG/Proof/HB/LacunaryGeom.lean`. Justification: design note
`formal/work/p2b/P3B.md`, "Declared inputs" (owner: the s2 lacunary unit; the statement is cheap and
P3B can discharge it in stage 2 if the orchestrator assigns it). The full Spec of [s2:lemLacunary]
(blueprint s2b `LacunaryGeomStatement`, `LacunarySeqStatement`, …) must import this file for (i).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemLacunary]:
"(i) If `X_1, …, X_R ≥ 0` and `X_r ≤ X_{r+1}/2` for all `r < R`, then `Σ_{r ≤ R} X_r ≤ 2X_R` and
`Σ_{r ≤ R} (R-r+1) X_r ≤ 4X_R`."

Formal reading.
* A real sequence `X : ℕ → ℝ` read at the indices `1, …, R` (`Finset.Icc 1 R`); "for all
  `r < R`" is `r ∈ Finset.Ico 1 R`. `R ≥ 1` is implicit in "`X_1, …, X_R`" and is a hypothesis
  (for `R = 0` the conclusion would read `0 ≤ 2X_0` about an unconstrained `X_0`; blueprint s2b
  lean_shape). The weight `R - r + 1` is a natural number (`r ≤ R`, exact) cast to `ℝ`.
* No hypothesis on `D_*` (part (i) is pure arithmetic).
-/

@[expose] public section

namespace EG.Spec

/-- [s2:lemLacunary] (i) "If `X_1, …, X_R ≥ 0` and `X_r ≤ X_{r+1}/2` for all `r < R`, then
`Σ_{r ≤ R} X_r ≤ 2X_R` and `Σ_{r ≤ R} (R-r+1) X_r ≤ 4X_R`." -/
def LacunaryGeomStatement : Prop :=
  ∀ (X : ℕ → ℝ) (R : ℕ), 1 ≤ R → (∀ r ∈ Finset.Icc 1 R, 0 ≤ X r) →
    (∀ r ∈ Finset.Ico 1 R, X r ≤ X (r + 1) / 2) →
    ∑ r ∈ Finset.Icc 1 R, X r ≤ 2 * X R ∧
      ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * X r ≤ 4 * X R

end EG.Spec
