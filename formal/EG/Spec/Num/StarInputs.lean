module

public import EG.Defs.Link.Star

/-!
# The numeric parts of (S2) and (S3) (manuscript s3:eqStar), used by Lemma 17*

Statement file (`EG/Spec/**`), unit NUM. The probe uses these facts in
`NumL17sCaseAExponentStatement` and `NumL17sCaseBExponentStatement` (`EG/Spec/Num/L17s.lean`).
Stage 1 declared them as inputs; fix round 1 (review I-1, `formal/work/p2b/NUM.md`) proves them in
`EG/Proof/Num/StarInputs.lean` from the definitions of `EG/Defs/Link/Star.lean` and the Lib API
`EG/Lib/Link/Star.lean` (Bernoulli's inequality for (S2), the ceiling bounds for (S3)), with the
real-arithmetic margins of (S3) stated separately in `NumStarS3MarginStatement`. The file name is
kept for stability.

They are conjuncts of the blueprint's `EG.Spec.StarFactsStatement` (blueprint s3a, node
`s3:eqStar`, file `EG/Spec/Link/Star.lean`, owned by the s3 unit and not yet written): the "S2
(numeric part)" conjunct `1/10 * ρ / ℓ_* ≤ p` and the "S3" conjunct. When that Spec exists, the
integrator should check that the texts agree (design note `formal/work/p2b/NUM.md`, hazard NUM-H1).

Manuscript v6.1, `s3.tex`, the facts after (eqStar):
"(S2) The number `p_*` exists, is unique, and satisfies `p_* ≥ 0.1ρ/ℓ_*`, so
`p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`. […]"
"(S3) `Δ_* ≤ 2p^{-2}+8.34p^{-1}+2.34`. Hence `Δ_* ≤ 3p^{-2}` if `p ≤ 0.11`, and
`Δ_* ≤ 13p^{-2}` for every `p ∈ (0,1]`." (with `p := p_*`)
The parameters are those of `EG/Defs/Link/Star.lean`; both facts depend only on `n` and `ρ`, and
the statements carry the domain hypotheses `n ≥ 2`, `0 < ρ ≤ 1` of (eqStar).
-/

@[expose] public section


namespace EG.Spec

/-- [s3:eqS2] (numeric part) "The number `p_*` exists, is unique, and satisfies
`p_* ≥ 0.1ρ/ℓ_*`, so `p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`." (Existence and uniqueness of the explicit
`EG.Star.p` are `EG.Star.p_spec` / `EG.Star.p_unique` in `EG/Lib/Link/Star.lean`; the union law
is the separate blueprint statement `StarUnionLawStatement`.) -/
def StarS2NumStatement : Prop :=
  ∀ (n : ℕ) (ρ : ℝ), 2 ≤ n → 0 < ρ → ρ ≤ 1 →
    0.1 * ρ / (Star.ell n : ℝ) ≤ Star.p n ρ ∧
    (Star.p n ρ)⁻¹ ^ 2 ≤ 100 * (Star.ell n : ℝ) ^ 2 * ρ⁻¹ ^ 2

/-- [s3:eqS3] "`Δ_* ≤ 2p^{-2}+8.34p^{-1}+2.34`. Hence `Δ_* ≤ 3p^{-2}` if `p ≤ 0.11`, and
`Δ_* ≤ 13p^{-2}` for every `p ∈ (0,1]`." (`p = p_*`.) -/
def StarS3Statement : Prop :=
  ∀ (n : ℕ) (ρ : ℝ), 2 ≤ n → 0 < ρ → ρ ≤ 1 →
    (Star.Delta n ρ : ℝ) ≤ 2 * (Star.p n ρ)⁻¹ ^ 2 + 8.34 * (Star.p n ρ)⁻¹ + 2.34 ∧
    (Star.p n ρ ≤ 0.11 → (Star.Delta n ρ : ℝ) ≤ 3 * (Star.p n ρ)⁻¹ ^ 2) ∧
    (Star.Delta n ρ : ℝ) ≤ 13 * (Star.p n ρ)⁻¹ ^ 2

/-- [s3:eqS3] The real-arithmetic margins of "`Δ_* ≤ 2p^{-2}+8.34p^{-1}+2.34`. Hence
`Δ_* ≤ 3p^{-2}` if `p ≤ 0.11`, and `Δ_* ≤ 13p^{-2}` for every `p ∈ (0,1]`": for every real
`p > 0`, `2p^{-2}+8.34p^{-1}+2.34 ≤ 3p^{-2}` if `p ≤ 0.11` (i.e. `8.34p + 2.34p^2 ≤ 1`;
at `p = 0.11`: `0.9174 + 0.0283 = 0.9457`, slack 5.4%; the TeX's split `8.34·0.11 ≤ 0.92`
has 0.3%), and `≤ 13p^{-2}` if `p ≤ 1` (`2 + 8.34 + 2.34 = 12.68`, slack 2.5%). -/
def NumStarS3MarginStatement : Prop :=
  ∀ p : ℝ, 0 < p →
    (p ≤ 0.11 → 2 * p⁻¹ ^ 2 + 8.34 * p⁻¹ + 2.34 ≤ 3 * p⁻¹ ^ 2) ∧
    (p ≤ 1 → 2 * p⁻¹ ^ 2 + 8.34 * p⁻¹ + 2.34 ≤ 13 * p⁻¹ ^ 2)

end EG.Spec
