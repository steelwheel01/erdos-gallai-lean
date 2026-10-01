module

public import EG.Defs.Stage1.Law
public import EG.Defs.Gamma.Full

/-!
# The claims of Definition "Round-split pool labels" (manuscript s7:defPool)

Statement file (`EG/Spec/**`), chunk s7a (P2 Specs). Status note: `formal/work/p2s/s7a.md`.
The definitions (`poolIdx`, `qPool`, `piPool`, `poolMass`, `poolLabelLaw`, `poolLaw`, `plabOf`,
`poolSet`, `poolL`, `poolRound`) are the locked Defs of `EG/Defs/Stage1/Pool.lean`; the stage-1
law is `EG.Stage1.law` (`EG/Defs/Stage1/Law.lean`). This file states only the mathematical claims
that the definition's text makes.

Manuscript v6.1, `s7.tex`, Definition [s7:defPool]:
"Every vertex `v` of `G` independently draws a *pool label*
`plab(v) ∈ {⊥} ∪ {(l,r) : 3 ≤ l ≤ R, 1 ≤ r ≤ l−2}`, `P(plab(v) = (l,r)) = q_l π_{l,r}`, where
`q_l := M_l^{-2}` and `π_{l,r} := 2^{-(l-1-r)}`, and `P(plab(v) = ⊥) := 1 − Σ_{l,r} q_l π_{l,r}`.
This is a probability distribution: for each `l` we have `Σ_{r=1}^{l-2} π_{l,r} = 1 − 2^{-(l-2)} < 1`,
and `Σ_l q_l ≤ Σ_l M_l^{-1} ≤ 2/D_* < 1` by Lemma s2:lemTower(b). Put
`Pool_{l,r} := plab^{-1}(l,r)`, `Pool_l := ⋃_{r=1}^{l-2} Pool_{l,r}` (a disjoint union), so that
`P(v ∈ Pool_l) = q_l(1 − 2^{-(l-2)}) ≤ q_l` for every `v`. The sets `Pool_l` (`3 ≤ l ≤ R`) are
pairwise disjoint, because every vertex has one label. For `w ∈ Pool_l` let `r(w)` denote the
unique `r` with `w ∈ Pool_{l,r}`. The pool labels are stage (1d) of the randomness schedule. They
are independent of all other stage-1 data, in particular of the colourings and labels of
Definition s3:defCOL."

Formal reading.
* Setting: the section setting of s7 ("`D_*` satisfies Γ1–Γ4, `G` is a graph with `n ≥ N_0`
  vertices and `d_1 ≥ D_*`, a valid run is fixed") as `EG.RunHyp N0 Dstar G run` (TRIAGE §2.6;
  Γ4 is not used). The only Γ-dependent claim is `Σ_l q_l ≤ 2/D_* < 1` (via s2:lemTower(b) and
  `D_* > 2` from Γ1); the other claims hold for every run and are stated under the same hypothesis
  for uniformity (stating them unconditionally would be stronger, not weaker).
* The label law is total (TRIAGE §2.7: a `dite` whose guard is `poolMass ≤ 1`, fallback `dirac ⊥`);
  "This is a probability distribution" is the guard `Σ_{l,r} q_l π_{l,r} ≤ 1`, and the TeX's
  argument gives the strict `< 1` (so `P(⊥) > 0`), which is what is stated.
* "`Σ_l`" is over the rounds `3 ≤ l ≤ R` of the label space (`Finset.Icc 3 run.R`); both sums of
  the chain are over that range.
* The probabilities are under the stage-1 law `EG.Stage1.law G run` (the law every consumer uses:
  s7:defCand/lemCand, s7:lemVstar, s7:lemEXprime); "every vertex `v`" is `v ∈ V(G)`;
  `plab(v) = Stage1.plabOf ω.pool v`; `2^{-(l-2)}` is the integer power `(2:ℝ) ^ (-((l:ℤ) - 2))`.
* "Every vertex independently draws … with this law" is: the law of the pool-label family is
  the product law `Stage1.poolLaw G run` (a product over `↥V(G)` of `poolLabelLaw`); "independent
  of all other stage-1 data" is `IndepFun` of the other three families and the pool labels.
* The disjointness of the `Pool_l` and the uniqueness of `r(w)` are deterministic (for every label
  family `π`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1

/-- [s7:defPool] "Every vertex `v` of `G` independently draws a pool label …,
`P(plab(v) = (l,r)) = q_l π_{l,r}` … and `P(plab(v) = ⊥) := 1 − Σ_{l,r} q_l π_{l,r}`. This is a
probability distribution: for each `l` we have `Σ_{r=1}^{l-2} π_{l,r} = 1 − 2^{-(l-2)} < 1`, and
`Σ_l q_l ≤ Σ_l M_l^{-1} ≤ 2/D_* < 1` by Lemma s2:lemTower(b). … so that
`P(v ∈ Pool_l) = q_l(1 − 2^{-(l-2)}) ≤ q_l` for every `v`. The sets `Pool_l` (`3 ≤ l ≤ R`) are
pairwise disjoint, because every vertex has one label. For `w ∈ Pool_l` let `r(w)` denote the
unique `r` with `w ∈ Pool_{l,r}`. … They are independent of all other stage-1 data". -/
def PoolLawStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : Run V),
    RunHyp N0 Dstar G run →
      -- `Σ_{r=1}^{l-2} π_{l,r} = 1 − 2^{-(l-2)} < 1`
      (∀ l : ℕ, 3 ≤ l →
          ∑ r ∈ (Finset.Icc 1 l).filter (fun r => r + 2 ≤ l), piPool l r =
              1 - (2 : ℝ) ^ (-((l : ℤ) - 2)) ∧
            1 - (2 : ℝ) ^ (-((l : ℤ) - 2)) < 1) ∧
      -- `Σ_l q_l ≤ Σ_l M_l^{-1} ≤ 2/D_* < 1`
      (∑ l ∈ Finset.Icc 3 run.R, qPool G run l ≤ ∑ l ∈ Finset.Icc 3 run.R, ((run.M G l : ℝ))⁻¹ ∧
        ∑ l ∈ Finset.Icc 3 run.R, ((run.M G l : ℝ))⁻¹ ≤ 2 / Dstar ∧ 2 / Dstar < 1) ∧
      -- "This is a probability distribution" (`P(⊥) = 1 − Σ q_l π_{l,r} > 0`)
      poolMass G run < 1 ∧
      -- "Every vertex `v` of `G` independently draws a pool label" with the law above
      (law G run).map Outcome.pool = poolLaw G run ∧
      (∀ v ∈ G.verts, ∀ l r : ℕ, (l, r) ∈ poolIdx run →
          (law G run).prob {ω | plabOf ω.pool v = some (l, r)} = qPool G run l * piPool l r) ∧
      (∀ v ∈ G.verts, (law G run).prob {ω | plabOf ω.pool v = none} = 1 - poolMass G run) ∧
      -- `P(v ∈ Pool_l) = q_l(1 − 2^{-(l-2)}) ≤ q_l`
      (∀ v ∈ G.verts, ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
          (law G run).prob {ω | v ∈ poolL G ω.pool l} =
              qPool G run l * (1 - (2 : ℝ) ^ (-((l : ℤ) - 2))) ∧
            (law G run).prob {ω | v ∈ poolL G ω.pool l} ≤ qPool G run l) ∧
      -- the `Pool_l` are pairwise disjoint; `r(w)` is the unique `r` with `w ∈ Pool_{l,r}`
      (∀ (π : ↥G.verts → Option (ℕ × ℕ)) (l l' : ℕ), l ≠ l' → Disjoint (poolL G π l) (poolL G π l')) ∧
      (∀ (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (w : V), w ∈ poolL G π l →
          w ∈ poolSet G π l (poolRound π w) ∧ ∀ r, w ∈ poolSet G π l r → r = poolRound π w) ∧
      -- "independent of all other stage-1 data"
      (law G run).IndepFun (fun ω => (ω.col, ω.zone, ω.js)) Outcome.pool

end EG.Spec
