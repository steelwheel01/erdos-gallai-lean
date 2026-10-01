module

public import EG.Defs.Stage1.COL
public import EG.Defs.Gamma.Full

/-!
# Statement of the failure bound of Lemma COL (a) (manuscript s3:lemCOL, proof of (a))

Statement file (`EG/Spec/**`) of probe unit P4B (probe P-4, part 2). A DECLARED INPUT of the probe:
the proof of Lemma COL (c) ends "Together with the failure probability of (a), (c) fails with
probability at most `N^{-2}/2`", and uses the bound `N^{-2}/4` for (a) derived in the proof of
(a). The lemma statement bounds (a), (b), (e) only jointly by `N^{-2}/2`, which is too weak for
(c) (blueprint s5 E1-COL-A-BOUND: "Recommend the s3 Spec export P(COL(a) fails) ≤ 6N^-4 (or
≤ N^-2/4, as proved inside lemCOL) as its own conjunct"). The proof (three applications of
Lemma 15⁺, conditioning on the split) is the s3 Lemma-COL unit's job. Design note
`formal/work/p2b/P4B.md`.

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemCOL] (a):
"Stage (i) is a uniform `2`-colouring of `E(H_Y)`. By Lemma s3:lemL15p with `k = 2` …, `Own_Y`
and `Lend_Y` are `(ε_Y,s_Y/4)`-expanders on `V(Y)`, except with probability at most `4N^{-5}`.
… every lent class is an `(ε_Y,s_Y/(8k))`-expander on `V(Y)`, except with probability at most
`2kN^{-5}`. If `Y` is light, … every own class an expander with parameters `2^{-6}` and
`s_r/(16k_own)`, except with probability at most `2k_own N^{-5}`. Using row 9 (`k ≤ λ^{3.3}`),
`k_own ≤ L ≤ 2λ` and `N^3 ≥ λ^{309}/8`, the total failure probability of (a) is at most
`2(2+k+k_own)N^{-5} ≤ 2(2+λ^{3.3}+2λ)N^{-5} ≤ N^{-2}/4`."

Formal reading (Stage-1 layer, design note `formal/work/p2d/stage1.md`, "For the consumers"):
the lending data of the ancestor `Y` is any random variable `D` with law `colLaw G run Y`
(`μ.map D = colLaw G run Y`); "(a)" is the event `EG.Stage1.COLa G run Y (D ω)`; `N = |V(Y)|`.
Hypotheses: Γ1 ("Assume condition s1:condG1") and a valid run with `d_1 ≥ D_*` (the s2/s3 setting,
as in `EG.Spec.TowerBRoundStatement`); `Y` an ancestor of any round.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u v

/-- [s3:lemCOL] (a), failure bound from its proof: "the total failure probability of (a) is at
most `2(2+k+k_own)N^{-5} ≤ … ≤ N^{-2}/4`", for every ancestor `Y` of a valid run with
`d_1 ≥ D_*`, under Γ1. -/
def COLaProbStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ Y ∈ run.ancestors G, ∀ (Ω : Type v) (μ : FinDist Ω) (D : Ω → Stage1.COLOut G run Y),
      μ.map D = Stage1.colLaw G run Y →
      μ.prob {ω | ¬ Stage1.COLa G run Y (D ω)} ≤ ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 4

end EG.Spec
