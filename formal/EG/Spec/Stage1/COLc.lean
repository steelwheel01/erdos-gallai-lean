module

public import EG.Defs.Stage1.COL
public import EG.Defs.Gamma.Full

/-!
# Statements of Lemma COL (c) and of its per-index step (manuscript s3:lemCOL (c))

Statement file (`EG/Spec/**`) of probe unit P4B (probe P-4, part 2): the COL(c) nodes of TRIAGE §4
row P-4 ("COL(c) (T16* per U-index, joint independence)"). Design note `formal/work/p2b/P4B.md`.
Refutation target of P-4: "COL(b)/(c) `t^JS` and `t_Y`" (this file: the multiplicity `t_Y` of the
U-lent classes).

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOL]:
"Assume condition s1:condG1. Let `Y` be an ancestor of round `r`, with the stage-1 lending data of
Definition s3:defCOL. If `r ≥ R-1`, then `k_lend(Y) = 0` and every statement below about lent
classes is vacuous. …
(c) Let `Y` be light. Let `(V_{l,c,σ})_{(l,c,σ) ∈ I^U(Y)}` be random subsets of `V(Y)`, independent
of the stage-1 lending data of `Y`, such that each `V_{l,c,σ}` is a `ρ_{l,c,σ}`-random subset of
`V(Y)` with `ρ_{l,c,σ} ≥ 1/(12L_Y^5)`. The family may be dependent across indices. Then, with
probability at least `1 - |V(Y)|^{-2}/2` over the lending data and the sets, every U-lent class
`LU_{Y,l,c,σ}` is `(2^{12}L_Y^4, t_Y)`-path connected through `V_{l,c,σ}`, where
`t_Y = ⌈λ_r^{1.6}⌉` (Definition s3:defCOL)."
Proof of (c): "Condition as in (b). The sets `V_{l,c,σ}` are independent of the colouring. For a
fixed index, apply Theorem s3:thmT16s to the fixed class `LU_{Y,l,c,σ}`, an `N`-vertex
`(2^{-6},s_r/(16k))`-expander, with `t := t_Y = ⌈λ^{1.6}⌉` (so `1 ≤ t ≤ 2λ^{1.6}`) and
`ρ := ρ_{l,c,σ} ≥ 1/(12L^5)`. Its hypotheses hold: `s_r/(16k) ≥ 2^{135}tL^{28}ρ^{-5}` by row 4
(with row 9), since `ρ^{-5} ≤ (12L^5)^5`; `ρN ≥ N/(12L^5) ≥ λ^{103}/(24(2λ)^5) ≥ L^2`. Each index
fails with probability at most `2^{86}tL^{19}(12L^5)^3N^{-3}`. The theorem is applied to one index
at a time, so dependence across indices is irrelevant. By row 7, the union over `I^U(Y)` is at
most `N^{-2}/4`. Together with the failure probability of (a), (c) fails with probability at most
`N^{-2}/2`." ("Condition as in (b)": "Condition on a stage-(i)/(ii) outcome in which (a) holds.")

Formal reading (Stage-1 layer, `formal/work/p2d/stage1.md` "For the consumers": "For (c), use
`μ.IndepFun D Vs`"):
* the lending data of `Y` is `D : Ω → COLOut G run Y` with `μ.map D = colLaw G run Y`;
* the family `(V_{l,c,σ})` is `Vs : Ω → LentTag → Finset V` (read at the U-tags `i ∈ I^U(Y)`);
  "independent of the stage-1 lending data of `Y`" is `μ.IndepFun D Vs` (the whole family jointly
  independent of `D`; no independence across indices is assumed); "each `V_i` is a `ρ_i`-random
  subset of `V(Y)`" is `μ.IsRSubset (Vs · i) (V(Y)) (ρ i)`;
* "every U-lent class … is path connected" is the event `EG.Stage1.COLc G run Y (D ω) (Vs ω)`;
* `N = |V(Y)|`, `L_Y = log₂ N` (`run.LY`), `t_Y = EG.Stage1.tY` (a natural number, cast to `ℝ`
  by `IsPathConnected`);
* the per-index step (`COLcIndexStatement`) is stated as the probability of "(a) holds and the
  class of the index `i` is not path connected", which is what "Condition on a stage-(i)/(ii)
  outcome in which (a) holds … Each index fails with probability at most …" bounds; its failure
  bound is the manuscript's `2^{86}tL^{19}(12L^5)^3N^{-3}` (with `ρ^{-3}` already replaced by
  `(12L^5)^3`, the form summed in row 7, `EG.Spec.COLJVRow7Statement`);
* hypotheses: Γ1 and a valid run with `d_1 ≥ D_*` (the s2/s3 setting, as for `COLaProbStatement`);
  `Y ∈ run.lightParts G` ("Let `Y` be light"; a light part is an ancestor). For `r ≥ R-1`,
  `I^U(Y) = ∅` and the statement is vacuous (the event `COLc` holds), as in the manuscript.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u v

/-- [s3:lemCOL] (c), proof, the per-index step ("T16* per U-index"): "Condition on a
stage-(i)/(ii) outcome in which (a) holds. … For a fixed index, apply Theorem s3:thmT16s to the
fixed class `LU_{Y,l,c,σ}` … with `t := t_Y` … and `ρ := ρ_{l,c,σ} ≥ 1/(12L^5)`. … Each index
fails with probability at most `2^{86}tL^{19}(12L^5)^3N^{-3}`": for a light part `Y`, an index
`i ∈ I^U(Y)` and a `ρ`-random subset `W` of `V(Y)` independent of the lending data `D`, the
probability that (a) holds and the lent class of `i` is not `(2^{12}L_Y^4, t_Y)`-path connected
through `W` is at most `2^{86} t_Y L_Y^{19} (12L_Y^5)^3 N^{-3}`. -/
def COLcIndexStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ Y ∈ run.lightParts G, ∀ i ∈ Stage1.IU G run Y,
    ∀ (Ω : Type v) (μ : FinDist Ω) (D : Ω → Stage1.COLOut G run Y) (W : Ω → Finset V) (ρ : ℝ),
      μ.map D = Stage1.colLaw G run Y →
      μ.IsRSubset W (run.ancVerts G Y) ρ → 1 / (12 * run.LY G Y ^ 5) ≤ ρ →
      μ.IndepFun D W →
      μ.prob {ω | Stage1.COLa G run Y (D ω) ∧
          ¬ (Stage1.lentClass G run Y (D ω).1 i).IsPathConnected
              ((2 : ℝ) ^ 12 * run.LY G Y ^ 4) (Stage1.tY G run Y) (W ω)} ≤
        (2 : ℝ) ^ 86 * (Stage1.tY G run Y : ℝ) * run.LY G Y ^ 19 * (12 * run.LY G Y ^ 5) ^ 3 *
          ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ)

/-- [s3:lemCOL] (c) "Let `Y` be light. Let `(V_{l,c,σ})_{(l,c,σ) ∈ I^U(Y)}` be random subsets of
`V(Y)`, independent of the stage-1 lending data of `Y`, such that each `V_{l,c,σ}` is a
`ρ_{l,c,σ}`-random subset of `V(Y)` with `ρ_{l,c,σ} ≥ 1/(12L_Y^5)`. The family may be dependent
across indices. Then, with probability at least `1 - |V(Y)|^{-2}/2` over the lending data and the
sets, every U-lent class `LU_{Y,l,c,σ}` is `(2^{12}L_Y^4, t_Y)`-path connected through
`V_{l,c,σ}`" (under Γ1, for a valid run with `d_1 ≥ D_*`). -/
def COLcStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    ∀ Y ∈ run.lightParts G,
    ∀ (Ω : Type v) (μ : FinDist Ω) (D : Ω → Stage1.COLOut G run Y)
      (Vs : Ω → Stage1.LentTag → Finset V) (ρ : Stage1.LentTag → ℝ),
      μ.map D = Stage1.colLaw G run Y →
      (∀ i ∈ Stage1.IU G run Y,
        μ.IsRSubset (fun ω => Vs ω i) (run.ancVerts G Y) (ρ i) ∧
          1 / (12 * run.LY G Y ^ 5) ≤ ρ i) →
      μ.IndepFun D Vs →
      μ.prob {ω | ¬ Stage1.COLc G run Y (D ω) (Vs ω)} ≤
        ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 2

end EG.Spec
