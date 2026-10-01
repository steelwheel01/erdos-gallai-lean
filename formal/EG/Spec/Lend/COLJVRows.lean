module

public import EG.Defs.Stage1.COL
public import EG.Defs.Gamma.Full

/-!
# Statements of rows 4, 7 and 8 of the COL-JV table, column 2 (manuscript s3:lemCOLJV (ii),
Table s3:tabCOLJV; CR1-PV)

Statement file (`EG/Spec/**`) of probe unit P4A (probe P-4, part 1): probe nodes. Design note
`formal/work/p2b/P4A.md`. Proofs (stage 2): `EG/Proof/Lend/COLJVRows.lean`, from Γ1 (f) (column 3,
`EG.COLTable.col3`), the declared inputs `EG.Spec.TowerBRoundStatement` ((B1), (B3)) and
`EG.Spec.COLJVCountStatement` (part (i)), and the definitions ((B4), `s_Y`, `t_Y`, `k_own`).

These three rows are the ones that CR1-PV touched or that carry the own-device thresholds:
rows 4 and 7 were rewritten with the U-multiplicity parameter `t_Y = ⌈λ_r^{1.6}⌉`
("`\fixes{… CR1-PV (rows 4 and 7 with t_Y)}`"), which is the path-connectivity multiplicity that
the per-vertex arc bound of Lemma PV (c) feeds (s5:lemParent Step 5: "`v` lies in at most
`M_l - 1 < t_Y` pairs"); row 8 (d) is the own-class threshold `s' ≥ 2^{145}L^{41}` of Lemma PV.

Manuscript v6.1, `s3.tex`, Table [s3:tabCOLJV] (column 2 "Requirement (use)", column 3):
"4 | T16* for U-lent classes: `s_Y/(8k_lend) ≥ 2^{135} t_Y L_Y^{28} (12L_Y^5)^5`,
    `t_Y = ⌈λ^{1.6}⌉` | `λ^{42.1} ≥ 2^{193}·12^5` (with row 9)†
 7 | T16* failures over `I^U(Y)` sum to at most `|V(Y)|^{-2}/4` | `λ^{64.4} ≥ 2^{127}·12^4`
 8 | own devices: (a) `s_r/4 ≥ 2^{150}L_Y^{42}`; (b) `s_r/4 ≥ 2^{146}L_Y^{38} log L_Y` (the threshold
    of VX⁺ for standalone parts; not used …); (c) `s_r/2 ≥ 2^{151}L_Y^{38} log L_Y`;
    (d) `s' := s_r/(16k_own) ≥ 2^{145}L_Y^{41}` and `s' ≥ 2⌈L_Y^6⌉` | (a) `λ^{58} ≥ 2^{194}`; …"
Caption: "Here `λ := λ_r` and `μ := log λ` …". Lemma [s3:lemCOLJV]: "Assume condition Γ1. Let `Y`
be an ancestor of round `r ≤ R` … (ii) Every requirement in column 2 and every inequality in
column 3 of Table s3:tabCOLJV holds. … Rows 1, 3 and 8 … hold for every round `r ≤ R`, that is,
also for `r ∈ {R-1, R}`: … rows 3 and 8 for every ancestor `Y` of round `r`. … Rows 4–7 and 10
concern lent classes or `p_Y`. They are asserted for `r ≤ R-2`".

Formal reading (TRIAGE §2.6: `Gamma1 D ∧ run.Valid G D`; blueprint s3b C4, C7, C8).
* `s_Y = run.ancS G Y` (`s_r/2` light, `s_r` standalone), `s_r = run.s G Y.1`,
  `L_Y = run.LY G Y`, `N = |V(Y)| = (run.ancVerts G Y).card`, `t_Y = EG.Stage1.tY G run Y`,
  `k_lend = EG.Stage1.klend G run Y`, `k_own = EG.Stage1.kown G run Y`, `I^U(Y) = EG.Stage1.IU`;
  `log = log₂`; `N^{-3}`, `N^{-2}` are integer powers.
* Row 7 in precise form (blueprint C7): the failure bound of Theorem 16*, `2^{86}tL^{19}ρ^{-3}N^{-3}`
  per class ([s3:thmT16s]), with `t = t_Y` and `ρ^{-3}` replaced by `(12L_Y^5)^3` (the manuscript's
  derivation: "`ρ^{-3} ≤ 1728L_Y^{15}`"; the same `12L_Y^5` form as row 4's column 2), summed over
  `I^U(Y)`. The consumer (s3:lemCOL (c)) combines it with the zone density `ρ_Y ≥ 1/(12L_Y^5)`
  (s5:lemZones (ii)) through the bridge `EG.colJVRow7_rhoY` (`EG/Proof/Lend/COLJVRows.lean`),
  which gives the sum with `EG.Stage1.rhoY ^ (-3)` in place of `(12L_Y^5)^3`.
* Scope: rows 4 and 7 for every ancestor with `r ≤ R-2`, as the lemma asserts them (no light
  guard: U-lent classes exist only for light `Y`, `I^U(Y) = ∅` for standalone `Y`, and the row-4
  inequality holds for standalone `Y` as well since `s_Y ≥ s_r/2`); row 8 for every ancestor.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s3:lemCOLJV] (ii), row 4 of Table s3:tabCOLJV, column 2 (CR1-PV): "T16* for U-lent classes:
`s_Y/(8k_lend) ≥ 2^{135} t_Y L_Y^{28} (12L_Y^5)^5`, `t_Y = ⌈λ^{1.6}⌉`", for every ancestor `Y` of
round `r ≤ R-2` of a valid run, under Γ1. -/
def COLJVRow4Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G, Y.1 + 2 ≤ run.R →
      (2 : ℝ) ^ 135 * (Stage1.tY G run Y : ℝ) * run.LY G Y ^ 28 * (12 * run.LY G Y ^ 5) ^ 5 ≤
        run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ))

/-- [s3:lemCOLJV] (ii), row 7 of Table s3:tabCOLJV, column 2 (CR1-PV): "T16* failures over
`I^U(Y)` sum to at most `|V(Y)|^{-2}/4`", with the per-class failure bound
`2^{86} t_Y L_Y^{19} (12L_Y^5)^3 N^{-3}` of Theorem 16* (`N = |V(Y)|`), for every ancestor `Y` of
round `r ≤ R-2` of a valid run, under Γ1. -/
def COLJVRow7Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G, Y.1 + 2 ≤ run.R →
      ∑ _i ∈ Stage1.IU G run Y,
          (2 : ℝ) ^ 86 * (Stage1.tY G run Y : ℝ) * run.LY G Y ^ 19 * (12 * run.LY G Y ^ 5) ^ 3 *
            ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) ≤
        ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 4

/-- [s3:lemCOLJV] (ii), row 8 of Table s3:tabCOLJV, column 2: "own devices: (a)
`s_r/4 ≥ 2^{150}L_Y^{42}`; (b) `s_r/4 ≥ 2^{146}L_Y^{38} log L_Y`; (c) `s_r/2 ≥ 2^{151}L_Y^{38} log L_Y`;
(d) `s' := s_r/(16k_own) ≥ 2^{145}L_Y^{41}` and `s' ≥ 2⌈L_Y^6⌉`", for every ancestor `Y` (every
round `r ≤ R`) of a valid run, under Γ1. -/
def COLJVRow8Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G,
      (2 : ℝ) ^ 150 * run.LY G Y ^ 42 ≤ (run.s G Y.1 : ℝ) / 4 ∧
      (2 : ℝ) ^ 146 * run.LY G Y ^ 38 * Real.logb 2 (run.LY G Y) ≤ (run.s G Y.1 : ℝ) / 4 ∧
      (2 : ℝ) ^ 151 * run.LY G Y ^ 38 * Real.logb 2 (run.LY G Y) ≤ (run.s G Y.1 : ℝ) / 2 ∧
      (2 : ℝ) ^ 145 * run.LY G Y ^ 41 ≤
        (run.s G Y.1 : ℝ) / (16 * (Stage1.kown G run Y : ℝ)) ∧
      2 * (⌈run.LY G Y ^ 6⌉₊ : ℝ) ≤ (run.s G Y.1 : ℝ) / (16 * (Stage1.kown G run Y : ℝ))

end EG.Spec
