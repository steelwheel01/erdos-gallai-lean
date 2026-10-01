module

public import EG.Spec.Lend.COLJVCount
public import EG.Spec.Lend.COLJVRows

/-!
# Statement of Lemma COL-JV (the COL-JV table; manuscript s3:lemCOLJV (ii), Table s3:tabCOLJV)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3b (`formal/work/p2s/s3b.md`; blueprint
`formal/work/p2/blueprint_s3b.md`, nodes `s3:lemCOLJV`, `s3:tabCOLJV`). No proof here.

Part (i) is the existing `EG.Spec.COLJVCountStatement` (`EG/Spec/Lend/COLJVCount.lean`, unit
P4A), and rows 4, 7 and 8 of part (ii) are the existing `EG.Spec.COLJVRow4Statement`,
`COLJVRow7Statement`, `COLJVRow8Statement` (`EG/Spec/Lend/COLJVRows.lean`, unit P4A); both files
are reused unchanged. This file adds column 3 and the remaining rows 1, 2, 3, 5, 6, 9, 11, 12, 13
of part (ii), and the whole lemma `COLJVStatement` as the conjunction of all of them. Row 10
("`p_Y ≥ λ^{-4}`") is the last conjunct of `COLJVCountStatement` ("and consequently
`p_Y ≥ λ^{-4}`"), with the same scope `r ≤ R-2`; it is not restated.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOLJV]:
"Assume condition s1:condG1. Let `Y` be an ancestor of round `r ≤ R`, and write `λ := λ_r` and
`μ := log λ`; if `r ≤ R-2`, write also `M := M_{r+2}`. Then: (i) … (ii) Every requirement in
column 2 and every inequality in column 3 of Table s3:tabCOLJV holds. (Column 4 is not part of
this assertion …) More precisely, for each row every inequality in column 3 holds at every
`μ ≥ log log D_*` by Γ1(f); in particular it holds at `μ = log λ_r` and, for rows 2, 11 and 12,
also at `μ = log λ_{l-2}` for every round `3 ≤ l ≤ R`, both of which are at least
`log log D_*`. At the value of `λ` fixed in the caption of Table s3:tabCOLJV, these inequalities
imply the requirement in column 2 (for row 4, together with row 9). So every requirement holds,
in every round. The scope of the rows is as follows.
• Rows 1, 3 and 8 (rule GC, the three levels of Lemma 15⁺, and the own-device thresholds) hold
  for every round `r ≤ R`, that is, also for `r ∈ {R-1,R}`: row 1 for every round-`r` pre-part,
  and rows 3 and 8 for every ancestor `Y` of round `r`. They involve neither `M_{r+2}` nor any
  lent class; for `r ≥ R-1` the lent level of row 3 is void, because `Y` has no lent classes.
• Rows 4–7 and 10 concern lent classes or `p_Y`. They are asserted for `r ≤ R-2`; for
  `r ≥ R-1` there are no lent classes and `p_Y` is not defined. Row 9 holds for every `r ≤ R`,
  trivially when `k_lend(Y) = 0`.
• Rows 2, 11 and 12 concern `λ_{l-2}` for rounds `3 ≤ l ≤ R`, and row 13 is G*; they do not
  depend on `Y`."

Table s3:tabCOLJV, column 2 ("Requirement (use)") of the rows stated here:
"1 | `θ^GC_r(Z^0) > τ_r` (rule GC)
 2 | `P_{l-2} ≥ M_l^{13}`, with `λ := λ_{l-2}`
 3 | Lemma 15⁺, lent level: `s_Y/4 ≥ 40 k_lend L_Y`
 5 | T16* for JS-lent classes: `s_Y/(8k_lend) ≥ 2^{135}(3M)L_Y^{28}M^{20}`
 6 | T16* failures over `I^JS(Y)` sum to at most `|V(Y)|^{-2}/4`
 9 | `k_lend(Y) ≤ λ^{3.3}`
11 | `λ_{l-2}^{95}/(8M_l^2) ≥ 2^{10}M_l^{10}`, with `λ := λ_{l-2}`
12 | `M_l ≤ λ_{l-2}^{1.6}`, with `λ := λ_{l-2}`
13 | G*" (column 3 of row 13: "`λ^{36} ≥ 2^{240}(Aμ)^{46A}`").
Caption: "Here `λ := λ_r` and `μ := log λ`, except in rows 2, 11 and 12, where `λ := λ_{l-2}` for
a round `3 ≤ l ≤ R`."
Proof, row 3: "The other two levels of Lemma s3:lemL15p are `s_Y ≥ 80L_Y` (the Own/Lend split,
`k = 2`) and `s_r/8 ≥ 40k_own L_Y` (own classes)."
Proof, row 6: "The failure bound of Theorem s3:thmT16s is `2^{86}tL^{19}ρ^{-3}N^{-3}` per class,
with `N := |V(Y)|`." (Lemma COL (b) applies it with `t := t^JS_l`, `ρ := ρ_l`.)

Formal reading (TRIAGE §2.6: s3 COL/COLJV Specs take `Gamma1 D ∧ run.Valid G D`; conventions of
`EG/Spec/Lend/COLJVRows.lean`).
* Rounds `r ∈ Finset.Icc 1 run.R`; an ancestor `Y ∈ run.ancestors G` has round `r = Y.1`;
  "`r ≤ R-2`" is `Y.1 + 2 ≤ run.R`; rounds `3 ≤ l ≤ R` use `l - 2` (natural subtraction, exact
  since `l ≥ 3`). `λ_r = run.lam G r`, `μ = log₂ λ_r`, `M_l = run.M G l` (`ℕ`),
  `P_l = run.P G l` (`ℕ`), `s_r = run.s G r` (`ℕ`), `τ_r = run.tau G r` (`ℕ`),
  `θ^GC_r(Z^0) = run.thetaGC G r a` (`ℕ`) for the round-`r` pre-part at address
  `a ∈ run.prePartAddrs G r`; `s_Y = run.ancS G Y`, `L_Y = run.LY G Y`,
  `N = |V(Y)| = (run.ancVerts G Y).card`, `k_lend = Stage1.klend`, `k_own = Stage1.kown`,
  `t^JS_l = Stage1.tJS`, `ρ_l = Stage1.rhoJS` (`= M_l^{-4}`), `I^JS(Y)` = the pairs `(l, j)` with
  `l ∈ Stage1.lateRounds run Y.1` (`r+2 ≤ l ≤ R`) and `j < Stage1.KJS G run l` (the image of this
  set under the tag `LentTag.JS` is `Stage1.IJS`).
* Column 3 at `μ` is `EG.COLTable.col3 μ` (item (f) of Γ1). "at `μ = log λ_r`" for every round
  `r`, and "for rows 2, 11 and 12, also at `μ = log λ_{l-2}` for every round `3 ≤ l ≤ R`": since
  `l - 2` is itself a round, both are the single statement "`col3 (log λ_r)` for every round
  `r ∈ [1,R]`" (`COLJVCol3Statement`).
* Row 1 compares natural numbers (`τ_r < θ^GC_r(Z^0)`), row 2 likewise (`M_l^{13} ≤ P_{l-2}`).
* Row 3 states all three levels of Lemma 15⁺ (blueprint TAB-COL2-INFORMAL, TRIAGE E1-ROW3-GAP),
  for every ancestor as the scope bullet says ("rows 3 and 8 for every ancestor `Y`"); the lent
  level reads `0 ≤ s_Y/4` when `k_lend(Y) = 0`, and `k_own` is defined for every ancestor
  (TRIAGE §2.7), as in `COLJVRow8Statement`.
* Row 5 is the literal column 2 with `M = M_{r+2}`; the per-`l` hypothesis of Theorem 16* that
  Lemma COL (b) needs follows by (B7) (`t^JS_l ≤ 3M`, `ρ_l^{-1} ≤ M^4`), a step of the proof of
  Lemma COL.
* Row 6 in precise form: the sum over `I^JS(Y)` of the Theorem-16* failure bound with
  `t = t^JS_l`, `ρ = ρ_l`, `L = L_Y`, `N = |V(Y)|` (integer powers `ρ_l^{-3}`, `N^{-3}`, `N^{-2}`).
* Rows 9 and 12 use `Real.rpow` with the exact exponents `33/10` and `8/5`; row 11 is a real
  inequality with natural-number powers.
* Row 13 ("G*") is `EG.Gamma1e` (item (e) of Γ1) at `μ = log λ_r` for every round `r` (the
  caption's `λ := λ_r`); `EG.COLTable.row 13 μ` is the same formula.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s3:lemCOLJV] (ii), column 3 of Table s3:tabCOLJV: "for each row every inequality in column 3
holds at every `μ ≥ log log D_*` by Γ1(f); in particular it holds at `μ = log λ_r` and, for rows 2,
11 and 12, also at `μ = log λ_{l-2}` for every round `3 ≤ l ≤ R`": `col3 (log λ_r)` for every
round `r ∈ [1,R]` of a valid run, under Γ1. -/
def COLJVCol3Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, COLTable.col3 (Real.logb 2 (run.lam G r))

/-- [s3:lemCOLJV] (ii), row 1 of Table s3:tabCOLJV, column 2: "`θ^GC_r(Z^0) > τ_r` (rule GC)",
"for every round-`r` pre-part" of every round `r ≤ R` of a valid run, under Γ1. -/
def COLJVRow1Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r, run.tau G r < run.thetaGC G r a

/-- [s3:lemCOLJV] (ii), row 2 of Table s3:tabCOLJV, column 2: "`P_{l-2} ≥ M_l^{13}`, with
`λ := λ_{l-2}`", for every round `3 ≤ l ≤ R` of a valid run, under Γ1. -/
def COLJVRow2Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ l : ℕ, 3 ≤ l → l ≤ run.R → run.M G l ^ 13 ≤ run.P G (l - 2)

/-- [s3:lemCOLJV] (ii), row 3 of Table s3:tabCOLJV, column 2, with the three levels of Lemma 15⁺
("Rows 1, 3 and 8 (rule GC, the three levels of Lemma 15⁺, …)"): the lent level
"`s_Y/4 ≥ 40 k_lend L_Y`", the Own/Lend split "`s_Y ≥ 80L_Y`" and the own classes
"`s_r/8 ≥ 40k_own L_Y`", for every ancestor `Y` (every round `r ≤ R`) of a valid run, under Γ1. -/
def COLJVRow3Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G,
      40 * (Stage1.klend G run Y : ℝ) * run.LY G Y ≤ run.ancS G Y / 4 ∧
      80 * run.LY G Y ≤ run.ancS G Y ∧
      40 * (Stage1.kown G run Y : ℝ) * run.LY G Y ≤ (run.s G Y.1 : ℝ) / 8

/-- [s3:lemCOLJV] (ii), row 5 of Table s3:tabCOLJV, column 2: "T16* for JS-lent classes:
`s_Y/(8k_lend) ≥ 2^{135}(3M)L_Y^{28}M^{20}`" (`M = M_{r+2}`), for every ancestor `Y` of round
`r ≤ R-2` of a valid run, under Γ1. -/
def COLJVRow5Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G, Y.1 + 2 ≤ run.R →
      (2 : ℝ) ^ 135 * (3 * (run.M G (Y.1 + 2) : ℝ)) * run.LY G Y ^ 28 *
          (run.M G (Y.1 + 2) : ℝ) ^ 20 ≤
        run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ))

/-- [s3:lemCOLJV] (ii), row 6 of Table s3:tabCOLJV, column 2: "T16* failures over `I^JS(Y)` sum
to at most `|V(Y)|^{-2}/4`", with the per-class failure bound `2^{86}tL^{19}ρ^{-3}N^{-3}` of
Theorem 16* at `t = t^JS_l`, `ρ = ρ_l`, summed over the JS indices `(l, j)`, `r+2 ≤ l ≤ R`,
`0 ≤ j < K^JS_l`, for every ancestor `Y` of round `r ≤ R-2` of a valid run, under Γ1. -/
def COLJVRow6Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G, Y.1 + 2 ≤ run.R →
      ∑ l ∈ Stage1.lateRounds run Y.1, ∑ _j ∈ Finset.range (Stage1.KJS G run l),
          (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) * run.LY G Y ^ 19 *
            Stage1.rhoJS G run l ^ (-3 : ℤ) * ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) ≤
        ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 4

/-- [s3:lemCOLJV] (ii), row 9 of Table s3:tabCOLJV, column 2: "`k_lend(Y) ≤ λ^{3.3}`"
(`λ = λ_r`), for every ancestor `Y` (every round `r ≤ R`, "trivially when `k_lend(Y) = 0`") of a
valid run, under Γ1. -/
def COLJVRow9Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G, (Stage1.klend G run Y : ℝ) ≤ run.lam G Y.1 ^ (33 / 10 : ℝ)

/-- [s3:lemCOLJV] (ii), row 11 of Table s3:tabCOLJV, column 2:
"`λ_{l-2}^{95}/(8M_l^2) ≥ 2^{10}M_l^{10}`, with `λ := λ_{l-2}`", for every round `3 ≤ l ≤ R` of a
valid run, under Γ1. -/
def COLJVRow11Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
      (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ run.lam G (l - 2) ^ 95 / (8 * (run.M G l : ℝ) ^ 2)

/-- [s3:lemCOLJV] (ii), row 12 of Table s3:tabCOLJV, column 2: "`M_l ≤ λ_{l-2}^{1.6}`, with
`λ := λ_{l-2}`", for every round `3 ≤ l ≤ R` of a valid run, under Γ1. -/
def COLJVRow12Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ l : ℕ, 3 ≤ l → l ≤ run.R → (run.M G l : ℝ) ≤ run.lam G (l - 2) ^ (8 / 5 : ℝ)

/-- [s3:lemCOLJV] (ii), row 13 of Table s3:tabCOLJV: "G*" (column 3:
"`λ^{36} ≥ 2^{240}(Aμ)^{46A}`"), at `λ = λ_r`, `μ = log λ_r`, for every round `r ≤ R` of a valid
run, under Γ1. -/
def COLJVRow13Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, Gamma1e (Real.logb 2 (run.lam G r))

/-- [s3:lemCOLJV] Lemma COL-JV, parts (i) and (ii): part (i) (`COLJVCountStatement`, which also
contains row 10, "`p_Y ≥ λ^{-4}`"), column 3 of the table, and rows 1–9 and 11–13 of column 2,
each with the scope of the lemma (module docstring). -/
def COLJVStatement : Prop :=
  COLJVCountStatement.{u} ∧ COLJVCol3Statement.{u} ∧
    COLJVRow1Statement.{u} ∧ COLJVRow2Statement.{u} ∧ COLJVRow3Statement.{u} ∧
    COLJVRow4Statement.{u} ∧ COLJVRow5Statement.{u} ∧ COLJVRow6Statement.{u} ∧
    COLJVRow7Statement.{u} ∧ COLJVRow8Statement.{u} ∧ COLJVRow9Statement.{u} ∧
    COLJVRow11Statement.{u} ∧ COLJVRow12Statement.{u} ∧ COLJVRow13Statement.{u}

end EG.Spec
