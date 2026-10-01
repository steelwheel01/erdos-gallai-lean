module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statements of Proposition "fresh and parentless mass" (manuscript s2:propParentless)

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:propParentless. Definitions: `EG/Defs/HB/Round.lean`, `Run.lean`,
`EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Proposition [s2:propParentless]:
"For every valid `HB*^{τ+}` run with `d_1 ≥ D_*`:
(i) If `x` lies in a round-`r` pre-part, then `H := home_r(x)` is an ancestor of round `r`
containing `x`: `x ∈ H^0 \ S_H = V(H)` if `H` is light, and `x ∈ H^0 = V(H)` otherwise. Hence, for
`Z ∈ Std_l` and `x ∈ U_Z`, `x ∈ F_Z` iff `j_0(x) ≥ l-1`. A vertex is a port of at most one part
per round, so it is a fresh port only at rounds `j_0(x)` and `j_0(x)+1`, and
(K4) `Σ_{l≤R} Σ_{Z∈Std_l} |F_Z| ≤ 2n`.
(ii) (admissible parents) If `Y` is a light part of round `r ≤ l-2` and `Z` is a light part of
round `l ≤ R`, then `|Y| ≥ P_r/2 ≥ P_{l-2}/2 ≥ M_l log^4 M_l ≥ |Z| L_Z^4`.
(iii) Let `Bad` be *any* set of light parts. Call a pair `(v,Z)`, with `Z` a light part of some
round `l` and `v ∈ Z`, *parentless with respect to `Bad`* if no light part outside `Bad` of a
round at most `l-2` contains `v`. Then the number of such pairs is at most
`2n + Σ_{Y∈Bad} |Y| (R - r(Y))`. More precisely, a vertex `v` is in parentless pairs only at its
light parts of rounds `j_1(v)` and `j_1(v)+1`, and at the later rounds at which the light part of
round `j_1(v)` containing `v` lies in `Bad`."

Three statements (this file): `FreshStatement` (i), `AdmissibleParentStatement` (ii),
`ParentlessCountStatement` (iii).

Formal reading.
* Hypotheses. (i) and (iii) hold for every valid run, with no condition on `D_*` and without
  `d_1 ≥ D_*` (blueprint PL-II-GAMMA; dropping unused hypotheses strengthens the statements).
  (ii) uses Lemma s2:lemTower (a), (b) and Lemma s2:lemCap(ii), so it carries `Gamma1core Dstar`
  (the standing assumption); its `d_1 ≥ D_*` is implied (a light part of a round `l ≥ 3` exists
  only if `R ≥ 3`, and then `d_1 ≥ D_*` by `Run.Valid`), so it is dropped too.
* Rounds 1-indexed; ancestors, parts and light parts are `PartId = (round, address)`;
  `V(Y) = run.ancVerts G Y` (`Y^0 \ S_Y` for a light part, `Y^0` for a standalone pre-part,
  [s2:defAncestors]); "`x ∈ H^0 \ S_H` if `H` is light, `x ∈ H^0` otherwise" is also stated
  explicitly. `home_r(x) = run.home G r x` (an `Option Addr`).
* (i) `U_Z = run.ports G l a`, `F_Z = run.fresh G l a` for `a ∈ Std_l`; `j_0(x) = run.j0 G x`
  (in `WithTop ℕ`, finite here since `x ∈ Z^0`); "`j_0(x) ≥ l-1`" is written `l ≤ j_0(x) + 1`
  (no natural subtraction; blueprint PL-J0-OFFSET). "a port of at most one part per round": at
  most one `a ∈ Std_l` has `x ∈ U_a`. "a fresh port only at rounds `j_0(x)` and `j_0(x)+1`":
  `x ∈ F_a` with `a ∈ Std_l` implies `l = j_0(x)` or `l = j_0(x) + 1`. (K4) in `ℕ`, `n = G.card`.
* (ii) "`Y` a light part of round `r ≤ l-2`, `Z` a light part of round `l ≤ R`": `Y, Z` in
  `run.lightParts G` (so `1 ≤ r` and `l ≤ R`) with `r + 2 ≤ l`; `|Y| = |V(Y)|`,
  `L_Z = run.LY G Z = log |V(Z)|`, `log = Real.logb 2`; `P_{l-2} = run.P G (l - 2)` (exact).
* (iii) `Bad` is an arbitrary finite set of part identities (blueprint PL-BAD-SCOPE; members that
  are not light parts only add nonnegative terms to the bound, so this is the statement for
  every set of light parts and slightly more; the s5 consumer, s5:defStages (eqPl), instantiates
  it with the demoted or parent-bad parts). "`(v,Z)` parentless": `Z ∈ run.lightParts G`,
  `v ∈ V(Z)`, and there is no `Y ∈ run.lightParts G` with `Y ∉ Bad`, `r(Y) + 2 ≤ r(Z)` and
  `v ∈ V(Y)`. "the number of such pairs" is written as `Σ_Z |{v ∈ V(Z) : (v,Z) parentless}|`
  (each pair counted once). The bound `2n + Σ_{Y∈Bad} |Y|(R - r(Y))` is in `ℕ` (`R - r(Y)`
  truncated; exact for the light parts, `r(Y) ≤ R`). "More precisely": for a parentless pair
  `(v,Z)` of round `l`, `l = j_1(v)`, or `l = j_1(v) + 1`, or `j_1(v) + 2 ≤ l` and the light part
  of round `j_1(v)` containing `v` is in `Bad` (`j_1 = run.j1 G`, in `WithTop ℕ`; the light part
  of round `j_1(v)` containing `v` is unique by s2:propStructure(iv), so "the" is written as
  "a").
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propParentless] (i) "If `x` lies in a round-`r` pre-part, then `H := home_r(x)` is an
ancestor of round `r` containing `x`: `x ∈ H^0 \ S_H = V(H)` if `H` is light, and `x ∈ H^0 = V(H)`
otherwise. Hence, for `Z ∈ Std_l` and `x ∈ U_Z`, `x ∈ F_Z` iff `j_0(x) ≥ l-1`. A vertex is a port
of at most one part per round, so it is a fresh port only at rounds `j_0(x)` and `j_0(x)+1`, and
(K4) `Σ_{l≤R} Σ_{Z∈Std_l} |F_Z| ≤ 2n`." (For every valid run; module docstring.) -/
def FreshStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    run.Valid G Dstar →
    (∀ r ∈ Finset.Icc 1 run.R, ∀ x : V, (∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a) →
      ∃ a : Addr, run.home G r x = some a ∧ a ∈ run.prePartAddrs G r ∧
        (r, a) ∈ run.ancestors G ∧ x ∈ run.ancVerts G (r, a) ∧
        (run.isLight G r a → x ∈ run.Z0 G r a \ run.guests G r a) ∧
        (¬ run.isLight G r a → x ∈ run.Z0 G r a)) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.Std G l, ∀ x ∈ run.ports G l a,
      (x ∈ run.fresh G l a ↔ (l : WithTop ℕ) ≤ run.j0 G x + 1)) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ x : V,
      ((run.Std G l).filter (fun a => x ∈ run.ports G l a)).card ≤ 1) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.Std G l, ∀ x ∈ run.fresh G l a,
      run.j0 G x = (l : WithTop ℕ) ∨ run.j0 G x + 1 = (l : WithTop ℕ)) ∧
    ∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card ≤ 2 * G.card

/-- [s2:propParentless] (ii) "(admissible parents) If `Y` is a light part of round `r ≤ l-2` and
`Z` is a light part of round `l ≤ R`, then `|Y| ≥ P_r/2 ≥ P_{l-2}/2 ≥ M_l log^4 M_l ≥ |Z| L_Z^4`."
(For every valid run, under Γ1 (a)–(e); module docstring.) -/
def AdmissibleParentStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.lightParts G, ∀ Z ∈ run.lightParts G, Y.1 + 2 ≤ Z.1 →
      (run.P G Y.1 : ℝ) / 2 ≤ ((run.ancVerts G Y).card : ℝ) ∧
      (run.P G (Z.1 - 2) : ℝ) / 2 ≤ (run.P G Y.1 : ℝ) / 2 ∧
      (run.M G Z.1 : ℝ) * Real.logb 2 (run.M G Z.1 : ℝ) ^ 4 ≤ (run.P G (Z.1 - 2) : ℝ) / 2 ∧
      ((run.ancVerts G Z).card : ℝ) * run.LY G Z ^ 4 ≤
        (run.M G Z.1 : ℝ) * Real.logb 2 (run.M G Z.1 : ℝ) ^ 4

open Classical in
/-- [s2:propParentless] (iii) "Let `Bad` be *any* set of light parts. Call a pair `(v,Z)`, with
`Z` a light part of some round `l` and `v ∈ Z`, *parentless with respect to `Bad`* if no light
part outside `Bad` of a round at most `l-2` contains `v`. Then the number of such pairs is at most
`2n + Σ_{Y∈Bad} |Y| (R - r(Y))`. More precisely, a vertex `v` is in parentless pairs only at its
light parts of rounds `j_1(v)` and `j_1(v)+1`, and at the later rounds at which the light part of
round `j_1(v)` containing `v` lies in `Bad`." (For every valid run and every finite set `Bad` of
part identities; module docstring.) -/
def ParentlessCountStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    run.Valid G Dstar → ∀ Bad : Finset PartId,
    (∑ Z ∈ run.lightParts G, ((run.ancVerts G Z).filter (fun v =>
        ¬ ∃ Y ∈ run.lightParts G, Y ∉ Bad ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y)).card ≤
      2 * G.card + ∑ Y ∈ Bad, (run.ancVerts G Y).card * (run.R - Y.1)) ∧
    ∀ Z ∈ run.lightParts G, ∀ v ∈ run.ancVerts G Z,
      (¬ ∃ Y ∈ run.lightParts G, Y ∉ Bad ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y) →
        run.j1 G v = (Z.1 : WithTop ℕ) ∨ run.j1 G v + 1 = (Z.1 : WithTop ℕ) ∨
        (run.j1 G v + 2 ≤ (Z.1 : WithTop ℕ) ∧
          ∃ Y ∈ Bad, Y ∈ run.lightParts G ∧ run.j1 G v = (Y.1 : WithTop ℕ) ∧
            v ∈ run.ancVerts G Y)

end EG.Spec
