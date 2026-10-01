module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages
public import EG.Defs.Probe.P4B.Trail

/-!
# Statements of the run-level steps of Lemma parent side (s5:lemParent Steps 5 and 9) and of the
parent-bad probability (s5:lemE1 (c), proof)

Statement file (`EG/Spec/**`) of probe unit P4B (probe P-4, part 2). The nodes hit the P-4
refutation target (TRIAGE §4: "a per-vertex multiplicity feeding a path-connectivity parameter
`t`: … Parent Step 5 `M_l − 1 ≤ t_Y`; COL(b)/(c) … `t_Y`"):
* `BundleEndCountStatement`: every vertex is an end of at most `M_l − 1` arcs of a U-bundle
  (Step 5, "Counting");
* `MlTyStatement`: `M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ t_Y`, hence `M_l − 1 < t_Y` (Step 5,
  "Comparison with `t_Y`");
* `EtaHalvingStatement`: `η` is non-increasing and halves under `x ↦ 2^{x/A}` (Step 9);
* `ParentBadProbStatement`: `P(Y parent-bad) ≤ |Y|^{-2}/2`, the application of Lemma COL (c) to
  the zones of `Y` ([s5:lemE1] (c), "joint independence": the zones of `Y` are dependent across
  indices and jointly independent of the colouring of `Y`).
The abstract steps are in `EG/Spec/Light/ParentSteps.lean`; the lemma is the s5 unit's
`EG.Spec.LemParentStatement`. Design note `formal/work/p2b/P4B.md`.

Formal reading: the s5 setting `EG.RunHyp N0 Dstar G run`; "a stage-1 outcome":
`ω ∈ (Stage1.law G run).supp`; the arcs of the round-`l` parts: any arc systems with
`EG.Light.ArcHyp ω l H0 arcs` (TRIAGE §2.8 PAR-ARCS-INPUT, as in `LemParentStatement`);
`M_l = run.M G l` (`ℕ`), `λ_r = run.lam G r`, `t_Y = EG.Stage1.tY G run Y` (`ℕ`); "the number of
arcs of `B_{l,c}` having `v` as an end" is the sum over the non-demoted light parts `Z` of round `l`
of the end count (`EG.pathEndCount`) of the phase-`c` arcs of `Z`; `η = EG.Light.etaCh`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemParent] Step 5, "Counting" (with (F-a), (F-c), (F-d)): "the number of pairs … containing
`v`, counted with multiplicity, is at most the number of arcs of `B_{l,c}` having `v` as an end.
By (F-d) and (F-c), all of them are arcs of the unique round-`l` light part `Z(v)` containing `v`,
and there are at most `|Z(v)|−1 ≤ M_l−1` of them": for any arc systems with the child-side
properties, every vertex is an end of at most `M_l − 1` phase-`c` arcs of all non-demoted light
parts of round `l` together (s5 setting). -/
def BundleEndCountStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
    ∀ (H0 : PartId → Finset (Sym2 V)) (arcs : PartId → List (Arc V)), ArcHyp ω l H0 arcs →
    ∀ (c : Fin 4) (v : V),
      ∑ Z ∈ childParts ω l, pathEndCount (((arcs Z).filter fun a => a.2 = c).map Prod.fst) v ≤
        run.M G l - 1

/-- [s5:lemParent] Step 5, "Comparison with `t_Y`": "Let `r = r(Y) ≤ l−2`. By Lemma
s2:lemTower(b) (row 12 of Table s3:tabCOLJV) and Lemma s2:lemTower(a),
`M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ ⌈λ_r^{1.6}⌉ = t_Y` (Definition s3:defCOL). So `v` lies in at
most `M_l − 1 < t_Y` pairs", for every light part `Y` and every round `l` with
`r(Y) + 2 ≤ l ≤ R` (s5 setting). -/
def MlTyStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ Y ∈ run.lightParts G, ∀ l : ℕ, Y.1 + 2 ≤ l → l ≤ run.R →
      (run.M G l : ℝ) ≤ run.lam G (l - 2) ^ (1.6 : ℝ) ∧
      run.lam G (l - 2) ^ (1.6 : ℝ) ≤ run.lam G Y.1 ^ (1.6 : ℝ) ∧
      run.M G l ≤ tY G run Y ∧
      run.M G l - 1 < tY G run Y

/-- [s5:lemParent] Step 9: "We claim that `η` is non-increasing on `[log₂D_*, ∞)` and that
`η(2^{x/A}) ≤ η(x)/2` there", with `η(x) := log₂(2A log₂(A log₂ x))/(log₂ x)^2`, under Γ1 (the
proof uses Γ1 (a), (b) at `x_1 = log₂ x ≥ log₂log₂D_*`). -/
def EtaHalvingStatement : Prop :=
  ∀ Dstar : ℝ, Gamma1 Dstar →
    AntitoneOn etaCh (Set.Ici (Real.logb 2 Dstar)) ∧
    ∀ x : ℝ, Real.logb 2 Dstar ≤ x → etaCh ((2 : ℝ) ^ (x / (Aexp : ℝ))) ≤ etaCh x / 2

/-- [s5:lemE1] (c), proof, first step: "By Lemma s5:lemZones(ii),(iv), for every sublabel
`(l,c,σ)` of `Y` the set `V_{l,c,σ} := Zone_{Y,l,c,σ} ⊆ V(Y)` contains each vertex of `Y`
independently with probability `ρ_Y ≥ 1/(12L_Y^5)`, independently of the colouring of `Y`. (The
zones of `Y` are dependent across indices, since they are disjoint; Lemma s3:lemCOL(c) allows
this.) So Lemma s3:lemCOL(c), applied with this family, gives `P(Y parent-bad) ≤ |Y|^{-2}/2`",
for every light part `Y`, over the stage-1 law (s5 setting). -/
def ParentBadProbStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ Y ∈ run.lightParts G,
      (Stage1.law G run).prob {ω | parentBad ω Y} ≤ ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 2

end EG.Spec
