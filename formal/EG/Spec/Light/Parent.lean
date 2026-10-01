module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages
public import EG.Defs.Light.Constants

/-!
# Statement of Lemma parent side: multi-parent chaining over U-bundles (manuscript s5:lemParent)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemParent.

Manuscript v6.1, `s5.tex` (before the lemma): "For a round `l ≥ 3` put
`J̄_l := max{J_Z : Z a light part of round l}` (and `J̄_l := 0` if there is none), and let `ν_l` be
the number of ancestors of rounds `≤ l−2`, as in Proposition s2:propOV." Lemma [s5:lemParent]:
"Fix a stage-1 outcome and, for every non-demoted light part `Z`, a stage-3 outcome in the event
`𝒢_Z` of Lemma s5:lemChild. Fix a round `l` with `3 ≤ l ≤ R` and, for every non-demoted light
part `Z` of round `l`, an edge set `H_0(Z)` with `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`; the arcs of `Z` are
those given by Lemma s5:lemChild for this `H_0(Z)`. For `c ∈ [4]` the *U-bundle* `B_{l,c}` is the
set of all phase-`c` arcs of all non-demoted light parts of round `l`; `E(B_{l,c})` denotes the
union of their edge sets. Then for every `c ∈ [4]` there is a set `LentU_{l,c}` of edges, disjoint
from `E(B_{l,c})`, such that `E(B_{l,c}) ∪ LentU_{l,c}` decomposes into cycles and single edges,
where:
(i) `LentU_{l,c} ⊆ ⋃_Y ⋃_{σ∈[T^sl_Y]} LU_{Y,l,c,σ}`, the union over the good parents `Y` of rounds
`≤ l−2`; every edge of `LentU_{l,c} ∩ LU_{Y,l,c,σ}` lies on a *connector*, a path in
`LU_{Y,l,c,σ}` all of whose interior vertices lie in `Zone_{Y,l,c,σ}`;
(ii) the number of objects, summed over `c ∈ [4]`, is at most
`4·14(J̄_l+1)M_l(M_l+1)ν_l + cap_l`, `cap_l ≤ 14(J̄_l+1)n/(102 log₂λ_{l−2})^2`, where `cap_l` is
the number of *visit-capping pieces*; and
`∑_{l=3}^{R} (4·14(J̄_l+1)M_l(M_l+1)ν_l + cap_l) ≤ ε_ch(D_*) n`, where
`ε_ch(D_*) := 614/D_* + log₂(2A log₂(A log₂log₂D_*)) / (371 (log₂log₂D_*)^2)`;
(iii) no other edge is used: every object consists of edges of `E(B_{l,c}) ∪ LentU_{l,c}`, and
every such edge lies in exactly one object.
The sets `LentU_{l,c}` for distinct pairs `(l,c)` are pairwise disjoint, and the objects and
`LentU_{l,c}` depend only on the stage-1 outcome and on the bundle `B_{l,c}`. Moreover
`ε_ch(D_*) → 0` as `D_* → ∞`."

Formal reading (Defs `EG/Defs/Light/Stages.lean`, design note `work/p2d/light.md` D-L-6;
TRIAGE §2.8 PAR-ARCS-INPUT, §2.12).
* Setting: `EG.RunHyp N0 Dstar G run`; "a stage-1 outcome": `ω ∈ (Stage1.law G run).supp`.
* **Arcs as input (PAR-ARCS-INPUT, TRIAGE §2.8).** "the arcs of `Z` are those given by Lemma
  s5:lemChild": any arc systems with the child-side properties, `EG.Light.ArcHyp ω l H0 arcs`
  (`H0Adm` and the lemChild conclusion (b)–(d) `ArcSys` for every non-demoted light part of round
  `l`). The stage-3 outcomes enter only through these arcs, so they are not quantified.
* `B_{l,c}`: `EG.Light.bundleEdges ω l arcs c`; the available U-lent edges of (i):
  `EG.Light.lentUAvail ω l c`; connectors: `EG.Light.IsConnector ω l c Y σ p`; `σ ∈ [T^sl_Y]` is
  `σ < Tslot G run Y` (0-based); "the good parents of rounds `≤ l−2`": `goodParents ω l`.
* "decomposes into cycles and single edges" and (iii): `IsDecomp ↑(E(B_{l,c}) ∪ LentU_{l,c}) (D c)`.
* (ii), per round: `cap_l` is existential (`cap : ℕ`, "the number of visit-capping pieces");
  `J̄_l = EG.Light.Jbar G run l`, `M_l = run.M G l` (`ℕ`, TRIAGE M-INTEGER), `ν_l = run.nuAnc G l`,
  `λ_{l−2} = run.lam G (l − 2)` (`l ≥ 3`), `n = G.card`, `log₂ = Real.logb 2`.
* (ii), the sum over rounds: `LemParentSumStatement`. **T0:** the sum is stated with `cap_l`
  replaced by its bound `14(J̄_l+1)n/(102 log₂λ_{l−2})^2` (a function of the run), since the
  per-round `cap_l` is existential; this is exactly what the proof (Step 9) bounds, and with the
  per-round statement it gives the manuscript's sum. `ε_ch = EG.Light.epsChain` (the locked copy).
* "The sets `LentU_{l,c}` for distinct pairs `(l,c)` are pairwise disjoint": for distinct `c`
  (same `l`) in `LemParentStatement`; for distinct `l` through (i) and `LemParentAvailDisjointStatement`
  (the available sets of distinct pairs `(l,c)` are disjoint), which is how Step 8 proves it
  ("… lie in disjoint colour classes (the index `(l,c,σ)` differs)").
* **T0 (TRIAGE §2.12):** "depend only on the stage-1 outcome and on the bundle `B_{l,c}`" is not
  stated (pure existence).
* "`ε_ch(D_*) → 0`": `LemParentLimitStatement` (proved in `EG.Lib.Light.Constants`,
  `EG.Light.tendsto_epsChain`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemParent] Lemma parent side, for one round `3 ≤ l ≤ R` and any arc systems with the
child-side properties: for every phase `c` a set `LentU_{l,c}` disjoint from `E(B_{l,c})` and a
decomposition of `E(B_{l,c}) ∪ LentU_{l,c}` with (i)–(iii), the sets `LentU_{l,c}` pairwise
disjoint over `c`, in the setting of Section s5 (`RunHyp`). -/
def LemParentStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
    ∀ (H0 : PartId → Finset (Sym2 V)) (arcs : PartId → List (Arc V)), ArcHyp ω l H0 arcs →
      ∃ (LentU : Fin 4 → Finset (Sym2 V)) (D : Fin 4 → List (Obj V)) (cap : ℕ),
        (∀ c, Disjoint (LentU c) (bundleEdges ω l arcs c)) ∧
        -- decomposition into cycles and single edges; (iii)
        (∀ c, IsDecomp ((bundleEdges ω l arcs c ∪ LentU c : Finset (Sym2 V)) : Set (Sym2 V))
          (D c)) ∧
        -- (i)
        (∀ c, LentU c ⊆ lentUAvail ω l c) ∧
        (∀ c, ∀ Y ∈ goodParents ω l, ∀ σ < Tslot G run Y, ∀ e ∈ LentU c,
          e ∈ (LU G run Y (ω.colAt Y) l c σ).edges →
            ∃ p : List V, IsConnector ω l c Y σ p ∧ e ∈ walkEdges p) ∧
        -- (ii), per round
        (cap : ℝ) ≤ 14 * ((Jbar G run l : ℝ) + 1) * (G.card : ℝ) /
          (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 ∧
        ((∑ c, (D c).length : ℕ) : ℝ) ≤
          4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
            (run.nuAnc G l : ℝ) + cap ∧
        -- pairwise disjoint over `c`
        (∀ c c', c ≠ c' → Disjoint (LentU c) (LentU c'))

/-- [s5:lemParent] (ii), the sum over the rounds:
"`∑_{l=3}^{R} (4·14(J̄_l+1)M_l(M_l+1)ν_l + cap_l) ≤ ε_ch(D_*) n`", with `cap_l` replaced by its
bound `14(J̄_l+1)n/(102 log₂λ_{l−2})^2` of (ii) (module docstring, T0), in the setting of
Section s5 (`RunHyp`). -/
def LemParentSumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∑ l ∈ Finset.Icc 3 run.R,
        (4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
            (run.nuAnc G l : ℝ) +
          14 * ((Jbar G run l : ℝ) + 1) * (G.card : ℝ) /
            (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2) ≤
      epsChain Dstar * (G.card : ℝ)

/-- [s5:lemParent] "The sets `LentU_{l,c}` for distinct pairs `(l,c)` are pairwise disjoint",
through the available sets of (i): for distinct pairs `(l,c) ≠ (l',c')` the sets
`⋃_Y ⋃_σ LU_{Y,l,c,σ}` and `⋃_Y ⋃_σ LU_{Y,l',c',σ}` (over the good parents of rounds `≤ l−2`,
resp. `≤ l'−2`) are disjoint, for every stage-1 outcome, in the setting of Section s5
(`RunHyp`). -/
def LemParentAvailDisjointStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ (l l' : ℕ) (c c' : Fin 4), (l, c) ≠ (l', c') →
      Disjoint (lentUAvail ω l c) (lentUAvail ω l' c')

/-- [s5:lemParent] "Moreover `ε_ch(D_*) → 0` as `D_* → ∞`." -/
def LemParentLimitStatement : Prop :=
  Filter.Tendsto epsChain Filter.atTop (nhds 0)

end EG.Spec
