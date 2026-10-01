module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma "rule GC" (manuscript s2:lemGC)

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). Design note
`formal/work/p2b/P3A.md`. Definitions: `EG/Defs/HB/Round.lean`, `EG/Defs/HB/Run.lean`,
`EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemGC]:
"For every valid `HB*^{τ+}` run and every round `r ≤ R`:
(i) the pre-parts, their leaf graphs, `Dup*_r`, `D_r`, `home_r` and the guest sets `S_Z` are
defined in (R1)–(R4) before and independently of condition (GC); (GC) only decides whether a
pre-part satisfying (L1) and (L2) is light or standalone;
(ii) for every light part `Y` of round `r` and every guest `x ∈ S_Y`,
`e_{X^0_Y}(x, Y) < θ^GC_r(Y^0)`, where `Y` denotes the vertex set `Y^0 \ S_Y`;
(iii) GC-parts are standalone; for a GC-part `Y`, every edge of `G'_r` with both ends in `Y^0` is
assigned at round `r` (the edges of `X^0_Y`, those between a guest and `Y^0 \ S_Y` included, by
(R5)(1)), so no edge of `G_{r+1}` has both ends in `V(Y) = Y^0`; and every guest `x ∈ S_Y` lies in
`D_r ⊆ Dup*_r`;
(iv) `θ^GC_r(Z^0) > τ_r` for every round-`r` pre-part `Z`."

Formal reading.
* "For every valid run and every round `r ≤ R`": `∀ Dstar G run, run.Valid G Dstar →
  ∀ r ∈ Finset.Icc 1 run.R` (rounds are 1-indexed; CONVENTIONS "The s2 hierarchy").
  Pre-parts are addresses `a ∈ run.prePartAddrs G r`; `Y^0 = run.Z0 G r a`, `X^0_Y = run.X0 G r a`,
  `S_Y = run.guests G r a`, `θ^GC_r(Y^0) = run.thetaGC G r a`, `τ_r = run.tau G r`.
* (i), first clause, is definitional: `Round.prePartAddrs`, `Round.X0`, `Round.DupStar`,
  `Round.D`, `Round.home`, `Round.guests` do not refer to `Round.isGC` or `Round.isLight`
  (design constraint TRIAGE §2.2, checked by the Defs review; recorded in the design note). The
  second clause is `GCDefStatement`.
* (ii), (iii) hold for every valid run with no hypothesis on `D_*` (`GCStatement`).
  `e_{X^0_Y}(x, Y)` is `(X^0_Y).eBetween {x} (Y^0 \ S_Y)` (disjoint sets, since `x ∈ S_Y`).
  "assigned at round `r`" is `run.assign G r e ≠ none` (to *some* part, not necessarily `Y`;
  blueprint GC-III-WHICH-PART); "(the edges of `X^0_Y` … by (R5)(1))" is `E(X^0_Y) ⊆ E_r(Y)`;
  "`V(Y) = Y^0`" is `run.ancVerts G (r, a) = run.Z0 G r a`.
* (iv) is Lemma [s2:lemTower] (c) and uses the standing assumption on `D_*` through it: the
  statement carries `Gamma1core Dstar` (`GCThetaStatement`; blueprint GC-IV-GAMMA).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemGC] (i), second clause: "(GC) only decides whether a pre-part satisfying (L1) and (L2)
is light or standalone": a round-`r` pre-part satisfying (L1) and (L2) is light iff it satisfies
(GC), and a pre-part failing (L1) or (L2) is not light, whatever (GC) says. (The first clause is
definitional; module docstring.) -/
def GCDefStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r,
      (run.isL1 G r a → run.isL2 G r a → (run.isLight G r a ↔ run.isGC G r a)) ∧
      (¬ (run.isL1 G r a ∧ run.isL2 G r a) → ¬ run.isLight G r a)

/-- [s2:lemGC] (ii), (iii) "(ii) for every light part `Y` of round `r` and every guest
`x ∈ S_Y`, `e_{X^0_Y}(x, Y) < θ^GC_r(Y^0)`, where `Y` denotes the vertex set `Y^0 \ S_Y`;
(iii) GC-parts are standalone; for a GC-part `Y`, every edge of `G'_r` with both ends in `Y^0` is
assigned at round `r` (the edges of `X^0_Y`, those between a guest and `Y^0 \ S_Y` included, by
(R5)(1)), so no edge of `G_{r+1}` has both ends in `V(Y) = Y^0`; and every guest `x ∈ S_Y` lies in
`D_r ⊆ Dup*_r`." -/
def GCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R,
      (∀ a ∈ run.prePartAddrs G r, run.isLight G r a → ∀ x ∈ run.guests G r a,
        (run.X0 G r a).eBetween {x} (run.Z0 G r a \ run.guests G r a) < run.thetaGC G r a) ∧
      (∀ a ∈ run.prePartAddrs G r, run.isGCPart G r a →
        a ∈ run.Std G r ∧
        run.ancVerts G (r, a) = run.Z0 G r a ∧
        (∀ e ∈ (run.graph' G r).edges, e ∈ (run.Z0 G r a).sym2 → run.assign G r e ≠ none) ∧
        (run.X0 G r a).edges ⊆ run.E G r a ∧
        (∀ e ∈ (run.graph G (r + 1)).edges, e ∉ (run.Z0 G r a).sym2) ∧
        run.guests G r a ⊆ run.D G r ∧
        run.D G r ⊆ run.DupStar G r)

/-- [s2:lemGC] (iv) "`θ^GC_r(Z^0) > τ_r` for every round-`r` pre-part `Z`." (Lemma [s2:lemTower]
(c); hypothesis `Gamma1core Dstar`, the part of the standing assumption on `D_*` that
[s2:lemTower] uses.) -/
def GCThetaStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r, run.tau G r < run.thetaGC G r a

end EG.Spec
