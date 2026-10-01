module

public import EG.Defs.Probe.P3B.Origin

/-!
# Statement of Proposition ORIGIN^τ (manuscript s2:propOrigin), parts (a), (b) and the final
paragraph

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). Design note
`formal/work/p2b/P3B.md`. Definitions: `EG/Defs/HB/Run.lean` (locked) and the new probe Defs
`EG/Defs/Probe/P3B/Origin.lean` (`Run.OriginBeta`, `Run.OriginAlpha`).

Manuscript v6.1, `s2.tex`, Proposition [s2:propOrigin] (ORIGIN^τ):
"Fix a valid `HB*^{τ+}` run, a round `r ≤ R`, a round-`r` pre-part `Y` and a vertex
`u ∈ Y^0 \ Dup*_r`.
(a) `u` lies in a unique `s = 0` piece `𝒫` and in a unique leaf of the two-level recursion, namely
`Y` (so `Y^0 ⊆ V(𝒫)`). Every edge `ux` of `G_{r+1}` is of exactly one of the following two types:
(β) `x ∉ Y^0`, and `ux` was deleted by the `τ`-run of `𝒫` (so `x ∈ V(𝒫)`);
(α) `Y` is light, `x ∈ S_Y`, and `ux ∈ E(X^0_Y)` (a *guest–core edge*: it is not deleted and not
assigned at round `r`, and passes down).
A standalone `Y` (GC-parts included) has no edges of type (α). Since `E(G_l) ⊆ E(G_{r+1})` for
`l > r`, the same classification applies to the edges `ux` of `G_l`.
(b) For every vertex `h` and every round `l > r`,
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l) is of type (β)} ≤ τ_r - 1`.
(c) `Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n / log P_r`, the sum over all round-`r` pre-parts `Y`.
An edge of type (α) has its core end `u` outside `Dup*_r` (it is not true that (α)-edges occur
only at vertices of `Dup*_r`); a guest `x` of a light `Y` is the guest end of fewer than
`θ^GC_r(Y^0)` edges of type (α) (Lemma [s2:lemGC](ii)); and there is no third type."

Formal reading.
* "a valid run": `run.Valid G Dstar` for some `D_*`; no hypothesis on `D_*` (blueprint s2b
  OR-THINCUT-NO-GAMMA: (a), (b) and the final paragraph hold for every valid run, since
  `s_r < τ_r` holds for every `d` by (R2), `M_r ≥ 2^{40}`). Rounds are 1-indexed:
  `r ∈ Finset.Icc 1 run.R`; the pre-part `Y` is its address `a ∈ run.prePartAddrs G r`;
  `Y^0 = run.Z0 G r a`, `Dup*_r = run.DupStar G r`, `S_Y = run.guests G r a`,
  `X^0_Y = run.X0 G r a`, `τ_r = run.tau G r`, `θ^GC_r(Y^0) = run.thetaGC G r a`.
* The `s = 0` pieces are the leaf addresses `run.pieceAddrs r` of the first-level tree with graphs
  `run.piece G r q`; "the unique piece `𝒫` containing `u`" is stated as: the piece above `a`
  (`run.pieceOf r a`) is a piece, and a piece contains `u` iff it is that piece. The leaves of the
  two-level recursion are `(run.twoLevel G r).leafAddrs` with vertex sets `run.Z0 G r b`
  (`Z0` is the vertex set of the leaf graph at address `b`, for every leaf, not only pre-parts);
  "a unique leaf, namely `Y`" is: a leaf contains `u` iff it is `a`. Leaves and pieces are
  addresses (distinct leaves with equal vertex sets are distinct, [s2:lemSEP]).
* (β), (α) are `run.OriginBeta G r a u x`, `run.OriginAlpha G r a u x` (probe Defs). "Exactly
  one" is an exclusive disjunction (blueprint OR-EXACTLY-ONE); the parenthetical "(so
  `x ∈ V(𝒫)`)" is a conjunct of the (β) branch. Of the parenthetical of (α) ("it is not deleted
  and not assigned at round `r`, and passes down"), "not deleted" is a conjunct of the (α) branch:
  `ux` is not in the deleted set of the `τ`-run of `𝒫` (a consequence of `ux ∈ E(X^0_Y)` and
  [s2:lemSEP](i); it is not implied by `¬ (β)`, which holds trivially in the (α) branch since
  `x ∈ S_Y ⊆ Y^0`). "Not assigned at round `r`, and passes down" is the hypothesis
  `ux ∈ E(G_{r+1})` (resp. `E(G_l)`) itself and is not restated (fix round 1, review C2).
* "A standalone `Y` (GC-parts included) has no edges of type (α)" (last conjunct of
  `OriginTypesStatement`): this clause holds by definition, since `Run.OriginAlpha` contains
  `run.isLight G r a` (a one-term proof, `fun h hα => h hα.1`); the TeX sentence is equally
  definitional ("(α) `Y` is light, …"). It is kept for fidelity (fix round 1, review C1).
* "the same classification applies to the edges `ux` of `G_l`": the classification is stated for
  every `l > r` (every natural number; `G_l` is stationary for `l ≥ R + 1`); `l = r + 1` is the
  first sentence.
* (b): "`≤ τ_r - 1`" is the natural-number subtraction; `τ_r ≥ 1` for every `d`
  (`τ_r = ⌈128 s_r log² M_r⌉` with `s_r ≥ 1`, `M_r ≥ 2^{40}`), so no truncation occurs. "every
  vertex `h`" ranges over all of `V`. The edge "`hu` of type (β)" is `run.OriginBeta G r a u h`
  (core end `u`, other end `h`).
* (c) is (K3) of [s2:propOV] (blueprint OR-C-POINTER: "do not restate"); it is the declared input
  `EG.Spec.OVK3Statement` (`EG/Spec/HB/OVRunK.lean`), which carries `Gamma2a`.
* The final paragraph: the first and last clauses are the setting of (a) and the exhaustiveness
  of (a); the middle clause is `OriginGuestCapStatement`: for a light `Y`, a guest `x ∈ S_Y` and
  a round `l > r`, fewer than `θ^GC_r(Y^0)` vertices `u ∈ Y^0 \ Dup*_r` have `ux ∈ E(G_l)` of type
  (α). (Distinct `u` give distinct edges `ux`, so this counts the edges.)
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propOrigin] (a) "`u` lies in a unique `s = 0` piece `𝒫` and in a unique leaf of the
two-level recursion, namely `Y` (so `Y^0 ⊆ V(𝒫)`). Every edge `ux` of `G_{r+1}` is of exactly one
of the following two types: (β) `x ∉ Y^0`, and `ux` was deleted by the `τ`-run of `𝒫` (so
`x ∈ V(𝒫)`); (α) `Y` is light, `x ∈ S_Y`, and `ux ∈ E(X^0_Y)` (a *guest–core edge*: it is not
deleted and not assigned at round `r`, and passes down). A standalone `Y` (GC-parts included) has
no edges of type (α). Since `E(G_l) ⊆ E(G_{r+1})` for `l > r`, the same classification applies to
the edges `ux` of `G_l`." (For every valid run, round `r ≤ R`, round-`r` pre-part `Y` and
`u ∈ Y^0 \ Dup*_r`; module docstring. The (α) branch also states "not deleted" by the `τ`-run of
`𝒫`. The last conjunct, "standalone ⇒ no (α)-edges", holds by definition: `Run.OriginAlpha`
contains `run.isLight`.) -/
def OriginTypesStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r,
      ∀ u ∈ run.Z0 G r a \ run.DupStar G r,
        run.pieceOf r a ∈ run.pieceAddrs r ∧
        (∀ q ∈ run.pieceAddrs r, u ∈ (run.piece G r q).verts ↔ q = run.pieceOf r a) ∧
        (∀ b ∈ (run.twoLevel G r).leafAddrs, u ∈ run.Z0 G r b ↔ b = a) ∧
        run.Z0 G r a ⊆ (run.piece G r (run.pieceOf r a)).verts ∧
        (∀ l : ℕ, r < l → ∀ x : V, s(u, x) ∈ (run.graph G l).edges →
          (run.OriginBeta G r a u x ∧ x ∈ (run.piece G r (run.pieceOf r a)).verts ∧
              ¬ run.OriginAlpha G r a u x) ∨
            (run.OriginAlpha G r a u x ∧ ¬ run.OriginBeta G r a u x ∧
              s(u, x) ∉ (run.tauRun r (run.pieceOf r a)).deleted
                (run.piece G r (run.pieceOf r a)))) ∧
        (¬ run.isLight G r a → ∀ l : ℕ, r < l → ∀ x : V, s(u, x) ∈ (run.graph G l).edges →
          ¬ run.OriginAlpha G r a u x)

open Classical in
/-- [s2:propOrigin] (b) "For every vertex `h` and every round `l > r`,
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l) is of type (β)} ≤ τ_r - 1`." (For every valid run, round
`r ≤ R` and round-`r` pre-part `Y`.) -/
def OriginThinStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r, ∀ h : V, ∀ l : ℕ, r < l →
      ((run.Z0 G r a \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges ∧ run.OriginBeta G r a u h)).card ≤
        run.tau G r - 1

open Classical in
/-- [s2:propOrigin] (final paragraph) "a guest `x` of a light `Y` is the guest end of fewer than
`θ^GC_r(Y^0)` edges of type (α) (Lemma [s2:lemGC](ii))": for a light round-`r` pre-part `Y`, a
guest `x ∈ S_Y` and a round `l > r`, fewer than `θ^GC_r(Y^0)` vertices `u ∈ Y^0 \ Dup*_r` have
`ux ∈ E(G_l)` of type (α). (For every valid run.) -/
def OriginGuestCapStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r, run.isLight G r a →
      ∀ x ∈ run.guests G r a, ∀ l : ℕ, r < l →
        ((run.Z0 G r a \ run.DupStar G r).filter
            (fun u => s(u, x) ∈ (run.graph G l).edges ∧ run.OriginAlpha G r a u x)).card <
          run.thetaGC G r a

end EG.Spec
