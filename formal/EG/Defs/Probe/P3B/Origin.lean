module

public import EG.Defs.HB.Run

/-!
# The edge types (α), (β) of Proposition ORIGIN^τ (manuscript s2:propOrigin)

NEW DEFS FILE of probe unit P3B (probe P-3, part 2). It adds the two statement-shape predicates of
Proposition ORIGIN^τ that no locked Defs file provides (blueprint s2b, `s2:propOrigin`,
"defs_needed": `TypeBeta`, `TypeAlpha`; hazard OR-TYPE-DEF); design note `formal/work/p2b/P3B.md`.

Manuscript v6.1, `s2.tex`, Proposition [s2:propOrigin] (a):
"Fix a valid `HB*^{τ+}` run, a round `r ≤ R`, a round-`r` pre-part `Y` and a vertex
`u ∈ Y^0 \ Dup*_r`. … Every edge `ux` of `G_{r+1}` is of exactly one of the following two types:
(β) `x ∉ Y^0`, and `ux` was deleted by the `τ`-run of `𝒫` (so `x ∈ V(𝒫)`);
(α) `Y` is light, `x ∈ S_Y`, and `ux ∈ E(X^0_Y)` (a *guest–core edge*: it is not deleted and not
assigned at round `r`, and passes down)."
Here `𝒫` is "the unique `s = 0` piece" containing `u` (and `Y^0 ⊆ V(𝒫)`).

Formal reading.
* The pre-part `Y` is its address `a` in the two-level recursion of round `r`
  (`a ∈ run.prePartAddrs G r`); `Y^0 = run.Z0 G r a`, `S_Y = run.guests G r a`,
  `X^0_Y = run.X0 G r a`.
* "the `τ`-run of `𝒫`": `𝒫` is the piece above the pre-part, `run.pieceOf r a` (the leaf of the
  `s = 0` recursion on the path `a`, `EG.HB.STree.leafPrefix`); its `τ`-run is the tree
  `run.tauRun r (run.pieceOf r a)` rooted at the piece graph `run.piece G r (run.pieceOf r a)`.
  That the piece containing `u` is this piece is a conclusion of `OriginTypesStatement`, not
  part of the definition.
* "`ux` was deleted by the `τ`-run of `𝒫`" is membership in the deleted set
  (`EG.HB.STree.deleted`, the union of the sets `F''_ν` of the non-leaf nodes) of that `τ`-run, as
  the blueprint requires (OR-TYPE-DEF: not "`ux ∈ F''` of some node of the two-level recursion";
  the two agree because the first level deletes nothing, a lemma).
* The parenthetical consequences ("so `x ∈ V(𝒫)`"; "it is not deleted and not assigned at round
  `r`, and passes down") are not part of the predicates; `x ∈ V(𝒫)` is a conclusion of
  `OriginTypesStatement`.
* Both predicates are total (every run, round, address, `u`, `x`); they are read by the Specs only
  under the hypotheses above. The edge is `s(u, x)` (`Sym2`, so `s(u, x) = s(x, u)`).
-/

@[expose] public section

namespace EG.HB.Run

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V)

/-- [s2:propOrigin] (a) "(β) `x ∉ Y^0`, and `ux` was deleted by the `τ`-run of `𝒫`": for the
pre-part at address `a` of round `r`, `x ∉ Y^0` and `s(u, x)` lies in the deleted set of the
`τ`-run of the piece `run.pieceOf r a` above `a` (rooted at the piece graph). -/
def OriginBeta (r : ℕ) (a : Addr) (u x : V) : Prop :=
  x ∉ run.Z0 G r a ∧
    s(u, x) ∈ (run.tauRun r (run.pieceOf r a)).deleted (run.piece G r (run.pieceOf r a))

/-- [s2:propOrigin] (a) "(α) `Y` is light, `x ∈ S_Y`, and `ux ∈ E(X^0_Y)`": for the pre-part at
address `a` of round `r`. -/
def OriginAlpha (r : ℕ) (a : Addr) (u x : V) : Prop :=
  run.isLight G r a ∧ x ∈ run.guests G r a ∧ s(u, x) ∈ (run.X0 G r a).edges

end EG.HB.Run
