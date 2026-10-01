module

public import EG.Defs.HB.Run

/-!
# Statement of Lemma EL, edge laminarity (manuscript s2:lemEL) — declared input of unit P3A

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). This statement is a DECLARED INPUT
of the probe: [s2:lemGC] (iii) cites it, and the probe does not prove it; the stub is
`EG.edgeLaminarity` in `EG/Proof/HB/EL.lean`. Justification: design note
`formal/work/p2b/P3A.md`, "Declared inputs".

Manuscript v6.1, `s2.tex`, Lemma [s2:lemEL]:
"For every ancestor `Y` of round `r` and every round `l > r`, no edge of `G_l` has both ends in
`V(Y)`."

Formal reading.
* "For every ancestor `Y` of round `r`" of a valid run: `Y ∈ run.ancestors G` (a `PartId`
  `(r, a)` with `a` a round-`r` pre-part address; `r = Y.1`), with `V(Y) = run.ancVerts G Y`
  (`Y^0 \ S_Y` for a light part, `Y^0` for a standalone pre-part, [s2:defAncestors]).
* "every round `l > r`": every natural number `l > r`. This includes the stopping round
  `l = R + 1` (whose graph carries `E_0`) and, in Lean, every `l > R + 1`, where `G_l` is
  stationary (`run.graph G l = run.graph G (R + 1)`; blueprint EL-STATIONARY), so the statement
  is the manuscript's statement plus copies of the case `l = R + 1`.
* "no edge of `G_l` has both ends in `V(Y)`": `e ∉ (V(Y)).sym2` for every `e ∈ E(G_l)`.
* No hypothesis on `D_*` (the lemma holds for every valid run).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemEL] "For every ancestor `Y` of round `r` and every round `l > r`, no edge of `G_l` has
both ends in `V(Y)`." (For every valid run; module docstring.) -/
def ELStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G, ∀ l : ℕ, Y.1 < l →
      ∀ e ∈ (run.graph G l).edges, e ∉ (run.ancVerts G Y).sym2

end EG.Spec
