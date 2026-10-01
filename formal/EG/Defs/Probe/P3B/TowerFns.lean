module

public import EG.Defs.Log

/-!
# The functions `𝖺`, `𝖻`, `𝖼` of the tower facts (manuscript s6, before s6:thmCONC)

NEW DEFS FILE of probe unit P3B (probe P-3, part 2). The three functions are defined in the text of
`s6.tex` between Definition [s6:defDesign] and Theorem [s6:thmCONC] and are read by the displayed
facts (s6:eqTowerHalf) and (s6:eqTowerEnd); no locked Defs file provides them (blueprint s6a,
`s6:thmCONC`, "defs_needed": `towerA`, `towerB`, `towerC`). Design note
`formal/work/p2b/P3B.md`.

Manuscript v6.1, `s6.tex`:
"For `d ≥ D_*` put
`𝖺(d) := (2 log* d + 2)/log d`, `𝖻(d) := (2 log* d + 1)/log log d`,
`𝖼(d) := (2 log* d + 1)/(log d)^{1/2}`."
("All logarithms are to base `2`.")

Formal reading.
* `log = Real.logb 2`, `log* = EG.logStar` (`EG.Defs.Log`, cast to `ℝ`), `(log d)^{1/2}` is
  `Real.rpow` with the exponent `(1 : ℝ) / 2` (the same form as in `EG.Chain.epsCONC`).
* The functions are total in `d`; the manuscript defines them for `d ≥ D_*` only, and every
  statement reading them assumes `d ≥ D_*` under Γ1 (then `log log d ≥ 2^8`, so all denominators
  are positive). Values for small `d` are junk and unused.
* Names `towA`, `towB`, `towC` (namespace `EG.Chain`); `towerC` is not used because `EG.towerC`
  is the declared-input theorem of [s2:lemTower] (c) and `EG.tower` is the tower function
  `T_k`.
-/

@[expose] public section

namespace EG.Chain

/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem) "`𝖺(d) := (2 log* d + 2)/log d`". -/
noncomputable def towA (d : ℝ) : ℝ := (2 * (logStar d : ℝ) + 2) / Real.logb 2 d

/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem) "`𝖻(d) := (2 log* d + 1)/log log d`". -/
noncomputable def towB (d : ℝ) : ℝ := (2 * (logStar d : ℝ) + 1) / Real.logb 2 (Real.logb 2 d)

/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem) "`𝖼(d) := (2 log* d + 1)/(log d)^{1/2}`". -/
noncomputable def towC (d : ℝ) : ℝ := (2 * (logStar d : ℝ) + 1) / Real.logb 2 d ^ ((1 : ℝ) / 2)

end EG.Chain
