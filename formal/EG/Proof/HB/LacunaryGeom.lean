module

public import EG.Spec.HB.LacunaryGeom
public import EG.Lib.HB.Lacunary

/-!
# Declared-input stub of unit P3B: Lemma "tower-lacunary sums" (i) (manuscript s2:lemLacunary (i))

The tower sums of [s6:thmCONC] (iii) and [s6:thmCONCL] (iv) apply [s2:lemLacunary] (i) to
`X_r = 𝖺(d_r)`, `𝖻(d_r)`, `𝖼(d_r)`. It is not a node of probe P-3 (owner: the s2 lacunary unit;
the full Lacunary Spec must import `EG/Spec/HB/LacunaryGeom.lean`). It is elementary (induction
`X_r ≤ 2^{-(R-r)} X_R` and two geometric series), and P3B can discharge it in stage 2 if the
orchestrator assigns it. Justification: design note `formal/work/p2b/P3B.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:lemLacunary] (i) "If `X_1, …, X_R ≥ 0` and `X_r ≤ X_{r+1}/2` for all
`r < R`, then `Σ_{r ≤ R} X_r ≤ 2X_R` and `Σ_{r ≤ R} (R-r+1) X_r ≤ 4X_R`." Owner: s2 lacunary
unit (blueprint s2b, `LacunaryGeomStatement`). -/
theorem lacunaryGeom : EG.Spec.LacunaryGeomStatement := EG.HB.lacGeom

end EG
