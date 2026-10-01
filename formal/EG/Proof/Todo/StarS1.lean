module

public import EG.Spec.Link.Star
public import EG.Lib.Link.Star

/-!
# P3 stub: `EG.Spec.StarS1Statement` (s3:eqS1)

Generated at the P2→P3 transition (2026-09-30). Proved in P3 from the floor bounds of
`EG/Lib/Link/Star.lean`. Keep the name `EG.Todo.StarS1`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:eqS1] see `EG.Spec.StarS1Statement`. -/
theorem StarS1 : EG.Spec.StarS1Statement := by
  intro n hn
  exact ⟨Star.lt_ell n, Star.ell_le n, Star.two_pow_ten_le_ell hn⟩

end EG.Todo
