module

public import EG.Spec.Ext.Cor22
public import EG.Lib.Ext.Cor22
public import EG.Proof.Todo.Lovasz

/-!
# Corollary 22 of Bucić–Montgomery (manuscript s1:citCor22)

Formerly a declared-input stub of unit P4A (design note `formal/work/p2b/P4A.md`, "Declared
inputs"). Proved in P3 (unit P3-s1) from Lovász's theorem ([s1:citThm21], the stub
`EG.Todo.Lovasz`) by [BM]'s argument, `EG.Cor22.cor22_of_lovasz` (`EG/Lib/Ext/Cor22.lean`).
-/

public section

namespace EG

/-- [s1:citCor22] "Every graph can be decomposed into paths such that each
vertex is an end of at most two of the paths." Proved in P3 from Lovász's theorem
([s1:citThm21], `EG.Todo.Lovasz`) by [BM]'s argument (`EG.Cor22.cor22_of_lovasz`). -/
theorem cor22 : EG.Spec.Cor22Statement :=
  fun _ _ F hF => Cor22.cor22_of_lovasz EG.Todo.Lovasz F hF

end EG
