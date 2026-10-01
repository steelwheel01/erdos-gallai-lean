module

public import EG.Spec.Found.EulerMulti
public import EG.Lib.Found.EulerMulti

/-!
# Cited result s1:citEuler (b), multigraph form

Formerly a declared input of probe unit P4B (design note `formal/work/p2b/P4B.md`), used by
s5:lemParent Step 3 (through `EG.Spec.ArcClassEulerStatement`). Proved in P3 (unit P3-s1) by
the maximal-trail argument, `EG.MTrail.EulerProof.exists_eulerian` (`EG/Lib/Found/EulerMulti.lean`).
-/

public section

namespace EG

/-- [s1:citEuler] (b) "A connected graph (or multigraph) in which every vertex has even degree has
a closed trail using every edge exactly once." Proved in P3 (`EG.MTrail.EulerProof.exists_eulerian`). -/
theorem eulerMulti : EG.Spec.EulerMultiStatement :=
  fun _ _ _ _ E ends hE hconn heven => MTrail.EulerProof.exists_eulerian E ends hE hconn heven

end EG
