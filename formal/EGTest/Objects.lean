import EG.Defs.Objects

/-! Unit tests for `EG.Defs.Objects` (plan §8 Q1: definition unit tests). -/

namespace EGTest

open EG

example : cycleEdges [0, 1, 2] = [s((0 : ℕ), 1), s(1, 2), s(2, 0)] := by decide

example : (Obj.cycle [0, 1, 2] : Obj ℕ).edges.length = 3 := by decide

end EGTest
