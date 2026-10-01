import Lean
/-! `initialize`: code that runs whenever the module is imported with initializers enabled. -/
initialize RT.counter : IO.Ref Nat ← IO.mkRef 0
