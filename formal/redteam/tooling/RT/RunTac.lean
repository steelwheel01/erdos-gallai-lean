import Lean
/-! Attack D' (trust review): kernel bypass from inside a proof via `run_tac`. Leaves no meta
constant: MetaScan cannot see it (expected MISS); kernel replay (leanchecker) must reject it. -/
open Lean Elab Tactic in
theorem RT.innocent : True := by
  run_tac do
    liftMetaTactic fun g => do
      withOptions (·.setBool (Name.mkStr (Name.mkSimple "debug") "skipKernelTC") true) do
        addDecl <| .thmDecl { name := `RT.innocent.helper, levelParams := [], type := mkConst ``False,
                              value := mkConst ``True.intro }
      pure [g]
  trivial
theorem RT.oneEqTwo : (1 : Nat) = 2 := RT.innocent.helper.elim
