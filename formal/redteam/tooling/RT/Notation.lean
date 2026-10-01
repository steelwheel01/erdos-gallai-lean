/-! Even a `local notation` leaves a macro and a parser constant (both `meta`). -/
local notation "⟪" x "⟫" => x + 1
theorem RT.t : ⟪(1 : Nat)⟫ = 2 := rfl
