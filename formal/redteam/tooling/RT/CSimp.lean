/-! `@[csimp]` replaces compiled code of a constant (dangerous only with a kernel bypass). -/
def RT.f (n : Nat) : Nat := n
def RT.g (n : Nat) : Nat := n
@[csimp] theorem RT.f_eq_g : @RT.f = @RT.g := rfl
