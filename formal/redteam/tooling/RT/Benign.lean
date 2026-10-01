/-! Benign constructs a proof may use: MetaScan and lint must report nothing. -/
namespace RT
structure S where
  a : Nat
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable
inductive T | x | y
  deriving Repr, DecidableEq
instance : ToString S := ⟨fun s => toString s.a⟩
def f (n : Nat) : {m : Nat // m > n} := ⟨n + 1, by omega⟩
theorem t (h' : 1 = 1) (c' : Nat) : c' + 0 = c' := by simp
theorem u : (3 : Nat) ∣ 6 := by decide
set_option maxHeartbeats 400000 in
theorem v : ∀ n : Nat, n + 0 = n := fun n => rfl
def ch : Char := '"'
def str : String := "-- /- not a comment"
end RT
