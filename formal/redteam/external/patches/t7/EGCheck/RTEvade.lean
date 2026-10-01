/-! t7: the tokens the lint is supposed to catch (control fixture). -/
def EGCheck.rtFoo (n : Nat) : Nat := n
def EGCheck.rtBar (n : Nat) : Nat := n
attribute [implemented_by EGCheck.rtFoo] EGCheck.rtBar
@[extern "rt_x"] def EGCheck.rtBaz (n : Nat) : Nat := n
theorem EGCheck.rt7nd : True := by native_decide
