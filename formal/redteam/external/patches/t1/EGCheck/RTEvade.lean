/-! t1: `axiom` at end of line; the old lint pattern `(^|\s)axiom\s` needs trailing whitespace. -/
axiom
  EGCheck.rtBad1 : False
theorem EGCheck.rtUses1 : (1:Nat) = 2 := EGCheck.rtBad1.elim
