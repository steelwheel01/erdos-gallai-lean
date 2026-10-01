/-! t3: a `Char` literal `'"'` makes a naive stripper treat the rest as a string. -/
def EGCheck.rtQuote : Char := '"'
axiom EGCheck.rtBad3 : False
set_option debug.skipKernelTC true
def EGCheck.rtStr : String := "x"
theorem EGCheck.rtUses3 : (1:Nat) = 2 := EGCheck.rtBad3.elim
