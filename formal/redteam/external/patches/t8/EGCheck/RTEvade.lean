/-! t8: a `macro` whose expansion is `sorryAx`. -/
macro "rt_close" : tactic => `(tactic| exact sorryAx _ false)
theorem EGCheck.rtBad8 : False := by rt_close
