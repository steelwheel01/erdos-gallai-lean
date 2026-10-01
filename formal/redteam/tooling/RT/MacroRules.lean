import Lean
/-! A macro for an existing (builtin) syntax kind. -/
macro_rules | `(tactic| trivial) => `(tactic| exact sorry)
