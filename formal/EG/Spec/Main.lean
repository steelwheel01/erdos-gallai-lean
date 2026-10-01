module

public import EG.Defs.Objects

/-!
# Internal main theorem statement (PLAN_FORMALIZATION.md §3, design decision 8)

PROTECTED FILE (`EG/Spec/**`): frozen statement. `EG/Proof/Main.lean` proves it;
`EGCheck/Bridge.lean` transports it to `Erdos184.erdos_184`.
-/

@[expose] public section


namespace EG.Spec

/-- Every finite simple graph on `n` vertices decomposes into at most `c * n` objects. -/
def MainInternal : Prop :=
  ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V

end EG.Spec
