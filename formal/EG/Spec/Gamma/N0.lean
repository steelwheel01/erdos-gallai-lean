module

public import EG.Defs.Gamma.Full
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Statements: the size threshold `N_0` exists (manuscript s1:defConstants (ii))

PROTECTED FILE (`EG/Spec/**`): statement file. Proofs: `EG/Lib/Vortex/Size.lean`
(`EG.Vortex.eventually_size`), `EG/Proof/Gamma/N0.lean`. Design note: `formal/work/p2b/GAMMA.md`.

Manuscript v6.1, `s1.tex`, Definition [s1:defConstants] (ii) (quoted in full in
`EG/Defs/Gamma/Full.lean`): "… Every requirement on `N_0` in this item is an *eventuality*: it
holds for every sufficiently large value of `N_0`. Indeed `N_0 ≥ 2^{40}` is a lower bound, and
every other requirement asks that an explicit inequality in `N`, which holds for all sufficiently
large `N`, hold for every `N ≥ N_0`. So such an `N_0` exists (finitely many eventualities have a
common threshold), and only its existence is used".

The size conditions are those of the three vortex proofs, `EG.Vortex.TPVSize`, `PVSize`,
`VXSize` (s4 proofs of Lemma TPV, Lemma PV, Theorem VX⁺, "Size conditions. We use: (i)
`L ≥ 2^{10}`; (ii) `N ≥ L^3`; (iii) `4β ≤ L` (a consequence of (i)); (iv) `η(N) ≤ 1/100`").
-/

@[expose] public section

namespace EG.Spec

open Filter

/-- [s1:defConstants] (ii) "every other requirement asks that an explicit inequality in `N`,
which holds for all sufficiently large `N`, hold for every `N ≥ N_0`": the size conditions of the
proofs of Lemma s4:lemTPV, Lemma s4:lemPV and Theorem s4:thmVXp hold for all sufficiently large
vertex counts `N`. (Required Lib lemma `EG.Vortex.eventually_size`, TRIAGE §3 item 14.) -/
def VortexEventuallySizeStatement : Prop :=
  ∀ᶠ N : ℕ in atTop, Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N

/-- [s1:defConstants] (ii) "Every requirement on `N_0` in this item is an *eventuality*: it holds
for every sufficiently large value of `N_0`." -/
def N0EventuallyStatement : Prop :=
  ∀ᶠ N0 : ℝ in atTop, N0Cond N0

/-- [s1:defConstants] (ii) "So such an `N_0` exists (finitely many eventualities have a common
threshold)". (Lean name of the proof: `EG.exists_N0`.) -/
def N0ExistsStatement : Prop :=
  ∃ N0 : ℝ, N0Cond N0

end EG.Spec
