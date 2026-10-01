module

public import EG.Spec.Gamma.N0
public import EG.Lib.Gamma.Full
public import EG.Lib.Vortex.Size

/-!
# `N_0` exists (manuscript s1:defConstants (ii)): reductions

Unit GAMMA, design note `formal/work/p2b/GAMMA.md`. Manuscript v6.1, `s1.tex`,
Definition [s1:defConstants] (ii): "Every requirement on `N_0` in this item is an *eventuality*:
it holds for every sufficiently large value of `N_0`. Indeed `N_0 ≥ 2^{40}` is a lower bound,
and every other requirement asks that an explicit inequality in `N`, which holds for all
sufficiently large `N`, hold for every `N ≥ N_0`. So such an `N_0` exists (finitely many
eventualities have a common threshold)".

The two steps of this argument are reductions to the eventuality of the size conditions
(`EG.Spec.VortexEventuallySizeStatement`, proved as the Lib lemma `EG.Vortex.eventually_size`
in `EG/Lib/Vortex/Size.lean`). The final theorems `EG.vortexEventuallySize`,
`EG.eventually_N0Cond` and `EG.exists_N0` follow from these reductions and that lemma.
No `sorry`.
-/

public section

namespace EG

open Filter

/-- [s1:defConstants] (ii) "Indeed `N_0 ≥ 2^{40}` is a lower bound, and every other requirement
asks that an explicit inequality in `N`, which holds for all sufficiently large `N`, hold for
every `N ≥ N_0`": the eventuality of the size conditions in `N` gives the eventuality of
`N0Cond` in `N_0`. -/
theorem n0Eventually_of_size (h : Spec.VortexEventuallySizeStatement) :
    Spec.N0EventuallyStatement := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  filter_upwards [eventually_ge_atTop (max ((2 : ℝ) ^ 40) (M : ℝ))] with N0 hN0
  refine ⟨le_trans (le_max_left _ _) hN0, fun N hN => hM N ?_⟩
  exact_mod_cast (le_max_right _ _).trans (hN0.trans hN)

/-- [s1:defConstants] (ii) "So such an `N_0` exists". -/
theorem n0Exists_of_eventually (h : Spec.N0EventuallyStatement) : Spec.N0ExistsStatement :=
  h.exists

/-- [s1:defConstants] (ii) "every other requirement asks that an explicit inequality in `N`,
which holds for all sufficiently large `N`, hold for every `N ≥ N_0`" (the Lib lemma
`EG.Vortex.eventually_size`, TRIAGE §3 item 14). -/
theorem vortexEventuallySize : Spec.VortexEventuallySizeStatement := Vortex.eventually_size

/-- [s1:defConstants] (ii) "Every requirement on `N_0` in this item is an *eventuality*: it holds
for every sufficiently large value of `N_0`." -/
theorem eventually_N0Cond : Spec.N0EventuallyStatement :=
  n0Eventually_of_size vortexEventuallySize

/-- [s1:defConstants] (ii) "So such an `N_0` exists (finitely many eventualities have a common
threshold)". -/
theorem exists_N0 : Spec.N0ExistsStatement := n0Exists_of_eventually eventually_N0Cond

end EG
