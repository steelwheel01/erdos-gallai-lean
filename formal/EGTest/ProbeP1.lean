import EGTest.Quot
import EG.Spec.Quot.Simple
import EG.Spec.Quot.MULT
import EG.Spec.Quot.WellDef
import EG.Spec.Quot.Lift
import EG.Proof.Quot.WellDef

/-! Non-vacuity checks for the statements of probe unit P1 (probe P-1: s7 lift, `Q_l` simple,
MULT, WellDef; design note `formal/work/p2b/P1.md`).

Every round-level statement of the unit (`QuotSimpleStatement`, `MultStatement`,
`MultSublayerStatement`, `ParMultSublayerStatement`, `WellDefParStatement`,
`WellDefListsStatement`, `CuckooSDRStatement`, `WellDefE1Statement`, `WellDefE2Statement`,
`LiftRolesStatement`, `LiftDecompStatement`, `LiftAccountingStatement`,
`LiftJConsumerStatement`) has the hypotheses `I.Valid` and `R.Valid`, plus some of: a port `u`
(carrying a live item), a non-ultra hub `h`, a pooled vertex `w` of pool round `r`, a HUB colour
`κ < 4M`, a decomposition `Dec` of `E(Q_l)`. All of them hold on the valid input
`EGTest.Quot.Live.I` of `EGTest/Quot.lean` (hub `0`, port `1`, `Pool_l = [2, 2^500)`,
`M = 2^40`, one live `J^hub` item `01`) with the chosen valid rules and every `ξ`; its quotient has
an edge for every `ξ` (`Live.Q_nonempty`), so the statements about `Q_l` are not about the empty
graph. The proved part (ii) is evaluated on the instance.

Not checked here: the run-level statements `MultRunStatement` and `LiftJConsumerRunStatement`
need a valid run with `R ≥ 3` (the only valid run in the tests, `EGTest.HB.run1`, has `R = 1`); see
the design note, "Hazards". -/

namespace EGTest.ProbeP1

open EG EG.Quot EGTest.Quot.Live

noncomputable section

/-- The chosen fixed rules of the valid input `Live.I`. -/
def R0 : Rules I := I.chosenRules

theorem R0_valid : R0.Valid := RoundInput.chosenRules_valid I_valid

/-- The common hypotheses of every round-level statement of the unit hold. -/
example : I.Valid ∧ R0.Valid := ⟨I_valid, R0_valid⟩

theorem one_mem_ports : (1 : ℕ) ∈ I.ports := by simp [I]

theorem zero_mem_hubs : (0 : ℕ) ∈ I.hubs := by simp [I]

theorem two_mem_pool : (2 : ℕ) ∈ I.pool := by
  simp only [I, Finset.mem_Ico]
  exact ⟨le_rfl, two_lt_N⟩

/-- `CuckooSDRStatement`, `WellDefE2Statement`: a port carrying a live item. -/
example : (1 : ℕ) ∈ I.ports ∧ ∃ e ∈ I.live, (1 : ℕ) ∈ e :=
  ⟨one_mem_ports, s(0, 1), by rw [I_live]; exact Finset.mem_singleton_self _, Sym2.mem_mk_right _ _⟩

/-- `WellDefListsStatement`: a non-ultra hub. -/
example : (0 : ℕ) ∈ I.hubs ∧ ¬ I.ultra 0 := ⟨zero_mem_hubs, I_not_ultra⟩

/-- `WellDefListsStatement` (proved, `EG.wellDefLists`) on the instance: `k_0 = 1`. -/
example : I.kh 0 ≤ ⌈8 * (I.M : ℝ) / 7⌉₊ ∧ 3 * I.kh 0 ≤ 4 * I.M :=
  wellDefLists ℕ I I_valid 0 zero_mem_hubs I_not_ultra

example : I.kh 0 = 1 := I_kh

/-- `MultStatement`, `MultSublayerStatement`, `ParMultSublayerStatement`: a HUB colour `κ = 0`
(`< 4M` and `< 3M`), the hub `0`, the pooled vertex `2` of pool round `1`. -/
example : (0 : ℕ) < 4 * I.M ∧ (0 : ℕ) < 3 * I.M ∧ (0 : ℕ) ∈ I.hubs ∧ (2 : ℕ) ∈ I.pool ∧
    I.poolRound 2 = 1 :=
  ⟨by simp [I], by simp [I], zero_mem_hubs, two_mem_pool, rfl⟩

/-- `LiftDecompStatement`: for every `ξ`, `Dec_l = R0.dec ξ` is a decomposition of `E(Q_l)` into
cycles and single edges. -/
example (ξ : Xi I.G I.M) : IsDecomp ((R0.Q ξ).edges : Set (Sym2 (QVert ℕ))) (R0.dec ξ) :=
  (R0_valid.dec ξ).1

/-- For every `ξ` the quotient has an edge (so `Q_l`, `Dec_l` and the lift are not empty). -/
example (ξ : Xi I.G I.M) : (R0.Q ξ).edges.Nonempty := Q_nonempty R0 R0_valid ξ

/-- The statements are propositions (parse checks). -/
example : List Prop :=
  [EG.Spec.QuotSimpleStatement, EG.Spec.MultStatement, EG.Spec.MultSublayerStatement,
    EG.Spec.ParMultSublayerStatement, EG.Spec.MultRunStatement, EG.Spec.WellDefParStatement,
    EG.Spec.WellDefListsStatement, EG.Spec.CuckooSDRStatement, EG.Spec.WellDefE1Statement,
    EG.Spec.WellDefE2Statement, EG.Spec.LiftRolesStatement, EG.Spec.LiftDecompStatement,
    EG.Spec.LiftAccountingStatement, EG.Spec.LiftJConsumerStatement,
    EG.Spec.LiftJConsumerRunStatement]

/-- Fix round 1 (review issue C3): conjuncts (3), (4) of `WellDefParStatement` elaborate with the
same `Decidable` instances as conjuncts (2), (5) of `LiftRolesStatement` (checked up to reducible
unfolding, so stage 2 can pass them across without `Finset.filter_congr_decidable`). -/
example (h : EG.Spec.WellDefParStatement) (V : Type) [DecidableEq V] (I : RoundInput V)
    (hI : I.Valid) (R : Rules I) (hR : R.Valid) :
    (∀ (u : V) (κ : ℕ),
      (R.parObjs.filter (fun o => (∃ b, o.endAt b = u) ∧ R.parColour o = some κ)).card ≤ 1) ∧
    (∀ (x : V) (κ : ℕ),
      (R.parObjs.filter (fun o => o.middle = some x ∧ R.parColour o = some κ)).card ≤ 1) := by
  unfold EG.Spec.WellDefParStatement at h
  with_reducible exact ⟨(h V I hI R hR).2.2.1, (h V I hI R hR).2.2.2⟩

end

end EGTest.ProbeP1
