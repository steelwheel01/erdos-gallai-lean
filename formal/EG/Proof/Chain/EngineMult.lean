module

public import EG.Spec.Chain.EngineMult

/-!
# The engine's multiplicity bounds feeding JS-LC (probe P-2 refutation target)

`EG.jsMultNum : EG.Spec.JsMultNumStatement`: the numeric part (`⌈(M−1)/2⌉ ≤ ⌈M/2⌉ ≤ M − 1`,
`max(2M − 2, (M − 1) + ⌈M/2⌉) = 2M − 2 < 2M + 2` for `M ≥ 2`). The engine part
(`EG.Spec.HccpEndMultStatement`) is proved in stage 2 of the probe. Probe unit P2E, design note
`formal/work/p2b/P2E.md`.
-/

public section

namespace EG

/-- `⌈M/2⌉₊ = (M + 1) / 2` for natural `M` (the real ceiling of `M/2`). -/
theorem natCeil_natCast_div_two (M : ℕ) : ⌈(M : ℝ) / 2⌉₊ = (M + 1) / 2 := by
  rcases Nat.even_or_odd M with ⟨r, hr⟩ | ⟨r, hr⟩
  · subst hr
    have h1 : (r + r + 1) / 2 = r := by omega
    rw [h1]
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp
    · rw [Nat.ceil_eq_iff (by omega)]
      have : (↑(r - 1) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub h]; simp
      rw [this]; push_cast
      constructor <;> linarith
  · subst hr
    have h1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    rw [h1, Nat.ceil_eq_iff (by omega)]
    simp only [Nat.add_sub_cancel]; push_cast
    constructor <;> linarith

/-- `⌈(M−1)/2⌉₊ = M / 2` for natural `M ≥ 1`. -/
theorem natCeil_natCast_sub_one_div_two {M : ℕ} (hM : 1 ≤ M) :
    ⌈((M : ℝ) - 1) / 2⌉₊ = M / 2 := by
  have h : ((M : ℝ) - 1) = ((M - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hM]; simp
  rw [h, natCeil_natCast_div_two]
  omega

/-- [s6:lemJSLC:proof-claim-c] (proof of [s6:lemJSLC], joint-routing claim (c), numeric part)
"For `M_l ≥ 2`,
`⌈M_l/2⌉ ≤ M_l − 1`, so both are at most `2M_l − 2 < t = 2M_l + 2`" (and
`pad(u) ≤ ⌈(M_l − 1)/2⌉ ≤ ⌈M_l/2⌉`). -/
theorem jsMultNum : EG.Spec.JsMultNumStatement := by
  intro M hM
  rw [natCeil_natCast_sub_one_div_two (by omega), natCeil_natCast_div_two]
  refine ⟨by omega, by omega, by omega, ?_, by omega⟩
  rw [max_eq_left (by omega)]
