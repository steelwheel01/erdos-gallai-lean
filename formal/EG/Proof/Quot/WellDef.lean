module

public import EG.Spec.Quot.WellDef
public import EG.Lib.Quot.Quotient

/-!
# Proof of Lemma "The round step is well defined" (manuscript s7:lemWellDef) — probe P-1

Unit P1 (probe P-1), design note `formal/work/p2b/P1.md`. Parts (i), (ii), (iv), (v); part (iii)
is in `EG/Proof/Quot/Cuckoo.lean`. The fold invariants are in `EG/Lib/Quot/Colour.lean` ((b)),
`EG/Lib/Quot/Junction.lean` ((e1)) and `EG/Lib/Quot/E2.lean` ((e2)).

(ii) "If `h` is non-ultra then `c^live_h ≤ θ^ult_l ≤ M_l Hcd_l/7`, so
`k_h = ⌈8c^live_h/Hcd_l⌉ ≤ ⌈8M_l/7⌉`. Hence `3k_h ≤ 3(8M_l/7 + 1) = 24M_l/7 + 3 ≤ 4M_l`, because
`M_l ≥ 21/4`." Here `Hcd_l > 0` and `M_l ≥ 2^40` come from `RoundInput.Valid`.
-/

public section

namespace EG

open EG.Quot

/-- [s7:lemWellDef] (ii) *Disjoint lists.* "Every non-ultra hub `h` has `k_h ≤ ⌈8M_l/7⌉` and
`3k_h ≤ 4M_l`." -/
theorem wellDefLists : EG.Spec.WellDefListsStatement := by
  intro V _ I hI h _ hnu
  have hM : (2 : ℝ) ^ 40 ≤ (I.M : ℝ) := by exact_mod_cast hI.M_ge
  have hMpos : (0 : ℝ) < I.M := lt_of_lt_of_le (by positivity) hM
  have hH : 0 < I.Hcd :=
    lt_of_lt_of_le (by positivity) hI.Hcd_ge
  -- `c^live_h ≤ θ^ult_l ≤ M_l Hcd_l / 7`
  have hc : (I.clive h : ℝ) ≤ (I.M : ℝ) * I.Hcd / 7 := by
    have h1 : I.clive h ≤ I.thult := not_lt.1 hnu
    have h2 : (I.thult : ℝ) ≤ (I.M : ℝ) * I.Hcd / 7 := by
      show ((⌊(I.M : ℝ) * I.Hcd / 7⌋₊ : ℕ) : ℝ) ≤ _
      exact Nat.floor_le (by positivity)
    exact le_trans (by exact_mod_cast h1) h2
  have hk : 8 * (I.clive h : ℝ) / I.Hcd ≤ 8 * (I.M : ℝ) / 7 := by
    rw [div_le_iff₀ hH]
    have : 8 * (I.M : ℝ) / 7 * I.Hcd = 8 * ((I.M : ℝ) * I.Hcd / 7) := by ring
    rw [this]
    linarith
  have hk1 : I.kh h ≤ ⌈8 * (I.M : ℝ) / 7⌉₊ := Nat.ceil_mono hk
  refine ⟨hk1, ?_⟩
  have hk2 : (I.kh h : ℝ) < 8 * (I.M : ℝ) / 7 + 1 :=
    lt_of_le_of_lt (by exact_mod_cast hk1) (Nat.ceil_lt_add_one (by positivity))
  have : (3 * I.kh h : ℝ) < 4 * (I.M : ℝ) := by nlinarith
  exact_mod_cast this.le

/-- [s7:lemWellDef] (i) *PAR palette.* "Every PAR object shares a port or a middle with fewer than
`3M_l` other PAR objects, so the greedy colouring of (b) succeeds. Consequently every port carries
at most one PAR object of each colour, and every fresh centre is the middle of at most one cherry
of each colour." -/
theorem wellDefPar : EG.Spec.WellDefParStatement := by
  intro V _ I hI R hR
  refine ⟨fun o ho => ?_, fun o ho => Rules.parColour_some hI hR ho,
    fun u κ => Rules.card_parObjs_end_colour_le hI hR u κ,
    fun x κ => Rules.card_parObjs_middle_colour_le hI hR x κ⟩
  exact Rules.card_conflicts_lt hI hR ho

/-- [s7:lemWellDef] (iv) *Greedy step.* "Step (e1) always finds a junction. Two coloured items of
the same non-ultra hub `h` with the same colour `κ` receive distinct junctions." -/
theorem wellDefE1 : EG.Spec.WellDefE1Statement := by
  intro V _ I hI R hR L
  have hsome : ∀ it ∈ R.e1Items L, ∃ w, (R.e1State L).junc it = some w ∧ w ∈ I.cand it.2 := by
    intro it hit
    obtain ⟨w, hw⟩ := Rules.e1_junc_some hI hR L hit
    exact ⟨w, hw, Rules.e1_junc_cand hw⟩
  refine ⟨hsome, fun it hit it' hit' hne hh hc heq => ?_⟩
  obtain ⟨w, hw, -⟩ := hsome it hit
  have hinv := Rules.e1Inv_e1State (R := R) L
  unfold Rules.E1Inv at hinv
  exact hinv.2.2 it it' w hne hh hc hw (heq ▸ hw)

/-- [s7:lemWellDef] (v) *Injections.* "At every port `u` carrying a live item,
`|Cand_l(u) \ Used(u)| ≥ Hcd_l − (M_l − 1) ≥ Hcd_l/2 ≥ M_l > |E'(u)|`, so step (e2) is well
defined." -/
theorem wellDefE2 : EG.Spec.WellDefE2Statement := by
  intro V _ I hI R hR ξ u hu hlive
  obtain ⟨h1, h2, h3, h4⟩ := Rules.wellDefE2_ineqs hI hR ξ hu hlive
  exact ⟨h1, h2, h3, h4, fun e he => Rules.e2Junc_some hI hR ξ hu hlive he⟩

end EG
