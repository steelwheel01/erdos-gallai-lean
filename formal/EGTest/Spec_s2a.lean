import EG.Spec.HB.HS
import EG.Spec.HB.CapRound
import EG.Spec.HB.HBtpFacts
import EGTest.HB
import EGTest.Found

/-! Cheap non-vacuity checks for the new s2a Specs (`EG/Spec/HB/{HS,CapRound,HBtpFacts}.lean`;
`formal/work/p2s/s2a.md`).

* Lemma HS: all hypotheses of `HSStatement` and `HSCorStatement` hold for the complete graph `K₁₁`
  (a `(2^{-5}, 0)`-expander on 11 vertices, proved below) with `W = ∅`, `s = s_W = 0`.
* `Round.Valid` (hypothesis of `HBStep1Statement`, `CapRoundStatement`) is satisfiable
  (`EGTest.HB.round_valid`, a round on `K₃`), and `Run.Valid` (hypothesis of
  `AncestorFactsStatement`, `CapRunTauStatement`) is satisfiable (`EGTest.HB.run1_valid`).
* `Gamma2a` is satisfiable.

Not checked here: the joint satisfiability of `Gamma2a Dstar`, `Dstar ≤ d_l` and validity (the
hypotheses of `CapRoundStatement`, `CapRunTauStatement`): it needs a graph of average degree
`≥ 2^{117}` with a valid round on it, i.e. s2:propExists (a statement of chunk s2b); no concrete
example is feasible.
-/

open EG EG.FGraph EG.HB

namespace EGTest.Spec_s2a

/-- The complete graph on 11 vertices. -/
def K11 : FGraph (Fin 11) := ofSimpleGraph ⊤

theorem K11_card : K11.card = 11 := by decide

theorem K11_isExpander : K11.IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 := by
  intro U F hU hF h1 h2 h3
  have hF0 : F = ∅ := by
    rw [zero_mul] at h3
    exact Finset.card_eq_zero.1 (by exact_mod_cast le_antisymm h3 (Nat.cast_nonneg _))
  subst hF0
  have hK : ∀ u ∈ K11.verts, ∀ v ∈ K11.verts, u ≠ v → K11.Adj u v := fun u _ v _ huv => by
    rw [K11, ofSimpleGraph_adj]; exact huv
  rw [deleteEdges_empty, EGTest.nbrSet_of_complete hK hU (Finset.card_pos.1 (by omega)),
    Finset.card_sdiff_of_subset hU]
  have hcard : K11.verts.card = 11 := by decide
  rw [card_def, hcard] at h2 ⊢
  have hU7 : U.card ≤ 7 := by
    have : (U.card : ℝ) < 8 := by push_cast at h2; linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hlog : 1 ≤ Real.logb 2 ((11 : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = Real.logb 2 2 from (Real.logb_self_eq_one (by norm_num)).symm]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have hlog2 : 1 ≤ Real.logb 2 ((11 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hlog
  have hsub : ((11 - U.card : ℕ) : ℝ) ≥ 4 := by
    have : 4 ≤ 11 - U.card := by omega
    exact_mod_cast this
  have hUr : (U.card : ℝ) ≤ 7 := by exact_mod_cast hU7
  have hnum : (0 : ℝ) ≤ (2 : ℝ) ^ (-5 : ℤ) * U.card := by positivity
  calc (2 : ℝ) ^ (-5 : ℤ) * U.card / Real.logb 2 ((11 : ℕ) : ℝ) ^ 2
      ≤ (2 : ℝ) ^ (-5 : ℤ) * U.card := div_le_self hnum hlog2
    _ ≤ 4 := by rw [zpow_neg, zpow_ofNat]; norm_num; linarith
    _ ≤ ((11 - U.card : ℕ) : ℝ) := hsub

/-- The hypotheses of `EG.Spec.HSStatement` are satisfiable (`X = K₁₁`, `W = ∅`,
`ε' = 2^{-5}`, `s = s_W = 0`). -/
example : ∃ (X : FGraph (Fin 11)) (W : Finset (Fin 11)) (ε' s sW : ℝ),
    0 < ε' ∧ 0 ≤ s ∧ 11 ≤ X.card ∧ X.IsExpander ε' s ∧ W ⊆ X.verts ∧
    (W.card : ℝ) ≤ (X.card : ℝ) / 2 ∧ sW ≤ s ∧
    (∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ sW) :=
  ⟨K11, ∅, _, 0, 0, by positivity, le_rfl, K11_card.ge, K11_isExpander,
    Finset.empty_subset _, by simp; positivity, le_rfl, by simp⟩

/-- The hypotheses of `EG.Spec.HSCorStatement` are satisfiable (`X = K₁₁`, `W = ∅`, `s = 0`). -/
example : ∃ (X : FGraph (Fin 11)) (W : Finset (Fin 11)) (s : ℝ),
    0 ≤ s ∧ 11 ≤ X.card ∧ X.IsExpander ((2 : ℝ) ^ (-5 : ℤ)) s ∧ W ⊆ X.verts ∧
    (W.card : ℝ) ≤ (X.card : ℝ) / 2 ∧
    (∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ s / 2) :=
  ⟨K11, ∅, 0, le_rfl, K11_card.ge, K11_isExpander, Finset.empty_subset _, by simp; positivity, by simp⟩

/-- `Round.Valid` (hypothesis of `HBStep1Statement` and `CapRoundStatement`) is satisfiable. -/
example : ∃ (H : FGraph (Fin 3)) (c : RoundChoice (Fin 3)), Round.Valid H c :=
  ⟨_, _, EGTest.HB.round_valid⟩

/-- `Run.Valid` (hypothesis of `AncestorFactsStatement` and `CapRunTauStatement`) is satisfiable,
with a run that has one round (`R = 1`), so the round quantifiers are not empty. -/
example : ∃ (G : FGraph (Fin 3)) (run : Run (Fin 3)) (Dstar : ℝ),
    run.Valid G Dstar ∧ run.R = 1 :=
  ⟨_, _, _, EGTest.HB.run1_valid, rfl⟩

/-- `Γ2(a)` is satisfiable. -/
example : Gamma2a ((2 : ℝ) ^ 117) := le_rfl

end EGTest.Spec_s2a
