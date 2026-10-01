import EG.Spec.Link.Monotone
import EG.Spec.Link.Multiset
import EG.Spec.Link.Star
import EG.Spec.Link.P13s
import EG.Spec.Link.L17s
import EG.Spec.Link.P18s
import EG.Lib.Link.Star
import EG.Lib.Prob.Indep
import EG.Lib.Prob.Basic
import EG.Lib.Found.Graph

/-! Cheap non-vacuity and fidelity checks for the s3a Specs written by the P2 s3a Spec unit
(`EG/Spec/Link/{Monotone,Multiset,Star,P13s,L17s,P18s}.lean`; `formal/work/p2s/s3a.md`).

* The (eqStar) domain hypotheses (`n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `1 ≤ t`) are
  satisfiable (`n = 2`, `ε' = ρ = t = 1`).
* `StarS1Statement`, `StarS2PStatement`, `StarS6Statement` and `StarP13sParamsStatement` are
  proved from the Lib API of the locked Defs (`EG/Lib/Link/Star.lean`): the statements agree with
  the definitions (fidelity of the `0.9`/`9/10` literal, of the `ℕ` exponent `ℓ_* − 1`, and of the
  P13* hypothesis form).
* The hypotheses of `StarUnionLawStatement` are satisfiable: the product space
  `pi (i ↦ rsubset S p_i)` with the coordinate layers.
* The hypotheses of `MultisetCountStatement` are satisfiable (one pair, `I = I' = {0}`, `t = 1`),
  and its conclusion holds there.
* The random-set hypothesis `IsRSubset R G.verts ρ` of `L17sStatement` / `P18sStatement` is
  satisfiable (`rsubset` itself).
* The parameter hypotheses of `P13sStatement` other than expansion are satisfiable, and each of
  its two alternatives is satisfiable (so the conclusion is not contradictory by encoding).
* The hypotheses of `MonotoneStatement` (iii) (joint routing) are satisfiable for the empty
  family.

Not checked: joint satisfiability of the expansion hypotheses with the other hypotheses. For
`P13sStatement` and `L17sStatement` this needs an `(ε',s₁)`-expander with `s₁ ≥ 8d_*λ_* ≥ 8` on
`n ≥ 2` vertices (e.g. a large complete graph; no cheap library example with `s > 0`), and for
`P18sStatement` an expander with `s₁ ≥ θ_* + 1 > 2^{39}` (only exists for huge `n`); well-expanding
nonempty `U` needs `n > θ_*`.
-/

open EG EG.FGraph EG.FinDist

namespace EGTest.Spec_s3a

/-! ### (eqStar) -/

/-- The (eqStar) domain hypotheses are satisfiable. -/
example : 2 ≤ (2 : ℕ) ∧ (2 : ℝ) ^ (-7 : ℤ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧
    (1 : ℝ) ≤ 1 := by
  refine ⟨le_rfl, ?_, le_rfl, one_pos, le_rfl, le_rfl⟩
  rw [zpow_neg, zpow_ofNat]; norm_num

/-- (S1) holds for the locked definitions (fidelity check). -/
theorem starS1 : Spec.StarS1Statement := fun n hn =>
  ⟨Star.lt_ell n, Star.ell_le n, Star.two_pow_ten_le_ell hn⟩

/-- (S2), existence and uniqueness, holds for the locked definitions (fidelity check). -/
theorem starS2P : Spec.StarS2PStatement := by
  intro n ρ hn h0 h1
  have h09 : (0.9 : ℝ) = 9 / 10 := by norm_num
  rw [h09]
  exact ⟨⟨Star.p_pos hn h0 h1, Star.p_le_one h1, Star.one_sub_p_pow hn h1⟩,
    fun x _ hx1 hx => Star.p_unique hn h1 hx1 hx⟩

/-- The hypotheses of `StarUnionLawStatement` are satisfiable: independent layers on the product
space, layer `i` being `p_*`-random (`i + 1 < ℓ_*`) or `q_*`-random (the last one). -/
example {α : Type} [DecidableEq α] (S : Finset α) (n : ℕ) (ρ : ℝ) (hn : 2 ≤ n) (h0 : 0 < ρ)
    (h1 : ρ ≤ 1) :
    let pr : Fin (Star.ell n) → ℝ := fun i =>
      if (i : ℕ) + 1 < Star.ell n then Star.p n ρ else Star.q ρ
    ∃ (h0' : ∀ i, 0 ≤ pr i) (h1' : ∀ i, pr i ≤ 1),
      let μ := pi (fun i => rsubset S (pr i) (h0' i) (h1' i))
      μ.iIndepFun (fun i (ω : Fin (Star.ell n) → Finset α) => ω i) ∧
      ∀ i : Fin (Star.ell n), μ.IsRSubset (fun ω => ω i) S (pr i) := by
  intro pr
  have hp0 := (Star.p_pos hn h0 h1).le
  have hp1 := Star.p_le_one (n := n) h1
  have hq0 := (Star.q_pos h0).le
  have hq1 : Star.q ρ ≤ 1 := by unfold Star.q; linarith
  have h0' : ∀ i, 0 ≤ pr i := fun i => by
    simp only [pr]; split_ifs <;> assumption
  have h1' : ∀ i, pr i ≤ 1 := fun i => by
    simp only [pr]; split_ifs <;> assumption
  exact ⟨h0', h1', iIndepFun_eval_pi _, fun i => ⟨h0' i, h1' i, map_eval_pi _ i⟩⟩

/-- The parameter hypotheses of Proposition 13* are satisfiable at the (eqStar) values: the
statement `StarP13sParamsStatement` has satisfiable hypotheses (shown above) and all its
conclusions mention only locked definitions. Here: the hypotheses of `P13sStatement` other than
expansion, `W`, `F`, hold for `σ = 24`, `λ = d = 1`, `Δ = 1 + 1`, `n = 2` (`L = 1`), `ε' = 1`. -/
example : 0 < (24 : ℝ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ (1 : ℕ) ≤ 2 ∧
    24 * Real.logb 2 ((2 : ℕ) : ℝ) ^ 2 / 1 ≤ (24 : ℝ) ∧
    8 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * Real.logb 2 ((2 : ℕ) : ℝ) ^ 2 / (1 * 24) ≤
      ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) := by
  have hL : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    push_cast; exact Real.logb_self_eq_one (by norm_num)
  rw [hL]
  refine ⟨by norm_num, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num⟩

/-- (S6) holds for the locked definitions (fidelity check). -/
theorem starS6 : Spec.StarS6Statement := by
  intro n ε' ρ hn hε7 hε1 h0 h1
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε7
  have hL := Star.one_le_L hn
  have hp := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := n) h1
  refine ⟨?_, ?_, ?_, ?_, by linarith⟩
  · unfold Star.sigma
    rw [le_div_iff₀ hε]
    nlinarith [one_le_pow₀ (n := 2) hL]
  · have := Star.six_div_p_le_lam n ρ
    rw [div_le_iff₀ hp] at this; linarith
  · have := Star.one_div_p_le_d n ρ
    rw [div_le_iff₀ hp] at this; linarith
  · have := Star.d_lt hn h0 h1
    have h2 : (Star.d n ρ : ℝ) * Star.p n ρ ≤ (1 / Star.p n ρ + 1) * Star.p n ρ :=
      mul_le_mul_of_nonneg_right this.le hp.le
    rw [add_mul, one_div, inv_mul_cancel₀ hp.ne'] at h2
    linarith

/-- The parameter hypotheses of Proposition 13* hold at the (eqStar) values (fidelity check of
`StarP13sParamsStatement` against the locked definitions). -/
theorem starP13sParams : Spec.StarP13sParamsStatement := by
  intro n ε' ρ hn hε7 hε1 h0 h1
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε7
  have hL := Star.L_pos hn
  have hLe : Star.L n = Real.logb 2 (n : ℝ) := rfl
  have hσ : Star.sigma n ε' = 24 * Real.logb 2 (n : ℝ) ^ 2 / ε' := rfl
  have heq : (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) / 3 =
      8 * (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) * Real.logb 2 (n : ℝ) ^ 2 /
        (ε' * Star.sigma n ε') := by
    rw [hσ, ← hLe]
    field_simp
    ring
  refine ⟨hσ, Star.dlam_div_three_le n ρ, heq, Star.sigma_pos hn hε, Star.one_le_lam hn h0 h1,
    Star.one_le_d hn h0 h1, Star.lam_le_Delta n ρ, hσ.ge, ?_⟩
  rw [← heq]; exact Star.dlam_div_three_le n ρ

/-! ### Proposition 13*: both alternatives are satisfiable -/

section P13s

/-- The path `0 — 1 — 2` on `Fin 3`. -/
def P3 : FGraph (Fin 3) where
  verts := Finset.univ
  edges := {s(0, 1), s(1, 2)}
  edge_verts _ _ _ _ := Finset.mem_univ _
  loopless e he := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp

/-- Alternative (a) of Proposition 13* is satisfiable: `W = {1}`, one star with centre `1` and
leaves `{0, 2}` (`λ = 2`), `F = ∅`. -/
example : ∃ (C : Finset (Fin 3)) (lv : Fin 3 → Finset (Fin 3)), C ⊆ {1} ∧
    (({1} : Finset (Fin 3)).card : ℝ) / 1 ≤ (C.card : ℝ) ∧
    (∀ c ∈ C, (lv c).card = 2 ∧ lv c ⊆ P3.verts \ {1} ∧
      ∀ x ∈ lv c, (P3.deleteEdges ∅).Adj c x) ∧
    (C : Set (Fin 3)).PairwiseDisjoint lv := by
  refine ⟨{1}, fun _ => {0, 2}, subset_rfl, by simp, ?_, by simp⟩
  intro c hc
  simp only [Finset.mem_singleton] at hc
  subst hc
  refine ⟨by decide, by decide, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> decide

/-- Alternative (b) of Proposition 13* is satisfiable: `W = {1}`, `X = {0, 2}`, `H = P3`, `d = 1`,
`Δ = 2`, `F = ∅`. -/
example : ∃ (X : Finset (Fin 3)) (H : FGraph (Fin 3)), X ⊆ P3.verts \ {1} ∧
    H ≤ P3.deleteEdges ∅ ∧ H.verts = {1} ∪ X ∧ H.edges ⊆ P3.edgesBetween {1} X ∧
    (1 : ℝ) * (({1} : Finset (Fin 3)).card : ℝ) / (2 * 1 ^ 2) ≤ (X.card : ℝ) ∧
    (∀ x ∈ X, H.deg x = 1) ∧ (∀ w ∈ ({1} : Finset (Fin 3)), H.deg w ≤ 2) := by
  refine ⟨{0, 2}, P3, by decide, ⟨subset_rfl, by simp [deleteEdges]⟩, by decide, by decide,
    by rw [show ({0, 2} : Finset (Fin 3)).card = 2 by decide]; norm_num, by decide, by decide⟩

end P13s

/-! ### Remark on multisets: the counting step -/

/-- The hypotheses of `MultisetCountStatement` are satisfiable (one pair `(0, 1)`, `t = 1`,
`I = I' = {0}`), and the conclusion `|I| ≤ 2t|I'|` holds there. -/
example :
    let P : Fin 1 → Fin 2 × Fin 2 := fun _ => (0, 1)
    (∀ i, (P i).1 ≠ (P i).2) ∧
    (∀ v : Fin 2, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ 1) ∧
    ({0} : Finset (Fin 1)) ⊆ {0} ∧
    (({0} : Finset (Fin 1)) : Set (Fin 1)).PairwiseDisjoint
      (fun i => ({(P i).1, (P i).2} : Finset (Fin 2))) ∧
    (∀ i ∈ ({0} : Finset (Fin 1)), i ∉ ({0} : Finset (Fin 1)) →
      ¬ (insert i (({0} : Finset (Fin 1)) : Set (Fin 1))).PairwiseDisjoint
        (fun j => ({(P j).1, (P j).2} : Finset (Fin 2)))) ∧
    ((({0} : Finset (Fin 1)).card : ℝ) ≤ 2 * 1 * (({0} : Finset (Fin 1)).card : ℝ)) := by
  intro P
  refine ⟨fun _ => by decide, ?_, subset_rfl, by simp, by simp, by norm_num⟩
  intro v
  have : (Finset.univ.filter (fun i : Fin 1 => (P i).1 = v ∨ (P i).2 = v)).card ≤ 1 :=
    (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-! ### Random-set hypotheses of Lemma 17* and Lemma 19* -/

/-- The hypothesis `μ.IsRSubset R G.verts ρ` of `L17sStatement` and `P18sStatement` (ii) is
satisfiable, on the space `rsubset V(G) ρ` with `R = id`. -/
example {V : Type} [DecidableEq V] (G : FGraph V) (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (rsubset G.verts ρ h0.le h1).IsRSubset (fun T => T) G.verts ρ :=
  isRSubset_rsubset h0.le h1

/-- The event of Lemma 19* is not contradictory by encoding: on the graph without vertices the
quantified statement holds vacuously (`U = ∅` is excluded by `U.Nonempty`). -/
example {V : Type} [DecidableEq V] (ℓ : ℕ) (μ' : ℝ) :
    let G : FGraph V := ⟨∅, ∅, by simp, by simp⟩
    ∀ U : Finset V, U.Nonempty → U ⊆ G.verts → ∀ F : Finset (Sym2 V), F ⊆ G.edges →
      (F.card : ℝ) ≤ μ' * (U.card : ℝ) →
      ((∅ : Finset V).card : ℝ) / 2 < ((ball (G.deleteEdges F) ℓ U ∅).card : ℝ) := by
  intro G U hU hUG
  obtain ⟨x, hx⟩ := hU
  exact absurd (hUG hx) (by simp [G])

/-! ### Monotonicity lemma (iii): joint routing hypotheses -/

/-- The hypotheses of the joint-routing conjunct of `MonotoneStatement` are satisfiable (the
empty family, `κ = Empty`). -/
example {V : Type} [DecidableEq V] (X : FGraph V) :
    let P : ∀ k : Empty, (fun _ => Unit) k → V × V := fun k => k.elim
    (∀ k i, (P k i).1 ∈ X.verts ∧ (P k i).2 ∈ X.verts ∧ (P k i).1 ≠ (P k i).2) ∧
    (∀ v : V,
      ((∑ k, (Finset.univ.filter (fun i => (P k i).1 = v ∨ (P k i).2 = v)).card : ℕ) : ℝ) ≤ 0) := by
  intro P
  exact ⟨fun k => k.elim, fun v => by simp⟩

end EGTest.Spec_s3a
