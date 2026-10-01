module

public import EG.Lib.Prob.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Conditioning a product law on a product event

`(pi μ).cond {f | ∀ i, f i ∈ A i} = pi (fun i => (μ i).cond (A i))`: conditioning independent
coordinates on an event that is an intersection of events of the single coordinates keeps them
independent, with the conditioned marginals. Used for [s7:lemCC] (i): "the junction of the
`κ`-end at a port `x` is a function of `≺_x` alone, and the orders of distinct ports are
independent. So conditioning on `(I_x)_x` keeps the partner ends independent, and it conditions the
partner end at `v_o` only on the event `I_{v_o} = 0`."
-/

public section

namespace EG

namespace FinDist

open Finset

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} (μ : ∀ i, FinDist (κ i))

theorem prob_pi_forall (A : ∀ i, Set (κ i)) :
    (pi μ).prob {f | ∀ i, f i ∈ A i} = ∏ i, (μ i).prob (A i) := by
  rw [← prob_pi_univ_pi]
  congr 1
  ext f
  simp [Set.mem_pi]

/-- If the product event has positive probability, every factor does. -/
theorem prob_pos_of_prob_pi_pos (A : ∀ i, Set (κ i))
    (hA : 0 < (pi μ).prob {f | ∀ i, f i ∈ A i}) (i : ι) : 0 < (μ i).prob (A i) := by
  rw [prob_pi_forall] at hA
  rcases (μ i).prob_nonneg (A i) |>.eq_or_lt with h | h
  · exfalso
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h.symm] at hA
    exact lt_irrefl _ hA
  · exact h

/-- Conditioning a product law on a product event gives the product of the conditioned
marginals. -/
theorem pi_cond_forall (A : ∀ i, Set (κ i)) (hA : 0 < (pi μ).prob {f | ∀ i, f i ∈ A i}) :
    (pi μ).cond {f | ∀ i, f i ∈ A i} hA =
      pi (fun i => (μ i).cond (A i) (prob_pos_of_prob_pi_pos μ A hA i)) := by
  classical
  ext f
  rw [cond_w, pi_w, prob_pi_forall]
  simp only [cond_w]
  rw [Finset.prod_div_distrib]
  congr 1
  by_cases h : ∀ i, f i ∈ A i
  · rw [Set.indicator_of_mem (show f ∈ {f | ∀ i, f i ∈ A i} from h), pi_w]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (h i) _).symm
  · rw [Set.indicator_of_notMem (show f ∉ {f | ∀ i, f i ∈ A i} from h)]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- A variable uniform on a finite set `C` (`|C| ≥ 2`), conditioned on avoiding `w`, is uniform
on `C \ {w}` ([s7:lemCC] (i) "Given `I_{v_o} = 0` it is therefore uniform on `C(v_o) \ {w}`"). -/
theorem cond_uniform_erase {Ω V : Type*} [DecidableEq V] (ν : FinDist Ω) (X : Ω → Option V)
    (C : Finset V) (hsome : ∀ σ, ∃ u ∈ C, X σ = some u)
    (hunif : ∀ u ∈ C, ν.prob {σ | X σ = some u} = 1 / (C.card : ℝ)) (hC2 : 2 ≤ C.card)
    (w w' : V) :
    ν.prob ({σ | X σ = some w'} ∩ {σ | X σ ≠ some w}) / ν.prob {σ | X σ ≠ some w} =
      if w' ∈ C.erase w then 1 / ((C.erase w).card : ℝ) else 0 := by
  classical
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast lt_of_lt_of_le (by norm_num) hC2
  have hC2r : (2 : ℝ) ≤ C.card := by exact_mod_cast hC2
  have hzero : ∀ u ∉ C, ν.prob {σ | X σ = some u} = 0 := by
    intro u hu
    rw [prob_eq_zero_iff]
    intro σ hσ
    obtain ⟨u', hu', he⟩ := hsome σ
    simp only [Set.mem_ofPred_eq] at hσ
    rw [hσ] at he
    exact absurd (Option.some.inj he ▸ hu') hu
  have hnotw : ν.prob {σ | X σ ≠ some w} = 1 - (if w ∈ C then 1 / (C.card : ℝ) else 0) := by
    have e : {σ | X σ ≠ some w} = {σ | X σ = some w}ᶜ := by ext σ; simp
    rw [e, prob_compl]
    split_ifs with hw
    · rw [hunif w hw]
    · rw [hzero w hw, sub_zero]
  have hcard : ((C.erase w).card : ℝ) = C.card - (if w ∈ C then 1 else 0) := by
    split_ifs with hwC
    · rw [Finset.card_erase_of_mem hwC, Nat.cast_sub (Finset.card_pos.2 ⟨w, hwC⟩)]; simp
    · rw [Finset.erase_eq_of_notMem hwC]; simp
  by_cases hw' : w' ∈ C.erase w
  · rw [if_pos hw']
    obtain ⟨hne, hw'C⟩ := Finset.mem_erase.1 hw'
    have hinter : {σ | X σ = some w'} ∩ {σ | X σ ≠ some w} = {σ | X σ = some w'} := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · intro h; refine ⟨h, ?_⟩; rw [h]; simpa using hne
    rw [hinter, hunif w' hw'C, hnotw, hcard]
    split_ifs with hwC
    · have : (C.card : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    · simp only [sub_zero, div_one]
  · rw [if_neg hw']
    have hinter : {σ | X σ = some w'} ∩ {σ | X σ ≠ some w} = ∅ := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩
      apply hw'
      obtain ⟨u, hu, he⟩ := hsome σ
      rw [h1] at he
      cases Option.some.inj he
      exact Finset.mem_erase.2 ⟨fun h => h2 (h ▸ h1), hu⟩
    rw [hinter, prob_empty, zero_div]

end FinDist

end EG
