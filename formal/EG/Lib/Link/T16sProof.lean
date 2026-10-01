module

public import EG.Spec.Link.T16s
public import EG.Spec.Link.T16sForced
public import EG.Spec.Link.L15
public import EG.Spec.Link.P18s
public import EG.Spec.Link.L9rho
public import EG.Spec.Link.Star
public import EG.Lib.Link.L17sStep2

/-!
# Theorem 16* (manuscript s3:thmT16s): the assembly — P3-s3

Manuscript v6.1, `s3.tex`, proof of Theorem [s3:thmT16s]: Step 0 (Theorem 16* (b),
`Spec.T16sForcedStatement`), Step 1 (Lemma 15⁺, `Spec.L15pStatement`), Step 2 (Lemma 19*,
`Spec.P18sStatement` (ii), one colour class at a time), Step 3 (Chernoff for `|V|`), Step 4
(assembly through Lemma 9_ρ, `Spec.L9rhoStatement`) and Step 5 (the probability). The auxiliary
colouring is realized on the product space `colouring × μ`; the event depends only on `V`
(`prob_prod_snd`), which is Lemma s3:lemMonotone (iii) in the TeX.
-/

public section

namespace EG.T16sProof

open Finset

universe u v

variable {V : Type u} [DecidableEq V]

/-- The colour class `X_i` of a colouring `c` of `E(X)`, as a graph on `V(X)`. -/
noncomputable def cls (X : FGraph V) {k : ℕ} (c : ↥X.edges → Fin k) (i : Fin k) : FGraph V :=
  X.restrictEdges (FinDist.selectSet X.edges fun e => decide (c e = i))

theorem mem_cls_edges {X : FGraph V} {k : ℕ} {c : ↥X.edges → Fin k} {i : Fin k} {e : Sym2 V} :
    e ∈ (cls X c i).edges ↔ ∃ he : e ∈ X.edges, c ⟨e, he⟩ = i := by
  unfold cls FGraph.restrictEdges
  simp only [Finset.mem_filter, FinDist.mem_selectSet, decide_eq_true_eq]
  constructor
  · rintro ⟨-, he, h⟩; exact ⟨he, h⟩
  · rintro ⟨he, h⟩; exact ⟨he, he, h⟩

/-- Pigeonhole: "The classes partition `E(X)`, so some `i` has `|F ∩ E(X_i)| ≤ |F|/K_*`." -/
theorem exists_class_small (X : FGraph V) {k : ℕ} (hk : 1 ≤ k) (c : ↥X.edges → Fin k)
    (F : Finset (Sym2 V)) : ∃ i : Fin k, (k : ℝ) * ((F ∩ (cls X c i).edges).card : ℝ) ≤ F.card := by
  classical
  have hsum : ∑ i : Fin k, ((F ∩ (cls X c i).edges).card : ℝ) ≤ F.card := by
    have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin k)), ∀ j ∈ (Finset.univ : Finset (Fin k)),
        i ≠ j → Disjoint (F ∩ (cls X c i).edges) (F ∩ (cls X c j).edges) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro e hei hej
      obtain ⟨he, hi⟩ := mem_cls_edges.1 (Finset.mem_inter.1 hei).2
      obtain ⟨he', hj⟩ := mem_cls_edges.1 (Finset.mem_inter.1 hej).2
      exact hij (hi.symm.trans hj)
    have h1 := Finset.card_biUnion hdisj
    have h2 : (Finset.univ.biUnion fun i => F ∩ (cls X c i).edges) ⊆ F :=
      Finset.biUnion_subset.2 fun i _ => Finset.inter_subset_left
    have := Finset.card_le_card h2
    rw [h1] at this
    exact_mod_cast this
  by_contra hno
  push Not at hno
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have := Finset.sum_lt_sum_of_nonempty hne fun i _ => hno i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith

/-- Path connectivity holds vacuously on at most one vertex. -/
theorem isPathConnected_of_card_le_one {X : FGraph V} (hN : X.card ≤ 1) (ℓ t : ℝ) (W : Finset V) :
    X.IsPathConnected ℓ t W := by
  intro ι _ P hP _
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    obtain ⟨h1, h2, h3⟩ := hP i
    exfalso
    have : ({(P i).1, (P i).2} : Finset V) ⊆ X.verts := by
      intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_pair h3] at this
    rw [FGraph.card_def] at hN
    omega
  · rw [not_nonempty_iff] at hι
    exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

/-- [s3:thmT16s] Theorem 16*. -/
theorem t16s (hL15 : Spec.L15pStatement.{u}) (hP18 : Spec.P18sStatement.{u, v})
    (hL9 : Spec.L9rhoStatement.{u}) (hForced : Spec.T16sForcedStatement.{u})
    (hCh : Spec.ChernoffGenStatement.{v, u}) (hS5 : Spec.StarS5Statement) :
    Spec.T16sStatement.{u, v} := by
  intro V _ X ε' s ρ t Ω μ W hε1 hε2 hX h0 h1 ht hW hL2 hs
  classical
  set N := X.card with hNdef
  set L := Real.logb 2 (N : ℝ) with hLdef
  have ht0 : (0 : ℝ) < t := by linarith
  by_cases hN1 : N ≤ 1
  · -- nothing to prove
    have hL0 : L = 0 := by
      rw [hLdef]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hN1 with h | h <;> rw [h] <;> simp
    have hall : μ.prob {ω | X.IsPathConnected ((2 : ℝ) ^ 12 * L ^ 4) t (W ω)} = 1 := by
      rw [FinDist.prob_eq_one_iff]
      intro ω _
      exact isPathConnected_of_card_le_one hN1 _ _ _
    rw [hall, hL0]; simp
  push Not at hN1
  have hN2 : 2 ≤ N := hN1
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hN2r
  have hLeq : Star.L N = L := rfl
  -- Step 0
  obtain ⟨hforce, -⟩ := hForced V X ε' s ρ t hε1 hε2 hX h0 h1 ht hs hN2
  have hρ5 : 1 ≤ ρ ^ (-5 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]; exact one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ h0.le h1)
  have hρ3 : 1 ≤ ρ ^ (-3 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]; exact one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ h0.le h1)
  have hL28 : 1 ≤ L ^ 28 := one_le_pow₀ hL1
  have hL19 : 1 ≤ L ^ 19 := one_le_pow₀ hL1
  have hsN : s < N := by
    obtain ⟨v, hv⟩ : X.verts.Nonempty := Finset.card_pos.1 (by rw [← FGraph.card_def]; omega)
    have h1' := hX.lt_deg hε hN2 hv
    have h2' : (X.deg v : ℝ) < X.card := by exact_mod_cast FGraph.deg_lt_card hv
    linarith
  have hs135 : (2 : ℝ) ^ 135 ≤ s := by
    have : (1 : ℝ) ≤ t * L ^ 28 * ρ ^ (-5 : ℤ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht hL28) hρ5
    have e : (2 : ℝ) ^ 135 * t * L ^ 28 * ρ ^ (-5 : ℤ) = 2 ^ 135 * (t * L ^ 28 * ρ ^ (-5 : ℤ)) := by
      ring
    nlinarith
  have hN30 : 2 ^ 30 ≤ N := by
    have : ((2 ^ 30 : ℕ) : ℝ) ≤ N := by push_cast; nlinarith
    exact_mod_cast this
  have hρN1 : (2 : ℝ) ^ 27 * L ≤ ρ * N := by
    have a1 : L ≤ L ^ (28 / 5 : ℝ) := by
      calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ ≤ L ^ (28 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have a2 : (1 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have a3 : 0 ≤ L ^ (28 / 5 : ℝ) := by positivity
    have : (2 : ℝ) ^ 27 * L ≤ 2 ^ 27 * L ^ (28 / 5 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) := by
      calc (2 : ℝ) ^ 27 * L ≤ 2 ^ 27 * L ^ (28 / 5 : ℝ) * 1 := by rw [mul_one]; gcongr
        _ ≤ _ := by gcongr
    linarith
  have hρN84 : 84 ≤ ρ * N := by nlinarith
  -- `e^{−ρN/8} ≤ N^{-3}`
  have hexp : Real.exp (-(ρ * N / 8)) ≤ (N : ℝ) ^ (-3 : ℤ) := by
    have hlog : Real.log N ≤ L := by
      rw [hLdef, Real.logb]
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
      rw [le_div_iff₀ hl2p]; nlinarith
    have hN0 : (0 : ℝ) < N := by linarith
    have e1 : (N : ℝ) ^ (-3 : ℤ) = Real.exp (-(3 * Real.log N)) := by
      rw [zpow_neg, zpow_ofNat, Real.exp_neg, show (3 : ℝ) * Real.log N = ((3 : ℕ) : ℝ) * Real.log N
        by norm_num, Real.exp_nat_mul, Real.exp_log hN0]
    rw [e1, Real.exp_le_exp]
    have hlN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    nlinarith
  -- (S5)
  obtain ⟨s51, s52, -, -, s55, s56⟩ := hS5 N ε' ρ t hN2 hε1 hε2 h0 h1 ht
  set K := Star.K N ε' ρ t with hKdef
  have hK1 : 1 ≤ K := Star.K_pos hN2 hε h0 ht0
  have : NeZero K := ⟨Star.K_ne_zero hN2 hε h0 ht0⟩
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hθ0 := Star.theta_pos hN2 hε h0
  have h2K : 2 * (K : ℝ) * (Star.theta N ε' ρ + 1) ≤ s := by
    refine s55.trans (le_trans ?_ hs)
    rw [hLeq]
    have hc : (2 : ℝ) ^ (130.6 : ℝ) ≤ 2 ^ 135 := by
      rw [show (2 : ℝ) ^ 135 = (2 : ℝ) ^ (135 : ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have : 0 ≤ t * L ^ 28 * ρ ^ (-5 : ℤ) := by positivity
    nlinarith
  have h40 : 40 * (K : ℝ) * L ≤ s := by rw [← hLeq]; linarith
  have hsK : Star.theta N ε' ρ + 1 ≤ s / (2 * K) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  -- the product space
  set col := FinDist.randColouring (↥X.edges) K with hcol
  set P := col.prod μ with hP
  set good : (↥X.edges → Fin K) → Prop := fun c => ∀ i : Fin K,
    (cls X c i).IsExpander ε' (s / (2 * (K : ℝ))) with hgood
  set Ev : FGraph V → Finset V → Prop := fun H T => ∀ U : Finset V, U.Nonempty → U ⊆ H.verts →
    ∀ F : Finset (Sym2 V), F ⊆ H.edges → (F.card : ℝ) ≤ Star.mu H.card ε' ρ * (U.card : ℝ) →
    (T.card : ℝ) / 2 < ((ball (H.deleteEdges F) (Star.ell H.card) U T).card : ℝ) with hEv
  -- Step 1
  have hA1 : P.prob (Prod.fst ⁻¹' {c | ¬ good c}) ≤ 2 * K * (N : ℝ) ^ (-5 : ℤ) := by
    rw [FinDist.prob_prod_fst]
    have h := (hL15 V X ε' s K hε hε2 h40 hX).2
    have hc : {c : ↥X.edges → Fin K | ¬ good c} = {c | good c}ᶜ := rfl
    rw [hc, FinDist.prob_compl]
    have : col.prob {c | good c} = (FinDist.randColouring (↥X.edges) K).prob {c | ∀ i : Fin K,
        (X.restrictEdges (FinDist.selectSet X.edges fun e => decide (c e = i))).IsExpander ε'
          (s / (2 * (K : ℝ)))} := rfl
    rw [this]; linarith
  -- Step 2 (per class)
  have hA2 : ∀ i : Fin K, P.prob {p | (cls X p.1 i).IsExpander ε' (s / (2 * (K : ℝ))) ∧
      ¬ Ev (cls X p.1 i) (W p.2)} ≤ (N : ℝ) ^ (-6 : ℤ) := by
    intro i
    rw [hP, FinDist.prob_prod]
    refine FinDist.expect_le_of_le _ fun c => ?_
    by_cases hc : (cls X c i).IsExpander ε' (s / (2 * (K : ℝ)))
    · have h18 := (hP18 V (cls X c i) ε' (s / (2 * K)) ρ hc hN2 hε1 hε2 h0 h1 hsK).2 Ω μ W hW
      have hcc : (cls X c i).card = N := rfl
      rw [hcc] at h18
      have hs : Prod.mk c ⁻¹' {p : (↥X.edges → Fin K) × Ω | (cls X p.1 i).IsExpander ε'
          (s / (2 * (K : ℝ))) ∧ ¬ Ev (cls X p.1 i) (W p.2)} ⊆
          {ω | Ev (cls X c i) (W ω)}ᶜ := fun ω hω => hω.2
      refine (FinDist.prob_mono _ hs).trans ?_
      rw [FinDist.prob_compl]
      have : μ.prob {ω | Ev (cls X c i) (W ω)} = μ.prob {ω | ∀ U : Finset V, U.Nonempty →
          U ⊆ (cls X c i).verts → ∀ F : Finset (Sym2 V), F ⊆ (cls X c i).edges →
          (F.card : ℝ) ≤ Star.mu (cls X c i).card ε' ρ * (U.card : ℝ) →
          ((W ω).card : ℝ) / 2 < ((ball ((cls X c i).deleteEdges F) (Star.ell (cls X c i).card)
            U (W ω)).card : ℝ)} := rfl
      rw [this]; exact sub_le_comm.1 h18
    · refine le_trans (le_of_eq ?_) (by positivity)
      rw [FinDist.prob_eq_zero_iff]
      intro ω hω
      exact absurd hω.1 hc
  -- Step 3
  have hA3 : P.prob (Prod.snd ⁻¹' {ω | ((W ω ∩ X.verts).card : ℝ) ≤ (1 - 1 / 2) * (ρ * N)}) ≤
      Real.exp (-(ρ * N / 8)) := by
    rw [FinDist.prob_prod_snd]
    have h := L17sProof.card_inter_le_tail hCh X.verts subset_rfl hW (δ := 1 / 2) (μ₀ := ρ * N)
      (by norm_num) (by norm_num) (by positivity) (le_of_eq rfl)
    refine h.trans (le_of_eq ?_)
    congr 1; ring
  have hA0 : P.prob (Prod.snd ⁻¹' {ω | ¬ W ω ⊆ X.verts}) = 0 := by
    rw [FinDist.prob_prod_snd, FinDist.prob_eq_zero_iff]
    intro ω hω
    by_contra hw
    exact hω (hW.subset_ae ω (lt_of_le_of_ne (μ.w_nonneg ω) (Ne.symm hw)))
  -- Step 4: the deterministic assembly
  have hdet : (Prod.snd ⁻¹' {ω | X.IsPathConnected ((2 : ℝ) ^ 12 * L ^ 4) t (W ω)})ᶜ ⊆
      ((Prod.fst ⁻¹' {c | ¬ good c} ∪ ⋃ i : Fin K, {p : (↥X.edges → Fin K) × Ω |
        (cls X p.1 i).IsExpander ε' (s / (2 * (K : ℝ))) ∧ ¬ Ev (cls X p.1 i) (W p.2)}) ∪
        Prod.snd ⁻¹' {ω | ((W ω ∩ X.verts).card : ℝ) ≤ (1 - 1 / 2) * (ρ * N)}) ∪
        Prod.snd ⁻¹' {ω | ¬ W ω ⊆ X.verts} := by
    rintro ⟨c, ω⟩ hp
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion, not_or,
      not_exists, not_and, not_not, not_le] at hno
    obtain ⟨⟨⟨hg, hev⟩, hWc⟩, hWV⟩ := hno
    have hWc' : ρ * N / 2 ≤ ((W ω).card : ℝ) := by
      rw [Finset.inter_eq_left.2 hWV] at hWc; linarith
    apply hp
    refine (hL9 V X (W ω) ρ t hN30 h0 h1 ht hWV hWc' hρN84).2 ?_
    intro U hU hUV F hFE hFc
    obtain ⟨i, hi⟩ := exists_class_small X hK1 c F
    set Fi := F ∩ (cls X c i).edges with hFi
    have hEi := hev i (hg i)
    have hFic : (Fi.card : ℝ) ≤ Star.mu N ε' ρ * U.card := by
      have hmu0 := Star.mu_pos hN2 hε h0
      have hsb : Star.sbar N ρ t ≤ K * Star.mu N ε' ρ := by
        rwa [div_le_iff₀ hmu0] at s51
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have : (K : ℝ) * Fi.card ≤ K * (Star.mu N ε' ρ * U.card) := by
        calc (K : ℝ) * Fi.card ≤ F.card := hi
          _ ≤ Star.sbar N ρ t * U.card := hFc
          _ ≤ K * Star.mu N ε' ρ * U.card := mul_le_mul_of_nonneg_right hsb hU0
          _ = K * (Star.mu N ε' ρ * U.card) := by ring
      exact le_of_mul_le_mul_left this hK0
    have hb := hEi U hU hUV Fi Finset.inter_subset_right hFic
    refine hb.trans_le ?_
    have hle : (cls X c i).deleteEdges Fi ≤ X.deleteEdges F := by
      refine ⟨subset_rfl, fun e he => ?_⟩
      rw [FGraph.deleteEdges_edges, Finset.mem_sdiff] at he ⊢
      refine ⟨(FGraph.restrictEdges_le (H := X) _).2 he.1, fun heF => he.2 ?_⟩
      exact Finset.mem_inter.2 ⟨heF, he.1⟩
    exact_mod_cast Finset.card_le_card (ball_mono hle)
  -- Step 5: the probability
  have hmain : μ.prob {ω | X.IsPathConnected ((2 : ℝ) ^ 12 * L ^ 4) t (W ω)} =
      P.prob (Prod.snd ⁻¹' {ω | X.IsPathConnected ((2 : ℝ) ^ 12 * L ^ 4) t (W ω)}) :=
    (FinDist.prob_prod_snd (μ := col) (ν := μ) _).symm
  have hsumA2 := (P.prob_iUnion_le _).trans (Finset.sum_le_sum fun i _ => hA2 i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumA2
  have htot := (P.prob_mono hdet).trans ((P.prob_union_le _ _).trans (add_le_add
    ((P.prob_union_le _ _).trans (add_le_add ((P.prob_union_le _ _).trans
      (add_le_add hA1 hsumA2)) hA3)) (le_of_eq hA0)))
  rw [FinDist.prob_compl] at htot
  rw [hmain]
  -- numerics
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hN65 : (N : ℝ) ^ (-6 : ℤ) ≤ (N : ℝ) ^ (-3 : ℤ) :=
    zpow_le_zpow_right₀ hN1r (by norm_num)
  have hN53 : (N : ℝ) ^ (-5 : ℤ) ≤ (N : ℝ) ^ (-3 : ℤ) :=
    zpow_le_zpow_right₀ hN1r (by norm_num)
  set T := t * L ^ 19 * ρ ^ (-3 : ℤ) with hT
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht hL19) hρ3
  have hKT : (K : ℝ) ≤ 2 ^ 84 * T := by
    have := s52; rw [hLeq] at this
    have e : (6 * 2 ^ 81 + 1) * t * L ^ 19 * ρ ^ (-3 : ℤ) = (6 * 2 ^ 81 + 1) * T := by
      rw [hT]; ring
    rw [e] at this
    linarith
  have hN3 : 0 ≤ (N : ℝ) ^ (-3 : ℤ) := by positivity
  have hfin : 2 * K * (N : ℝ) ^ (-5 : ℤ) + K * (N : ℝ) ^ (-6 : ℤ) + Real.exp (-(ρ * N / 8)) + 0 ≤
      2 ^ 86 * T * (N : ℝ) ^ (-3 : ℤ) := by
    have a1 : 2 * (K : ℝ) * (N : ℝ) ^ (-5 : ℤ) ≤ 2 * (2 ^ 84 * T) * (N : ℝ) ^ (-3 : ℤ) := by
      apply mul_le_mul (by linarith) hN53 (by positivity) (by positivity)
    have a2 : (K : ℝ) * (N : ℝ) ^ (-6 : ℤ) ≤ (2 ^ 84 * T) * (N : ℝ) ^ (-3 : ℤ) :=
      mul_le_mul hKT hN65 (by positivity) (by positivity)
    have a3 : Real.exp (-(ρ * N / 8)) ≤ T * (N : ℝ) ^ (-3 : ℤ) := by
      calc Real.exp (-(ρ * N / 8)) ≤ (N : ℝ) ^ (-3 : ℤ) := hexp
        _ = 1 * (N : ℝ) ^ (-3 : ℤ) := (one_mul _).symm
        _ ≤ T * (N : ℝ) ^ (-3 : ℤ) := mul_le_mul_of_nonneg_right hT1 hN3
    have hTN : 0 ≤ T * (N : ℝ) ^ (-3 : ℤ) := by positivity
    linarith
  have e2 : (2 : ℝ) ^ 86 * t * L ^ 19 * ρ ^ (-3 : ℤ) * (N : ℝ) ^ (-3 : ℤ) =
      2 ^ 86 * T * (N : ℝ) ^ (-3 : ℤ) := by rw [hT]; ring
  rw [e2]
  exact sub_le_comm.1 (htot.trans hfin)

end EG.T16sProof
