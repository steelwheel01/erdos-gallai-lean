module

public import EG.Spec.Link.L15
public import EG.Lib.Found.ColourClass
public import EG.Lib.Prob.Chernoff
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proof of Lemma 15⁺, random splitting of expanders (manuscript s3:lemL15p)

Proves `EG.Spec.L15pStatement` (`EG.l15p`).

The proof follows the manuscript (s3.tex, proof of Lemma 15⁺):

* `EG.L15.step1` (Step 1): for `U` with `1 ≤ |U| ≤ 2N/3` and `T` with `|T| < ε′|U|/L²`,
  `e_X(U, Nbr_X(U) \ T) > s|U|` (the manuscript's `|T| ≤ m - 1` with `m = ⌈ε′u/L²⌉` is the same
  condition on the integer `|T|`);
* `EG.L15.step2` (Step 2): if the colour class `X_i` is not an `(ε′,s′)`-expander, there are such
  `U`, `T` (with `T := Nbr_{X_i-F}(U) ⊆ Nbr_X(U)`) for which at most `s′|U|` edges of `X` between
  `U` and `Nbr_X(U) \ T` have colour `i`;
* Step 3: the lower Chernoff bound with `δ = 1/2` for a colour class of the uniform colouring
  (`EG.FinDist.chernoff_randColouring_lower_half`, [s1:citChernoff]) together with
  `EG.L15.exp_neg_five_mul_logb_le` (`e^{-5uL} ≤ N^{-7u}`);
* Step 4 (union bound): `EG.L15.card_powerset_filter_card_lt_le` (at most `N^u` sets `T`) and
  `EG.L15.sum_powerset_erase_pow_le` (`∑_{∅ ≠ U ⊆ V(X)} N^{-6|U|} = (1 + N^{-6})^N - 1 ≤ 2N^{-5}`).

The manuscript sums `N^{2u} N^{-7.2u}` over `u ≥ 1` (`e^{-5uL} ≤ N^{-7.2u}`); here the cruder
`e^{-5uL} ≤ N^{-7u}` suffices, because the number of sets `U` is counted exactly by the binomial
theorem instead of by `N^u`.
-/

public section


namespace EG

open Finset

namespace L15

variable {V : Type*} [DecidableEq V]

/-- The edges of `X` between `U` and `Nbr_X(U) \ T`, as elements of `↥E(X)` (the coordinates of
the colouring). -/
def cross (X : FGraph V) (U T : Finset V) : Finset X.edges :=
  (X.edgesBetween U (X.nbrSet U \ T)).subtype (· ∈ X.edges)

theorem card_cross (X : FGraph V) (U T : Finset V) :
    (cross X U T).card = X.eBetween U (X.nbrSet U \ T) := by
  rw [cross, card_subtype, filter_true_of_mem fun e he => X.edgesBetween_subset _ _ he]
  rfl

theorem coe_mem_edgesBetween_of_mem_cross {X : FGraph V} {U T : Finset V} {e : X.edges}
    (he : e ∈ cross X U T) : (e : Sym2 V) ∈ X.edgesBetween U (X.nbrSet U \ T) :=
  (mem_subtype.1 he)

/-- [s3:lemL15p] proof, Step 1: "`e_X(U, 𝒩 \ 𝒯) > su` for every `𝒯 ⊆ 𝒩` with `|𝒯| ≤ m - 1`",
where `𝒩 = Nbr_X(U)` and `m = ⌈ε′u/L²⌉`; for the integer `|𝒯|`, `|𝒯| ≤ m - 1` is
`|𝒯| < ε′u/L²`. (The condition `𝒯 ⊆ 𝒩` is not needed.) -/
theorem step1 {X : FGraph V} {ε' s : ℝ} (hX : X.IsExpander ε' s) {U T : Finset V}
    (hU : U ⊆ X.verts) (h1 : 1 ≤ U.card) (h2 : (U.card : ℝ) ≤ 2 * X.card / 3)
    (hT : (T.card : ℝ) < ε' * U.card / Real.logb 2 X.card ^ 2) :
    s * U.card < X.eBetween U (X.nbrSet U \ T) := by
  by_contra h
  push Not at h
  have key := hX U (X.edgesBetween U (X.nbrSet U \ T)) hU (X.edgesBetween_subset _ _) h1 h2 h
  have hsub : (X.deleteEdges (X.edgesBetween U (X.nbrSet U \ T))).nbrSet U ⊆ T := by
    intro v hv
    rw [FGraph.mem_nbrSet, FGraph.deleteEdges_verts] at hv
    obtain ⟨hvV, hvU, u, hu, huv'⟩ := hv
    obtain ⟨huv, hF⟩ := FGraph.deleteEdges_adj.1 huv'
    by_contra hvT
    exact hF (X.mem_edgesBetween.2 ⟨huv, u, hu, v,
      mem_sdiff.2 ⟨X.mem_nbrSet.2 ⟨hvV, hvU, u, hu, huv⟩, hvT⟩, rfl⟩)
  have hc : (((X.deleteEdges (X.edgesBetween U (X.nbrSet U \ T))).nbrSet U).card : ℝ) ≤
      T.card := by exact_mod_cast card_le_card hsub
  linarith

/-- [s3:lemL15p] proof, Step 2: "Suppose that `U` violates the `(ε′,s/(2k))`-condition in `H`.
Then there is `F ⊆ E(H)` with `|F| ≤ su/(2k)` and `|Nbr_{H-F}(U)| < ε′u/L²` … Put
`𝒯 := Nbr_{H-F}(U)`. Since `H ⊆ X`, we have `𝒯 ⊆ 𝒩` and `|𝒯| ≤ m - 1`, and every edge of `H`
between `U` and `𝒩 \ 𝒯` lies in `F`. Hence `e_H(U, 𝒩 \ 𝒯) ≤ su/(2k)`." Here for a general
`s′` in place of `s/(2k)`; `e_H(U, 𝒩 \ 𝒯)` is the number of edges of `X` between `U` and
`𝒩 \ 𝒯` of colour `i`. -/
theorem step2 {X : FGraph V} {k : ℕ} (c : X.edges → Fin k) (i : Fin k) {ε' s' : ℝ}
    (h : ¬ (X.colourClass c i).IsExpander ε' s') :
    ∃ U ⊆ X.verts, 1 ≤ U.card ∧ (U.card : ℝ) ≤ 2 * X.card / 3 ∧
      ∃ T ⊆ X.nbrSet U, (T.card : ℝ) < ε' * U.card / Real.logb 2 X.card ^ 2 ∧
        (#{e ∈ cross X U T | c e = i} : ℝ) ≤ s' * U.card := by
  unfold FGraph.IsExpander at h
  push Not at h
  obtain ⟨U, F, hU, hF, h1, h2, h3, h4⟩ := h
  set H := X.colourClass c i with hH
  set T := (H.deleteEdges F).nbrSet U with hTdef
  have hHX : H ≤ X := FGraph.colourClass_le X c i
  refine ⟨U, hU, h1, h2, T, FGraph.nbrSet_mono ((H.deleteEdges_le F).trans hHX) U, h4, ?_⟩
  have hcard : #{e ∈ cross X U T | c e = i} ≤ F.card := by
    refine card_le_card_of_injOn (fun e => (e : Sym2 V)) ?_ Subtype.val_injective.injOn
    intro e he
    rw [coe_filter] at he
    obtain ⟨he, hci⟩ := he
    have heB := coe_mem_edgesBetween_of_mem_cross he
    rw [FGraph.mem_edgesBetween] at heB
    obtain ⟨-, a, ha, b, hb, hab⟩ := heB
    rw [mem_sdiff] at hb
    obtain ⟨hbN, hbT⟩ := hb
    by_contra heF
    apply hbT
    have hbN' := X.mem_nbrSet.1 hbN
    have hHe : (e : Sym2 V) ∈ H.edges := (FGraph.coe_mem_colourClass_edges X c i e).2 hci
    rw [hTdef, FGraph.mem_nbrSet, FGraph.deleteEdges_verts]
    refine ⟨hbN'.1, hbN'.2.1, a, ha, ?_⟩
    rw [FGraph.deleteEdges_adj, FGraph.adj_iff, hab]
    exact ⟨hHe, heF⟩
  calc (#{e ∈ cross X U T | c e = i} : ℝ) ≤ F.card := by exact_mod_cast hcard
    _ ≤ s' * U.card := h3

/-! ### Numerics and counting (Steps 3 and 4) -/

/-- `L = log₂ N ≥ 1` for `N ≥ 2`. -/
theorem one_le_logb {N : ℕ} (hN : 2 ≤ N) : 1 ≤ Real.logb 2 (N : ℝ) := by
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one one_lt_two).symm
    _ ≤ Real.logb 2 (N : ℝ) := Real.logb_le_logb_of_le one_lt_two two_pos h2

/-- [s3:lemL15p] proof, Step 4: "`e^{-5uL} = N^{-5u log e} ≤ N^{-7.2u}`"; here the weaker
`e^{-5uL} ≤ N^{-7u}` (from `7 ln 2 ≤ 5`), for `N ≥ 1` and `L = log₂ N`. -/
theorem exp_neg_five_mul_logb_le {N : ℕ} (hN : 1 ≤ N) (u : ℕ) :
    Real.exp (-(5 * u * Real.logb 2 N)) ≤ ((N : ℝ)⁻¹) ^ (7 * u) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have heq : ((N : ℝ)⁻¹) ^ (7 * u) = Real.exp (-(((7 * u : ℕ) : ℝ) * Real.log N)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hNpos, inv_pow]
  rw [heq, Real.exp_le_exp, neg_le_neg_iff, Real.logb]
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hul : 0 ≤ (u : ℝ) * Real.log N := mul_nonneg hu hlogN
  rw [mul_div_assoc', le_div_iff₀ hlog2]
  push_cast
  nlinarith

/-- [s3:lemL15p] proof, Step 4: "The number of sets `𝒯` with `|𝒯| ≤ m - 1` is at most
`∑_{j<m} N^j ≤ N^m`": the subsets of a set of at most `N ≥ 2` elements with fewer than `u`
elements number at most `N^u`. -/
theorem card_powerset_filter_card_lt_le {S : Finset V} {N : ℕ} (u : ℕ) (hS : S.card ≤ N)
    (hN : 2 ≤ N) : (S.powerset.filter (fun T => T.card < u)).card ≤ N ^ u := by
  have hsub : S.powerset.filter (fun T => T.card < u) ⊆
      (range u).biUnion (fun j => S.powersetCard j) := by
    intro T hT
    rw [mem_filter, mem_powerset] at hT
    exact mem_biUnion.2 ⟨T.card, mem_range.2 hT.2, mem_powersetCard.2 ⟨hT.1, rfl⟩⟩
  calc _ ≤ ((range u).biUnion (fun j => S.powersetCard j)).card := card_le_card hsub
    _ ≤ ∑ j ∈ range u, (S.powersetCard j).card := card_biUnion_le
    _ = ∑ j ∈ range u, S.card.choose j := by simp only [card_powersetCard]
    _ ≤ ∑ j ∈ range u, N ^ j :=
      sum_le_sum fun j _ => (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hS j)
    _ ≤ N ^ u := (Nat.geomSum_lt hN fun j hj => mem_range.1 hj).le

/-- [s3:lemL15p] proof, Step 4 (the final sum): for a set `S` of `N ≥ 2` elements,
`∑_{∅ ≠ U ⊆ S} (N^{-6})^{|U|} = (1 + N^{-6})^N - 1 ≤ e^{N^{-5}} - 1 ≤ 2N^{-5}`. -/
theorem sum_powerset_erase_pow_le {S : Finset V} (hN : 2 ≤ S.card) :
    ∑ U ∈ S.powerset.erase ∅, (((S.card : ℝ)⁻¹) ^ 6) ^ U.card ≤ 2 * ((S.card : ℝ)⁻¹) ^ 5 := by
  set N := S.card with hNdef
  set a : ℝ := (N : ℝ)⁻¹ with ha
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hNa : (N : ℝ) * a = 1 := mul_inv_cancel₀ hNpos.ne'
  have hsum : ∑ U ∈ S.powerset, (a ^ 6) ^ U.card = (a ^ 6 + 1) ^ N := by
    rw [hNdef, ← sum_pow_mul_eq_add_pow]
    simp
  have herase := add_sum_erase S.powerset (fun U => (a ^ 6) ^ U.card) (empty_mem_powerset S)
  simp only [card_empty, pow_zero] at herase
  have h1 : (a ^ 6 + 1) ^ N ≤ Real.exp (a ^ 5) := by
    calc (a ^ 6 + 1) ^ N ≤ (Real.exp (a ^ 6)) ^ N :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp (N * a ^ 6) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (a ^ 5) := by
        congr 1
        calc (N : ℝ) * a ^ 6 = (N * a) * a ^ 5 := by ring
          _ = a ^ 5 := by rw [hNa, one_mul]
  have ha5 : 0 ≤ a ^ 5 := by positivity
  have ha5' : a ^ 5 ≤ 1 := pow_le_one₀ ha0 ha1
  have h2 : Real.exp (a ^ 5) ≤ 1 + 2 * a ^ 5 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := a ^ 5) (by rw [abs_of_nonneg ha5]; exact ha5')
    have h' := (abs_le.1 h).2
    nlinarith
  linarith

/-! ### The probability bound for one colour -/

open FinDist in
/-- [s3:lemL15p] proof, Step 3: "`Z := e_H(U, 𝒩 \ 𝒯) ∼ Bin(e, 1/k)`, with mean `μ_Z := e/k`
… By the lower Chernoff bound (Cited result [s1:citChernoff]) with `δ = 1/2`,
`P(Z < μ_Z/2) ≤ e^{-μ_Z/8} ≤ e^{-su/(8k)} ≤ e^{-5uL}`", followed by `e^{-5uL} ≤ N^{-7u}`
(`exp_neg_five_mul_logb_le`). Hypotheses: `e = |cross X U T| > s u` (Step 1) and `s ≥ 40kL`. -/
theorem prob_step3_le {X : FGraph V} {s : ℝ} {k : ℕ} [NeZero k] (hN : 1 ≤ X.card)
    (hs : 40 * (k : ℝ) * Real.logb 2 X.card ≤ s) {U T : Finset V}
    (h1 : s * U.card < X.eBetween U (X.nbrSet U \ T)) (i : Fin k) :
    (randColouring X.edges k).prob
        {c | (#{e ∈ cross X U T | c e = i} : ℝ) < ((cross X U T).card / k) / 2} ≤
      ((X.card : ℝ)⁻¹) ^ (7 * U.card) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hL : 0 ≤ Real.logb 2 (X.card : ℝ) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hN)
  have hch := chernoff_randColouring_lower_half (cross X U T) i
    (m := (cross X U T).card / k) (by positivity) le_rfl
  refine hch.trans ((Real.exp_le_exp.2 ?_).trans (exp_neg_five_mul_logb_le hN U.card))
  rw [card_cross, neg_le_neg_iff]
  have hu : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have h40 : 40 * (k : ℝ) * Real.logb 2 X.card * U.card ≤ s * U.card :=
    mul_le_mul_of_nonneg_right hs hu
  rw [div_div, le_div_iff₀ (by positivity)]
  nlinarith

open FinDist in
/-- [s3:lemL15p] "for each `i ∈ [k]`, `X_i` is an `(ε′,s/(2k))`-expander with probability at
least `1 − 2N^{−5}`", in the form `P(X_i is not an (ε′,s/(2k))-expander) ≤ 2N^{-5}`
(proof, Steps 1–4). -/
theorem prob_not_isExpander_colourClass_le {X : FGraph V} {ε' s : ℝ} {k : ℕ} [NeZero k]
    (hε0 : 0 < ε') (hε1 : ε' ≤ 1) (hs : 40 * (k : ℝ) * Real.logb 2 X.card ≤ s)
    (hX : X.IsExpander ε' s) (i : Fin k) :
    (randColouring X.edges k).prob
        {c | ¬ (X.colourClass c i).IsExpander ε' (s / (2 * k))} ≤
      2 * (X.card : ℝ) ^ (-5 : ℤ) := by
  classical
  -- `N ≤ 1`: every graph on at most one vertex is an expander.
  rcases le_or_gt X.card 1 with hN1 | hN2
  · have hempty : {c : X.edges → Fin k | ¬ (X.colourClass c i).IsExpander ε' (s / (2 * k))} =
        ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact FGraph.isExpander_of_card_le_one ((FGraph.colourClass_card X c i).le.trans hN1)
    rw [hempty, prob_empty]
    positivity
  -- `N ≥ 2`, so `L ≥ 1`.
  have hN : 2 ≤ X.card := hN2
  have hL : 1 ≤ Real.logb 2 (X.card : ℝ) := one_le_logb hN
  set L := Real.logb 2 (X.card : ℝ) with hLdef
  set a : ℝ := (X.card : ℝ)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have hNa : (X.card : ℝ) * a = 1 := mul_inv_cancel₀ (by positivity)
  -- the pairs `(U, 𝒯)` of Steps 2–4
  set 𝒰 : Finset (Finset V) :=
    X.verts.powerset.filter (fun U => 1 ≤ U.card ∧ (U.card : ℝ) ≤ 2 * X.card / 3) with h𝒰
  set 𝒯 : Finset V → Finset (Finset V) := fun U =>
    (X.nbrSet U).powerset.filter (fun T => (T.card : ℝ) < ε' * U.card / L ^ 2) with h𝒯
  set A : Finset V → Finset V → Set (X.edges → Fin k) := fun U T =>
    {c | (#{e ∈ cross X U T | c e = i} : ℝ) < ((cross X U T).card / k) / 2} with hA
  -- Step 2 + Step 1: a failure lies in the union of the events `A U T`.
  have hsub : {c : X.edges → Fin k | ¬ (X.colourClass c i).IsExpander ε' (s / (2 * k))} ⊆
      ⋃ U ∈ 𝒰, ⋃ T ∈ 𝒯 U, A U T := by
    intro c hc
    obtain ⟨U, hU, h1, h2, T, hT, hTc, hZ⟩ := step2 c i hc
    have hst1 := step1 hX hU h1 h2 hTc
    simp only [Set.mem_iUnion]
    refine ⟨U, mem_filter.2 ⟨mem_powerset.2 hU, h1, h2⟩, T,
      mem_filter.2 ⟨mem_powerset.2 hT, hTc⟩, ?_⟩
    show (#{e ∈ cross X U T | c e = i} : ℝ) < ((cross X U T).card / k) / 2
    have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
    rw [card_cross]
    calc (#{e ∈ cross X U T | c e = i} : ℝ) ≤ s / (2 * k) * U.card := hZ
      _ = s * U.card / k / 2 := by field_simp
      _ < (X.eBetween U (X.nbrSet U \ T) : ℝ) / k / 2 := by gcongr
  -- Step 3 for each pair.
  have hAle : ∀ U ∈ 𝒰, ∀ T ∈ 𝒯 U, (randColouring X.edges k).prob (A U T) ≤ a ^ (7 * U.card) := by
    intro U hU T hT
    obtain ⟨hU, h1, h2⟩ := mem_filter.1 hU
    exact prob_step3_le (by omega) hs (step1 hX (mem_powerset.1 hU) h1 h2 (mem_filter.1 hT).2) i
  -- Step 4: at most `N^u` sets `T` for each `U`.
  have hcount : ∀ U ∈ 𝒰, ((𝒯 U).card : ℝ) ≤ (X.card : ℝ) ^ U.card := by
    intro U hU
    have hsub𝒯 : 𝒯 U ⊆ X.verts.powerset.filter (fun T => T.card < U.card) := by
      intro T hT
      obtain ⟨hT, hTc⟩ := mem_filter.1 hT
      refine mem_filter.2 ⟨mem_powerset.2 ((mem_powerset.1 hT).trans
        (FGraph.nbrSet_subset_verts U)), ?_⟩
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
      have hu : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hle : ε' * U.card / L ^ 2 ≤ U.card :=
        (div_le_self (by positivity) hL2).trans (mul_le_of_le_one_left hu hε1)
      exact_mod_cast hTc.trans_le hle
    exact_mod_cast (card_le_card hsub𝒯).trans
      (card_powerset_filter_card_lt_le U.card le_rfl hN)
  have h𝒰sub : 𝒰 ⊆ X.verts.powerset.erase ∅ := by
    intro U hU
    obtain ⟨hU, h1, -⟩ := mem_filter.1 hU
    refine mem_erase.2 ⟨?_, hU⟩
    rintro rfl
    simp at h1
  calc (randColouring X.edges k).prob
        {c | ¬ (X.colourClass c i).IsExpander ε' (s / (2 * k))}
      ≤ (randColouring X.edges k).prob (⋃ U ∈ 𝒰, ⋃ T ∈ 𝒯 U, A U T) :=
        (randColouring X.edges k).prob_mono hsub
    _ ≤ ∑ U ∈ 𝒰, (randColouring X.edges k).prob (⋃ T ∈ 𝒯 U, A U T) :=
        (randColouring X.edges k).prob_biUnion_le _ _
    _ ≤ ∑ U ∈ 𝒰, ∑ T ∈ 𝒯 U, (randColouring X.edges k).prob (A U T) :=
      sum_le_sum fun U _ => (randColouring X.edges k).prob_biUnion_le _ _
    _ ≤ ∑ U ∈ 𝒰, ∑ T ∈ 𝒯 U, a ^ (7 * U.card) :=
      sum_le_sum fun U hU => sum_le_sum fun T hT => hAle U hU T hT
    _ = ∑ U ∈ 𝒰, ((𝒯 U).card : ℝ) * a ^ (7 * U.card) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ ∑ U ∈ 𝒰, (a ^ 6) ^ U.card := by
      refine sum_le_sum fun U hU => ?_
      calc ((𝒯 U).card : ℝ) * a ^ (7 * U.card) ≤ (X.card : ℝ) ^ U.card * a ^ (7 * U.card) :=
            mul_le_mul_of_nonneg_right (hcount U hU) (by positivity)
        _ = ((X.card : ℝ) * a) ^ U.card * (a ^ 6) ^ U.card := by ring
        _ = (a ^ 6) ^ U.card := by rw [hNa, one_pow, one_mul]
    _ ≤ ∑ U ∈ X.verts.powerset.erase ∅, (a ^ 6) ^ U.card :=
      sum_le_sum_of_subset_of_nonneg h𝒰sub fun _ _ _ => by positivity
    _ ≤ 2 * a ^ 5 := sum_powerset_erase_pow_le hN
    _ = 2 * (X.card : ℝ) ^ (-5 : ℤ) := by rw [ha, zpow_neg, inv_pow, zpow_ofNat]

end L15

universe u

open FinDist in
/-- [s3:lemL15p] "Let `X` be an `N`-vertex `(ε′,s)`-expander with `0 < ε′ ≤ 1`, put
`L := log N`, and let `k ≥ 1` be an integer with `s ≥ 40kL`. Give every edge of `X` a colour from
`[k]`, independently and uniformly at random, and for `i ∈ [k]` let `X_i` be the graph with vertex
set `V(X)` whose edges are the edges of colour `i`. Then for each `i ∈ [k]`, `X_i` is an
`(ε′,s/(2k))`-expander with probability at least `1 − 2N^{−5}`. Hence all `k` classes are
`(ε′,s/(2k))`-expanders with probability at least `1 − 2kN^{−5}`." -/
theorem l15p : EG.Spec.L15pStatement.{u} := by
  intro V _ X ε' s k _ hε0 hε1 hs hX
  have hgood : ∀ i : Fin k, 1 - 2 * (X.card : ℝ) ^ (-5 : ℤ) ≤
      (randColouring X.edges k).prob
        {c | (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))} := by
    intro i
    have h := L15.prob_not_isExpander_colourClass_le hε0 hε1 hs hX i
    have hc := (randColouring X.edges k).prob_add_prob_compl
      {c | (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))}
    rw [Set.compl_ofPred] at hc
    linarith
  refine ⟨hgood, ?_⟩
  have hinter := (randColouring X.edges k).prob_biInter_ge univ
    (fun i => {c | (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))})
  have heq : (⋂ i ∈ (univ : Finset (Fin k)),
      {c : X.edges → Fin k | (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))}) =
      {c | ∀ i : Fin k, (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))} := by
    ext c
    simp
  have hsum : ∑ i ∈ (univ : Finset (Fin k)), (randColouring X.edges k).prob
      {c | (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))}ᶜ ≤
      ∑ _i ∈ (univ : Finset (Fin k)), 2 * (X.card : ℝ) ^ (-5 : ℤ) := by
    refine sum_le_sum fun i _ => ?_
    rw [Set.compl_ofPred]
    exact L15.prob_not_isExpander_colourClass_le hε0 hε1 hs hX i
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [heq] at hinter
  show 1 - 2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) ≤ (randColouring X.edges k).prob
    {c | ∀ i : Fin k, (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ)))}
  linarith

open FinDist in
/-- Deterministic consequence of [s3:lemL15p] (no manuscript label of its own; the form used
downstream when a single good colouring is fixed): if `2kN^{-5} < 1`, there is a colouring
`c : ↥E(X) → Fin k` of positive probability all of whose colour classes
`X.colourClass c i = X.restrictEdges (selectSet X.edges fun e => decide (c e = i))` are
`(ε′,s/(2k))`-expanders. -/
theorem exists_colouring_forall_isExpander {V : Type u} [DecidableEq V] {X : FGraph V}
    {ε' s : ℝ} {k : ℕ} [NeZero k] (hε0 : 0 < ε') (hε1 : ε' ≤ 1)
    (hs : 40 * (k : ℝ) * Real.logb 2 X.card ≤ s) (hX : X.IsExpander ε' s)
    (hN : 2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) < 1) :
    ∃ c : X.edges → Fin k, 0 < (randColouring X.edges k).w c ∧ ∀ i : Fin k,
      (X.colourClass c i).IsExpander ε' (s / (2 * (k : ℝ))) := by
  have h := (l15p.{u} V X ε' s k hε0 hε1 hs hX).2
  obtain ⟨c, hc, hw⟩ := (randColouring X.edges k).exists_of_prob_pos (by linarith)
  exact ⟨c, hw, hc⟩

open FinDist in
/-- [s3:lemL15p] for a colouring drawn jointly with other randomness (a transport of the
statement, with no manuscript label of its own): if the random colouring `c : Ω → (↥E(X) → Fin k)`
has, under `μ`, the law of the uniform colouring (`μ.map c = randColouring X.edges k`), then both
bounds of Lemma 15⁺ hold under `μ`. This is the form needed when the colouring is drawn
"uniformly and independently of `V`" ([s3:thmT16s], Step 1) or uniformly given an earlier split
([s3:lemCOL]); the hypothesis `hc` comes from `FinDist.map_fst_prod`, `FinDist.map_snd_prod`,
`FinDist.map_fst_compProd` or `FinDist.IsRSubset.map_pair_eq_prod` (see `l15p_prod_fst`). -/
theorem l15p_of_map_eq {Ω : Type*} {V : Type u} [DecidableEq V] {X : FGraph V} {ε' s : ℝ}
    {k : ℕ} [NeZero k] (hε0 : 0 < ε') (hε1 : ε' ≤ 1)
    (hs : 40 * (k : ℝ) * Real.logb 2 X.card ≤ s) (hX : X.IsExpander ε' s) (μ : FinDist Ω)
    (c : Ω → X.edges → Fin k) (hc : μ.map c = randColouring X.edges k) :
    (∀ i : Fin k, 1 - 2 * (X.card : ℝ) ^ (-5 : ℤ) ≤
      μ.prob {ω | (X.colourClass (c ω) i).IsExpander ε' (s / (2 * (k : ℝ)))}) ∧
    1 - 2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) ≤
      μ.prob {ω | ∀ i : Fin k, (X.colourClass (c ω) i).IsExpander ε' (s / (2 * (k : ℝ)))} := by
  obtain ⟨h1, h2⟩ := l15p.{u} V X ε' s k hε0 hε1 hs hX
  rw [← hc, prob_map] at h2
  refine ⟨fun i => ?_, h2⟩
  have h1i := h1 i
  rw [← hc, prob_map] at h1i
  exact h1i

open FinDist in
/-- [s3:lemL15p] for a colouring drawn independently of a second random object (a transport of
the statement, with no manuscript label of its own): on the product space
`randColouring X.edges k × ν` (e.g. `ν` the law of the `ρ`-random set `V` of [s3:thmT16s]),
both bounds of Lemma 15⁺ hold for the colour classes of the first coordinate. -/
theorem l15p_prod_fst {β : Type*} {V : Type u} [DecidableEq V] {X : FGraph V} {ε' s : ℝ}
    {k : ℕ} [NeZero k] (hε0 : 0 < ε') (hε1 : ε' ≤ 1)
    (hs : 40 * (k : ℝ) * Real.logb 2 X.card ≤ s) (hX : X.IsExpander ε' s) (ν : FinDist β) :
    (∀ i : Fin k, 1 - 2 * (X.card : ℝ) ^ (-5 : ℤ) ≤
      ((randColouring X.edges k).prod ν).prob
        {p | (X.colourClass p.1 i).IsExpander ε' (s / (2 * (k : ℝ)))}) ∧
    1 - 2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) ≤
      ((randColouring X.edges k).prod ν).prob
        {p | ∀ i : Fin k, (X.colourClass p.1 i).IsExpander ε' (s / (2 * (k : ℝ)))} :=
  l15p_of_map_eq hε0 hε1 hs hX _ Prod.fst (map_fst_prod _ ν)

end EG
