module

public import EG.Spec.Link.P18s
public import EG.Lib.Link.Star
public import EG.Lib.Found.Graph
public import EG.Lib.Prob.Basic
public import EG.Spec.Link.L17s
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Proposition 18* (manuscript s3:lemP18s (i)) — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemP18s] (i): "Let `U' ⊆ U` be maximal subject to
`|Nbr_G(U')| ≥ θ_*|U'|` …". Here `U'` is taken of maximum cardinality among the well-expanding
subsets of `U`, which gives the maximality property used ("By maximality this is less than
`θ_*(|U'|+1)`").
-/

public section

namespace EG.P18sProof

open Finset

variable {V : Type*} [DecidableEq V]

/-- `Nbr_G(U' ∪ {v}) ⊇ (N_G(v) \ (U' ∪ Nbr_G(U'))) ∪ (Nbr_G(U') \ {v})`, a disjoint union. -/
theorem card_nbrSet_insert_ge (G : FGraph V) (U' : Finset V) (v : V) (hv : v ∈ G.verts)
    (hvU : v ∉ U') :
    (G.nbrs v \ (U' ∪ G.nbrSet U')).card + (G.nbrSet U').card ≤
      (G.nbrSet (insert v U')).card + 1 := by
  classical
  have hsub : (G.nbrs v \ (U' ∪ G.nbrSet U')) ∪ (G.nbrSet U' \ {v}) ⊆ G.nbrSet (insert v U') := by
    intro x hx
    rw [FGraph.mem_nbrSet]
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.1 hx
      rw [Finset.mem_union, not_or] at hx2
      have hadj := FGraph.mem_nbrs.1 hx1
      refine ⟨G.nbrs_subset_verts v hx1, ?_, v, Finset.mem_insert_self _ _, hadj⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => (G.self_not_mem_nbrs v) (h ▸ hx1), hx2.1⟩
    · obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.1 hx
      rw [FGraph.mem_nbrSet] at hx1
      obtain ⟨hxV, hxU, u, hu, hadj⟩ := hx1
      refine ⟨hxV, ?_, u, Finset.mem_insert_of_mem hu, hadj⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hx2 (Finset.mem_singleton.2 h), hxU⟩
  have hdisj : Disjoint (G.nbrs v \ (U' ∪ G.nbrSet U')) (G.nbrSet U' \ {v}) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.1 hx1).2 (Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.1 hx2).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 : (G.nbrSet U').card ≤ (G.nbrSet U' \ {v}).card + 1 := by
    have := Finset.card_le_card_sdiff_add_card (s := G.nbrSet U') (t := {v})
    rwa [Finset.card_singleton] at this
  omega

/-- [s3:lemP18s] (i) Proposition 18*, for a real `θ ≥ 1` and an `(ε',s)`-expander with
`s ≥ θ + 1`, `ε' > 0`, `n ≥ 2`. -/
theorem prop18 (G : FGraph V) {ε' s θ : ℝ} (hG : G.IsExpander ε' s) (hn : 2 ≤ G.card)
    (hε : 0 < ε') (hε1 : ε' ≤ 1) (hθ : 1 ≤ θ) (hs : θ + 1 ≤ s) (U : Finset V)
    (hUV : U ⊆ G.verts) (hU1 : 1 ≤ U.card) (hU23 : (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3) :
    ∃ U' ⊆ U, G.IsWellExpanding θ U' ∧
      ε' * (U.card : ℝ) / (3 * θ * Real.logb 2 (G.card : ℝ) ^ 2) ≤ (U'.card : ℝ) := by
  classical
  set L := Real.logb 2 (G.card : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < G.card))]
    simp only [Real.rpow_one]; exact_mod_cast hn
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  -- a well-expanding `U' ⊆ U` of maximum cardinality
  set T := U.powerset.filter (fun U' => G.IsWellExpanding θ U') with hT
  have hTne : T.Nonempty := ⟨∅, by
    rw [hT, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    unfold FGraph.IsWellExpanding; simp⟩
  obtain ⟨U', hU'T, hmax⟩ := Finset.exists_max_image T Finset.card hTne
  rw [hT, Finset.mem_filter, Finset.mem_powerset] at hU'T
  obtain ⟨hU'U, hU'we⟩ := hU'T
  refine ⟨U', hU'U, hU'we, ?_⟩
  have hden : 0 < 3 * θ * L ^ 2 := by positivity
  by_cases heq : U' = U
  · rw [heq, div_le_iff₀ hden]
    have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
    have : ε' ≤ 3 * θ * L ^ 2 := by nlinarith
    nlinarith
  obtain ⟨v0, hv0U, hv0U'⟩ : ∃ v ∈ U, v ∉ U' := by
    by_contra h
    push Not at h
    exact heq (Finset.Subset.antisymm hU'U h)
  -- maximality: `|Nbr(U' ∪ {v})| < θ(|U'|+1)` for `v ∈ U \ U'`
  have hlt : ∀ v ∈ U, v ∉ U' → ((G.nbrSet (insert v U')).card : ℝ) < θ * ((U'.card : ℝ) + 1) := by
    intro v hv hvU'
    by_contra hge
    push Not at hge
    have hmem : insert v U' ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hv hU'U, ?_⟩
      unfold FGraph.IsWellExpanding
      rw [Finset.card_insert_of_notMem hvU']; push_cast; exact hge
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hvU'] at this
    omega
  have hwe : θ * (U'.card : ℝ) ≤ (G.nbrSet U').card := hU'we
  -- `a_v < θ + 1`, and `|Nbr(U')| < θ(|U'|+1) + 1`
  have ha : ∀ v ∈ U, v ∉ U' → ((G.nbrs v \ (U' ∪ G.nbrSet U')).card : ℝ) < θ + 1 := by
    intro v hv hvU'
    have h1 := card_nbrSet_insert_ge G U' v (hUV hv) hvU'
    have h1' : ((G.nbrs v \ (U' ∪ G.nbrSet U')).card : ℝ) + (G.nbrSet U').card ≤
        (G.nbrSet (insert v U')).card + 1 := by exact_mod_cast h1
    have h2 := hlt v hv hvU'
    nlinarith
  have hNU' : ((G.nbrSet U').card : ℝ) < θ * ((U'.card : ℝ) + 1) + 1 := by
    have h1 := card_nbrSet_insert_ge G U' v0 (hUV hv0U) hv0U'
    have h1' : ((G.nbrs v0 \ (U' ∪ G.nbrSet U')).card : ℝ) + (G.nbrSet U').card ≤
        (G.nbrSet (insert v0 U')).card + 1 := by exact_mod_cast h1
    have h2 := hlt v0 hv0U hv0U'
    have h3 : (0 : ℝ) ≤ (G.nbrs v0 \ (U' ∪ G.nbrSet U')).card := Nat.cast_nonneg _
    linarith
  -- the edge set `F`
  set F : Finset (Sym2 V) := (U \ U').biUnion
    (fun v => (G.nbrs v \ (U' ∪ G.nbrSet U')).image (fun x => s(v, x))) with hFdef
  have hFE : F ⊆ G.edges := by
    intro e he
    obtain ⟨v, -, he⟩ := Finset.mem_biUnion.1 he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 he
    exact FGraph.mem_nbrs.1 (Finset.mem_sdiff.1 hx).1
  have hFc : (F.card : ℝ) ≤ s * U.card := by
    have h1 : F.card ≤ ∑ v ∈ U \ U', ((G.nbrs v \ (U' ∪ G.nbrSet U')).image (fun x => s(v, x))).card :=
      Finset.card_biUnion_le
    have h2 : ((∑ v ∈ U \ U', ((G.nbrs v \ (U' ∪ G.nbrSet U')).image
        (fun x => s(v, x))).card : ℕ) : ℝ) ≤ ∑ _v ∈ U \ U', (θ + 1) := by
      rw [Nat.cast_sum]
      refine Finset.sum_le_sum fun v hv => ?_
      have := ha v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2
      have h3 : (((G.nbrs v \ (U' ∪ G.nbrSet U')).image (fun x => s(v, x))).card : ℝ) ≤
          (G.nbrs v \ (U' ∪ G.nbrSet U')).card := by exact_mod_cast Finset.card_image_le
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h4 : ((U \ U').card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have h5 : (F.card : ℝ) ≤ ((U \ U').card : ℝ) * (θ + 1) := (Nat.cast_le.2 h1).trans h2
    have h6 : ((U \ U').card : ℝ) * (θ + 1) ≤ U.card * s :=
      mul_le_mul h4 hs (by linarith) (Nat.cast_nonneg _)
    linarith
  have key := hG U F hUV hFE hU1 hU23 hFc
  -- `Nbr_{G-F}(U) ⊆ Nbr_G(U')`
  have hsub : (G.deleteEdges F).nbrSet U ⊆ G.nbrSet U' := by
    intro x hx
    rw [FGraph.mem_nbrSet] at hx
    obtain ⟨hxV, hxU, u, hu, hadj⟩ := hx
    rw [FGraph.deleteEdges_adj] at hadj
    have hxU' : x ∉ U' := fun h => hxU (hU'U h)
    by_cases huU' : u ∈ U'
    · rw [FGraph.mem_nbrSet]; exact ⟨hxV, hxU', u, huU', hadj.1⟩
    · by_contra hxN
      apply hadj.2
      rw [hFdef, Finset.mem_biUnion]
      refine ⟨u, Finset.mem_sdiff.2 ⟨hu, huU'⟩, Finset.mem_image.2 ⟨x, ?_, rfl⟩⟩
      refine Finset.mem_sdiff.2 ⟨FGraph.mem_nbrs.2 hadj.1, ?_⟩
      rw [Finset.mem_union, not_or]; exact ⟨hxU', hxN⟩
  have hk : ε' * (U.card : ℝ) / L ^ 2 ≤ (G.nbrSet U').card := by
    exact key.trans (by exact_mod_cast Finset.card_le_card hsub)
  have hpos : 0 < ε' * (U.card : ℝ) / L ^ 2 := by
    have : (1 : ℝ) ≤ U.card := by exact_mod_cast hU1
    positivity
  -- `U' ≠ ∅`
  have hU'1 : 1 ≤ U'.card := by
    by_contra h0
    have : U' = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [this] at hk
    have : G.nbrSet (∅ : Finset V) = ∅ := by
      ext x; simp [FGraph.mem_nbrSet]
    rw [this, Finset.card_empty, Nat.cast_zero] at hk
    linarith
  have hU'1' : (1 : ℝ) ≤ U'.card := by exact_mod_cast hU'1
  have h3 : θ * ((U'.card : ℝ) + 1) + 1 ≤ 3 * θ * U'.card := by nlinarith
  rw [div_le_iff₀ hden]
  have h4 : ε' * (U.card : ℝ) < 3 * θ * U'.card * L ^ 2 := by
    have h5 : ε' * (U.card : ℝ) / L ^ 2 < 3 * θ * U'.card := by linarith
    rwa [div_lt_iff₀ (by positivity)] at h5
  nlinarith

/-- The number of subsets of `E` with at most `u` elements is at most `(|E|+1)^u`. -/
theorem card_filter_powerset_le {α : Type*} [DecidableEq α] (E : Finset α) (u : ℕ) :
    (E.powerset.filter (fun F => F.card ≤ u)).card ≤ (E.card + 1) ^ u := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (u + 1))
    (fun F hF => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_filter.1 hF).2))]
  have e1 : ∀ f ∈ Finset.range (u + 1),
      ((E.powerset.filter (fun F => F.card ≤ u)).filter (fun F => F.card = f)).card =
        E.card.choose f := by
    intro f hf
    rw [← Finset.card_powersetCard]
    congr 1
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hf)⟩, h3⟩
  rw [Finset.sum_congr rfl e1, add_pow]
  refine Finset.sum_le_sum fun f hf => ?_
  rw [one_pow, mul_one]
  have h1 := Nat.choose_le_pow E.card f
  have h2 : 1 ≤ u.choose f := Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hf))
  calc E.card.choose f ≤ E.card ^ f := h1
    _ = E.card ^ f * 1 := (mul_one _).symm
    _ ≤ E.card ^ f * u.choose f := Nat.mul_le_mul_left _ h2

/-- `e^{-7uL} ≤ n^{-10u}` (`L = log₂ n`, `n ≥ 1`), as `ln 2 < 0.7`. -/
theorem exp_neg_le_pow (n u : ℕ) (hn : 1 ≤ n) :
    Real.exp (-(7 * (u : ℝ) * Real.logb 2 (n : ℝ))) ≤ ((n : ℝ) ^ (10 * u))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : ((n : ℝ) ^ (10 * u))⁻¹ = Real.exp (-((10 * u : ℕ) * Real.log n)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0]
  rw [e1, Real.exp_le_exp, neg_le_neg_iff, Real.logb]
  push_cast
  rw [mul_div_assoc', le_div_iff₀ hl2p]
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have : 10 * (u : ℝ) * Real.log n * Real.log 2 ≤ 7 * u * Real.log n := by
    have h1 : 0 ≤ (u : ℝ) * Real.log n := mul_nonneg hu hlog
    nlinarith
  linarith

/-- The sum of the union bound of Lemma 19*: `Σ_{u=1}^{n} n^{3u}e^{-7uL} ≤ n^{-6}`, in the form
`Σ_{U ⊆ V(G), U ≠ ∅} (|E(G)|+1)^{|U|} e^{-7|U|L} ≤ n^{-6}`. -/
theorem union_sum_le (G : FGraph V) (hn : 2 ≤ G.card) :
    ∑ U ∈ G.verts.powerset, (if U.Nonempty then ((G.edges.card + 1) ^ U.card : ℝ) *
        Real.exp (-(7 * (U.card : ℝ) * Real.logb 2 (G.card : ℝ))) else 0) ≤
      (G.card : ℝ) ^ (-6 : ℤ) := by
  classical
  set n := G.card with hndef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  -- `|E| + 1 ≤ n^2`
  have hE : ((G.edges.card + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 := FGraph.card_edges_le_card_sym2 (H := G)
    rw [Finset.card_sym2, Nat.choose_two_right, ← FGraph.card_def] at h1
    have h2 : 2 * (G.edges.card + 1) ≤ 2 * n ^ 2 := by
      have := Nat.div_mul_le_self ((n + 1) * n) 2
      have h3 : 2 * G.edges.card ≤ (n + 1) * n := by
        calc 2 * G.edges.card ≤ 2 * ((n + 1) * n / 2) := Nat.mul_le_mul_left _ h1
          _ ≤ (n + 1) * n := by rw [mul_comm]; exact Nat.div_mul_le_self _ 2
      nlinarith
    have : G.edges.card + 1 ≤ n ^ 2 := by omega
    exact_mod_cast this
  -- each term is at most `n^{-7u}`
  have hterm : ∀ U ∈ G.verts.powerset, (if U.Nonempty then ((G.edges.card + 1) ^ U.card : ℝ) *
      Real.exp (-(7 * (U.card : ℝ) * Real.logb 2 (n : ℝ))) else 0) ≤
      (if 1 ≤ U.card then ((n : ℝ) ^ 2) ^ U.card * ((n : ℝ) ^ (10 * U.card))⁻¹ else 0) := by
    intro U _
    by_cases hU : U.Nonempty
    · rw [if_pos hU, if_pos (show 1 ≤ U.card from Finset.card_pos.2 hU)]
      have h1 : ((G.edges.card + 1 : ℕ) : ℝ) ^ U.card ≤ ((n : ℝ) ^ 2) ^ U.card :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hE _
      push_cast at h1
      exact mul_le_mul h1 (exp_neg_le_pow n U.card (by omega)) (Real.exp_pos _).le (by positivity)
    · rw [if_neg hU, if_neg (fun (h : 1 ≤ U.card) => hU (Finset.card_pos.1 h))]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_powerset_apply_card (fun u => if 1 ≤ u then ((n : ℝ) ^ 2) ^ u *
      ((n : ℝ) ^ (10 * u))⁻¹ else 0) (x := G.verts), ← FGraph.card_def, ← hndef]
  -- `C(n,u) n^{2u} n^{-10u} ≤ (n^{-7})^u`
  set x : ℝ := ((n : ℝ) ^ 7)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, inv_le_comm₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ n ^ 7 := le_trans hn2 (le_self_pow₀ (by linarith) (by norm_num))
    linarith
  have hterm2 : ∀ u ∈ Finset.range (n + 1), (n.choose u) • (if 1 ≤ u then ((n : ℝ) ^ 2) ^ u *
      ((n : ℝ) ^ (10 * u))⁻¹ else 0) ≤ (if 1 ≤ u then x ^ u else 0) := by
    intro u _
    split_ifs with hu
    · rw [nsmul_eq_mul]
      have hc : (n.choose u : ℝ) ≤ (n : ℝ) ^ u := by exact_mod_cast Nat.choose_le_pow n u
      have e : (n : ℝ) ^ u * (((n : ℝ) ^ 2) ^ u * ((n : ℝ) ^ (10 * u))⁻¹) = x ^ u := by
        rw [hx, inv_pow, ← pow_mul, ← pow_mul]
        have hne : (n : ℝ) ≠ 0 := hn0.ne'
        field_simp
        ring
      calc (n.choose u : ℝ) * (((n : ℝ) ^ 2) ^ u * ((n : ℝ) ^ (10 * u))⁻¹)
          ≤ (n : ℝ) ^ u * (((n : ℝ) ^ 2) ^ u * ((n : ℝ) ^ (10 * u))⁻¹) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = x ^ u := e
    · simp
  refine (Finset.sum_le_sum hterm2).trans ?_
  -- `Σ_{1 ≤ u ≤ n} x^u ≤ x/(1-x) ≤ 2x = 2n^{-7} ≤ n^{-6}`
  have hsplit : ∑ u ∈ Finset.range (n + 1), (if 1 ≤ u then x ^ u else 0) =
      ∑ u ∈ Finset.Ico 1 (n + 1), x ^ u := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hsplit]
  have hg := geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) hx0 (by linarith)
  rw [pow_one] at hg
  refine hg.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have e2 : (n : ℝ) ^ (-6 : ℤ) = n * x := by
    rw [hx, zpow_neg, zpow_ofNat]
    field_simp
  rw [e2]
  have : 2 * x ≤ n * x := mul_le_mul_of_nonneg_right hn2 hx0
  nlinarith

universe u v

/-- [s3:lemP18s] (ii) Lemma 19*, from Proposition 18* and Lemma 17* (`hL17`). -/
theorem lemma19 (hL17 : Spec.L17sStatement.{u, v}) {V : Type u} [DecidableEq V] (G : FGraph V)
    {ε' s₁ ρ : ℝ} (hG : G.IsExpander ε' s₁) (hn : 2 ≤ G.card) (hε1 : (2 : ℝ) ^ (-7 : ℤ) ≤ ε')
    (hε2 : ε' ≤ 1) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hs : Star.theta G.card ε' ρ + 1 ≤ s₁)
    (h8 : 8 * (Star.d G.card ρ : ℝ) * (Star.lam G.card ρ : ℝ) ≤ Star.theta G.card ε' ρ)
    (hθ1 : 1 ≤ Star.theta G.card ε' ρ)
    (Ω : Type v) (μ : FinDist Ω) (R : Ω → Finset V) (hR : μ.IsRSubset R G.verts ρ) :
    1 - (G.card : ℝ) ^ (-6 : ℤ) ≤
      μ.prob {ω | ∀ U : Finset V, U.Nonempty → U ⊆ G.verts →
        ∀ F : Finset (Sym2 V), F ⊆ G.edges →
          (F.card : ℝ) ≤ Star.mu G.card ε' ρ * (U.card : ℝ) →
          ((R ω).card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell G.card) U (R ω)).card : ℝ)} := by
  classical
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  set n := G.card with hndef
  set θ := Star.theta n ε' ρ with hθdef
  set L := Real.logb 2 (n : ℝ) with hLdef
  set P := (G.verts.powerset ×ˢ G.edges.powerset).filter
    (fun p => p.1.Nonempty ∧ p.2.card ≤ p.1.card ∧ G.IsWellExpanding θ p.1) with hPdef
  set Bad : Finset V × Finset (Sym2 V) → Set Ω := fun p =>
    {ω | ((ball (G.deleteEdges p.2) (Star.ell n) p.1 (R ω)).card : ℝ) ≤ ((R ω).card : ℝ) / 2}
    with hBad
  have hmu : 2 * Star.mu n ε' ρ = ε' / (3 * θ * L ^ 2) := by
    rw [Star.mu, hθdef, Star.L_eq]; ring
  -- the deterministic consequence
  have hdet : (⋃ p ∈ P, Bad p)ᶜ ⊆ {ω | ∀ U : Finset V, U.Nonempty → U ⊆ G.verts →
        ∀ F : Finset (Sym2 V), F ⊆ G.edges →
          (F.card : ℝ) ≤ Star.mu n ε' ρ * (U.card : ℝ) →
          ((R ω).card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell n) U (R ω)).card : ℝ)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
    have key : ∀ U₀ : Finset V, U₀ ⊆ G.verts → 1 ≤ U₀.card →
        (U₀.card : ℝ) ≤ 2 * (n : ℝ) / 3 → ∀ F : Finset (Sym2 V), F ⊆ G.edges →
        (F.card : ℝ) ≤ 2 * Star.mu n ε' ρ * (U₀.card : ℝ) →
        ((R ω).card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell n) U₀ (R ω)).card : ℝ) := by
      intro U₀ hU₀V hU₀1 hU₀23 F hFE hFc
      obtain ⟨U', hU'U, hwe, hcard⟩ := prop18 G hG hn hε hε2 hθ1 hs U₀ hU₀V hU₀1 hU₀23
      rw [hmu] at hFc
      have hFU' : F.card ≤ U'.card := by
        have : (F.card : ℝ) ≤ U'.card := by
          refine hFc.trans (le_of_eq_of_le ?_ hcard)
          rw [← hLdef]; ring
        exact_mod_cast this
      have hU'pos : 0 < (U'.card : ℝ) := by
        have h1 : (1 : ℝ) ≤ U₀.card := by exact_mod_cast hU₀1
        have hθ0 : 0 < θ := by linarith
        have hL : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < n))
        have : 0 < ε' * (U₀.card : ℝ) / (3 * θ * L ^ 2) := by positivity
        exact this.trans_le hcard
      have hU'ne : U'.Nonempty := Finset.card_pos.1 (by exact_mod_cast hU'pos)
      have hmem : (U', F) ∈ P := by
        rw [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
          Finset.mem_powerset]
        exact ⟨⟨hU'U.trans hU₀V, hFE⟩, hU'ne, hFU', hwe⟩
      have hnb := hω (U', F) hmem
      simp only [hBad, Set.mem_ofPred_eq, not_le] at hnb
      exact hnb.trans_le (by exact_mod_cast Finset.card_le_card (ball_mono_left hU'U))
    intro U hUne hUV F hFE hFc
    have hmu0 : 0 ≤ Star.mu n ε' ρ := (Star.mu_pos hn hε h0).le
    by_cases hsmall : (U.card : ℝ) ≤ 2 * (n : ℝ) / 3
    · refine key U hUV (Finset.card_pos.2 hUne) hsmall F hFE ?_
      have : (0 : ℝ) ≤ Star.mu n ε' ρ * U.card := by positivity
      linarith
    · push Not at hsmall
      have hUn : U.card ≤ n := Finset.card_le_card hUV
      obtain ⟨Ub, hUbU, hUbc⟩ := Finset.exists_subset_card_eq (s := U) (n := (n + 1) / 2) (by
        have h3 : (2 * (n : ℝ)) < 3 * U.card := by linarith
        have h3' : 2 * n < 3 * U.card := by exact_mod_cast h3
        omega)
      have hUb1 : 1 ≤ Ub.card := by omega
      have hUb23 : (Ub.card : ℝ) ≤ 2 * (n : ℝ) / 3 := by
        rw [hUbc]
        have : 3 * ((n + 1) / 2) ≤ 2 * n := by omega
        have : (3 : ℝ) * (((n + 1) / 2 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast this
        linarith
      have hUbn : (n : ℝ) ≤ 2 * Ub.card := by
        rw [hUbc]
        have : n ≤ 2 * ((n + 1) / 2) := by omega
        exact_mod_cast this
      have hFUb : (F.card : ℝ) ≤ 2 * Star.mu n ε' ρ * (Ub.card : ℝ) := by
        have h1 : Star.mu n ε' ρ * (U.card : ℝ) ≤ Star.mu n ε' ρ * n :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hUn) hmu0
        have h2 : Star.mu n ε' ρ * (n : ℝ) ≤ Star.mu n ε' ρ * (2 * Ub.card) :=
          mul_le_mul_of_nonneg_left hUbn hmu0
        linarith
      have := key Ub (hUbU.trans hUV) hUb1 hUb23 F hFE hFUb
      exact this.trans_le (by exact_mod_cast Finset.card_le_card (ball_mono_left hUbU))
  -- the union bound
  have hpb : ∀ p ∈ P, μ.prob (Bad p) ≤ Real.exp (-(7 * (p.1.card : ℝ) * L)) := by
    intro p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
      Finset.mem_powerset] at hp
    exact hL17 V G ε' s₁ ρ Ω μ R hG hn hε1 hε2 h0 h1 (h8.trans (by linarith)) hR p.1 p.2
      hp.1.1 hp.1.2 hp.2.2.1 hp.2.2.2
  have hsum : ∑ p ∈ P, Real.exp (-(7 * (p.1.card : ℝ) * L)) ≤ (n : ℝ) ^ (-6 : ℤ) := by
    refine le_trans ?_ (union_sum_le G hn)
    rw [hPdef, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_le_sum fun U hU => ?_
    by_cases hUne : U.Nonempty
    · rw [if_pos hUne]
      have h1 : ∑ F ∈ G.edges.powerset, (if U.Nonempty ∧ F.card ≤ U.card ∧
            G.IsWellExpanding θ U then Real.exp (-(7 * (U.card : ℝ) * L)) else 0) ≤
          ∑ F ∈ G.edges.powerset.filter (fun F => F.card ≤ U.card),
            Real.exp (-(7 * (U.card : ℝ) * L)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun F _ => ?_
        split_ifs with ha hb
        · exact le_rfl
        · exact absurd ha.2.1 hb
        · exact (Real.exp_pos _).le
        · exact le_rfl
      refine h1.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc := card_filter_powerset_le G.edges U.card
      have hc' : (((G.edges.powerset.filter (fun F => F.card ≤ U.card)).card : ℕ) : ℝ) ≤
          ((G.edges.card + 1 : ℕ) : ℝ) ^ U.card := by exact_mod_cast hc
      push_cast at hc'
      exact mul_le_mul_of_nonneg_right hc' (Real.exp_pos _).le
    · rw [if_neg hUne]
      refine le_of_eq (Finset.sum_eq_zero fun F _ => ?_)
      rw [if_neg (fun h => hUne h.1)]
  -- conclusion
  have hU : μ.prob (⋃ p ∈ P, Bad p) ≤ (n : ℝ) ^ (-6 : ℤ) :=
    (μ.prob_biUnion_le P Bad).trans ((Finset.sum_le_sum hpb).trans hsum)
  have := μ.prob_mono hdet
  rw [μ.prob_compl] at this
  linarith

end EG.P18sProof
