module

public import EG.Lib.Quot.Round
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers for Lemma "Ultra-hub copies" (manuscript s7:lemUltra (iv))

* `logb_add_eight_mul_le`: "`g(x) := (log₂x + 8)/x` is decreasing on `[1,∞)`", in the form
  `(log₂y + 8)·x ≤ (log₂x + 8)·y` for `1 ≤ x ≤ y`;
* `RoundInput.sum_clive_le`: `Σ_h c^live_h ≤ |J_l| ≤ n(M_l − 1)` (items of distinct hubs are
  distinct edges; hubs and ports are disjoint, (J3)); "By (J2) … `Σ_h c^live_h ≤ |J_l|`";
* `RoundInput.Hcd_eq`, `RoundInput.thult_ge`: `θ^ult_l ≥ M_l Hcd_l/7 − 1` and `θ^ult_l ≥ 1`.
-/

public section

namespace EG.Quot

open Real

/-- "The function `g(x) := (log₂x + 8)/x` is decreasing on `[1, ∞)`" (cross-multiplied). -/
theorem logb_add_eight_mul_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (logb 2 y + 8) * x ≤ (logb 2 x + 8) * y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 ≤ logb 2 x := logb_nonneg (by norm_num) hx
  -- `log₂ y = log₂ x + log₂ (y/x)` and `log₂ t ≤ (t − 1)/ln 2 ≤ 8(t − 1)`
  have ht : 1 ≤ y / x := by rw [le_div_iff₀ hx0]; linarith
  have hsplit : logb 2 y = logb 2 x + logb 2 (y / x) := by
    rw [logb_div hy0.ne' hx0.ne']; ring
  have hln2 : (1 : ℝ) / 8 < Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num); norm_num at this ⊢; linarith
  have hlog : logb 2 (y / x) ≤ 8 * (y / x - 1) := by
    rw [logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h1 := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos ht)
    have h2 : 0 ≤ y / x - 1 := by linarith
    nlinarith
  have hkey : x * logb 2 (y / x) ≤ 8 * (y - x) := by
    have := mul_le_mul_of_nonneg_left hlog hx0.le
    have e : x * (8 * (y / x - 1)) = 8 * (y - x) := by field_simp
    linarith
  rw [hsplit]
  nlinarith

/-- The final computation of [s7:lemUltra] (iv) (with `Σ_h c^live_h ≤ nM`): if
`Hcd = L/(8M^2)`, `θ ≥ L/(57M)`, `θ > 0`, `K ≥ 8` and `e < 3`, then
`(4MK/θ + 4e/Hcd)·nM ≤ 320 nM^3 K/L`. -/
theorem ultraSum_arith {M n θ L Hc e K : ℝ} (hM : 0 < M) (hn : 0 ≤ n) (hθ : 0 < θ) (hL : 0 < L)
    (hHc : Hc = L / (8 * M ^ 2)) (hθL : L / (57 * M) ≤ θ) (hK : 8 ≤ K) (he0 : 0 < e)
    (he : e < 3) :
    (4 * M * K / θ + 4 * e / Hc) * (n * M) ≤ 320 * (n * M ^ 3 * K) / L := by
  have hinvθ : 1 / θ ≤ 57 * M / L := by
    rw [div_le_div_iff₀ hθ hL]
    rw [div_le_iff₀ (by positivity)] at hθL
    linarith
  have hK0 : 0 ≤ K := by linarith
  have t1 : 4 * M * K / θ ≤ 228 * M ^ 2 * K / L := by
    have e1 : 4 * M * K / θ = 4 * M * K * (1 / θ) := by ring
    rw [e1]
    calc 4 * M * K * (1 / θ) ≤ 4 * M * K * (57 * M / L) :=
          mul_le_mul_of_nonneg_left hinvθ (by positivity)
      _ = 228 * M ^ 2 * K / L := by ring
  have t2 : 4 * e / Hc ≤ 12 * M ^ 2 * K / L := by
    rw [hHc, div_div_eq_mul_div, div_le_div_iff_of_pos_right hL]
    have hM2 : 0 ≤ M ^ 2 := by positivity
    nlinarith
  have hsum : 4 * M * K / θ + 4 * e / Hc ≤ 240 * M ^ 2 * K / L := by
    have := add_le_add t1 t2
    have e2 : 228 * M ^ 2 * K / L + 12 * M ^ 2 * K / L = 240 * M ^ 2 * K / L := by ring
    linarith
  calc (4 * M * K / θ + 4 * e / Hc) * (n * M) ≤ 240 * M ^ 2 * K / L * (n * M) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ ≤ 320 * (n * M ^ 3 * K) / L := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL]
        have : 0 ≤ n * M ^ 3 * K := by positivity
        nlinarith

namespace RoundInput

variable {V : Type*} [DecidableEq V] (I : RoundInput V)

/-- `Σ_{h ∈ S} c^live_h ≤ |J_l|` for every set `S` of vertices (the live hub items of distinct hubs
are distinct edges of `J^hub_l`, since hubs are not ports). -/
theorem sum_clive_le_card_J (hd : Disjoint I.hubs I.ports) (S : Finset V) :
    ∑ h ∈ S, I.clive h ≤ I.J.card := by
  classical
  have h1 : ∑ h ∈ S, I.clive h = (I.hubItems.filter (fun p => p.1 ∈ S)).card := by
    have hmaps : ((I.hubItems.filter (fun p => p.1 ∈ S) : Finset (V × V)) : Set (V × V)).MapsTo
        Prod.fst (S : Set V) := fun p hp => by
      simpa using (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun h hh => ?_
    unfold clive
    rw [Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun p _ => ?_
    constructor
    · intro e; exact ⟨e ▸ hh, e⟩
    · exact fun e => e.2
  rw [h1]
  refine le_trans ?_ (Finset.card_le_card (show I.Jhub ⊆ I.J from fun e he => by
    unfold J; simp [he]))
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    exact ((Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2).2
  · intro p hp q hq hpq
    have hp' := (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
    have hq' := (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hq).1).1)
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      exact Finset.disjoint_left.1 hd hp'.1 (h1 ▸ hq'.2)

omit [DecidableEq V] in
theorem Hcd_eq : I.Hcd = I.lam ^ 95 / (8 * (I.M : ℝ) ^ 2) := rfl

omit [DecidableEq V] in
theorem thult_eq : I.thult = ⌊(I.M : ℝ) * I.Hcd / 7⌋₊ := rfl

omit [DecidableEq V] in
/-- `θ^ult_l > M_l Hcd_l / 7 − 1`. -/
theorem thult_gt : (I.M : ℝ) * I.Hcd / 7 - 1 < I.thult := by
  rw [thult_eq]
  have := Nat.lt_floor_add_one ((I.M : ℝ) * I.Hcd / 7)
  linarith

omit [DecidableEq V] in
/-- `θ^ult_l ≥ 1` as soon as `M_l Hcd_l ≥ 7`. -/
theorem one_le_thult (h : 7 ≤ (I.M : ℝ) * I.Hcd) : 1 ≤ I.thult := by
  rw [thult_eq]
  exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)

end RoundInput

end EG.Quot
