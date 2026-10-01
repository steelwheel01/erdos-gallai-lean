module

public import EG.Defs.Stage1.Pool
public import EG.Lib.Prob.Indep

/-!
# API for the pool labels (s7:defPool)

Lemmas about `EG/Defs/Stage1/Pool.lean`:
* `mem_poolIdx` (`3 ≤ l ≤ R`, `1 ≤ r`, `r + 2 ≤ l`);
* the law under its guard: `poolLabelLaw_w_of_le`, `prob_poolLabelLaw_some`
  (`P(plab(v) = (l,r)) = q_l π_{l,r}`), `prob_poolLabelLaw_none`;
* `piPool_eq` (`π_{l,r} = (1/2)^{l-1-r}` for `r + 2 ≤ l`), `sum_piPool`
  (`Σ_{r=1}^{l-2} π_{l,r} = 1 - 2^{-(l-2)}`);
* sets: `mem_poolSet`, `mem_poolL`, `disjoint_poolL` ("The sets `Pool_l` (`3 ≤ l ≤ R`) are
  pairwise disjoint, because every vertex has one label"), `disjoint_poolSet` (the union
  defining `Pool_l` is disjoint), `mem_poolSet_poolRound` and `poolRound_eq` ("For `w ∈ Pool_l`
  let `r(w)` denote the unique `r` with `w ∈ Pool_{l,r}`").
* `two_pow_le_M` (`2^40 ≤ M_l`), `qPool_pos`, `qPool_le` (`0 < q_l ≤ 2^{-80}`).
`poolMass ≤ 1` under Γ is an s7 Spec (s2:lemTower (b)).
-/

public section

namespace EG.Stage1

open EG.HB EG.FinDist Finset

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

omit [DecidableEq V] in
theorem mem_poolIdx {l r : ℕ} :
    (l, r) ∈ poolIdx run ↔ 3 ≤ l ∧ l ≤ run.R ∧ 1 ≤ r ∧ r + 2 ≤ l := by
  simp only [poolIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

theorem poolLabelLaw_w_of_le (h : poolMass G run ≤ 1) (o : Option (ℕ × ℕ)) :
    (poolLabelLaw G run).w o = plabWeight G run o := by
  unfold poolLabelLaw
  rw [dif_pos h]
  rfl

/-- [s7:defPool] "`P(plab(v) = (l,r)) = q_l π_{l,r}`". -/
theorem prob_poolLabelLaw_some (h : poolMass G run ≤ 1) {l r : ℕ} (hp : (l, r) ∈ poolIdx run) :
    (poolLabelLaw G run).prob {some (l, r)} = qPool G run l * piPool l r := by
  classical
  rw [prob_singleton, poolLabelLaw_w_of_le G run h]
  simp [plabWeight, hp]

/-- [s7:defPool] "`P(plab(v) = ⊥) := 1 - Σ_{l,r} q_l π_{l,r}`". -/
theorem prob_poolLabelLaw_none (h : poolMass G run ≤ 1) :
    (poolLabelLaw G run).prob {none} = 1 - poolMass G run := by
  rw [prob_singleton, poolLabelLaw_w_of_le G run h]
  rfl

/-- `π_{l,r} = (1/2)^{l-1-r}` with a natural exponent, for `r + 2 ≤ l`. -/
theorem piPool_eq {l r : ℕ} (h : r + 2 ≤ l) : piPool l r = (1 / 2 : ℝ) ^ (l - 1 - r) := by
  rw [piPool, show (-((l : ℤ) - 1 - (r : ℤ))) = -((l - 1 - r : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_sub (by omega : r ≤ l - 1)]; ring,
    zpow_neg, zpow_natCast, one_div, inv_pow]

/-- [s7:defPool] "for each `l` we have `Σ_{r=1}^{l-2} π_{l,r} = 1 - 2^{-(l-2)}`". -/
theorem sum_piPool (l : ℕ) (hl : 3 ≤ l) :
    ∑ r ∈ (Finset.Icc 1 l).filter (fun r => r + 2 ≤ l), piPool l r = 1 - (1 / 2 : ℝ) ^ (l - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 3 := ⟨l - 3, by omega⟩
  have e : (Finset.Icc 1 (k + 3)).filter (fun r => r + 2 ≤ k + 3) = Finset.Icc 1 (k + 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e, Finset.sum_congr rfl fun r hr => piPool_eq (by simp at hr; omega)]
  induction k with
  | zero => norm_num [piPool_eq]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ∀ r ∈ Finset.Icc 1 (k + 1), (1 / 2 : ℝ) ^ (k + 1 + 3 - 1 - r) =
        (1 / 2) * (1 / 2 : ℝ) ^ (k + 3 - 1 - r) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      rw [← pow_succ']
      congr 1
      omega
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    have ih' := ih (by omega) (by
      ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega)
    rw [ih', show k + 1 + 3 - 1 - (k + 1 + 1) = 1 by omega, show k + 1 + 3 - 2 = (k + 3 - 2) + 1 by omega,
      pow_succ]
    ring

variable {G}

theorem mem_poolSet {π : ↥G.verts → Option (ℕ × ℕ)} {l r : ℕ} {v : V} :
    v ∈ poolSet G π l r ↔ v ∈ G.verts ∧ plabOf π v = some (l, r) := by
  simp [poolSet]

theorem mem_poolL {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {v : V} :
    v ∈ poolL G π l ↔ v ∈ G.verts ∧ ∃ r, 1 ≤ r ∧ r + 2 ≤ l ∧ plabOf π v = some (l, r) := by
  simp only [poolL, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, mem_poolSet]
  constructor
  · rintro ⟨r, ⟨⟨h1, -⟩, h2⟩, hv, hp⟩
    exact ⟨hv, r, h1, h2, hp⟩
  · rintro ⟨hv, r, h1, h2, hp⟩
    exact ⟨r, ⟨⟨h1, by omega⟩, h2⟩, hv, hp⟩

/-- [s7:defPool] "The sets `Pool_l` (`3 ≤ l ≤ R`) are pairwise disjoint, because every vertex has
one label" (for every outcome). -/
theorem disjoint_poolL (π : ↥G.verts → Option (ℕ × ℕ)) {l l' : ℕ} (h : l ≠ l') :
    Disjoint (poolL G π l) (poolL G π l') := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  obtain ⟨-, r, -, -, hr⟩ := mem_poolL.1 h1
  obtain ⟨-, r', -, -, hr'⟩ := mem_poolL.1 h2
  rw [hr] at hr'
  exact h (Prod.mk.inj (Option.some.inj hr')).1

/-- [s7:defPool] "`Pool_l := ⋃_{r=1}^{l-2} Pool_{l,r}` (a disjoint union)". -/
theorem disjoint_poolSet (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) {r r' : ℕ} (h : r ≠ r') :
    Disjoint (poolSet G π l r) (poolSet G π l r') := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  rw [mem_poolSet] at h1 h2
  rw [h1.2] at h2
  exact h (Prod.mk.inj (Option.some.inj h2.2)).2

/-- [s7:defPool] "For `w ∈ Pool_l` let `r(w)` denote the unique `r` with `w ∈ Pool_{l,r}`":
existence. -/
theorem mem_poolSet_poolRound {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {w : V}
    (hw : w ∈ poolL G π l) : w ∈ poolSet G π l (poolRound π w) := by
  obtain ⟨hv, r, -, -, hr⟩ := mem_poolL.1 hw
  rw [mem_poolSet]
  refine ⟨hv, ?_⟩
  simp [poolRound, hr]

/-- Uniqueness of `r(w)`. -/
theorem poolRound_eq {π : ↥G.verts → Option (ℕ × ℕ)} {l r : ℕ} {w : V}
    (hw : w ∈ poolSet G π l r) : poolRound π w = r := by
  rw [mem_poolSet] at hw
  simp [poolRound, hw.2]

/-! ### Size of `q_l` -/

variable (G)

/-- [s2:defHBtp] (R2) "`M_l := ⌈max(2^{40}, …)⌉`": `2^40 ≤ M_l` for every round. -/
theorem two_pow_le_M (l : ℕ) : 2 ^ 40 ≤ run.M G l := by
  change 2 ^ 40 ≤ MOf (run.d G l)
  unfold MOf
  have h : ((2 ^ 40 : ℕ) : ℝ) ≤
      max ((2 : ℝ) ^ 40) (2 ^ 16 * TOf (run.d G l) * Real.logb 2 (TOf (run.d G l)) ^ 4) :=
    calc ((2 ^ 40 : ℕ) : ℝ) = (2 : ℝ) ^ 40 := by push_cast; ring
      _ ≤ _ := le_max_left _ _
  have := Nat.ceil_mono h
  rwa [Nat.ceil_natCast] at this

/-- `q_l = M_l^{-2} > 0`. -/
theorem qPool_pos (l : ℕ) : 0 < qPool G run l := by
  unfold qPool
  have : (0 : ℝ) < run.M G l := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) (two_pow_le_M G run l) : 0 < run.M G l)
  exact zpow_pos this _

/-- `q_l = M_l^{-2} ≤ 2^{-80}`. -/
theorem qPool_le (l : ℕ) : qPool G run l ≤ 2 ^ (-80 : ℤ) := by
  unfold qPool
  have h : (2 : ℝ) ^ 40 ≤ run.M G l := by exact_mod_cast two_pow_le_M G run l
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  have h2 : ((2 : ℝ) ^ 40) ^ 2 ≤ (run.M G l : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  calc ((run.M G l : ℝ) ^ 2)⁻¹ ≤ (((2 : ℝ) ^ 40) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
    _ = ((2 : ℝ) ^ 80)⁻¹ := by norm_num

end EG.Stage1
