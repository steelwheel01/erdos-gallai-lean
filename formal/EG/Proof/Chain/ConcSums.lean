module

public import EG.Proof.Chain.CONCL
public import EG.Proof.Chain.ConcTower
public import EG.Proof.HB.TowerC
public import EG.Proof.HB.OVRunK
public import EG.Proof.HB.LacunaryGeom

/-!
# The sums of Theorems CONC (iii) and CONC-L (iv) (manuscript s6:thmCONC, s6:thmCONCL)

Unit P3B (probe P-3, part 2), proof round 1. Statements: `EG/Spec/Chain/CONC.lean`
(`ConcIIIStatement`, `ConcTauSumStatement`, `ConcDStarSumStatement`) and
`EG/Spec/Chain/CONCL.lean` (`ConcLGCSumStatement`, `ConcLSumStatement`). Design note
`formal/work/p2b/P3B.md`.

Declared inputs used: `EG.towerA` ([s2:lemTower] (a): `R - r ≤ 2 log* d_r - 1`; through
`EG.towerHalf`), `EG.towerC` ([s2:lemTower] (c): `τ_r/P_r ≤ 2^{σ+11}/λ_r`), `EG.ovK1`, `EG.ovK3`
([s2:propOV] (K1), (K3)), `EG.lacunaryGeom` ([s2:lemLacunary] (i)).

Structure (as in the manuscript):
* re-indexing (hazard H1): `sum_ancestors` (`Σ_{Y ancestor} = Σ_{r ∈ [1,R]} Σ_{a pre-part of r}`),
  `ancestors_filter_fst`, `sum_Icc_swap` (`Σ_{l ∈ [1,R]} Σ_Y [r(Y)+2 ≤ l] A_Y =
  Σ_Y Σ_{l ∈ [r(Y)+2, R]} A_Y`);
* the three tower sums `Σ_r 𝖺(d_r) ≤ 2𝖺(d_R)` etc. (`tower_sum_le`, from (s6:eqTowerHalf) and
  Lemma Lacunary (i)) and (s6:eqTowerEnd);
* the `τ`-, `d^*`- and `θ^GC`-sums; then (iii) and (iv) from the per-ancestor bounds.
-/

public section

namespace EG

open EG.HB EG.Chain Real

namespace Chain

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V}

/-! ### Re-indexing -/

theorem ancestors_filter_fst (r : ℕ) :
    (run.ancestors G).filter (fun Y => Y.1 = r) = (run.prePartAddrs G r).image (fun a => (r, a)) := by
  ext ⟨r', a⟩
  simp only [Finset.mem_filter, Run.mem_ancestors, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨a, h, rfl, rfl⟩
  · rintro ⟨a', ha', rfl, rfl⟩; exact ⟨ha', rfl⟩

theorem card_ancestors_filter_fst (r : ℕ) :
    ((run.ancestors G).filter (fun Y => Y.1 = r)).card = (run.prePartAddrs G r).card := by
  rw [ancestors_filter_fst, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]

/-- `Σ_{Y ancestor} F(Y) = Σ_{r ∈ [1,R]} Σ_{a pre-part of round r} F(r, a)`. -/
theorem sum_ancestors (F : PartId → ℝ) :
    ∑ Y ∈ run.ancestors G, F Y = ∑ r ∈ Finset.Icc 1 run.R, ∑ a ∈ run.prePartAddrs G r, F (r, a) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := run.ancestors G) (g := Prod.fst)
    (t := Finset.Icc 1 run.R) (fun Y hY => Finset.mem_Icc.2 (Run.isRound_of_mem_parts run G hY)) F]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [ancestors_filter_fst, Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).2)]

/-- `Σ_{l ∈ [1,R]} Σ_{Y ∈ S} [r(Y) + 2 ≤ l] A_Y = Σ_{Y ∈ S} Σ_{l ∈ [r(Y)+2, R]} A_Y`. -/
theorem sum_Icc_swap (R : ℕ) (S : Finset PartId) (A : PartId → ℝ) :
    ∑ l ∈ Finset.Icc 1 R, ∑ Y ∈ S, (if Y.1 + 2 ≤ l then A Y else 0) =
      ∑ Y ∈ S, ∑ _l ∈ Finset.Icc (Y.1 + 2) R, A Y := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- `#[r+2, R] ≤ 2 log* d_r + 1` from [s2:lemTower] (a) (`R - r ≤ 2 log* d_r - 1`). -/
theorem card_Icc_le {r R L : ℕ} (h : (R : ℤ) - r ≤ 2 * (L : ℤ) - 1) :
    ((Finset.Icc (r + 2) R).card : ℝ) ≤ 2 * (L : ℝ) + 1 := by
  rw [Nat.card_Icc]
  have : R + 1 - (r + 2) ≤ 2 * L + 1 := by omega
  exact_mod_cast this

/-! ### Facts at a round -/

theorem logb_pos_of_valid {Dstar : ℝ} (hΓ : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ}
    (hr : run.IsRound r) :
    Dstar ≤ run.d G r ∧ (2 : ℝ) ^ 256 ≤ logb 2 (run.d G r) ∧
      (2 : ℝ) ^ 8 ≤ logb 2 (logb 2 (run.d G r)) := by
  have hd := Run.Valid.dstar_le run G hv hr
  refine ⟨hd, le_trans hΓ.two_pow_256_le_logb
    (Real.logb_le_logb_of_le (by norm_num) (by linarith [hΓ.two_lt]) hd),
    le_trans hΓ.two_pow_eight_le_loglog (loglog_mono hΓ.two_lt hd)⟩

theorem towA_nonneg {Dstar d : ℝ} (hΓ : Gamma1core Dstar) (hd : Dstar ≤ d) : 0 ≤ towA d := by
  unfold towA
  have : 0 < logb 2 d := lt_of_lt_of_le (by linarith [hΓ.one_lt_logb])
    (Real.logb_le_logb_of_le (by norm_num) (by linarith [hΓ.two_lt]) hd)
  positivity

theorem towB_nonneg {Dstar d : ℝ} (hΓ : Gamma1core Dstar) (hd : Dstar ≤ d) : 0 ≤ towB d := by
  unfold towB
  have : 0 < logb 2 (logb 2 d) :=
    lt_of_lt_of_le (by linarith [hΓ.two_pow_eight_le_loglog]) (loglog_mono hΓ.two_lt hd)
  positivity

theorem towC_nonneg (d : ℝ) : 0 ≤ towC d := by
  unfold towC
  have := rpow_half_nonneg (logb 2 d)
  positivity

/-- (s6:eqTowerHalf) and Lemma [s2:lemLacunary] (i): `Σ_{r ≤ R} f(d_r) ≤ 2 f(d_R)` for
`f = 𝖺, 𝖻, 𝖼`. -/
theorem tower_sum_le {Dstar : ℝ} (hΓ : Gamma1core Dstar) (hv : run.Valid G Dstar)
    (hR : 1 ≤ run.R) :
    ∑ r ∈ Finset.Icc 1 run.R, towA (run.d G r) ≤ 2 * towA (run.d G run.R) ∧
    ∑ r ∈ Finset.Icc 1 run.R, towB (run.d G r) ≤ 2 * towB (run.d G run.R) ∧
    ∑ r ∈ Finset.Icc 1 run.R, towC (run.d G r) ≤ 2 * towC (run.d G run.R) := by
  have hd : ∀ r ∈ Finset.Icc 1 run.R, Dstar ≤ run.d G r := fun r hr =>
    Run.Valid.dstar_le run G hv (Finset.mem_Icc.1 hr)
  have hH := fun r hr => towerHalf _ G Dstar run hΓ hv r hr
  refine ⟨(lacunaryGeom (fun r => towA (run.d G r)) run.R hR
      (fun r hr => towA_nonneg hΓ (hd r hr)) (fun r hr => (hH r hr).1)).1,
    (lacunaryGeom (fun r => towB (run.d G r)) run.R hR
      (fun r hr => towB_nonneg hΓ (hd r hr)) (fun r hr => (hH r hr).2.1)).1,
    (lacunaryGeom (fun r => towC (run.d G r)) run.R hR
      (fun r _ => towC_nonneg _) (fun r hr => (hH r hr).2.2)).1⟩

theorem two_pow_sigma14 : (2 : ℝ) ^ (sigmaC + 14) = (2 : ℝ) ^ (sigmaC + 11) * 8 := by
  have : sigmaC + 14 = (sigmaC + 11) + 3 := by rw [Nat.add_assoc]
  rw [this, pow_add]
  norm_num

theorem kStar_six {Dstar : ℝ} (hΓ : Gamma1core Dstar) : (6 : ℝ) ≤ (logStar Dstar : ℝ) := by
  exact_mod_cast (kStar Dstar hΓ).2.2.2

end Chain

open Chain in
/-- [s6:thmCONC] (proof of (iii), "*The `τ`-term.*") and [s6:thmCONCL] (proof of (iv),
"*`τ`-terms.*"): `Σ_{(Y,l)} (τ_{r(Y)} - 1) ≤ 2^{σ+14} n log* D_*/log D_*` over all ancestors. -/
theorem concTauSum : EG.Spec.ConcTauSumStatement := by
  intro V _ G D run hΓ hv
  have hk6 := kStar_six hΓ
  have ht0 : 0 < logb 2 D := lt_trans zero_lt_one hΓ.one_lt_logb
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hRHS : 0 ≤ (2 : ℝ) ^ (sigmaC + 14) * (G.card : ℝ) * (logStar D : ℝ) / logb 2 D := by
    positivity
  rw [show (∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R,
      ((run.tau G Y.1 - 1 : ℕ) : ℝ)) = ∑ Y ∈ run.ancestors G,
        ((Finset.Icc (Y.1 + 2) run.R).card : ℝ) * ((run.tau G Y.1 - 1 : ℕ) : ℝ) from
      Finset.sum_congr rfl (fun Y _ => by rw [Finset.sum_const, nsmul_eq_mul]),
    sum_ancestors]
  rcases Nat.eq_zero_or_pos run.R with hR0 | hR
  · rw [hR0]; simpa using hRHS
  have hd1 : D ≤ run.d G 1 := Run.Valid.dstar_le run G hv ⟨le_rfl, hR⟩
  obtain ⟨-, -, hA3, -, -⟩ := towerA _ G D run hΓ hv hd1
  have hK1 := ovK1 _ G D run hΓ.gamma2a hv
  set c : ℝ := (2 : ℝ) ^ (sigmaC + 11) with hc
  have hc0 : 0 ≤ c := by positivity
  -- per round
  have hround : ∀ r ∈ Finset.Icc 1 run.R,
      ∑ a ∈ run.prePartAddrs G r, ((Finset.Icc ((r, a).1 + 2) run.R).card : ℝ) *
        ((run.tau G (r, a).1 - 1 : ℕ) : ℝ) ≤ 1.37 * c * (G.card : ℝ) * towA (run.d G r) := by
    intro r hr
    obtain ⟨hdr, hl256, -⟩ := logb_pos_of_valid hΓ hv (Finset.mem_Icc.1 hr)
    have hlam0 : 0 < run.lam G r := lt_of_lt_of_le (by positivity) hl256
    obtain ⟨-, -, hC3, -⟩ := towerC _ G D run hΓ hv hd1 r hr
    obtain ⟨-, -, hK13⟩ := hK1.1 r hr
    dsimp only
    rw [Finset.sum_const, nsmul_eq_mul]
    have hP0 : (0 : ℝ) ≤ (run.P G r : ℝ) := Nat.cast_nonneg _
    have hcard : ((run.prePartAddrs G r).card : ℝ) ≤ 1.37 * (G.card : ℝ) / (run.P G r : ℝ) := by
      rw [← card_ancestors_filter_fst]; exact hK13
    have hIcc := card_Icc_le (r := r) (hA3 r hr)
    have hIcc' : ((Finset.Icc (r + 2) run.R).card : ℝ) ≤ 2 * (logStar (run.d G r) : ℝ) + 2 := by
      linarith
    have htau : ((run.tau G r - 1 : ℕ) : ℝ) ≤ (run.tau G r : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    calc ((run.prePartAddrs G r).card : ℝ) * (((Finset.Icc (r + 2) run.R).card : ℝ) *
          ((run.tau G r - 1 : ℕ) : ℝ))
        ≤ (1.37 * (G.card : ℝ) / (run.P G r : ℝ)) *
            ((2 * (logStar (run.d G r) : ℝ) + 2) * (run.tau G r : ℝ)) := by
          apply mul_le_mul hcard _ (by positivity) (by positivity)
          exact mul_le_mul hIcc' htau (by positivity) (by positivity)
      _ = 1.37 * (G.card : ℝ) * (2 * (logStar (run.d G r) : ℝ) + 2) *
            ((run.tau G r : ℝ) / (run.P G r : ℝ)) := by ring
      _ ≤ 1.37 * (G.card : ℝ) * (2 * (logStar (run.d G r) : ℝ) + 2) * (c / run.lam G r) :=
          mul_le_mul_of_nonneg_left hC3 (by positivity)
      _ = 1.37 * c * (G.card : ℝ) * towA (run.d G r) := by
          unfold towA; simp only [Run.lam, lamOf]; ring
  have hsum := (tower_sum_le hΓ hv hR).1
  have hdR : D ≤ run.d G run.R := Run.Valid.dstar_le run G hv ⟨hR, le_rfl⟩
  have hend := (towerEnd D hΓ (run.d G run.R) hdR).1
  have hkey : 1.37 * 2 * (2 * (logStar D : ℝ) + 4) ≤ 8 * (logStar D : ℝ) := by nlinarith
  calc ∑ r ∈ Finset.Icc 1 run.R, ∑ a ∈ run.prePartAddrs G r,
        ((Finset.Icc ((r, a).1 + 2) run.R).card : ℝ) * ((run.tau G (r, a).1 - 1 : ℕ) : ℝ)
      ≤ ∑ r ∈ Finset.Icc 1 run.R, 1.37 * c * (G.card : ℝ) * towA (run.d G r) :=
        Finset.sum_le_sum hround
    _ = 1.37 * c * (G.card : ℝ) * ∑ r ∈ Finset.Icc 1 run.R, towA (run.d G r) := by
        rw [Finset.mul_sum]
    _ ≤ 1.37 * c * (G.card : ℝ) * (2 * ((2 * (logStar D : ℝ) + 4) / logb 2 D)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) hc0) hn)
        linarith
    _ = (1.37 * 2 * (2 * (logStar D : ℝ) + 4)) * (c * (G.card : ℝ) / logb 2 D) := by ring
    _ ≤ (8 * (logStar D : ℝ)) * (c * (G.card : ℝ) / logb 2 D) :=
        mul_le_mul_of_nonneg_right hkey (div_nonneg (mul_nonneg hc0 hn) ht0.le)
    _ = (2 : ℝ) ^ (sigmaC + 14) * (G.card : ℝ) * (logStar D : ℝ) / logb 2 D := by
        rw [hc, two_pow_sigma14]; ring

namespace Chain

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}

/-- `d^*_{Y,l} ≤ [r(Y) + 2 ≤ l] |Y^0 ∩ Dup*_{r(Y)}|` (proof of CONC (iii), "*The `d^*`-term.*":
a port counted in `d^*_{Y,l}` lies in `V(Y) ∩ Dup*_{r(Y)} ⊆ Y^0 ∩ Dup*_{r(Y)}`). -/
theorem dStar_le_ite (hδ : IsDesignation run G δ) (Y : PartId) (l : ℕ) :
    (dStar run G δ Y l : ℝ) ≤
      if Y.1 + 2 ≤ l then ((run.Z0 G Y.1 Y.2 ∩ run.DupStar G Y.1).card : ℝ) else 0 := by
  have hfacts : ∀ u ∈ (classedPorts run G l).filter (fun u => δ l u = Y ∧ u ∈ run.DupStar G Y.1),
      Y.1 + 2 ≤ l ∧ u ∈ run.Z0 G Y.1 Y.2 ∩ run.DupStar G Y.1 := by
    intro u hu
    obtain ⟨hu1, hY, hD⟩ := Finset.mem_filter.1 hu
    obtain ⟨a, ha, hua⟩ := (mem_classedPorts run G).1 hu1
    have hl : 3 ≤ l := by
      by_contra hl
      rw [classed_eq_empty_of_le_two run G (by omega)] at hua
      exact Finset.notMem_empty u hua
    have hV := hδ.mem_ancVerts hl ha hua
    have h2 := hδ.round_add_two_le hl ha hua
    rw [hY] at hV h2
    exact ⟨h2, Finset.mem_inter.2 ⟨Run.partVerts_subset_Z0 run G Y.1 Y.2 hV, hD⟩⟩
  unfold dStar
  split_ifs with h
  · exact_mod_cast Finset.card_le_card (fun u hu => (hfacts u hu).2)
  · have : (classedPorts run G l).filter (fun u => δ l u = Y ∧ u ∈ run.DupStar G Y.1) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.2 (fun u hu => h (hfacts u hu).1)
    rw [this]; simp

/-- `log P_r ≥ C' log log d_r` (`P_r = ⌈λ_r^{C'}⌉ ≥ λ_r^{C'}`). -/
theorem Cp_loglog_le_logb_P {Dstar : ℝ} (hΓ : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ}
    (hr : run.IsRound r) :
    (Cp : ℝ) * logb 2 (logb 2 (run.d G r)) ≤ logb 2 (run.P G r : ℝ) := by
  obtain ⟨-, hl256, -⟩ := logb_pos_of_valid hΓ hv hr
  have hlam : 0 < logb 2 (run.d G r) := lt_of_lt_of_le (by positivity) hl256
  have hpow : 0 < logb 2 (run.d G r) ^ Cp := by positivity
  have hP : logb 2 (run.d G r) ^ Cp ≤ (run.P G r : ℝ) := Nat.le_ceil _
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpow hP
  rwa [Real.logb_pow] at this

/-- `Σ_Y θ^GC_r(Y^0) ≤ 1.38 n λ_r^{-1/2}` over the pre-parts of round `r` (proof of CONC-L (iv),
"*`θ^GC`-terms.*", via (K1) and `P_r ≥ λ_r`). -/
theorem sum_thetaGC_le {Dstar : ℝ} (hΓ : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ}
    (hr : r ∈ Finset.Icc 1 run.R) :
    ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ) ≤
      1.38 * (G.card : ℝ) / logb 2 (run.d G r) ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, hl256, -⟩ := logb_pos_of_valid hΓ hv (Finset.mem_Icc.1 hr)
  set lam := logb 2 (run.d G r) with hlamdef
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hl256
  set s := lam ^ ((1 : ℝ) / 2) with hsdef
  have hs2 : s ^ 2 = lam := rpow_half_sq hlam0.le
  have hs0 : 0 ≤ s := rpow_half_nonneg lam
  have hs137 : 137 ≤ s := by nlinarith
  have hsp : 0 < s := by linarith
  have hneg : lam ^ (-(1 / 2 : ℝ)) = 1 / s := by
    rw [Real.rpow_neg hlam0.le, ← hsdef, one_div]
  obtain ⟨hK11, -, hK13⟩ := (ovK1 _ G Dstar run hΓ.gamma2a hv).1 r hr
  rw [card_ancestors_filter_fst] at hK13
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  -- each `θ^GC ≤ |Y^0| λ^{-1/2} + 1`
  have hθ : ∀ a ∈ run.prePartAddrs G r,
      (run.thetaGC G r a : ℝ) ≤ ((run.Z0 G r a).card : ℝ) / s + 1 := by
    intro a _
    rw [Run.thetaGC_eq]
    unfold HB.thetaGC
    have h0 : 0 ≤ ((run.Z0 G r a).card : ℝ) * lamOf (run.d G r) ^ (-(1 / 2 : ℝ)) := by
      unfold lamOf; rw [← hlamdef, hneg]; positivity
    have h1 := Nat.ceil_lt_add_one h0
    have e : ((run.Z0 G r a).card : ℝ) * lamOf (run.d G r) ^ (-(1 / 2 : ℝ)) =
        ((run.Z0 G r a).card : ℝ) / s := by
      unfold lamOf; rw [← hlamdef, hneg]; ring
    rw [e] at h1 ⊢
    exact h1.le
  have hP : s ^ 2 ≤ (run.P G r : ℝ) := by
    rw [hs2]
    have h1 : lam ≤ lam ^ Cp := le_self_pow₀ (by linarith) (by rw [Cp_eq]; norm_num)
    exact h1.trans (Nat.le_ceil _)
  calc ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ)
      ≤ ∑ a ∈ run.prePartAddrs G r, (((run.Z0 G r a).card : ℝ) / s + 1) := Finset.sum_le_sum hθ
    _ = ((∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a).card : ℕ) : ℝ) / s +
          ((run.prePartAddrs G r).card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div]; push_cast; simp
    _ ≤ 1.37 * (G.card : ℝ) / s + 1.37 * (G.card : ℝ) / s ^ 2 := by
        gcongr
        exact hK13.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hP)
    _ ≤ 1.38 * (G.card : ℝ) / s := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hsp]
        nlinarith [mul_nonneg hn (sq_nonneg s),
          mul_le_mul_of_nonneg_left hs137 (mul_nonneg hn (sq_nonneg s))]

theorem final_arith {c n k t t' ε C q A B E : ℝ} (hc : 0 ≤ c) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (ht : 0 < t) (ht' : 0 < t') (hε : 0 ≤ ε) (hC : 0 < C) (_hq : 0 < q)
    (hA : A ≤ c * n * k / t) (hB : B ≤ 80 * ε * n * k / (C * t'))
    (hE : E ≤ 4 * n * (2 * k + 2) / q) :
    A + E + B ≤ (2 * c * k / t + 200 * ε * k / (C * t') + 4 * (2 * k + 2) / q) * n := by
  have e1 : 2 * c * k / t * n = 2 * (c * n * k / t) := by ring
  have e2 : 200 * ε * k / (C * t') * n = 5 / 2 * (80 * ε * n * k / (C * t')) := by ring
  have e3 : 4 * (2 * k + 2) / q * n = 4 * n * (2 * k + 2) / q := by ring
  have p1 : 0 ≤ c * n * k / t := by positivity
  have p2 : 0 ≤ 80 * ε * n * k / (C * t') := by positivity
  rw [add_mul, add_mul, e1, e2, e3]
  linarith

end Chain

open Chain in
/-- [s6:thmCONC] (proof of (iii), "*The `d^*`-term.*") and [s6:thmCONCL] (proof of (iv),
"*`d^*`-terms.*"): `Σ_{(Y,l)} d^*_{Y,l} ≤ 80 ε n log* D_*/(C' log log D_*)` over all ancestors. -/
theorem concDStarSum : EG.Spec.ConcDStarSumStatement := by
  intro V _ G D run hΓ hv δ hδ
  have hk6 := kStar_six hΓ
  have ht'0 : 0 < logb 2 (logb 2 D) := lt_of_lt_of_le (by norm_num) hΓ.two_pow_eight_le_loglog
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hε := epsC_pos
  have hCp : (0 : ℝ) < (Cp : ℝ) := by rw [cast_Cp]; norm_num
  have hRHS : 0 ≤ 80 * epsC * (G.card : ℝ) * (logStar D : ℝ) /
      ((Cp : ℝ) * logb 2 (logb 2 D)) := by positivity
  set z : PartId → ℝ := fun Y => ((run.Z0 G Y.1 Y.2 ∩ run.DupStar G Y.1).card : ℝ) with hz
  calc ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (dStar run G δ Y l : ℝ)
      ≤ ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (if Y.1 + 2 ≤ l then z Y else 0) :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun Y _ => dStar_le_ite hδ Y l))
    _ = ∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, z Y := sum_Icc_swap _ _ _
    _ = ∑ r ∈ Finset.Icc 1 run.R, ((Finset.Icc (r + 2) run.R).card : ℝ) *
          ∑ a ∈ run.prePartAddrs G r, z (r, a) := by
        rw [sum_ancestors]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 80 * epsC * (G.card : ℝ) * (logStar D : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 D)) := by
        rcases Nat.eq_zero_or_pos run.R with hR0 | hR
        · rw [hR0]; simpa using hRHS
        have hd1 : D ≤ run.d G 1 := Run.Valid.dstar_le run G hv ⟨le_rfl, hR⟩
        obtain ⟨-, -, hA3, -, -⟩ := towerA _ G D run hΓ hv hd1
        have hK3 := ovK3 _ G D run hΓ.gamma2a hv
        have hround : ∀ r ∈ Finset.Icc 1 run.R, ((Finset.Icc (r + 2) run.R).card : ℝ) *
            ∑ a ∈ run.prePartAddrs G r, z (r, a) ≤
              16 * epsC * (G.card : ℝ) / (Cp : ℝ) * towB (run.d G r) := by
          intro r hr
          obtain ⟨-, -, hll⟩ := logb_pos_of_valid hΓ hv (Finset.mem_Icc.1 hr)
          have hll0 : 0 < logb 2 (logb 2 (run.d G r)) := lt_of_lt_of_le (by positivity) hll
          have hlogP := Cp_loglog_le_logb_P hΓ hv (Finset.mem_Icc.1 hr)
          have hK32 := (hK3 r hr).2
          push_cast at hK32
          have hIcc := card_Icc_le (r := r) (hA3 r hr)
          have hzsum : ∑ a ∈ run.prePartAddrs G r, z (r, a) ≤
              16 * epsC * (G.card : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 (run.d G r))) :=
            hK32.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hlogP)
          have hz0 : 0 ≤ ∑ a ∈ run.prePartAddrs G r, z (r, a) :=
            Finset.sum_nonneg (fun a _ => Nat.cast_nonneg _)
          calc ((Finset.Icc (r + 2) run.R).card : ℝ) * ∑ a ∈ run.prePartAddrs G r, z (r, a)
              ≤ (2 * (logStar (run.d G r) : ℝ) + 1) *
                  (16 * epsC * (G.card : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 (run.d G r)))) :=
                mul_le_mul hIcc hzsum hz0 (by positivity)
            _ = 16 * epsC * (G.card : ℝ) / (Cp : ℝ) * towB (run.d G r) := by
                unfold towB; field_simp
        have hsum := (tower_sum_le hΓ hv hR).2.1
        have hdR : D ≤ run.d G run.R := Run.Valid.dstar_le run G hv ⟨hR, le_rfl⟩
        have hend := (towerEnd D hΓ (run.d G run.R) hdR).2.1
        have hkey : 32 * (2 * (logStar D : ℝ) + 3) ≤ 80 * (logStar D : ℝ) := by nlinarith
        have hcoef : 0 ≤ 16 * epsC * (G.card : ℝ) / (Cp : ℝ) := by positivity
        calc ∑ r ∈ Finset.Icc 1 run.R, ((Finset.Icc (r + 2) run.R).card : ℝ) *
              ∑ a ∈ run.prePartAddrs G r, z (r, a)
            ≤ ∑ r ∈ Finset.Icc 1 run.R, 16 * epsC * (G.card : ℝ) / (Cp : ℝ) * towB (run.d G r) :=
              Finset.sum_le_sum hround
          _ = 16 * epsC * (G.card : ℝ) / (Cp : ℝ) * ∑ r ∈ Finset.Icc 1 run.R, towB (run.d G r) := by
              rw [Finset.mul_sum]
          _ ≤ 16 * epsC * (G.card : ℝ) / (Cp : ℝ) *
                (2 * ((2 * (logStar D : ℝ) + 3) / logb 2 (logb 2 D))) := by
              apply mul_le_mul_of_nonneg_left _ hcoef
              linarith
          _ = (32 * (2 * (logStar D : ℝ) + 3)) *
                (epsC * (G.card : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 D))) := by
              field_simp; ring
          _ ≤ (80 * (logStar D : ℝ)) * (epsC * (G.card : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 D))) :=
              mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = 80 * epsC * (G.card : ℝ) * (logStar D : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 D)) := by
              ring

open Chain in
/-- [s6:thmCONCL] (proof of (iv), "*`θ^GC`-terms.*") "`Σ_{(Y,l), Y light} θ^GC_r(Y^0) ≤
1.38 n Σ_{r ≤ R} 𝖼(d_r) ≤ 2.76 n 𝖼(d_R) ≤ 2.76 n (2k_*+3)/(log D_*)^{1/2} ≤
4n(2 log* D_* + 2)/(log D_*)^{1/2}`." -/
theorem concLGCSum : EG.Spec.ConcLGCSumStatement := by
  intro V _ G D run hΓ hv
  have hk6 := kStar_six hΓ
  have ht0 : 0 < logb 2 D := lt_trans zero_lt_one hΓ.one_lt_logb
  have hq : 0 < logb 2 D ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hRHS : 0 ≤ 4 * (G.card : ℝ) * (2 * (logStar D : ℝ) + 2) / logb 2 D ^ ((1 : ℝ) / 2) := by
    positivity
  calc ∑ Y ∈ run.lightParts G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, (run.thetaGC G Y.1 Y.2 : ℝ)
      ≤ ∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, (run.thetaGC G Y.1 Y.2 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun Y hY => (Run.mem_ancestors run G).2 ((Run.mem_lightParts run G).1 hY).1)
          (fun Y _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    _ = ∑ r ∈ Finset.Icc 1 run.R, ((Finset.Icc (r + 2) run.R).card : ℝ) *
          ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ) := by
        rw [sum_ancestors]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * (G.card : ℝ) * (2 * (logStar D : ℝ) + 2) / logb 2 D ^ ((1 : ℝ) / 2) := by
        rcases Nat.eq_zero_or_pos run.R with hR0 | hR
        · rw [hR0]; simpa using hRHS
        have hd1 : D ≤ run.d G 1 := Run.Valid.dstar_le run G hv ⟨le_rfl, hR⟩
        obtain ⟨-, -, hA3, -, -⟩ := towerA _ G D run hΓ hv hd1
        have hround : ∀ r ∈ Finset.Icc 1 run.R, ((Finset.Icc (r + 2) run.R).card : ℝ) *
            ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ) ≤
              1.38 * (G.card : ℝ) * towC (run.d G r) := by
          intro r hr
          obtain ⟨-, hl256, -⟩ := logb_pos_of_valid hΓ hv (Finset.mem_Icc.1 hr)
          have hs : 0 < logb 2 (run.d G r) ^ ((1 : ℝ) / 2) :=
            Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hl256) _
          have hIcc := card_Icc_le (r := r) (hA3 r hr)
          have hθ := sum_thetaGC_le hΓ hv hr
          have hθ0 : 0 ≤ ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ) :=
            Finset.sum_nonneg (fun a _ => Nat.cast_nonneg _)
          calc ((Finset.Icc (r + 2) run.R).card : ℝ) *
                ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ)
              ≤ (2 * (logStar (run.d G r) : ℝ) + 1) *
                  (1.38 * (G.card : ℝ) / logb 2 (run.d G r) ^ ((1 : ℝ) / 2)) :=
                mul_le_mul hIcc hθ hθ0 (by positivity)
            _ = 1.38 * (G.card : ℝ) * towC (run.d G r) := by
                unfold towC; ring
        have hsum := (tower_sum_le hΓ hv hR).2.2
        have hdR : D ≤ run.d G run.R := Run.Valid.dstar_le run G hv ⟨hR, le_rfl⟩
        have hend := (towerEnd D hΓ (run.d G run.R) hdR).2.2
        have hkey : 1.38 * 2 * (2 * (logStar D : ℝ) + 3) ≤ 4 * (2 * (logStar D : ℝ) + 2) := by
          nlinarith
        calc ∑ r ∈ Finset.Icc 1 run.R, ((Finset.Icc (r + 2) run.R).card : ℝ) *
              ∑ a ∈ run.prePartAddrs G r, (run.thetaGC G r a : ℝ)
            ≤ ∑ r ∈ Finset.Icc 1 run.R, 1.38 * (G.card : ℝ) * towC (run.d G r) :=
              Finset.sum_le_sum hround
          _ = 1.38 * (G.card : ℝ) * ∑ r ∈ Finset.Icc 1 run.R, towC (run.d G r) := by
              rw [Finset.mul_sum]
          _ ≤ 1.38 * (G.card : ℝ) *
                (2 * ((2 * (logStar D : ℝ) + 3) / logb 2 D ^ ((1 : ℝ) / 2))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
          _ = (1.38 * 2 * (2 * (logStar D : ℝ) + 3)) *
                ((G.card : ℝ) / logb 2 D ^ ((1 : ℝ) / 2)) := by ring
          _ ≤ (4 * (2 * (logStar D : ℝ) + 2)) * ((G.card : ℝ) / logb 2 D ^ ((1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = 4 * (G.card : ℝ) * (2 * (logStar D : ℝ) + 2) / logb 2 D ^ ((1 : ℝ) / 2) := by ring

namespace Chain

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}

open Classical in
/-- The per-ancestor bound in the form summed in CONC (iii) and CONC-L (iv):
`m_{Y,l} ≤ [r(Y)+2 ≤ l] ((τ_r - 1) + [Y light] θ^GC_r(Y^0)) + d^*_{Y,l}`. -/
theorem mY_le_ite {Dstar : ℝ} (hv : run.Valid G Dstar) (hδ : IsDesignation run G δ)
    {Y : PartId} (hY : Y ∈ run.ancestors G) (l : ℕ) :
    (mY run G δ Y l : ℝ) ≤
      (if Y.1 + 2 ≤ l then ((run.tau G Y.1 - 1 : ℕ) : ℝ) +
        (if run.isLight G Y.1 Y.2 then (run.thetaGC G Y.1 Y.2 : ℝ) else 0) else 0) +
      (dStar run G δ Y l : ℝ) := by
  have hPA := concLPerAncestor _ G Dstar run hv δ hδ Y hY l
  split_ifs with hl hlight
  · have h := hPA.1 hlight
    have h' : (mY run G δ Y l : ℝ) ≤ ((run.tau G Y.1 - 1 : ℕ) : ℝ) +
        ((run.thetaGC G Y.1 Y.2 - 1 : ℕ) : ℝ) + (dStar run G δ Y l : ℝ) := by exact_mod_cast h
    have hθ : ((run.thetaGC G Y.1 Y.2 - 1 : ℕ) : ℝ) ≤ (run.thetaGC G Y.1 Y.2 : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith
  · have h := hPA.2 hlight
    have h' : (mY run G δ Y l : ℝ) ≤ ((run.tau G Y.1 - 1 : ℕ) : ℝ) + (dStar run G δ Y l : ℝ) := by
      exact_mod_cast h
    linarith
  · rw [mY_eq_zero_of_not_anc run G δ hδ (fun h => hl h.2)]
    simp

end Chain

open Classical Chain in
/-- [s6:thmCONC] (iii) "`Σ_{(Y,l): Y standalone} m_{Y,l} ≤ 2^{σ+14} n log* D_*/log D_*
+ 100 ε n log* D_*/(C' log log D_*)`." -/
theorem concIII : EG.Spec.ConcIIIStatement := by
  intro V _ G D run hΓ hv δ hδ
  have hτ := concTauSum V G D run hΓ hv
  have hd := concDStarSum V G D run hΓ hv δ hδ
  have hsub : run.stdParts G ⊆ run.ancestors G := Finset.filter_subset _ _
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have ht'0 : 0 < logb 2 (logb 2 D) := lt_of_lt_of_le (by norm_num) hΓ.two_pow_eight_le_loglog
  have hCp : (0 : ℝ) < (Cp : ℝ) := by rw [cast_Cp]; norm_num
  have h80 : 80 * epsC * (G.card : ℝ) * (logStar D : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 D)) ≤
      100 * epsC * (G.card : ℝ) * (logStar D : ℝ) / ((Cp : ℝ) * logb 2 (logb 2 D)) := by
    have := epsC_pos
    gcongr
    norm_num
  have hstd : ∀ Y ∈ run.stdParts G, ∀ l, (mY run G δ Y l : ℝ) ≤
      (if Y.1 + 2 ≤ l then ((run.tau G Y.1 - 1 : ℕ) : ℝ) else 0) + (dStar run G δ Y l : ℝ) := by
    intro Y hY l
    have h := mY_le_ite hv hδ (hsub hY) l
    have hnl : ¬ run.isLight G Y.1 Y.2 := (Finset.mem_filter.1 hY).2
    simp only [hnl, if_false, add_zero] at h
    exact h
  calc ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.stdParts G, (mY run G δ Y l : ℝ)
      ≤ ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.stdParts G,
          ((if Y.1 + 2 ≤ l then ((run.tau G Y.1 - 1 : ℕ) : ℝ) else 0) +
            (dStar run G δ Y l : ℝ)) :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun Y hY => hstd Y hY l))
    _ = ∑ Y ∈ run.stdParts G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, ((run.tau G Y.1 - 1 : ℕ) : ℝ) +
          ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.stdParts G, (dStar run G δ Y l : ℝ) := by
        simp only [Finset.sum_add_distrib]
        rw [sum_Icc_swap]
    _ ≤ ∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, ((run.tau G Y.1 - 1 : ℕ) : ℝ) +
          ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (dStar run G δ Y l : ℝ) := by
        gcongr
    _ ≤ _ := by linarith

open Classical Chain in
/-- [s6:thmCONCL] (iv) "For every valid run and every designation, summing over *all* ancestors
(light and standalone, GC-parts included), `Σ_{(Y,l)} m_{Y,l} ≤ ε_CONC(D_*) n`." -/
theorem concLSum : EG.Spec.ConcLSumStatement := by
  intro V _ G D run hΓ hv δ hδ
  have hτ := concTauSum V G D run hΓ hv
  have hd := concDStarSum V G D run hΓ hv δ hδ
  have hθ := concLGCSum V G D run hΓ hv
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have ht0 : 0 < logb 2 D := lt_trans zero_lt_one hΓ.one_lt_logb
  have ht'0 : 0 < logb 2 (logb 2 D) := lt_of_lt_of_le (by norm_num) hΓ.two_pow_eight_le_loglog
  have hCp : (0 : ℝ) < (Cp : ℝ) := by rw [cast_Cp]; norm_num
  have hq : 0 < logb 2 D ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
  have hlight : ∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R,
      (if run.isLight G Y.1 Y.2 then (run.thetaGC G Y.1 Y.2 : ℝ) else 0) =
      ∑ Y ∈ run.lightParts G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, (run.thetaGC G Y.1 Y.2 : ℝ) := by
    rw [Run.lightParts, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    split_ifs <;> simp
  have hsplit : ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) ≤
      ∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, ((run.tau G Y.1 - 1 : ℕ) : ℝ) +
      ∑ Y ∈ run.lightParts G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R, (run.thetaGC G Y.1 Y.2 : ℝ) +
      ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (dStar run G δ Y l : ℝ) := by
    rw [← hlight]
    calc ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ)
        ≤ ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G,
            ((if Y.1 + 2 ≤ l then ((run.tau G Y.1 - 1 : ℕ) : ℝ) +
              (if run.isLight G Y.1 Y.2 then (run.thetaGC G Y.1 Y.2 : ℝ) else 0) else 0) +
            (dStar run G δ Y l : ℝ)) :=
          Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun Y hY => mY_le_ite hv hδ hY l))
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [sum_Icc_swap]
          simp only [Finset.sum_add_distrib]
  refine hsplit.trans ?_
  unfold epsCONC
  rw [show (2 : ℝ) ^ (sigmaC + 15) = 2 * (2 : ℝ) ^ (sigmaC + 14) by
    rw [pow_succ]; ring]
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (sigmaC + 14) := by positivity
  have := final_arith (c := (2 : ℝ) ^ (sigmaC + 14)) (n := (G.card : ℝ)) (k := (logStar D : ℝ))
    (t := logb 2 D) (t' := logb 2 (logb 2 D)) (ε := epsC) (C := (Cp : ℝ))
    (q := logb 2 D ^ ((1 : ℝ) / 2)) hc hn (Nat.cast_nonneg _) ht0 ht'0 epsC_pos.le hCp hq hτ hd hθ
  convert this using 2

end EG
