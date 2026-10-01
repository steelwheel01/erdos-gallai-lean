module

public import EG.Spec.Light.E1
public import EG.Spec.Light.Stages
public import EG.Spec.Light.ParentRun
public import EG.Spec.Stage1.COLa
public import EG.Spec.Found.Chernoff
public import EG.Proof.Todo.ChernoffGen
public import EG.Proof.Todo.EqZp
public import EG.Proof.Light.Setting
public import EG.Proof.Light.Stages
public import EG.Proof.Light.ParentBadProb
public import EG.Proof.Stage1.COLa
public import EG.Lib.Light.E1Aux
public import EG.Lib.Light.Stages
public import EG.Lib.Lend.Standing
public import EG.Lib.Stage1.Zones
public import EG.Lib.HB.TowerRun
public import EG.Lib.Gamma.Full

/-!
# P3 stub: `EG.Spec.LemE1Statement` (s5:lemE1)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LemE1`; consumers import this module.

Proof (P3), as in `s5.tex`:
* (a) for each round `l ∈ [r, R]` and each `w ∈ Y`, the Chernoff lower tail
  (`EG.Todo.ChernoffGen`, Cited result s1:citChernoffGen) for the independent indicators
  `χ_u = 1[wu ∈ M_Y, choice(u) = none]`, `u ∈ A_Y(w)` (`EG.Light.prob_count_lt_le`; independence
  `EG.Stage1.iIndepFun_edge_zone`; `P(χ_u = 1) = (1/2)(1/k_own)(1 − Σzp) ≥ 1/(4L)` by
  `k_own ≤ L` and (s5:eqZp), `EG.Todo.EqZp`; `|A_Y(w)| = vm_Y ≥ L^6`, the embedded claim of
  s5:defStages, `EG.stagesHB`), then a union bound over `R − r + 1 ≤ 3L` rounds and `|Y|` vertices
  ((s5:eqLY), `EG.eqLY`);
* (b) `P(demoted) ≤ P(¬E1) + P(¬COL(a)) ≤ 3L|Y|e^{−L^5/32} + |Y|^{-2}/4 ≤ |Y|^{-2}/2`
  (`EG.colaProb`, s3:lemCOL (a); `|Y| = 2^L`, `L ≥ 102·2^8`);
* (c) `P(Y ∈ Bad) ≤ P(demoted) + P(parent-bad) ≤ |Y|^{-2}` (`EG.parentBadProb`: s3:lemCOL (c)
  applied to the zones, s5:lemZones (ii), (iv)).
-/

public section

namespace EG.Todo

open EG.HB EG.Stage1 EG.Light FinDist Real

/-- Numerics of (b): for `N = 2^L` with `L ≥ 64`, `3 L N e^{-L^5/32} ≤ N^{-2}/4`. -/
theorem e1_numeric {N L : ℝ} (hN : 0 < N) (hNL : N = (2 : ℝ) ^ L) (hL : 64 ≤ L) :
    3 * L * N * Real.exp (-(L ^ 5) / 32) ≤ N ^ (-2 : ℤ) / 4 := by
  have hL0 : 0 < L := by linarith
  -- `N ≤ e^L`
  have hNe : N ≤ Real.exp L := by
    rw [hNL, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    nlinarith
  -- `12 L ≤ e^L`
  have h12 : 12 * L ≤ Real.exp L := by
    have := Real.quadratic_le_exp_of_nonneg hL0.le
    nlinarith
  -- `4L ≤ L^5/32`
  have h4 : 4 * L ≤ L ^ 5 / 32 := by
    have h2 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    have e : L ^ 5 = L * L ^ 4 := by ring
    rw [e]
    nlinarith
  have hN3 : N ^ 3 ≤ Real.exp L ^ 3 := pow_le_pow_left₀ hN.le hNe 3
  have hkey : 12 * L * N ^ 3 ≤ Real.exp (L ^ 5 / 32) := by
    calc 12 * L * N ^ 3 ≤ Real.exp L * Real.exp L ^ 3 :=
          mul_le_mul h12 hN3 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 * L) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (L ^ 5 / 32) := Real.exp_le_exp.2 h4
  have hE : Real.exp (-(L ^ 5) / 32) = (Real.exp (L ^ 5 / 32))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hE, zpow_neg, zpow_ofNat]
  have hpos : 0 < Real.exp (L ^ 5 / 32) := Real.exp_pos _
  rw [mul_inv_le_iff₀ hpos]
  have : N ^ 2 * (N ^ 2)⁻¹ = 1 := by field_simp
  calc 3 * L * N = (N ^ 2)⁻¹ / 4 * (12 * L * N ^ 3) := by field_simp; ring
    _ ≤ (N ^ 2)⁻¹ / 4 * Real.exp (L ^ 5 / 32) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Proved in P3. [s5:lemE1] see `EG.Spec.LemE1Statement`. -/
theorem LemE1 : EG.Spec.LemE1Statement := by
  classical
  intro V _ G N0 Dstar run hR Y hY
  have hD : Gamma1core Dstar := hR.gamma1core
  have hv : run.Valid G Dstar := hR.valid
  have hanc : Y ∈ run.ancestors G := by
    unfold Run.lightParts at hY
    exact (Finset.mem_filter.1 hY).1
  have hLight := isLight_of_mem_lightParts hY
  have hRd := Standing.isRound_of_mem_ancestors hanc
  have hLY := EG.eqLY V G N0 Dstar run hR Y hY
  have hHB := EG.stagesHB V G N0 Dstar run hR Y hY
  set L := run.LY G Y with hLdef
  set N : ℝ := ((run.ancVerts G Y).card : ℝ) with hNdef
  -- `L ≥ 102 · 2^8`
  have hmu : (256 : ℝ) ≤ Real.logb 2 (run.lam G Y.1) :=
    (Run.paramHyp hD hv (r := Y.1) (Finset.mem_Icc.2 hRd)).mu_ge
  have hL102 : 102 * 256 ≤ L := by
    obtain ⟨-, -, h3, h4, -, -, -⟩ := hLY
    linarith
  have hL0 : 0 < L := by linarith
  have hNpos : 0 < N := by
    have : (run.ancVerts G Y).card ≠ 0 := by
      intro h0
      have : L = 0 := by rw [hLdef, Run.LY, h0]; simp
      linarith
    show (0 : ℝ) < ((run.ancVerts G Y).card : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hNL : N = (2 : ℝ) ^ L := (Real.rpow_logb (by norm_num) (by norm_num) hNpos).symm
  -- (a)
  have ha : (law G run).prob {ω | ¬ E1 ω Y} ≤ 3 * L * N * Real.exp (-(L ^ 5) / 32) := by
    set B : ℕ → V → Set (Outcome G run) := fun l w => {ω | (((AY G run Y w).filter fun u =>
        s(w, u) ∈ (ownM G run Y (ω.colAt Y)).edges ∧ zonePhase ω.zone l u = none).card : ℝ) <
          L ^ 5 / 8} with hB
    have hsub : {ω | ¬ E1 ω Y} ⊆ ⋃ l ∈ Finset.Icc Y.1 run.R, ⋃ w ∈ run.ancVerts G Y, B l w := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, E1, not_forall, not_le] at hω
      obtain ⟨l, hl, w, hw, hlt⟩ := hω
      simp only [Set.mem_iUnion]
      exact ⟨l, hl, w, hw, hlt⟩
    have hBle : ∀ l, ∀ w ∈ run.ancVerts G Y, (law G run).prob (B l w) ≤
        Real.exp (-(L ^ 5 / 32)) := by
      intro l w hw
      have hwX : w ∈ (run.X G Y.1 Y.2).verts := by rw [hHB.1]; exact hw
      obtain ⟨hAsub, hAcard⟩ := hHB.2.2.2.1 w hwX
      refine prob_count_lt_le EG.Todo.ChernoffGen hanc w l (AY G run Y w) L hL0 ?_ ?_ ?_ ?_
      · intro u hu
        have hu' := hAsub hu
        rw [FGraph.nbrs, Finset.mem_filter] at hu'
        refine ⟨ancVerts_subset_verts G run Y (hHB.1 ▸ hu'.1), ?_⟩
        rw [ancGraph_eq_X_of_isLight hLight]
        exact hu'.2
      · intro u _
        -- `zpSum(u) ≤ Σ_{Y ∋ u} L_Y^{-2} < 1/2` by (s5:eqZp)
        have hZp := EG.Todo.EqZp V G N0 Dstar run hR u
        have hle : zpSum G run u ≤ ∑ Y' ∈ (run.lightParts G).filter
            (fun Y' => (u : V) ∈ run.ancVerts G Y'), run.LY G Y' ^ (-2 : ℤ) := by
          unfold zpSum
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun Y' _ _ => zp_nonneg G run Y'
          intro Y' hY'
          simp only [availParts, Finset.mem_filter] at hY' ⊢
          exact ⟨hY'.1, hY'.2.1⟩
        linarith
      · have := Standing.kown_le (G := G) (run := run) Y
        linarith
      · rw [hAcard]
        have hvm : L ^ 6 ≤ (vm G run Y : ℝ) := Nat.le_ceil _
        rw [le_div_iff₀ (by positivity)]
        have : L ^ 5 / 4 * (4 * L) = L ^ 6 := by ring
        linarith
    have hcardI : ((Finset.Icc Y.1 run.R).card : ℝ) ≤ 3 * L := by
      rw [Nat.card_Icc]
      have hRR := hRd.2
      have h7 := hLY.2.2.2.2.2.2
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      linarith
    calc (law G run).prob {ω | ¬ E1 ω Y}
        ≤ (law G run).prob (⋃ l ∈ Finset.Icc Y.1 run.R, ⋃ w ∈ run.ancVerts G Y, B l w) :=
          prob_mono _ hsub
      _ ≤ ∑ l ∈ Finset.Icc Y.1 run.R, (law G run).prob (⋃ w ∈ run.ancVerts G Y, B l w) :=
          prob_biUnion_le _ _ _
      _ ≤ ∑ l ∈ Finset.Icc Y.1 run.R, ∑ w ∈ run.ancVerts G Y, (law G run).prob (B l w) :=
          Finset.sum_le_sum fun l _ => prob_biUnion_le _ _ _
      _ ≤ ∑ l ∈ Finset.Icc Y.1 run.R, ∑ w ∈ run.ancVerts G Y, Real.exp (-(L ^ 5 / 32)) :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w hw => hBle l w hw
      _ = ((Finset.Icc Y.1 run.R).card : ℝ) * (N * Real.exp (-(L ^ 5 / 32))) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ 3 * L * (N * Real.exp (-(L ^ 5 / 32))) :=
          mul_le_mul_of_nonneg_right hcardI (by positivity)
      _ = 3 * L * N * Real.exp (-(L ^ 5) / 32) := by ring_nf
  -- (b)
  have hCOLa := EG.colaProb V G Dstar run hR.gamma1 hv hR.le_d_one Y hanc (Outcome G run)
    (law G run) (fun ω => ω.cOutAt Y) (map_cOutAt G run hanc)
  have hb : (law G run).prob {ω | demoted ω Y} ≤ N ^ (-2 : ℤ) / 2 := by
    have hnum := e1_numeric hNpos hNL (by linarith)
    calc (law G run).prob {ω | demoted ω Y}
        = (law G run).prob ({ω | ¬ E1 ω Y} ∪ {ω | ¬ COLa G run Y (ω.cOutAt Y)}) := rfl
      _ ≤ (law G run).prob {ω | ¬ E1 ω Y} +
            (law G run).prob {ω | ¬ COLa G run Y (ω.cOutAt Y)} := prob_union_le _ _ _
      _ ≤ N ^ (-2 : ℤ) / 4 + N ^ (-2 : ℤ) / 4 := add_le_add (ha.trans hnum) hCOLa
      _ = N ^ (-2 : ℤ) / 2 := by ring
  -- (c)
  have hpb := EG.parentBadProb V G N0 Dstar run hR Y hY
  have hc : (law G run).prob {ω | Y ∈ Bad ω} ≤ N ^ (-2 : ℤ) := by
    have hsub : {ω : Outcome G run | Y ∈ Bad ω} ⊆
        {ω : Outcome G run | demoted ω Y} ∪ {ω : Outcome G run | parentBad ω Y} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Bad, Finset.mem_filter] at hω
      exact hω.2
    calc (law G run).prob {ω | Y ∈ Bad ω}
        ≤ (law G run).prob ({ω | demoted ω Y} ∪ {ω | parentBad ω Y}) := prob_mono _ hsub
      _ ≤ (law G run).prob {ω | demoted ω Y} + (law G run).prob {ω | parentBad ω Y} :=
          prob_union_le _ _ _
      _ ≤ N ^ (-2 : ℤ) / 2 + N ^ (-2 : ℤ) / 2 := add_le_add hb hpb
      _ = N ^ (-2 : ℤ) := by ring
  exact ⟨ha, hb, hc⟩

end EG.Todo
