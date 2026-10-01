module

public import EG.Lib.Vortex.TPVLaws
public import EG.Lib.Vortex.PVRunStep
public import EG.Proof.Link.T16s

/-!
# The labels of the PV run and the good events (G2), (G4), (G5) (manuscript s4:lemPV, statement
("The labels of the run …"), proof, "Probability of `𝒢_PV`")

Unit P3-s4. The label space of a PV run: for every `v ∈ Z` a pair `(lev(v), κ(v))` drawn from
`levLaw J ⊗ kapLaw5`, independently, where `κ(v) ∈ {0,…,4}` has `P(κ(v) = 0) = 1/2` and
`P(κ(v) = c) = 1/8` for `c ∈ [4]` (`kapLaw5`). (The level of a vertex of `Rt` is drawn but never
used: `U_j` contains all of `Rt`; this is the manuscript's label space up to these unused
levels.)

* (G2) for one pair `(j,c)`: `EG.PVProb.G2_class` (Theorem 16* on the `(1/L)`-random subset of
  `Z` and observation (MC)): "`R_{j,c}` fails to be `(2^{12}L^4,t)`-path connected through
  `V_{j,c}` with probability at most `2^{95}L^{30}N^{-3}`".
* (G4) for one pair `(w,j)`: `EG.PVProb.G4_single` ("observation (B) gives
  `P(|C^j_w| < 8) ≤ e^{-L^4/16}`"; (B) in its Chernoff form, the lower tail at `δ = 1/2` with the
  mean bound `(L^5/8)(4/L) = L^4/2`).
* (G5): `EG.PVProb.G5_prob` (Markov's inequality).
-/

public section

namespace EG

namespace PVProb

open Finset FinDist VortexLaw

variable {V : Type*} [DecidableEq V]

/-! ### The law of `κ` -/

/-- The weights of `κ`: `1/2` at `0`, `1/8` at `c ∈ [4]`. -/
@[expose] noncomputable def kapW5 (i : Fin 5) : ℝ := if i = 0 then 1 / 2 else 1 / 8

/-- The law of `κ` in Lemma PV: "`κ(v) ∈ {0,1,2,3,4}` with `P(κ(v) = 0) = 1/2` and
`P(κ(v) = c) = 1/8` for `c ∈ [4]`". -/
@[expose] noncomputable def kapLaw5 : FinDist (Fin 5) :=
  ofFintype kapW5 (fun i => by unfold kapW5; split_ifs <;> norm_num)
    (by simp [Fin.sum_univ_five, kapW5]; norm_num)

theorem kapLaw5_zero : kapLaw5.prob {x | x = 0} = 1 / 2 := by
  rw [Set.ofPred_eq_eq_singleton, prob_singleton]
  rfl

theorem kapLaw5_succ (c : Fin 4) : kapLaw5.prob {x | x = c.succ} = 1 / 8 := by
  rw [Set.ofPred_eq_eq_singleton, prob_singleton]
  show kapW5 c.succ = 1 / 8
  simp [kapW5, Fin.succ_ne_zero]

/-! ### The label space -/

/-- The per-vertex law of `(lev, κ)`. -/
@[expose] noncomputable def vLaw (J : ℕ) : FinDist (Fin (J + 1) × Fin 5) :=
  (levLaw J).prod kapLaw5

/-- The law of all vertex labels. -/
@[expose] noncomputable def labLaw (Z : Finset V) (J : ℕ) : FinDist (Z → Fin (J + 1) × Fin 5) :=
  pi fun _ : Z => vLaw J

/-- The level of a vertex (`0` outside `Z`). -/
@[expose] def levOf {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 5) (v : V) : ℕ :=
  if h : v ∈ Z then ((lab ⟨v, h⟩).1 : ℕ) else 0

/-- The label `κ` of a vertex (`0` outside `Z`). -/
@[expose] def kapOf {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 5) (v : V) : Fin 5 :=
  if h : v ∈ Z then (lab ⟨v, h⟩).2 else 0

theorem levOf_of_mem {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 5) {v : V}
    (h : v ∈ Z) : levOf lab v = ((lab ⟨v, h⟩).1 : ℕ) := by
  simp [levOf, h]

theorem kapOf_of_mem {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 5) {v : V}
    (h : v ∈ Z) : kapOf lab v = (lab ⟨v, h⟩).2 := by
  simp [kapOf, h]

/-- The probability of a rectangle event of one vertex label. -/
theorem vLaw_prob_rect {J : ℕ} (A : Set (Fin (J + 1))) (B : Set (Fin 5)) :
    (vLaw J).prob {x | x.1 ∈ A ∧ x.2 ∈ B} = (levLaw J).prob A * kapLaw5.prob B := by
  rw [vLaw, ← prob_prod_set_prod]
  rfl

/-! ### The law of `V_{j,c}` -/

/-- `V_{j,c}` as the set selected by the vertex labels. -/
theorem Vc_eq_selectSet {Z Pl : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 5) (j : ℕ)
    (c : Fin 4) :
    PVRun.Vc Z Pl (levOf lab) (kapOf lab) j c =
      selectSet Z fun a => decide (((a : V) ∉ Pl ∨ j + 1 ≤ ((lab a).1 : ℕ)) ∧
        (lab a).2 = c.succ) := by
  ext v
  simp only [PVRun.Vc, TPVRun.U, Finset.mem_filter, mem_selectSet, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hv, h⟩, hk⟩
    refine ⟨hv, ?_, ?_⟩
    · rwa [levOf_of_mem lab hv] at h
    · rwa [kapOf_of_mem lab hv] at hk
  · rintro ⟨hv, h, hk⟩
    refine ⟨⟨hv, ?_⟩, ?_⟩
    · rwa [levOf_of_mem lab hv]
    · rwa [kapOf_of_mem lab hv]

/-- The element probabilities of `V_{j,c}`: `1/8` on `Rt`, `2^{-(j+1)}/8` on `Pl`. -/
@[expose] noncomputable def qV (Pl : Finset V) (j : ℕ) (v : V) : ℝ :=
  (if v ∈ Pl then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 8)

theorem qV_nonneg (Pl : Finset V) (j : ℕ) (v : V) : 0 ≤ qV Pl j v := by
  unfold qV; split_ifs <;> positivity

theorem qV_le_one (Pl : Finset V) (j : ℕ) (v : V) : qV Pl j v ≤ 1 := by
  unfold qV
  have : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  split_ifs <;> nlinarith

theorem vLaw_prob_Vc {Pl : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 4) (v : V) :
    (vLaw J).prob {x | decide ((v ∉ Pl ∨ j + 1 ≤ (x.1 : ℕ)) ∧ x.2 = c.succ) = true} =
      qV Pl j v := by
  have e : {x : Fin (J + 1) × Fin 5 | decide ((v ∉ Pl ∨ j + 1 ≤ (x.1 : ℕ)) ∧ x.2 = c.succ) = true}
      = {x | x.1 ∈ {i : Fin (J + 1) | v ∉ Pl ∨ j + 1 ≤ (i : ℕ)} ∧ x.2 ∈ {y | y = c.succ}} := by
    ext x; simp
  rw [e, vLaw_prob_rect, kapLaw5_succ, qV]
  congr 1
  by_cases hv : v ∈ Pl
  · rw [if_pos hv]
    have : {i : Fin (J + 1) | v ∉ Pl ∨ j + 1 ≤ (i : ℕ)} = {i : Fin (J + 1) | j + 1 ≤ (i : ℕ)} := by
      ext i; simp [hv]
    rw [this, levLaw_tail hj]
  · rw [if_neg hv]
    have : {i : Fin (J + 1) | v ∉ Pl ∨ j + 1 ≤ (i : ℕ)} = Set.univ := by
      ext i; simp [hv]
    rw [this, prob_univ]

/-- The selection rule of `V_{j,c}`. -/
@[expose] def selVc (Pl : Finset V) {Z : Finset V} (J j : ℕ) (c : Fin 4) (a : Z)
    (x : Fin (J + 1) × Fin 5) : Bool :=
  decide (((a : V) ∉ Pl ∨ j + 1 ≤ (x.1 : ℕ)) ∧ x.2 = c.succ)

theorem map_selVc {Z Pl : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 4) :
    (labLaw Z J).map (fun lab => selectSet Z fun a => selVc Pl J j c a (lab a)) =
      indepSubset Z (qV Pl j) (fun a _ => qV_nonneg Pl j a) (fun a _ => qV_le_one Pl j a) :=
  map_selectSet_pi (fun a _ => qV_nonneg Pl j a) (fun a _ => qV_le_one Pl j a)
    (fun _ : Z => vLaw J) (selVc Pl J j c)
    (fun a => map_eq_bernoulli _ _ _ _ (vLaw_prob_Vc (Pl := Pl) hj c (a : V)))

/-- The law of `V_{j,c}` is the independent random subset of `Z` with element probabilities
`qV`. -/
theorem map_Vc {Z Pl : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 4) :
    (labLaw Z J).map (fun lab => PVRun.Vc Z Pl (levOf lab) (kapOf lab) j c) =
      indepSubset Z (qV Pl j) (fun a _ => qV_nonneg Pl j a) (fun a _ => qV_le_one Pl j a) := by
  rw [← map_selVc hj c]
  congr 1
  funext lab
  exact Vc_eq_selectSet lab j c

/-! ### Item (G2) for one pair `(j,c)` -/

/-- [s4:lemPV] proof, item (G2), for one fixed own class `X = R_{j,c}` (a spanning
`(2^{-6}, s')`-expander on `Z` with `s' ≥ 2^{145}L^{41}`): `R_{j,c}` fails to be
`(2^{12}L^4, 2^9L^8)`-path connected through `V_{j,c}` with probability at most
`2^{95}L^{30}N^{-3}` over the labels. -/
theorem G2_class {Z Pl : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 4) {X : FGraph V}
    (hXZ : X.verts = Z) {s' : ℝ} (hX : X.IsExpander (2 ^ (-6 : ℤ)) s')
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card) (hN : Vortex.L Z.card ^ 3 ≤ (Z.card : ℝ))
    (hJ : 8 * (2 : ℝ) ^ J ≤ Vortex.L Z.card)
    (hs : (2 : ℝ) ^ 145 * Vortex.L Z.card ^ 41 ≤ s') :
    (labLaw Z J).prob {lab | ¬ X.IsPathConnected ((2 : ℝ) ^ 12 * Vortex.L Z.card ^ 4)
      ((2 : ℝ) ^ 9 * Vortex.L Z.card ^ 8) (PVRun.Vc Z Pl (levOf lab) (kapOf lab) j c)} ≤
      (2 : ℝ) ^ 95 * Vortex.L Z.card ^ 30 * (Z.card : ℝ) ^ (-3 : ℤ) := by
  set L := Vortex.L Z.card with hLdef
  set ℓ := (2 : ℝ) ^ 12 * L ^ 4
  set t := (2 : ℝ) ^ 9 * L ^ 8
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  have hL1 : 1 ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hρ0 : (0 : ℝ) ≤ 1 / L := by positivity
  have hρ1 : 1 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
  -- the upward closed family
  let K : Set (Finset V) := {T | X.IsPathConnected ℓ t T}
  have hK : ∀ T T', T ⊆ T' → T' ⊆ Z → T ∈ K → T' ∈ K := fun T T' h _ hT =>
    hT.mono le_rfl rfl h le_rfl le_rfl
  -- the law of `V_{j,c}`
  have hlaw := map_Vc (Pl := Pl) (Z := Z) hj c
  have e1 : (labLaw Z J).prob {lab | ¬ X.IsPathConnected ℓ t
      (PVRun.Vc Z Pl (levOf lab) (kapOf lab) j c)} =
      (indepSubset Z (qV Pl j) (fun a _ => qV_nonneg Pl j a)
        (fun a _ => qV_le_one Pl j a)).prob Kᶜ := by
    rw [← hlaw, prob_map]
    rfl
  rw [e1, prob_compl]
  -- (MC): compare with the `(1/L)`-random subset
  have hq : ∀ a ∈ Z, 1 / L ≤ qV Pl j a := by
    intro a _
    unfold qV
    have h2J : (1 / 2 : ℝ) ^ J ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have h2J' : 8 / L ≤ (1 / 2 : ℝ) ^ J := by
      rw [one_div_pow, div_le_div_iff₀ hLpos (by positivity)]
      linarith
    split_ifs
    · have : 1 / L = 8 / L * (1 / 8) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (h2J'.trans h2J) (by norm_num)
    · rw [one_mul, div_le_div_iff₀ hLpos (by norm_num)]
      linarith
  have hmc := prob_indepSubset_mono Z (p := fun _ => 1 / L) (q := qV Pl j)
    (fun _ _ => hρ0) (fun _ _ => hρ1) (fun a _ => qV_nonneg Pl j a) (fun a _ => qV_le_one Pl j a)
    hq K hK
  -- Theorem 16*
  have hXc : X.card = Z.card := by rw [FGraph.card, hXZ]
  have hrs : (rsubset Z (1 / L) hρ0 hρ1).IsRSubset (fun T => T) X.verts (1 / L) := by
    rw [hXZ]; exact isRSubset_rsubset hρ0 hρ1
  have hlog : Real.logb 2 (X.card : ℝ) ^ 2 ≤ 1 / L * (X.card : ℝ) := by
    rw [hXc, ← Vortex.L_eq, ← hLdef]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hLpos]
    nlinarith
  have hs' : (2 : ℝ) ^ 135 * t * Real.logb 2 (X.card : ℝ) ^ 28 * (1 / L) ^ (-5 : ℤ) ≤ s' := by
    rw [hXc, ← Vortex.L_eq, ← hLdef]
    have : (1 / L) ^ (-5 : ℤ) = L ^ 5 := by
      rw [zpow_neg, one_div, inv_zpow, inv_inv]; norm_cast
    rw [this]
    refine le_trans ?_ hs
    have e : (2 : ℝ) ^ 135 * t * L ^ 28 * L ^ 5 = 2 ^ 144 * L ^ 41 := by ring
    rw [e]
    have : (0 : ℝ) ≤ L ^ 41 := by positivity
    nlinarith
  have ht1 : (1 : ℝ) ≤ t := by
    have : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ hL1
    nlinarith
  have hT16 := EG.t16s V X (2 ^ (-6 : ℤ)) s' (1 / L) t (Finset V) (rsubset Z (1 / L) hρ0 hρ1)
    (fun T => T) (by norm_num) (by norm_num) hX (by positivity) hρ1 ht1 hrs hlog hs'
  rw [hXc, ← Vortex.L_eq, ← hLdef] at hT16
  have hρ3 : (1 / L) ^ (-3 : ℤ) = L ^ 3 := by
    rw [zpow_neg, one_div, inv_zpow, inv_inv]; norm_cast
  rw [hρ3] at hT16
  have hrK : (rsubset Z (1 / L) hρ0 hρ1).prob {ω | X.IsPathConnected ℓ t ω} =
      (indepSubset Z (fun _ => 1 / L) (fun _ _ => hρ0) (fun _ _ => hρ1)).prob K := rfl
  rw [hrK] at hT16
  have : (2 : ℝ) ^ 86 * t * L ^ 19 * L ^ 3 * (Z.card : ℝ) ^ (-3 : ℤ) =
      (2 : ℝ) ^ 95 * L ^ 30 * (Z.card : ℝ) ^ (-3 : ℤ) := by ring
  linarith

/-! ### Item (G4) for one pair `(w, j)` -/

/-- The probability that a vertex `u ∈ Z` lies in `Z_j`. -/
theorem prob_mem_Zr {Z Pl : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) {u : V} (hu : u ∈ Z) :
    (labLaw Z J).prob {lab | u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j} =
      (if u ∈ Pl then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 2) := by
  have e : {lab : Z → Fin (J + 1) × Fin 5 | u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j} =
      {lab | lab ⟨u, hu⟩ ∈ {x : Fin (J + 1) × Fin 5 |
        x.1 ∈ {i : Fin (J + 1) | u ∉ Pl ∨ j + 1 ≤ (i : ℕ)} ∧ x.2 ∈ {y : Fin 5 | y = 0}}} := by
    ext lab
    simp [PVRun.Zr, TPVRun.U, levOf_of_mem lab hu, kapOf_of_mem lab hu, hu]
  rw [e, labLaw, prob_pi_eval, vLaw_prob_rect, kapLaw5_zero]
  congr 1
  by_cases hP : u ∈ Pl
  · rw [if_pos hP]
    have : {i : Fin (J + 1) | u ∉ Pl ∨ j + 1 ≤ (i : ℕ)} = {i : Fin (J + 1) | j + 1 ≤ (i : ℕ)} := by
      ext i; simp [hP]
    rw [this, levLaw_tail hj]
  · rw [if_neg hP]
    have : {i : Fin (J + 1) | u ∉ Pl ∨ j + 1 ≤ (i : ℕ)} = Set.univ := by
      ext i; simp [hP]
    rw [this, prob_univ]

/-- [s4:lemPV] proof, item (G4), for one pair `(w, j)`: for a fixed set `A = C_w ⊆ Z` with
`|A| ≥ L^5/8` ((E1′)), `P(|{u ∈ A : u ∈ Z_j}| < 8) ≤ e^{-L^4/16}`. -/
theorem G4_single {Z Pl : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) {A : Finset V} (hAZ : A ⊆ Z)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card) (hJ : 8 * (2 : ℝ) ^ J ≤ Vortex.L Z.card)
    (hm : Vortex.L Z.card ^ 5 / 8 ≤ (A.card : ℝ)) :
    (labLaw Z J).prob {lab | (A.filter fun u =>
      u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j).card < 8} ≤
      Real.exp (-(Vortex.L Z.card ^ 4 / 16)) := by
  classical
  set L := Vortex.L Z.card with hLdef
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  let Bu : V → Set (Z → Fin (J + 1) × Fin 5) :=
    fun u => {lab | u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j}
  -- independence
  have hInd : (labLaw Z J).IndepEvents A Bu := by
    refine indepEvents_pi_of_dependsOn (fun _ : Z => vLaw J) A
      (fun u => {a : Z | (a : V) = u}) ?_ Bu ?_
    · intro u _ v _ huv
      rw [Set.disjoint_left]
      intro a ha ha'
      simp only [Set.mem_ofPred_eq] at ha ha'
      exact huv (ha.symm.trans ha')
    · intro u hu f g hfg hf
      have huZ := hAZ hu
      have hfg' : f ⟨u, huZ⟩ = g ⟨u, huZ⟩ := hfg ⟨u, huZ⟩ rfl
      simp only [Bu, Set.mem_ofPred_eq, PVRun.Zr, TPVRun.U, Finset.mem_filter] at hf ⊢
      rw [levOf_of_mem f huZ, kapOf_of_mem f huZ] at hf
      rw [levOf_of_mem g huZ, kapOf_of_mem g huZ, ← hfg']
      exact hf
  -- the probabilities
  have h2J : 8 / L ≤ (1 / 2 : ℝ) ^ J := by
    rw [one_div_pow, div_le_div_iff₀ hLpos (by positivity)]
    linarith
  have hpB : ∀ u ∈ A, 4 / L ≤ (labLaw Z J).prob (Bu u) := by
    intro u hu
    rw [show (labLaw Z J).prob (Bu u) = _ from prob_mem_Zr hj (hAZ hu)]
    have hJj : (1 / 2 : ℝ) ^ J ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have h1 : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : 4 / L = 8 / L * (1 / 2) := by ring
    rw [this]
    split_ifs
    · exact mul_le_mul_of_nonneg_right (h2J.trans hJj) (by norm_num)
    · exact mul_le_mul_of_nonneg_right (h2J.trans h1) (by norm_num)
  have hsum : L ^ 4 / 2 ≤ ∑ u ∈ A, (labLaw Z J).prob (Bu u) := by
    have h1 := Finset.sum_le_sum hpB
    rw [sum_const, nsmul_eq_mul] at h1
    refine le_trans ?_ h1
    have : L ^ 4 / 2 = L ^ 5 / 8 * (4 / L) := by field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  -- Chernoff
  have hch := IndepEvents.chernoff_lower_half hInd
    (X := fun lab => ((A.filter fun u =>
      u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j).card : ℝ))
    (fun lab _ => by
      rw [sum_indicator_one_eq_card A _ lab (fun u =>
        u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j)]
      intro u _
      simp [Bu])
    (by positivity) hsum
  have e2 : L ^ 4 / 2 / 8 = L ^ 4 / 16 := by ring
  rw [e2] at hch
  refine le_trans (prob_mono _ fun lab hlab => ?_) hch
  simp only [Set.mem_ofPred_eq] at hlab ⊢
  have h8 : ((A.filter fun u =>
      u ∈ PVRun.Zr Z Pl (levOf lab) (kapOf lab) j).card : ℝ) < 8 := by exact_mod_cast hlab
  have hL4 : (2 : ℝ) ^ 10 ≤ L ^ 4 := by
    have : (1 : ℝ) ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
    nlinarith [pow_le_pow_left₀ (by norm_num) this 3]
  linarith

/-! ### Item (G5) -/

theorem prob_le_levOf {Z : Finset V} {J j : ℕ} (hj : j ≤ J) {v : V} (hv : v ∈ Z) :
    (labLaw Z J).prob {lab | j ≤ levOf lab v} = (1 / 2 : ℝ) ^ j := by
  have e : {lab : Z → Fin (J + 1) × Fin 5 | j ≤ levOf lab v} =
      {lab | lab ⟨v, hv⟩ ∈ {x : Fin (J + 1) × Fin 5 |
        x.1 ∈ {i : Fin (J + 1) | j ≤ (i : ℕ)} ∧ x.2 ∈ (Set.univ : Set (Fin 5))}} := by
    ext lab
    simp [levOf_of_mem lab hv]
  rw [e, labLaw, prob_pi_eval, vLaw_prob_rect, levLaw_tail hj, prob_univ, mul_one]

theorem expect_card_levOf {Z Pl : Finset V} (hPZ : Pl ⊆ Z) {J j : ℕ} (hj : j ≤ J) :
    (labLaw Z J).expect (fun lab => ((Pl.filter fun v => j ≤ levOf lab v).card : ℝ)) =
      Pl.card * (1 / 2 : ℝ) ^ j := by
  classical
  have h := (labLaw Z J).expect_card_filter Pl (fun v => {lab | j ≤ levOf lab v})
  simp only [Set.mem_ofPred_eq] at h
  rw [h]
  rw [sum_congr rfl fun v hv => prob_le_levOf hj (hPZ hv), sum_const, nsmul_eq_mul]

/-- [s4:lemPV] proof, item (G5): "`Σ_{j<J} |Pl ∩ U_j| ≤ 8|Pl|` and `|Pl ∩ U_J| ≤ 64|Pl|/L`"
hold with probability at least `1/2` ("`E Σ_{j<J}|Pl ∩ U_j| < 2|Pl|` and
`E|Pl ∩ U_J| = 2^{-J}|Pl| < 16|Pl|/L` …; by Markov's inequality each inequality of (G5) fails
with probability less than `1/4`"; s1:citMarkov (b)). -/
theorem G5_prob {Z Pl : Finset V} (hPZ : Pl ⊆ Z) {J : ℕ} {L : ℝ} (hLpos : 0 < L)
    (hJ : L < 16 * (2 : ℝ) ^ J) :
    1 / 2 ≤ (labLaw Z J).prob {lab |
      (∑ j ∈ range J, ((Pl.filter fun v => j ≤ levOf lab v).card : ℝ)) ≤ 8 * Pl.card ∧
      ((Pl.filter fun v => J ≤ levOf lab v).card : ℝ) ≤ 64 * Pl.card / L} := by
  classical
  have hM := (labLaw Z J).half_le_prob_le_four_mul_expect_and
    (X₁ := fun lab => ∑ j ∈ range J, ((Pl.filter fun v => j ≤ levOf lab v).card : ℝ))
    (X₂ := fun lab => ((Pl.filter fun v => J ≤ levOf lab v).card : ℝ))
    (fun _ => sum_nonneg fun _ _ => by positivity) (fun _ => by positivity)
  refine le_trans hM (prob_mono _ fun lab hlab => ?_)
  simp only [Set.mem_ofPred_eq] at hlab ⊢
  have e1 : (labLaw Z J).expect (fun lab => ∑ j ∈ range J,
      ((Pl.filter fun v => j ≤ levOf lab v).card : ℝ)) =
      Pl.card * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j := by
    rw [expect_sum, mul_sum]
    exact sum_congr rfl fun j hj => expect_card_levOf hPZ (mem_range.1 hj).le
  have e2 := expect_card_levOf (Z := Z) (Pl := Pl) hPZ (le_refl J)
  have hg : ∑ j ∈ range J, (1 / 2 : ℝ) ^ j ≤ 2 := by
    have h := geom_sum_half J
    have : ∑ j ∈ range J, (1 / 2 : ℝ) ^ j = 2 * ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [this, h]
    have : (0 : ℝ) ≤ (1 / 2) ^ J := by positivity
    linarith
  have hP0 : (0 : ℝ) ≤ Pl.card := by positivity
  have h2J : (1 / 2 : ℝ) ^ J ≤ 16 / L := by
    rw [one_div_pow, div_le_div_iff₀ (by positivity) hLpos]
    linarith
  rw [e1] at hlab
  rw [e2] at hlab
  refine ⟨le_trans hlab.1 (by nlinarith), le_trans hlab.2 ?_⟩
  rw [le_div_iff₀ hLpos]
  have : (Pl.card : ℝ) * (1 / 2) ^ J * L ≤ Pl.card * 16 := by
    have := mul_le_mul_of_nonneg_left h2J hP0
    rw [mul_div_assoc'] at this
    rw [le_div_iff₀ hLpos] at this
    linarith
  nlinarith

end PVProb

end EG
