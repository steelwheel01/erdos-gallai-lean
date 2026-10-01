module

public import EG.Lib.Vortex.TPVProb

/-!
# The good events of the VX⁺ run (manuscript s4:thmVXp, proof, items (G2), (G3), (G4))

Unit P3-s4. The label space of a VX⁺ run is that of a TPV run with `P = Z`
(`EG.TPVProb.runLaw`): a uniform `k`-colouring of `E(O)` and, for every `v ∈ Z`, a level and a
label `κ`.

* `EG.VXProb.G2_class_gen`: item (G2) for one class with a general multiplicity `t`
  ("`Prob(V' ∉ 𝒦_{j,c}) ≤ 2^{86}tL^{19}L^3N^{-3}`", then (MC)).
* `EG.VXProb.G3_single`: item (G3) for one `j`: "`|U_j|` is binomial with mean
  `2^{-j}N ≥ 2^{-J}N ≥ 6N/L`; by Cited result s1:citChernoff with `δ = 1/100` it exceeds `1.01`
  times its mean with probability at most `e^{-10^{-4}·6N/(3L)} ≤ e^{-N/(5000L)}`".
* `EG.VXProb.G4_gen`: item (G4) for one pair `(w, j)`, with a general lower bound `p₀` on
  `P(I_u = 1)` and a general threshold (observation (B) in its Chernoff form).
-/

public section

namespace EG

namespace VXProb

open Finset FinDist VortexLaw TPVProb

variable {V : Type*} [DecidableEq V]

/-- [s4:thmVXp] proof, item (G2), for one fixed class graph `X` and a general multiplicity
`t ≥ 1` with `2^{135}tL^{28}L^5 ≤ s'`: the class fails to be `(2^{12}L^4, t)`-path connected
through `V_{j,c}` with probability at most `2^{86}tL^{22}N^{-3}`. -/
theorem G2_class_gen {Z P : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 3) {X : FGraph V}
    (hXZ : X.verts = Z) {εO s' t : ℝ} (hε7 : (2 : ℝ) ^ (-7 : ℤ) ≤ εO) (hε1 : εO ≤ 1)
    (hX : X.IsExpander εO s')
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card) (hN : Vortex.L Z.card ^ 3 ≤ (Z.card : ℝ))
    (hJ : 6 * (2 : ℝ) ^ J ≤ Vortex.L Z.card) (ht1 : 1 ≤ t)
    (hs : (2 : ℝ) ^ 135 * t * Vortex.L Z.card ^ 33 ≤ s') :
    (labLaw Z J).prob {lab | ¬ X.IsPathConnected ((2 : ℝ) ^ 12 * Vortex.L Z.card ^ 4)
      t (TPVRun.Vc Z P (levOf lab) (kapOf lab) j c)} ≤
      (2 : ℝ) ^ 86 * t * Vortex.L Z.card ^ 22 * (Z.card : ℝ) ^ (-3 : ℤ) := by
  set L := Vortex.L Z.card with hLdef
  set ℓ := (2 : ℝ) ^ 12 * L ^ 4
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  have hL1 : 1 ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hρ0 : (0 : ℝ) ≤ 1 / L := by positivity
  have hρ1 : 1 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
  let K : Set (Finset V) := {T | X.IsPathConnected ℓ t T}
  have hK : ∀ T T', T ⊆ T' → T' ⊆ Z → T ∈ K → T' ∈ K := fun T T' h _ hT =>
    hT.mono le_rfl rfl h le_rfl le_rfl
  have hlaw := map_Vc (P := P) (Z := Z) hj c
  have e1 : (labLaw Z J).prob {lab | ¬ X.IsPathConnected ℓ t
      (TPVRun.Vc Z P (levOf lab) (kapOf lab) j c)} =
      (indepSubset Z (qV P j) (fun a _ => qV_nonneg P j a) (fun a _ => qV_le_one P j a)).prob Kᶜ
      := by
    rw [← hlaw, prob_map]
    rfl
  rw [e1, prob_compl]
  have hq : ∀ a ∈ Z, 1 / L ≤ qV P j a := by
    intro a _
    unfold qV
    have h2J : (1 / 2 : ℝ) ^ J ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have h2J' : 6 / L ≤ (1 / 2 : ℝ) ^ J := by
      rw [one_div_pow, div_le_div_iff₀ hLpos (by positivity)]
      linarith
    split_ifs
    · have : 1 / L = 6 / L * (1 / 6) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (h2J'.trans h2J) (by norm_num)
    · rw [one_mul, div_le_div_iff₀ hLpos (by norm_num)]
      linarith
  have hmc := prob_indepSubset_mono Z (p := fun _ => 1 / L) (q := qV P j)
    (fun _ _ => hρ0) (fun _ _ => hρ1) (fun a _ => qV_nonneg P j a) (fun a _ => qV_le_one P j a)
    hq K hK
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
    refine le_trans (le_of_eq ?_) hs
    ring
  have hT16 := EG.t16s V X εO s' (1 / L) t (Finset V) (rsubset Z (1 / L) hρ0 hρ1) (fun T => T)
    hε7 hε1 hX (by positivity) hρ1 ht1 hrs hlog hs'
  rw [hXc, ← Vortex.L_eq, ← hLdef] at hT16
  have hρ3 : (1 / L) ^ (-3 : ℤ) = L ^ 3 := by
    rw [zpow_neg, one_div, inv_zpow, inv_inv]; norm_cast
  rw [hρ3] at hT16
  have hrK : (rsubset Z (1 / L) hρ0 hρ1).prob {ω | X.IsPathConnected ℓ t ω} =
      (indepSubset Z (fun _ => 1 / L) (fun _ _ => hρ0) (fun _ _ => hρ1)).prob K := rfl
  rw [hrK] at hT16
  have : (2 : ℝ) ^ 86 * t * L ^ 19 * L ^ 3 * (Z.card : ℝ) ^ (-3 : ℤ) =
      (2 : ℝ) ^ 86 * t * L ^ 22 * (Z.card : ℝ) ^ (-3 : ℤ) := by ring
  linarith

/-- [s4:thmVXp] proof, item (G3), for one `j ≤ J`: `|U_j| ≥ 1.01·2^{-j}N` with probability at
most `e^{-N/(5000L)}`. -/
theorem G3_single {Z : Finset V} {J j : ℕ} (hj : j ≤ J)
    (hL : (0 : ℝ) < Vortex.L Z.card) (hJ : 6 * (2 : ℝ) ^ J ≤ Vortex.L Z.card) :
    (labLaw Z J).prob {lab | 1.01 * ((1 / 2 : ℝ) ^ j * Z.card) ≤
      ((Z.filter fun v => j ≤ levOf lab v).card : ℝ)} ≤
      Real.exp (-((Z.card : ℝ) / (5000 * Vortex.L Z.card))) := by
  classical
  set L := Vortex.L Z.card
  let A : V → Set (Z → Fin (J + 1) × Fin 4) := fun v => {lab | j ≤ levOf lab v}
  have hInd : (labLaw Z J).IndepEvents Z A := by
    refine indepEvents_pi_of_dependsOn (fun _ : Z => vLaw J) Z
      (fun v => {a : Z | (a : V) = v}) ?_ A ?_
    · intro u _ v _ huv
      rw [Set.disjoint_left]
      intro a ha ha'
      simp only [Set.mem_ofPred_eq] at ha ha'
      exact huv (ha.symm.trans ha')
    · intro v hv f g hfg hf
      have hfg' : f ⟨v, hv⟩ = g ⟨v, hv⟩ := hfg ⟨v, hv⟩ rfl
      simp only [A, Set.mem_ofPred_eq] at hf ⊢
      rw [levOf_of_mem f hv] at hf
      rw [levOf_of_mem g hv, ← hfg']
      exact hf
  have hsum : ∑ v ∈ Z, (labLaw Z J).prob (A v) = (1 / 2 : ℝ) ^ j * Z.card := by
    rw [sum_congr rfl fun v hv => prob_le_levOf hj hv, sum_const, nsmul_eq_mul, mul_comm]
  have hch := hInd.chernoff_upper (X := fun lab => ((Z.filter fun v => j ≤ levOf lab v).card : ℝ))
    (fun lab _ => by
      rw [sum_indicator_one_eq_card Z A lab (fun v => j ≤ levOf lab v)]
      intro v _
      simp [A])
    hsum.le (δ := 1 / 100) (by norm_num) (by norm_num)
  refine le_trans (le_of_eq ?_) (le_trans hch ?_)
  · congr 1
    ext lab
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  · rw [Real.exp_le_exp, neg_le_neg_iff]
    have hLpos := hL
    have h2 : 6 / L ≤ (1 / 2 : ℝ) ^ j := by
      have h2J : (1 / 2 : ℝ) ^ J ≤ (1 / 2 : ℝ) ^ j :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      refine le_trans ?_ h2J
      rw [one_div_pow, div_le_div_iff₀ hLpos (by positivity)]
      linarith
    have hN : (0 : ℝ) ≤ Z.card := by positivity
    have h3 : 6 / L * Z.card ≤ (1 / 2 : ℝ) ^ j * Z.card := mul_le_mul_of_nonneg_right h2 hN
    have e : (Z.card : ℝ) / (5000 * L) = (1 / 100) ^ 2 * (6 / L * Z.card) / 3 := by
      field_simp; ring
    rw [e]
    have : (0 : ℝ) ≤ (1 / 100) ^ 2 / 3 := by norm_num
    nlinarith

/-- [s4:thmVXp] proof, item (G4), for one pair `(w, j)`, in a general form: if every
`P(I_u = 1) = (1/k)·P(u ∈ Z_j)` (`u ∈ A`) is at least `p₀` and `2a ≤ M₀ ≤ |A|p₀`, then
`P(|C^j_w| < a) ≤ e^{-M₀/8}`. -/
theorem G4_gen {Z P : Finset V} {O : FGraph V} {J j : ℕ} (hj : j + 1 ≤ J) {w : V}
    {A : Finset V} (hA : ∀ u ∈ A, s(w, u) ∈ O.edges ∧ u ∈ Z) {p₀ M₀ a : ℝ}
    (hp : ∀ u ∈ A, p₀ ≤ 1 / ((3 * J + 1 : ℕ) : ℝ) *
      ((if u ∈ P then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 2)))
    (hM : M₀ ≤ A.card * p₀) (hM0 : 0 ≤ M₀) (ha : 2 * a ≤ M₀) :
    (runLaw O Z J).prob {ω | (((A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card : ℕ) : ℝ) < a} ≤
      Real.exp (-(M₀ / 8)) := by
  classical
  set k := 3 * J + 1 with hkdef
  let Au : V → Set (O.edges → Fin k) := fun u => {χ | s(w, u) ∈ Mof χ}
  let Bu : V → Set (Z → Fin (J + 1) × Fin 4) :=
    fun u => {lab | u ∈ TPVRun.Zr Z P (levOf lab) (kapOf lab) j}
  have hIndA : (randColouring O.edges k).IndepEvents A Au := by
    refine indepEvents_pi_of_dependsOn (fun _ : O.edges => uniform (Fin k)) A
      (fun u => {e : O.edges | (e : Sym2 V) = s(w, u)}) ?_ Au ?_
    · intro u _ v _ huv
      rw [Set.disjoint_left]
      intro e he he'
      simp only [Set.mem_ofPred_eq] at he he'
      exact huv (Sym2.congr_right.1 (he.symm.trans he'))
    · intro u _ f g hfg hf
      simp only [Au, Set.mem_ofPred_eq, mem_Mof] at hf ⊢
      obtain ⟨h, hf⟩ := hf
      refine ⟨h, ?_⟩
      rw [← hfg ⟨s(w, u), h⟩ rfl]
      exact hf
  have hIndB : (labLaw Z J).IndepEvents A Bu := by
    refine indepEvents_pi_of_dependsOn (fun _ : Z => vLaw J) A
      (fun u => {a : Z | (a : V) = u}) ?_ Bu ?_
    · intro u _ v _ huv
      rw [Set.disjoint_left]
      intro a ha ha'
      simp only [Set.mem_ofPred_eq] at ha ha'
      exact huv (ha.symm.trans ha')
    · intro u hu f g hfg hf
      have huZ := (hA u hu).2
      have hfg' : f ⟨u, huZ⟩ = g ⟨u, huZ⟩ := hfg ⟨u, huZ⟩ rfl
      simp only [Bu, Set.mem_ofPred_eq, TPVRun.Zr, TPVRun.U, Finset.mem_filter] at hf ⊢
      rw [levOf_of_mem f huZ, kapOf_of_mem f huZ] at hf
      rw [levOf_of_mem g huZ, kapOf_of_mem g huZ, ← hfg']
      exact hf
  have hInd := IndepEvents.prod hIndA hIndB
  have hpA : ∀ u ∈ A, (randColouring O.edges k).prob (Au u) = 1 / k := by
    intro u hu
    have h := (hA u hu).1
    have e : Au u = {χ | χ ⟨s(w, u), h⟩ = (0 : Fin k)} := by
      ext χ
      simp only [Au, Set.mem_ofPred_eq, mem_Mof]
      constructor
      · rintro ⟨_, h'⟩; exact Fin.ext h'
      · intro h'; exact ⟨h, by rw [h']; rfl⟩
    rw [e, prob_randColouring_apply]
  have hpI : ∀ u ∈ A, p₀ ≤ (runLaw O Z J).prob (Au u ×ˢ Bu u) := by
    intro u hu
    rw [runLaw, prob_prod_set_prod, hpA u hu]
    rw [show (labLaw Z J).prob (Bu u) = _ from prob_mem_Zr hj (hA u hu).2]
    exact hp u hu
  have hsum : M₀ ≤ ∑ u ∈ A, (runLaw O Z J).prob (Au u ×ˢ Bu u) := by
    have h1 := Finset.sum_le_sum hpI
    rw [sum_const, nsmul_eq_mul] at h1
    linarith
  have hch := IndepEvents.chernoff_lower_half hInd
    (X := fun ω => ((A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card : ℝ))
    (fun ω _ => by
      rw [sum_indicator_one_eq_card A _ ω (fun u => s(w, u) ∈ Mof ω.1 ∧
        u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j)]
      intro u _
      simp [Au, Bu, Set.mem_prod])
    hM0 hsum
  refine le_trans (prob_mono _ fun ω hω => ?_) hch
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hfin : ((A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card : ℝ) < M₀ / 2 := by linarith
  exact hfin

end VXProb

end EG
