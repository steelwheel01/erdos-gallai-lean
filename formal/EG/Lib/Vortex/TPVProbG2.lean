module

public import EG.Lib.Vortex.TPVLaws
public import EG.Lib.Vortex.TPVRun
public import EG.Proof.Link.T16s
public import EG.Proof.Link.L15
public import EG.Lib.Found.ColourClass

/-!
# The labels of the TPV run and the good event (G2) (manuscript s4:lemTPV, statement (a)–(c),
proof, item (G2))

Unit P3-s4. The label space of a TPV run: a uniform colouring `χ` of `E(O)` with `k` colours
(colour `0` is `M`, colour `3j + c + 1` is `R_{j,c}`), and for every `v ∈ Z` a pair
`(lev(v), κ(v))` drawn from `levLaw J ⊗ kapLaw`, independently. (The level of a vertex of `Q` is
drawn but never used: `U_j` contains all of `Q`.) This is the manuscript's label space up to the
unused levels of `Q`.

Item (G2): "Fix a colouring `χ` in (G1) and a pair `(j,c)` … `𝒦_{j,c}` … is closed upwards …
For `v ∈ Z` the event `v ∈ V_{j,c}` depends only on `κ(v)` and, if `v ∈ P`, on `lev(v)`, so these
events are mutually independent over `v` … `P(v ∈ V_{j,c}) ≥ 1/L` … apply Theorem 16* …
`P(V' ∉ 𝒦_{j,c}) ≤ 2^{96}L^{30}N^{-3}`. By observation (MC) … also
`P(V_{j,c} ∉ 𝒦_{j,c}) ≤ 2^{96}L^{30}N^{-3}`." (`EG.TPVProb.G2_class`.)
-/

public section

namespace EG

namespace TPVProb

open Finset FinDist VortexLaw

variable {V : Type*} [DecidableEq V]

/-! ### The label space and the objects it determines -/

/-- `R_{j,c}`: the edges of colour `3j + c + 1`. -/
@[expose] def Rof {E : Finset (Sym2 V)} {k : ℕ} (χ : E → Fin k) (j : ℕ) (c : Fin 3) :
    Finset (Sym2 V) :=
  selectSet E fun e => decide ((χ e : ℕ) = 3 * j + c + 1)

/-- `M`: the edges of colour `0`. -/
@[expose] def Mof {E : Finset (Sym2 V)} {k : ℕ} (χ : E → Fin k) : Finset (Sym2 V) :=
  selectSet E fun e => decide ((χ e : ℕ) = 0)

/-- The level of a vertex (`0` outside `Z`). -/
@[expose] def levOf {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 4) (v : V) : ℕ :=
  if h : v ∈ Z then ((lab ⟨v, h⟩).1 : ℕ) else 0

/-- The label `κ` of a vertex (`0` outside `Z`). -/
@[expose] def kapOf {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 4) (v : V) : Fin 4 :=
  if h : v ∈ Z then (lab ⟨v, h⟩).2 else 0

theorem levOf_of_mem {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 4) {v : V}
    (h : v ∈ Z) : levOf lab v = ((lab ⟨v, h⟩).1 : ℕ) := by
  simp [levOf, h]

theorem kapOf_of_mem {Z : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 4) {v : V}
    (h : v ∈ Z) : kapOf lab v = (lab ⟨v, h⟩).2 := by
  simp [kapOf, h]

omit [DecidableEq V] in
theorem Rof_subset {E : Finset (Sym2 V)} {k : ℕ} (χ : E → Fin k) (j : ℕ) (c : Fin 3) :
    Rof χ j c ⊆ E := selectSet_subset _ _

omit [DecidableEq V] in
theorem Mof_subset {E : Finset (Sym2 V)} {k : ℕ} (χ : E → Fin k) : Mof χ ⊆ E :=
  selectSet_subset _ _

omit [DecidableEq V] in
theorem mem_Rof {E : Finset (Sym2 V)} {k : ℕ} {χ : E → Fin k} {j : ℕ} {c : Fin 3} {e : Sym2 V} :
    e ∈ Rof χ j c ↔ ∃ h : e ∈ E, ((χ ⟨e, h⟩ : Fin k) : ℕ) = 3 * j + c + 1 := by
  simp [Rof, mem_selectSet]

omit [DecidableEq V] in
theorem mem_Mof {E : Finset (Sym2 V)} {k : ℕ} {χ : E → Fin k} {e : Sym2 V} :
    e ∈ Mof χ ↔ ∃ h : e ∈ E, ((χ ⟨e, h⟩ : Fin k) : ℕ) = 0 := by
  simp [Mof, mem_selectSet]

omit [DecidableEq V] in
theorem Rof_disjoint {E : Finset (Sym2 V)} {k : ℕ} (χ : E → Fin k) {j j' : ℕ} {c c' : Fin 3}
    (h : (j, c) ≠ (j', c')) : Disjoint (Rof χ j c) (Rof χ j' c') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨h1, e1⟩ := mem_Rof.1 he
  obtain ⟨h2, e2⟩ := mem_Rof.1 he'
  have : 3 * j + (c : ℕ) + 1 = 3 * j' + c' + 1 := e1.symm.trans e2
  have hc := c.2
  have hc' := c'.2
  apply h
  have hjj : j = j' := by omega
  subst hjj
  have : (c : ℕ) = c' := by omega
  rw [Fin.ext_iff.2 this]

omit [DecidableEq V] in
theorem Rof_disjoint_Mof {E : Finset (Sym2 V)} {k : ℕ} (χ : E → Fin k) (j : ℕ) (c : Fin 3) :
    Disjoint (Rof χ j c) (Mof χ) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨h1, e1⟩ := mem_Rof.1 he
  obtain ⟨h2, e2⟩ := mem_Mof.1 he'
  omega

omit [DecidableEq V] in
/-- For `j < J`, `R_{j,c}` is a colour class of the `(3J+1)`-colouring. -/
theorem Rof_eq {E : Finset (Sym2 V)} {J : ℕ} (χ : E → Fin (3 * J + 1)) {j : ℕ} (hj : j < J)
    (c : Fin 3) :
    Rof χ j c = selectSet E fun e => decide (χ e = ⟨3 * j + c + 1, by have := c.2; omega⟩) := by
  unfold Rof
  congr 1
  funext e
  simp [Fin.ext_iff]

/-! ### The law of `V_{j,c}` -/

/-- The per-vertex law of `(lev, κ)`. -/
@[expose] noncomputable def vLaw (J : ℕ) : FinDist (Fin (J + 1) × Fin 4) :=
  (levLaw J).prod kapLaw

/-- The law of all vertex labels. -/
@[expose] noncomputable def labLaw (Z : Finset V) (J : ℕ) : FinDist (Z → Fin (J + 1) × Fin 4) :=
  pi fun _ : Z => vLaw J

/-- `V_{j,c}` as the set selected by the vertex labels. -/
theorem Vc_eq_selectSet {Z P : Finset V} {J : ℕ} (lab : Z → Fin (J + 1) × Fin 4) (j : ℕ)
    (c : Fin 3) :
    TPVRun.Vc Z P (levOf lab) (kapOf lab) j c =
      selectSet Z fun a => decide (((a : V) ∉ P ∨ j + 1 ≤ ((lab a).1 : ℕ)) ∧
        (lab a).2 = c.succ) := by
  ext v
  simp only [TPVRun.Vc, TPVRun.U, Finset.mem_filter, mem_selectSet, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hv, h⟩, hk⟩
    refine ⟨hv, ?_, ?_⟩
    · rwa [levOf_of_mem lab hv] at h
    · rwa [kapOf_of_mem lab hv] at hk
  · rintro ⟨hv, h, hk⟩
    refine ⟨⟨hv, ?_⟩, ?_⟩
    · rwa [levOf_of_mem lab hv]
    · rwa [kapOf_of_mem lab hv]

/-- The probability of a rectangle event of one vertex label. -/
theorem vLaw_prob_rect {J : ℕ} (A : Set (Fin (J + 1))) (B : Set (Fin 4)) :
    (vLaw J).prob {x | x.1 ∈ A ∧ x.2 ∈ B} = (levLaw J).prob A * kapLaw.prob B := by
  rw [vLaw, ← prob_prod_set_prod]
  rfl

/-- The element probabilities of `V_{j,c}`: `1/6` on `Q`, `2^{-(j+1)}/6` on `P`. -/
@[expose] noncomputable def qV (P : Finset V) (j : ℕ) (v : V) : ℝ :=
  (if v ∈ P then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 6)

theorem qV_nonneg (P : Finset V) (j : ℕ) (v : V) : 0 ≤ qV P j v := by
  unfold qV; split_ifs <;> positivity

theorem qV_le_one (P : Finset V) (j : ℕ) (v : V) : qV P j v ≤ 1 := by
  unfold qV
  have : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  split_ifs <;> nlinarith

theorem vLaw_prob_Vc {P : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 3) (v : V) :
    (vLaw J).prob {x | decide ((v ∉ P ∨ j + 1 ≤ (x.1 : ℕ)) ∧ x.2 = c.succ) = true} =
      qV P j v := by
  have e : {x : Fin (J + 1) × Fin 4 | decide ((v ∉ P ∨ j + 1 ≤ (x.1 : ℕ)) ∧ x.2 = c.succ) = true}
      = {x | x.1 ∈ {i : Fin (J + 1) | v ∉ P ∨ j + 1 ≤ (i : ℕ)} ∧ x.2 ∈ {y | y = c.succ}} := by
    ext x; simp
  rw [e, vLaw_prob_rect, kapLaw_succ, qV]
  congr 1
  by_cases hv : v ∈ P
  · rw [if_pos hv]
    have : {i : Fin (J + 1) | v ∉ P ∨ j + 1 ≤ (i : ℕ)} = {i : Fin (J + 1) | j + 1 ≤ (i : ℕ)} := by
      ext i; simp [hv]
    rw [this, levLaw_tail hj]
  · rw [if_neg hv]
    have : {i : Fin (J + 1) | v ∉ P ∨ j + 1 ≤ (i : ℕ)} = Set.univ := by
      ext i; simp [hv]
    rw [this, prob_univ]

/-- The selection rule of `V_{j,c}`. -/
@[expose] def selVc (P : Finset V) {Z : Finset V} (J j : ℕ) (c : Fin 3) (a : Z)
    (x : Fin (J + 1) × Fin 4) : Bool :=
  decide (((a : V) ∉ P ∨ j + 1 ≤ (x.1 : ℕ)) ∧ x.2 = c.succ)

theorem map_selVc {Z P : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 3) :
    (labLaw Z J).map (fun lab => selectSet Z fun a => selVc P J j c a (lab a)) =
      indepSubset Z (qV P j) (fun a _ => qV_nonneg P j a) (fun a _ => qV_le_one P j a) :=
  map_selectSet_pi (fun a _ => qV_nonneg P j a) (fun a _ => qV_le_one P j a)
    (fun _ : Z => vLaw J) (selVc P J j c)
    (fun a => map_eq_bernoulli _ _ _ _ (vLaw_prob_Vc (P := P) hj c (a : V)))

/-- The law of `V_{j,c}` is the independent random subset of `Z` with element probabilities
`qV`. -/
theorem map_Vc {Z P : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 3) :
    (labLaw Z J).map (fun lab => TPVRun.Vc Z P (levOf lab) (kapOf lab) j c) =
      indepSubset Z (qV P j) (fun a _ => qV_nonneg P j a) (fun a _ => qV_le_one P j a) := by
  rw [← map_selVc hj c]
  congr 1
  funext lab
  exact Vc_eq_selectSet lab j c

/-! ### Item (G2) for one class -/

/-- [s4:lemTPV] proof, item (G2), for one fixed class graph `X` (a spanning
`(ε_O, s')`-expander on `Z` with `s' ≥ 2^{145}L^{41}`): `R_{j,c}` fails to be
`(2^{12}L^4, 2^{10}L^8)`-path connected through `V_{j,c}` with probability at most
`2^{96}L^{30}N^{-3}` over the vertex labels. -/
theorem G2_class {Z P : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) (c : Fin 3) {X : FGraph V}
    (hXZ : X.verts = Z) {εO s' : ℝ} (hε7 : (2 : ℝ) ^ (-7 : ℤ) ≤ εO) (hε1 : εO ≤ 1)
    (hX : X.IsExpander εO s')
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card) (hN : Vortex.L Z.card ^ 3 ≤ (Z.card : ℝ))
    (hJ : 6 * (2 : ℝ) ^ J ≤ Vortex.L Z.card)
    (hs : (2 : ℝ) ^ 145 * Vortex.L Z.card ^ 41 ≤ s') :
    (labLaw Z J).prob {lab | ¬ X.IsPathConnected ((2 : ℝ) ^ 12 * Vortex.L Z.card ^ 4)
      ((2 : ℝ) ^ 10 * Vortex.L Z.card ^ 8) (TPVRun.Vc Z P (levOf lab) (kapOf lab) j c)} ≤
      (2 : ℝ) ^ 96 * Vortex.L Z.card ^ 30 * (Z.card : ℝ) ^ (-3 : ℤ) := by
  set L := Vortex.L Z.card with hLdef
  set ℓ := (2 : ℝ) ^ 12 * L ^ 4
  set t := (2 : ℝ) ^ 10 * L ^ 8
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  have hL1 : 1 ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hρ0 : (0 : ℝ) ≤ 1 / L := by positivity
  have hρ1 : 1 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
  -- the upward closed family
  let K : Set (Finset V) := {T | X.IsPathConnected ℓ t T}
  have hK : ∀ T T', T ⊆ T' → T' ⊆ Z → T ∈ K → T' ∈ K := fun T T' h _ hT =>
    hT.mono le_rfl rfl h le_rfl le_rfl
  -- the law of `V_{j,c}`
  have hlaw := map_Vc (P := P) (Z := Z) hj c
  have e1 : (labLaw Z J).prob {lab | ¬ X.IsPathConnected ℓ t
      (TPVRun.Vc Z P (levOf lab) (kapOf lab) j c)} =
      (indepSubset Z (qV P j) (fun a _ => qV_nonneg P j a) (fun a _ => qV_le_one P j a)).prob Kᶜ
      := by
    rw [← hlaw, prob_map]
    rfl
  rw [e1, prob_compl]
  -- (MC): compare with the `(1/L)`-random subset
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
    refine le_trans (le_of_eq ?_) hs
    ring
  have ht1 : (1 : ℝ) ≤ t := by
    have : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ hL1
    nlinarith
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
      (2 : ℝ) ^ 96 * L ^ 30 * (Z.card : ℝ) ^ (-3 : ℤ) := by ring
  linarith

end TPVProb

end EG
