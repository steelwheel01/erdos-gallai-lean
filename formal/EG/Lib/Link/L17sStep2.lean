module

public import EG.Lib.Link.L17sReach
public import EG.Lib.Link.Star
public import EG.Lib.Prob.Indep
public import EG.Spec.Found.Chernoff
public import EG.Spec.Found.BBD
public import EG.Spec.Link.P13s
public import EG.Spec.Num.L17s
public import EG.Spec.Link.Star

/-!
# Lemma 17* (manuscript s3:lemL17s), Step 2: growth into a fixed set — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemL17s], Step 2: for a fixed `W ⊇ 𝓑_1` with
`|W| ≤ 2n/3` and a `p_*`-random `V_i`, `P(|A_i(W)| < g_*|W|) ≤ e^{−18uL}` (s3:eqL17claim), by
Proposition 13* and, in case (a), the Chernoff bound, in case (b), Lemma BBD.

The cited results enter as hypotheses (`Spec.ChernoffGenStatement`, `Spec.BBDStatement`,
`Spec.P13sStatement`) and so do the numeric steps of unit NUM (`EG/Spec/Num/L17s.lean`).

* `card_inter_le_tail`, `card_inter_ge_tail`: the Chernoff bounds for `|C ∩ R|`, `R` a
  `p`-random subset of `S ⊇ C`.
-/

public section

namespace EG.L17sProof

open Finset

universe u w

variable {V : Type u} [DecidableEq V]

/-- `|C ∩ R|` is a sum of independent indicators when `R` is `p`-random in `S ⊇ C`. -/
theorem sum_indicator_eq_card {Ω : Type w} (S C : Finset V) (hC : C ⊆ S) (R : Ω → Finset V)
    (ω : Ω) :
    ∑ a : S, (if (a : V) ∈ C ∧ (a : V) ∈ R ω then (1 : ℝ) else 0) = ((R ω ∩ C).card : ℝ) := by
  classical
  rw [Finset.sum_coe_sort S (fun a => if a ∈ C ∧ a ∈ R ω then (1 : ℝ) else 0), Finset.sum_boole]
  congr 1
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨hC h1, h1, h2⟩

theorem iIndep_indicator {Ω : Type w} {μ : FinDist Ω} {S : Finset V} {p : ℝ} (C : Finset V)
    {R : Ω → Finset V} (hR : μ.IsRSubset R S p) :
    μ.iIndepFun (fun (a : S) ω => if (a : V) ∈ C ∧ (a : V) ∈ R ω then (1 : ℝ) else 0) := by
  classical
  have h := hR.iIndepFun_mem.comp (fun (a : S) (b : Bool) => if (a : V) ∈ C ∧ b = true then
    (1 : ℝ) else 0)
  convert h using 3 with a ω
  simp

/-- Chernoff, lower tail: `P(|C ∩ R| ≤ (1−δ)μ₀) ≤ e^{−δ²μ₀/2}` for `0 ≤ μ₀ ≤ p|C|`. -/
theorem card_inter_le_tail (hCh : Spec.ChernoffGenStatement.{w, u}) {Ω : Type w}
    {μ : FinDist Ω} {S : Finset V} {p : ℝ} (C : Finset V) (hC : C ⊆ S) {R : Ω → Finset V}
    (hR : μ.IsRSubset R S p) {δ μ₀ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hμ0 : 0 ≤ μ₀)
    (hμ : μ₀ ≤ p * C.card) :
    μ.prob {ω | ((R ω ∩ C).card : ℝ) ≤ (1 - δ) * μ₀} ≤ Real.exp (-(δ ^ 2 * μ₀ / 2)) := by
  classical
  have hE : μ.expect (fun ω => ∑ a : S, (if (a : V) ∈ C ∧ (a : V) ∈ R ω then (1 : ℝ) else 0)) =
      p * C.card := by
    simp only [sum_indicator_eq_card S C hC R]
    rw [hR.expect_card_inter, Finset.inter_eq_right.2 hC]
  have h := (hCh Ω μ S (fun a ω => if (a : V) ∈ C ∧ (a : V) ∈ R ω then (1 : ℝ) else 0) δ μ₀
    (fun a ω => by split_ifs <;> simp) (iIndep_indicator C hR) hδ0 hδ1).2 hμ0 (hE ▸ hμ)
  simpa only [sum_indicator_eq_card S C hC R] using h

/-- Chernoff, upper tail: `P(|C ∩ R| ≥ (1+δ)μ₀) ≤ e^{−δ²μ₀/3}` for `μ₀ ≥ p|C|`. -/
theorem card_inter_ge_tail (hCh : Spec.ChernoffGenStatement.{w, u}) {Ω : Type w}
    {μ : FinDist Ω} {S : Finset V} {p : ℝ} (C : Finset V) (hC : C ⊆ S) {R : Ω → Finset V}
    (hR : μ.IsRSubset R S p) {δ μ₀ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hμ : p * C.card ≤ μ₀) :
    μ.prob {ω | (1 + δ) * μ₀ ≤ ((R ω ∩ C).card : ℝ)} ≤ Real.exp (-(δ ^ 2 * μ₀ / 3)) := by
  classical
  have hE : μ.expect (fun ω => ∑ a : S, (if (a : V) ∈ C ∧ (a : V) ∈ R ω then (1 : ℝ) else 0)) =
      p * C.card := by
    simp only [sum_indicator_eq_card S C hC R]
    rw [hR.expect_card_inter, Finset.inter_eq_right.2 hC]
  have h := (hCh Ω μ S (fun a ω => if (a : V) ∈ C ∧ (a : V) ∈ R ω then (1 : ℝ) else 0) δ μ₀
    (fun a ω => by split_ifs <;> simp) (iIndep_indicator C hR) hδ0 hδ1).1 (hE ▸ hμ)
  simpa only [sum_indicator_eq_card S C hC R] using h

/-- Step 2, case (a): "Every leaf of a star whose centre lies in `V_i` belongs to `A_i(W)`, and
distinct stars have distinct leaves. … `P(|Cen ∩ V_i| < p_*|Cen|/2) ≤ exp(−p_*|Cen|/8)`. Outside
this event, `|A_i(W)| ≥ λ_*p_*|Cen|/2 ≥ 3|Cen| ≥ 3|W|/σ_* = g_*|W|`." -/
theorem caseA (hCh : Spec.ChernoffGenStatement.{u, u}) (K : FGraph V) (W : Finset V)
    (lam : ℕ) (p σ g : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hσ : 0 < σ) (hlp : 6 ≤ (lam : ℝ) * p)
    (hg : g * W.card ≤ 3 * W.card / σ) (C : Finset V) (lv : V → Finset V) (hCW : C ⊆ W)
    (hWV : W ⊆ K.verts) (hC : (W.card : ℝ) / σ ≤ C.card)
    (hlv : ∀ c ∈ C, (lv c).card = lam ∧ lv c ⊆ K.verts \ W ∧ ∀ x ∈ lv c, K.Adj c x)
    (hdisj : (C : Set V).PairwiseDisjoint lv) :
    (FinDist.rsubset K.verts p hp0 hp1).prob {Y | ((Aset K W Y).card : ℝ) < g * W.card} ≤
      Real.exp (-(p * C.card / 8)) := by
  classical
  have hR := FinDist.isRSubset_rsubset (S := K.verts) hp0 hp1
  have hsub : {Y : Finset V | ((Aset K W Y).card : ℝ) < g * W.card} ⊆
      {Y | (((fun T => T) Y ∩ C).card : ℝ) ≤ (1 - 1 / 2) * (p * C.card)} := by
    intro Y hY
    simp only [Set.mem_ofPred_eq] at hY ⊢
    by_contra hlt
    push Not at hlt
    -- `|A| ≥ λ|C ∩ Y|`
    have hsub2 : (Y ∩ C).biUnion lv ⊆ Aset K W Y := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨hcY, hcC⟩ := Finset.mem_inter.1 hc
      obtain ⟨-, hlvW, hadj⟩ := hlv c hcC
      obtain ⟨hxV, hxW⟩ := Finset.mem_sdiff.1 (hlvW hxc)
      refine mem_Aset.2 ⟨?_, c, hCW hcC, hcY, hadj x hxc⟩
      rw [FGraph.mem_nbrSet]
      exact ⟨hxV, hxW, c, hCW hcC, hadj x hxc⟩
    have hcard : ((Y ∩ C).biUnion lv).card = lam * (Y ∩ C).card := by
      rw [Finset.card_biUnion (fun a ha b hb hab => hdisj (Finset.mem_inter.1 ha).2
        (Finset.mem_inter.1 hb).2 hab), Finset.sum_congr rfl (fun c hc => (hlv c
        (Finset.mem_inter.1 hc).2).1), Finset.sum_const, smul_eq_mul, mul_comm]
    have h1 : (lam : ℝ) * (Y ∩ C).card ≤ (Aset K W Y).card := by
      have := Finset.card_le_card hsub2
      rw [hcard] at this
      exact_mod_cast this
    have hl0 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    have h2 : (lam : ℝ) * (p * C.card / 2) ≤ (lam : ℝ) * (Y ∩ C).card :=
      mul_le_mul_of_nonneg_left (by linarith) hl0
    have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    have h3 : 3 * (C.card : ℝ) ≤ (lam : ℝ) * (p * C.card / 2) := by nlinarith
    have h4 : 3 * (W.card : ℝ) / σ ≤ 3 * C.card := by
      have := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 3)
      rw [mul_div_assoc] ; linarith
    linarith
  refine (FinDist.prob_mono _ hsub).trans ?_
  have h := card_inter_le_tail hCh C (hCW.trans hWV) hR (δ := 1 / 2) (μ₀ := p * C.card)
    (by norm_num) (by norm_num) (by positivity) le_rfl
  refine h.trans (le_of_eq ?_)
  congr 1; ring

/-! ### Case (b) -/

section CaseB

variable (K : FGraph V) (W X : Finset V) (H : FGraph V)

/-- The `H`-neighbours of `x`, as a subset of `W`. -/
noncomputable def Nset (x : V) : Finset V := by
  classical
  exact W.filter (fun w => s(w, x) ∈ H.edges)

theorem mem_Nset {x w : V} : w ∈ Nset W H x ↔ w ∈ W ∧ s(w, x) ∈ H.edges := by
  classical
  unfold Nset; rw [Finset.mem_filter]

/-- The count `Z` of the TeX: the number of `x ∈ X` with an `H`-neighbour in `Y`. -/
noncomputable def Zc (Y : Finset V) : ℕ := by
  classical
  exact (X.filter (fun x => ¬ Disjoint (Nset W H x) Y)).card

/-- The bounded-difference constants `c_k = |{x ∈ X : k ∈ N_H(x)}|`. -/
noncomputable def cdiff (k : V) : ℕ := by
  classical
  exact (X.filter (fun x => k ∈ Nset W H x)).card

variable {K W X H}

theorem Zc_eq (Y : Finset V) :
    Zc W X H Y = (X.filter (fun x => ¬ Disjoint (Nset W H x) Y)).card := by
  classical
  unfold Zc; congr

/-- "Every `x ∈ X` with an `H`-neighbour in `V_i` lies in `A_i(W)`." -/
theorem Zc_le_Aset (hXW : X ⊆ K.verts \ W) (hHK : H ≤ K) (Y : Finset V) :
    Zc W X H Y ≤ (Aset K W Y).card := by
  classical
  rw [Zc_eq]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨hxX, hnd⟩ := Finset.mem_filter.1 hx
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨w, hwN, hwY⟩ := hnd
  obtain ⟨hwW, hwx⟩ := (mem_Nset W H).1 hwN
  have hadj : K.Adj w x := hHK.2 hwx
  obtain ⟨hxV, hxW⟩ := Finset.mem_sdiff.1 (hXW hxX)
  refine mem_Aset.2 ⟨?_, w, hwW, hwY, hadj⟩
  rw [FGraph.mem_nbrSet]
  exact ⟨hxV, hxW, w, hwW, hadj⟩

/-- `N_H(x) = Nset x` has `d_H(x)` elements for `x ∈ X`. -/
theorem card_Nset (hXW : X ⊆ K.verts \ W) (hHv : H.verts = W ∪ X)
    (hHe : ∀ e ∈ H.edges, ∃ a ∈ W, ∃ b ∈ X, s(a, b) = e) {x : V} (hx : x ∈ X) :
    (Nset W H x).card = H.deg x := by
  classical
  rw [FGraph.deg_def]
  congr 1
  ext w
  rw [mem_Nset, FGraph.mem_nbrs, FGraph.adj_iff]
  have hxW : x ∉ W := (Finset.mem_sdiff.1 (hXW hx)).2
  constructor
  · rintro ⟨-, h⟩; rwa [Sym2.eq_swap]
  · intro h
    rw [Sym2.eq_swap] at h
    refine ⟨?_, h⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hHe _ h
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha
    · exact absurd ha hxW

theorem cdiff_eq (k : V) : cdiff W X H k = (X.filter (fun x => k ∈ Nset W H x)).card := by
  classical
  unfold cdiff; congr

theorem cdiff_le (hXW : X ⊆ K.verts \ W) (hHv : H.verts = W ∪ X) {Δ : ℕ}
    (hdW : ∀ w ∈ W, H.deg w ≤ Δ) (k : V) : cdiff W X H k ≤ Δ := by
  classical
  rw [cdiff_eq]
  by_cases hk : k ∈ W
  · refine le_trans (Finset.card_le_card fun x hx => ?_) (hdW k hk)
    obtain ⟨hxX, hkN⟩ := Finset.mem_filter.1 hx
    rw [FGraph.mem_nbrs, FGraph.adj_iff]
    exact ((mem_Nset W H).1 hkN).2
  · rw [Finset.card_eq_zero.2]
    · exact Nat.zero_le _
    · rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact hk ((mem_Nset W H).1 (Finset.mem_filter.1 hx).2).1

/-- Double count: `∑_k c_k = ∑_{x ∈ X} |N_H(x)|`. -/
theorem sum_cdiff (S : Finset V) (hWS : W ⊆ S) :
    ∑ k ∈ S, (cdiff W X H k : ℝ) = ∑ x ∈ X, ((Nset W H x).card : ℝ) := by
  classical
  simp only [cdiff_eq, Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : (Nset W H x) = S.filter (fun k => k ∈ Nset W H x) := by
    ext k
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨hWS ((mem_Nset W H).1 h).1, h⟩, fun h => h.2⟩
  rw [this, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [hk]

/-- Bounded differences: changing the bit of `k` changes `Z` by at most `c_k`. -/
theorem Zc_diff (Y Y' : Finset V) (k : V) (h : ∀ v, v ≠ k → (v ∈ Y ↔ v ∈ Y')) :
    |(Zc W X H Y : ℝ) - Zc W X H Y'| ≤ cdiff W X H k := by
  classical
  have key : ∀ A B : Finset V, (∀ v, v ≠ k → (v ∈ A ↔ v ∈ B)) →
      (Zc W X H A : ℝ) ≤ Zc W X H B + cdiff W X H k := by
    intro A B hAB
    rw [Zc_eq, Zc_eq, cdiff_eq]
    have hsub : X.filter (fun x => ¬ Disjoint (Nset W H x) A) ⊆
        X.filter (fun x => ¬ Disjoint (Nset W H x) B) ∪ X.filter (fun x => k ∈ Nset W H x) := by
      intro x hx
      obtain ⟨hxX, hnd⟩ := Finset.mem_filter.1 hx
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hk : k ∈ Nset W H x
      · exact Or.inr ⟨hxX, hk⟩
      · left
        refine ⟨hxX, ?_⟩
        rw [Finset.not_disjoint_iff] at hnd ⊢
        obtain ⟨w, hwN, hwA⟩ := hnd
        have hwk : w ≠ k := fun h => hk (h ▸ hwN)
        exact ⟨w, hwN, (hAB w hwk).1 hwA⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact_mod_cast this
  rw [abs_sub_le_iff]
  constructor
  · have := key Y Y' h; linarith
  · have := key Y' Y (fun v hv => (h v hv).symm); linarith

/-- Step 2, case (b): "Let `Z := |{x ∈ X : N_H(x) ∩ V_i ≠ ∅}|`. … `EZ ≥ (1−e^{−1})|X| ≥ 0.63|X|`.
… Apply the second bound of Lemma s1:lemBBD with … `c_k := deg_H(w_k)`, … `β := 2Δ_*|X|` and
`a := 0.3|X|` … `P(Z < 0.33|X|) ≤ exp(−|X|/(47Δ_*))`." (Here `c_k` counts the `H`-neighbours of
`k` in `X`, which is `deg_H(k)` for `k ∈ W` and `0` otherwise.) -/
theorem caseB (hBBD : Spec.BBDStatement.{u}) (hNumB : Spec.NumL17sBernsteinExponentStatement)
    (hNumM : Spec.NumL17sCaseBMeanStatement) (d Δ : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hXW : X ⊆ K.verts \ W) (hWV : W ⊆ K.verts) (hHK : H ≤ K) (hHv : H.verts = W ∪ X)
    (hHe : ∀ e ∈ H.edges, ∃ a ∈ W, ∃ b ∈ X, s(a, b) = e) (hdX : ∀ x ∈ X, H.deg x = d)
    (hdW : ∀ w ∈ W, H.deg w ≤ Δ) (hpd1 : 1 ≤ (d : ℝ) * p) (hpd2 : (d : ℝ) * p ≤ 2)
    (hΔ1 : (1 : ℝ) ≤ Δ) (hX0 : (0 : ℝ) < X.card) :
    (FinDist.rsubset K.verts p hp0 hp1).prob {Y | ((Aset K W Y).card : ℝ) < 0.33 * X.card} ≤
      Real.exp (-((X.card : ℝ) / (47 * Δ))) := by
  classical
  set rs := FinDist.rsubset K.verts p hp0 hp1 with hrsdef
  set μb := FinDist.pi fun _ : ↥K.verts => FinDist.bernoulli p hp0 hp1 with hμb
  have hrs : rs = μb.map (FinDist.selectSet K.verts) := rfl
  set Xc : ℝ := (X.card : ℝ) with hXc
  -- `E Z ≥ 0.63|X|`
  have hNs : ∀ x ∈ X, Nset W H x ⊆ K.verts := fun x _ w hw => hWV ((mem_Nset W H).1 hw).1
  have hEZ : 0.63 * Xc ≤ rs.expect (fun Y => (Zc W X H Y : ℝ)) := by
    have e1 : (fun Y => (Zc W X H Y : ℝ)) = fun Y =>
        ((X.filter fun x => Y ∈ {T : Finset V | ¬ Disjoint (Nset W H x) T}).card : ℝ) := by
      funext Y; rw [Zc_eq]; rfl
    rw [e1, rs.expect_card_filter]
    have hpx : ∀ x ∈ X, 1 - Real.exp (-1) ≤ rs.prob {T : Finset V | ¬ Disjoint (Nset W H x) T} := by
      intro x hx
      have hc : {T : Finset V | ¬ Disjoint (Nset W H x) T} = {T | Disjoint (Nset W H x) T}ᶜ := rfl
      rw [hc, FinDist.prob_compl, hrsdef, FinDist.prob_disjoint_rsubset _ _ (hNs x hx),
        card_Nset hXW hHv hHe hx, hdX x hx]
      have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
      have h2 : (1 - p) ^ d ≤ Real.exp (-p) ^ d := pow_le_pow_left₀ (by linarith) h1 d
      rw [← Real.exp_nat_mul] at h2
      have h3 : Real.exp ((d : ℝ) * -p) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      linarith
    have := Finset.sum_le_sum hpx
    rw [Finset.sum_const, nsmul_eq_mul] at this
    have hm := hNumM.1
    have : 0.63 * Xc ≤ Xc * (1 - Real.exp (-1)) := by nlinarith
    linarith
  -- Lemma BBD on the bits
  set Ψ : (↥K.verts → Bool) → ℝ := fun b => (Zc W X H (FinDist.selectSet K.verts b) : ℝ) with hΨ
  set c : ↥K.verts → ℝ := fun k => (cdiff W X H k : ℝ) with hc
  have hΔ0 : (0 : ℝ) ≤ Δ := by linarith
  have hck : ∀ k, 0 ≤ c k ∧ c k ≤ Δ := fun k =>
    ⟨Nat.cast_nonneg _, (Nat.cast_le.2 (cdiff_le hXW hHv hdW (k : V)) :
      ((cdiff W X H (k : V) : ℕ) : ℝ) ≤ ((Δ : ℕ) : ℝ))⟩
  have hdiff : ∀ (k : ↥K.verts) (x x' : ↥K.verts → Bool), (∀ j, j ≠ k → x j = x' j) →
      |Ψ x - Ψ x'| ≤ c k := by
    intro k x x' hxx
    refine Zc_diff _ _ (k : V) fun v hv => ?_
    rw [FinDist.mem_selectSet, FinDist.mem_selectSet]
    constructor
    · rintro ⟨hvS, h⟩
      exact ⟨hvS, by rw [← hxx ⟨v, hvS⟩ (fun h' => hv (congrArg Subtype.val h'))]; exact h⟩
    · rintro ⟨hvS, h⟩
      exact ⟨hvS, by rw [hxx ⟨v, hvS⟩ (fun h' => hv (congrArg Subtype.val h'))]; exact h⟩
  have hβ0 : 0 < 2 * (Δ : ℝ) * Xc := by positivity
  have hsumc : ∑ k, p * (1 - p) * c k ^ 2 ≤ 2 * (Δ : ℝ) * Xc := by
    have h1 : ∀ k, p * (1 - p) * c k ^ 2 ≤ p * Δ * c k := by
      intro k
      obtain ⟨hc0, hcΔ⟩ := hck k
      have : c k ^ 2 ≤ Δ * c k := by nlinarith
      have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
      have : p * (1 - p) * c k ^ 2 ≤ p * (Δ * c k) := by
        calc p * (1 - p) * c k ^ 2 ≤ p * c k ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); nlinarith
          _ ≤ p * (Δ * c k) := mul_le_mul_of_nonneg_left this hp0
      linarith
    have h2 : ∑ k, c k = (d : ℝ) * Xc := by
      rw [hc, Finset.sum_coe_sort K.verts (fun k => (cdiff W X H k : ℝ)),
        sum_cdiff K.verts hWV, Finset.sum_congr rfl (fun x hx => by
          rw [card_Nset hXW hHv hHe hx, hdX x hx]), Finset.sum_const, nsmul_eq_mul, mul_comm]
    calc ∑ k, p * (1 - p) * c k ^ 2 ≤ ∑ k, p * Δ * c k := Finset.sum_le_sum fun k _ => h1 k
      _ = p * Δ * ((d : ℝ) * Xc) := by rw [← Finset.mul_sum, h2]
      _ = Δ * ((d : ℝ) * p) * Xc := by ring
      _ ≤ Δ * 2 * Xc := by gcongr
      _ = 2 * (Δ : ℝ) * Xc := by ring
  have hB := hBBD ↥K.verts (fun _ => p) (fun _ => hp0) (fun _ => hp1) Ψ Δ c (2 * Δ * Xc)
    (0.3 * Xc) hΔ0 hck hdiff hβ0 hsumc (by positivity)
  dsimp only at hB
  obtain ⟨-, hlow⟩ := hB
  -- the event
  have hEΨ : μb.expect Ψ = rs.expect (fun Y => (Zc W X H Y : ℝ)) := by
    rw [hrs, FinDist.expect_map]
  have hsub : {Y : Finset V | ((Aset K W Y).card : ℝ) < 0.33 * Xc} ⊆
      {Y | (Zc W X H Y : ℝ) ≤ rs.expect (fun Y => (Zc W X H Y : ℝ)) - 0.3 * Xc} := by
    intro Y hY
    simp only [Set.mem_ofPred_eq] at hY ⊢
    have := Zc_le_Aset hXW hHK Y
    have h' : (Zc W X H Y : ℝ) ≤ (Aset K W Y).card := by exact_mod_cast this
    linarith
  refine (FinDist.prob_mono _ hsub).trans ?_
  rw [hrs, FinDist.prob_map]
  rw [← hrs, ← hEΨ]
  refine hlow.trans ?_
  obtain ⟨e1, e2, e3⟩ := hNumB Xc Δ hX0 (by linarith)
  rw [e1, e2]
  exact e3

end CaseB

/-- Step 2 (s3:eqL17claim): for a fixed `W ⊆ V(G)` with `θ_*u ≤ |W| ≤ 2n/3` and `|F| ≤ u`,
`P(|A(W)| < g_*|W|) ≤ e^{−18uL}` for a `p_*`-random subset of `V(G)`. -/
theorem step2 (hP13 : Spec.P13sStatement.{u}) (hPar : Spec.StarP13sParamsStatement)
    (hS6 : Spec.StarS6Statement) (hCh : Spec.ChernoffGenStatement.{u, u})
    (hBBD : Spec.BBDStatement.{u}) (hNumB : Spec.NumL17sBernsteinExponentStatement)
    (hNumM : Spec.NumL17sCaseBMeanStatement) (hNumAσ : Spec.NumL17sCaseASigmaStatement)
    (hNumAE : Spec.NumL17sCaseAExponentStatement) (hNumBG : Spec.NumL17sCaseBGrowthStatement)
    (hNumBE : Spec.NumL17sCaseBExponentStatement)
    (G : FGraph V) {ε' s₁ ρ : ℝ} (hG : G.IsExpander ε' s₁) (hn : 2 ≤ G.card)
    (hε1 : (2 : ℝ) ^ (-7 : ℤ) ≤ ε') (hε2 : ε' ≤ 1) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (hs₁ : 8 * (Star.d G.card ρ : ℝ) * (Star.lam G.card ρ : ℝ) ≤ s₁)
    (F : Finset (Sym2 V)) (hFE : F ⊆ G.edges) (u : ℕ) (hu1 : 1 ≤ u) (hFu : F.card ≤ u)
    (W : Finset V) (hWV : W ⊆ G.verts) (hWθ : Star.theta G.card ε' ρ * u ≤ W.card)
    (hW23 : (W.card : ℝ) ≤ 2 * (G.card : ℝ) / 3) :
    (FinDist.rsubset G.verts (Star.p G.card ρ) (Star.p_pos hn h0 h1).le
        (Star.p_le_one h1)).prob
      {Y | ((Aset (G.deleteEdges F) W Y).card : ℝ) < Star.g G.card ε' * W.card} ≤
      Real.exp (-(18 * (u : ℝ) * Star.L G.card)) := by
  classical
  set n := G.card with hndef
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  have hp0 := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := n) h1
  obtain ⟨hσeq, hdl3, hdleq, hσ0, hlam1, hd1, hlamD, hσL, hDl⟩ := hPar n ε' ρ hn hε1 hε2 h0 h1
  obtain ⟨-, hlp, hdp1, hdp2, hp2⟩ := hS6 n ε' ρ hn hε1 hε2 h0 h1
  have hθ1 : 1 ≤ Star.theta n ε' ρ := by
    have hL := Star.one_le_L hn
    have hl : (1 : ℝ) ≤ Star.ell n := by exact_mod_cast Star.ell_pos hn
    unfold Star.theta
    rw [le_div_iff₀ (by positivity)]
    have hερ : ε' * ρ ^ 2 ≤ 1 := by
      have : ρ ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
      nlinarith
    have : (1 : ℝ) ≤ (Star.ell n : ℝ) ^ 2 * Star.L n ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hl) (one_le_pow₀ hL)
    nlinarith
  have hu1' : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have huW : (u : ℝ) ≤ W.card := by nlinarith
  have hW1 : 1 ≤ W.card := by
    have : (1 : ℝ) ≤ W.card := le_trans hu1' huW
    exact_mod_cast this
  have hs8 : (8 : ℝ) ≤ s₁ := by
    have : (1 : ℝ) ≤ (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) := by
      have a1 : (1 : ℝ) ≤ Star.d n ρ := by exact_mod_cast hd1
      have a2 : (1 : ℝ) ≤ Star.lam n ρ := by exact_mod_cast hlam1
      nlinarith
    linarith
  have hFW : (F.card : ℝ) ≤ s₁ * W.card / 4 := by
    have hF : (F.card : ℝ) ≤ u := by exact_mod_cast hFu
    have hW0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    nlinarith
  rcases hP13 V G ε' s₁ (Star.sigma n ε') (Star.lam n ρ) (Star.d n ρ) (Star.Delta n ρ) W F hG hn
    hε1 hε2 hWV hW1 hW23 hFE hFW hσ0 hlam1 hd1 hlamD hσL hDl hs₁ with
    ⟨C, lv, hCW, hC, hlv, hdisj⟩ | ⟨X, H, hXW, hHK, hHv, hHe, hXc, hdX, hdW⟩
  · -- case (a)
    have hA := caseA hCh (G.deleteEdges F) W (Star.lam n ρ) (Star.p n ρ) (Star.sigma n ε')
      (Star.g n ε') hp0.le hp1 hσ0 hlp (by rw [← hNumAσ n ε' hn hε]) C lv hCW hWV hC hlv hdisj
    refine hA.trans (Real.exp_le_exp.2 ?_)
    obtain ⟨e1, e2⟩ := hNumAE n ε' ρ hn hε1 hε2 h0 h1 u W.card C.card hu1' hWθ hC
    linarith
  · -- case (b)
    have hX0 : (0 : ℝ) < X.card := by
      have hL := Star.one_le_L hn
      have hW1' : (1 : ℝ) ≤ W.card := by exact_mod_cast hW1
      have : 0 < ε' * (W.card : ℝ) / (2 * Real.logb 2 (n : ℝ) ^ 2) := by
        rw [← Star.L_eq]; positivity
      exact this.trans_le hXc
    have hΔ1 : (1 : ℝ) ≤ Star.Delta n ρ := by exact_mod_cast le_trans hlam1 hlamD
    have hB := caseB (K := G.deleteEdges F) (W := W) (X := X) (H := H) hBBD hNumB hNumM
      (Star.d n ρ) (Star.Delta n ρ) (Star.p n ρ) hp0.le hp1 hXW hWV hHK hHv
      (fun e he => (FGraph.mem_edgesBetween (H := G)).1 (hHe he) |>.2) hdX hdW hdp1
      (le_trans hdp2 hp2) hΔ1 hX0
    have hXc' : ε' * (W.card : ℝ) / (2 * Star.L n ^ 2) ≤ X.card := by rw [Star.L_eq]; exact hXc
    have hsub : {Y : Finset V | ((Aset (G.deleteEdges F) W Y).card : ℝ) < Star.g n ε' * W.card} ⊆
        {Y | ((Aset (G.deleteEdges F) W Y).card : ℝ) < 0.33 * X.card} := by
      intro Y hY
      simp only [Set.mem_ofPred_eq] at hY ⊢
      obtain ⟨g1, g2⟩ := hNumBG n ε' hn hε1 hε2 W.card X.card (Nat.cast_nonneg _) hXc'
      linarith
    refine (FinDist.prob_mono _ hsub).trans (hB.trans (Real.exp_le_exp.2 ?_))
    obtain ⟨e1, e2, e3⟩ := hNumBE n ε' ρ hn hε1 hε2 h0 h1 u W.card X.card hu1' hWθ hXc'
    linarith

end EG.L17sProof
