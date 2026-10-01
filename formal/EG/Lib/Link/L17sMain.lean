module

public import EG.Lib.Link.L17sStep2
public import EG.Spec.Link.L17s

/-!
# Lemma 17* (manuscript s3:lemL17s): the rounds — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemL17s], Steps 0, 3, 4, 5 and the conclusion, on
the layered probability space: independent layers `V_1, …, V_{ℓ_*}` (`V_i` `p_*`-random for
`i < ℓ_*`, `V_{ℓ_*}` `q_*`-random), realized as the product `ν = pi` over `Fin ℓ_*` (layer `k`
is the manuscript's `V_{k+1}`); the final transfer to an arbitrary `ρ`-random subset uses that
the union is `ρ`-random ((S2), `Spec.StarUnionLawStatement`).

* `prob_pi_le_of_section`: conditioning on the coordinates before `j` ("Condition on
  `V_1, …, V_{i−1}`. This fixes `W := 𝓑_i`, while `V_i` is still `p_*`-random").
-/

public section

namespace EG.L17sProof

open Finset

universe u

variable {V : Type u} [DecidableEq V]

/-- Conditioning on the coordinates in `P`: if `A = {ω | Q (f ω) (ω j)}` with `f` depending only
on the coordinates in `P ∌ j`, and every section `{y | Q z y}` has `μ_j`-probability at most `c`,
then `A` has probability at most `c` under the product. -/
theorem prob_pi_le_of_section {ι : Type} [Fintype ι] [DecidableEq ι] {β : Type u} [Nonempty β]
    (μs : ι → FinDist β) (P : ι → Prop) [DecidablePred P] (j : ι) (hj : ¬ P j)
    {γ : Type u} (f : (ι → β) → γ) (hf : ∀ ω ω' : ι → β, (∀ i, P i → ω i = ω' i) → f ω = f ω')
    (Q : γ → β → Prop) (c : ℝ) (hc : ∀ z, (μs j).prob {y | Q z y} ≤ c) :
    (FinDist.pi μs).prob {ω | Q (f ω) (ω j)} ≤ c := by
  classical
  rw [FinDist.prob_pi_split μs P]
  refine FinDist.expect_le_of_le _ fun x => ?_
  set e := (Equiv.piEquivPiSubtypeProd P (fun _ : ι => β)).symm with he
  have hcomb : ∀ y, e (x, y) = fun i => if h : P i then x ⟨i, h⟩ else y ⟨i, h⟩ := fun y => rfl
  set y0 : ∀ i : {i // ¬ P i}, β := fun _ => Classical.arbitrary β
  set z := f (e (x, y0))
  have hset : {y : ∀ i : {i // ¬ P i}, β | e (x, y) ∈ {ω : ι → β | Q (f ω) (ω j)}} =
      {y | y ⟨j, hj⟩ ∈ {Y | Q z Y}} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    have h1 : f (e (x, y)) = z := hf _ _ (fun i hi => by rw [hcomb, hcomb]; simp [hi])
    have h2 : e (x, y) j = y ⟨j, hj⟩ := by rw [hcomb]; simp [hj]
    rw [h1, h2]
  rw [hset, FinDist.prob_pi_eval (fun i : {i // ¬ P i} => μs i) ⟨j, hj⟩]
  exact hc z

/-! ### The layers and the reached sets -/

section Layers

variable (ℓ : ℕ)

/-- Layer `k` (the manuscript's `V_{k+1}`), `∅` for `k ≥ ℓ`. -/
def lay (ω : Fin ℓ → Finset V) (k : ℕ) : Finset V := if h : k < ℓ then ω ⟨k, h⟩ else ∅

/-- `V_1 ∪ ⋯ ∪ V_j`. -/
def pre (ω : Fin ℓ → Finset V) (j : ℕ) : Finset V := (Finset.range j).biUnion (lay ℓ ω)

/-- The reached set `𝓑_{j+1}` (interiors in `V_1 ∪ ⋯ ∪ V_j`, length at most `j+1`). -/
noncomputable def Cset (K : FGraph V) (U : Finset V) (ω : Fin ℓ → Finset V) (j : ℕ) : Finset V :=
  reach K U (pre ℓ ω j) (j + 1)

variable {ℓ}

theorem lay_subset_pre {ω : Fin ℓ → Finset V} {k j : ℕ} (hkj : k < j) :
    lay ℓ ω k ⊆ pre ℓ ω j :=
  Finset.subset_biUnion_of_mem (lay ℓ ω) (Finset.mem_range.2 hkj)

theorem pre_mono {ω : Fin ℓ → Finset V} {j j' : ℕ} (h : j ≤ j') : pre ℓ ω j ⊆ pre ℓ ω j' :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono h)

theorem pre_congr {ω ω' : Fin ℓ → Finset V} {j : ℕ} (h : ∀ i : Fin ℓ, (i : ℕ) < j → ω i = ω' i) :
    pre ℓ ω j = pre ℓ ω' j := by
  unfold pre
  refine Finset.biUnion_congr rfl fun k hk => ?_
  unfold lay
  split_ifs with hk'
  · exact h ⟨k, hk'⟩ (Finset.mem_range.1 hk)
  · rfl

theorem pre_ell (ω : Fin ℓ → Finset V) : pre ℓ ω ℓ = Finset.univ.biUnion ω := by
  ext v
  simp only [pre, lay, Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, hv⟩
    rw [dif_pos hk] at hv
    exact ⟨⟨k, hk⟩, hv⟩
  · rintro ⟨i, hv⟩
    exact ⟨i, i.2, by rw [dif_pos i.2]; exact hv⟩

theorem Cset_mono_le {K : FGraph V} {U : Finset V} {ω : Fin ℓ → Finset V} {j j' : ℕ}
    (h : j ≤ j') : Cset ℓ K U ω j ⊆ Cset ℓ K U ω j' :=
  reach_mono (pre_mono h) (by omega)

/-- "`A_i(W) ⊆ 𝓑_{i+1} \ 𝓑_i`" for `W = 𝓑_i` and the layer `V_i`. -/
theorem Aset_Cset_subset (K : FGraph V) (U : Finset V) (ω : Fin ℓ → Finset V) (j : ℕ) :
    Aset K (Cset ℓ K U ω j) (lay ℓ ω j) ⊆ Cset ℓ K U ω (j + 1) \ Cset ℓ K U ω j :=
  Aset_subset (pre_mono (Nat.le_succ j)) (lay_subset_pre (Nat.lt_succ_self j))

/-- Step 4: "Suppose all `E_i` hold, and suppose `|𝓑_{ℓ_*}| < 2n/3`. … `|𝓑_{ℓ_*}| ≥ n`, a
contradiction. Therefore `|𝓑_{ℓ_*}| ≥ 2n/3`." -/
theorem two_thirds_le_card (K : FGraph V) (U : Finset V) (hUV : U ⊆ K.verts) (hU : U.Nonempty)
    (ω : Fin ℓ → Finset V) (hℓ : 1 ≤ ℓ) (g : ℝ) (hg : 0 ≤ g)
    (hgn : (K.card : ℝ) ≤ (1 + g) ^ (ℓ - 1))
    (hE : ∀ j < ℓ - 1, ¬ (((Cset ℓ K U ω j).card : ℝ) < 2 * (K.card : ℝ) / 3 ∧
      ((Aset K (Cset ℓ K U ω j) (lay ℓ ω j)).card : ℝ) < g * (Cset ℓ K U ω j).card)) :
    2 * (K.card : ℝ) / 3 ≤ (Cset ℓ K U ω (ℓ - 1)).card := by
  classical
  by_contra hlt
  push Not at hlt
  have hstep : ∀ j < ℓ - 1, (1 + g) * ((Cset ℓ K U ω j).card : ℝ) ≤ (Cset ℓ K U ω (j + 1)).card := by
    intro j hj
    have hsmall : ((Cset ℓ K U ω j).card : ℝ) < 2 * (K.card : ℝ) / 3 :=
      lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card (Cset_mono_le (by omega))) hlt
    have hA : g * ((Cset ℓ K U ω j).card : ℝ) ≤ (Aset K (Cset ℓ K U ω j) (lay ℓ ω j)).card := by
      by_contra h; push Not at h; exact hE j hj ⟨hsmall, h⟩
    have hsub := Aset_Cset_subset K U ω j
    have h1 : ((Aset K (Cset ℓ K U ω j) (lay ℓ ω j)).card : ℝ) ≤
        ((Cset ℓ K U ω (j + 1) \ Cset ℓ K U ω j).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((Cset ℓ K U ω (j + 1) \ Cset ℓ K U ω j).card : ℝ) =
        (Cset ℓ K U ω (j + 1)).card - (Cset ℓ K U ω j).card := by
      rw [Finset.card_sdiff_of_subset (Cset_mono_le (Nat.le_succ j)),
        Nat.cast_sub (Finset.card_le_card (Cset_mono_le (Nat.le_succ j)))]
    linarith
  have hg' := card_growth (fun j => ((Cset ℓ K U ω j).card : ℝ)) g hg (ℓ - 1) hstep
  have hC0 : (1 : ℝ) ≤ (Cset ℓ K U ω 0).card := by
    have : U ⊆ Cset ℓ K U ω 0 := subset_reach hUV _ _
    have := Finset.card_le_card this
    have h1 : 1 ≤ U.card := Finset.card_pos.2 hU
    exact_mod_cast le_trans h1 this
  have hpos : (0 : ℝ) ≤ (1 + g) ^ (ℓ - 1) := by positivity
  have hn : (K.card : ℝ) ≤ (Cset ℓ K U ω (ℓ - 1)).card := by
    calc (K.card : ℝ) ≤ (1 + g) ^ (ℓ - 1) := hgn
      _ = (1 + g) ^ (ℓ - 1) * 1 := (mul_one _).symm
      _ ≤ (1 + g) ^ (ℓ - 1) * (Cset ℓ K U ω 0).card := mul_le_mul_of_nonneg_left hC0 hpos
      _ ≤ _ := hg'
  have hK0 : (0 : ℝ) < K.card := by
    have : 0 < K.card := by
      rw [FGraph.card_def]; exact Finset.card_pos.2 (hU.mono hUV)
    exact_mod_cast this
  linarith

end Layers

/-- (O3) "Deleting one edge removes at most one vertex from an outside neighbourhood, so
`|Nbr_{G−F}(U)| ≥ |Nbr_G(U)| − |F|`." -/
theorem card_nbrSet_le (G : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) :
    (G.nbrSet U).card ≤ ((G.deleteEdges F).nbrSet U).card + F.card := by
  classical
  have hex : ∀ x ∈ G.nbrSet U \ (G.deleteEdges F).nbrSet U, ∃ u ∈ U, s(u, x) ∈ F := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hx
    rw [FGraph.mem_nbrSet] at h1
    obtain ⟨hxV, hxU, u, hu, hadj⟩ := h1
    by_contra hno
    push Not at hno
    apply h2
    rw [FGraph.mem_nbrSet]
    exact ⟨hxV, hxU, u, hu, FGraph.deleteEdges_adj.2 ⟨hadj, hno u hu⟩⟩
  choose! φ hφU hφF using hex
  have hD : (G.nbrSet U \ (G.deleteEdges F).nbrSet U).card ≤ F.card := by
    refine Finset.card_le_card_of_injOn (fun x => s(φ x, x)) (fun x hx => hφF x hx) ?_
    intro x hx y hy hxy
    simp only at hxy
    rcases Sym2.eq_iff.1 hxy with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso
      have hxU : x ∉ U := (FGraph.mem_nbrSet.1 (Finset.mem_sdiff.1 hx).1).2.1
      exact hxU (h2 ▸ hφU y hy)
  have := Finset.card_le_card_sdiff_add_card (s := G.nbrSet U) (t := (G.deleteEdges F).nbrSet U)
  omega

/-- The law of one coordinate of a product. -/
theorem map_eval_pi {ι : Type} [Fintype ι] {β : Type u} (μs : ι → FinDist β) (i : ι) :
    (FinDist.pi μs).map (fun ω => ω i) = μs i := by
  ext T
  rw [FinDist.map_w, ← FinDist.prob_singleton (μs i) T]
  exact FinDist.prob_pi_eval μs i {T}

/-! ### The layer law -/

/-- The density of layer `i`: `p_*` for `i < ℓ_*` (manuscript numbering), `q_*` for the last. -/
noncomputable def rr (n : ℕ) (ρ : ℝ) (i : Fin (Star.ell n)) : ℝ :=
  if (i : ℕ) + 1 < Star.ell n then Star.p n ρ else Star.q ρ

theorem rr_nonneg {n : ℕ} {ρ : ℝ} (hn : 2 ≤ n) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (i : Fin (Star.ell n)) :
    0 ≤ rr n ρ i := by
  unfold rr; split_ifs
  · exact (Star.p_pos hn h0 h1).le
  · exact (Star.q_pos h0).le

theorem rr_le_one {n : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (i : Fin (Star.ell n)) :
    rr n ρ i ≤ 1 := by
  unfold rr; split_ifs
  · exact Star.p_le_one h1
  · unfold Star.q; linarith

/-- The law of the layers `(V_1, …, V_{ℓ_*})`: independent, `V_i` `rr i`-random in `V(G)`. -/
noncomputable def layLaw (G : FGraph V) {ρ : ℝ} (hn : 2 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    FinDist (Fin (Star.ell G.card) → Finset V) :=
  FinDist.pi fun i => FinDist.rsubset G.verts (rr G.card ρ i) (rr_nonneg hn h0 h1 i)
    (rr_le_one h0 h1 i)

theorem rsubset_congr (S : Finset V) {a b : ℝ} (h : a = b) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : FinDist.rsubset S a ha0 ha1 = FinDist.rsubset S b hb0 hb1 := by
  subst h; rfl

/-- The layers `V_i` are `rr i`-random under `layLaw`. -/
theorem layLaw_isRSubset (G : FGraph V) {ρ : ℝ} (hn : 2 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (i : Fin (Star.ell G.card)) :
    (layLaw G hn h0 h1).IsRSubset (fun ω => ω i) G.verts (rr G.card ρ i) :=
  ⟨rr_nonneg hn h0 h1 i, rr_le_one h0 h1 i, map_eval_pi _ i⟩

/-- Almost surely every layer lies in `V(G)`. -/
theorem prob_not_subset (G : FGraph V) {ρ : ℝ} (hn : 2 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (layLaw G hn h0 h1).prob {ω | ¬ Finset.univ.biUnion ω ⊆ G.verts} = 0 := by
  classical
  rw [FinDist.prob_eq_zero_iff]
  intro ω hω
  by_contra hw
  apply hω
  have hpos : 0 < (layLaw G hn h0 h1).w ω := lt_of_le_of_ne ((layLaw G hn h0 h1).w_nonneg ω) (Ne.symm hw)
  intro v hv
  obtain ⟨i, -, hvi⟩ := Finset.mem_biUnion.1 hv
  have hi : 0 < (FinDist.rsubset G.verts (rr G.card ρ i) (rr_nonneg hn h0 h1 i)
      (rr_le_one h0 h1 i)).w (ω i) := by
    rw [← FinDist.mem_supp_iff_pos]
    have := (FinDist.mem_supp_pi (μ := fun i => FinDist.rsubset G.verts (rr G.card ρ i)
      (rr_nonneg hn h0 h1 i) (rr_le_one h0 h1 i))).1 ((FinDist.mem_supp_iff_pos _).2 hpos)
    exact this i
  exact FinDist.subset_of_indepSubset_w_pos _ _ hi hvi

/-- Step 3: `P(E_i^c) ≤ e^{−18uL}` for `1 ≤ i ≤ ℓ_*−1` (here `j = i − 1`): "Condition on
`V_1, …, V_{i−1}`. This fixes `W := 𝓑_i ⊇ 𝓑_1`, while `V_i` is still `p_*`-random. If
`|W| ≥ 2n/3` then `E_i` holds. Otherwise … (s3:eqL17claim) gives
`P(E_i^c | V_1, …, V_{i−1}) ≤ e^{−18uL}`." -/
theorem prob_Ej_le (hP13 : Spec.P13sStatement.{u}) (hPar : Spec.StarP13sParamsStatement)
    (hS6 : Spec.StarS6Statement) (hCh : Spec.ChernoffGenStatement.{u, u})
    (hBBD : Spec.BBDStatement.{u}) (hNumB : Spec.NumL17sBernsteinExponentStatement)
    (hNumM : Spec.NumL17sCaseBMeanStatement) (hNumAσ : Spec.NumL17sCaseASigmaStatement)
    (hNumAE : Spec.NumL17sCaseAExponentStatement) (hNumBG : Spec.NumL17sCaseBGrowthStatement)
    (hNumBE : Spec.NumL17sCaseBExponentStatement)
    (G : FGraph V) {ε' s₁ ρ : ℝ} (hG : G.IsExpander ε' s₁) (hn : 2 ≤ G.card)
    (hε1 : (2 : ℝ) ^ (-7 : ℤ) ≤ ε') (hε2 : ε' ≤ 1) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (hs₁ : 8 * (Star.d G.card ρ : ℝ) * (Star.lam G.card ρ : ℝ) ≤ s₁)
    (U : Finset V) (F : Finset (Sym2 V)) (hFE : F ⊆ G.edges) (hu1 : 1 ≤ U.card)
    (hFU : F.card ≤ U.card)
    (hθ : Star.theta G.card ε' ρ * U.card ≤ (reach (G.deleteEdges F) U ∅ 1).card)
    (j : ℕ) (hj : j + 1 < Star.ell G.card) :
    (layLaw G hn h0 h1).prob {ω | ((Cset (Star.ell G.card) (G.deleteEdges F) U ω j).card : ℝ) <
        2 * (G.card : ℝ) / 3 ∧
      ((Aset (G.deleteEdges F) (Cset (Star.ell G.card) (G.deleteEdges F) U ω j)
        (lay (Star.ell G.card) ω j)).card : ℝ) <
        Star.g G.card ε' * (Cset (Star.ell G.card) (G.deleteEdges F) U ω j).card} ≤
      Real.exp (-(18 * (U.card : ℝ) * Star.L G.card)) := by
  classical
  set ℓ := Star.ell G.card with hℓ
  set K := G.deleteEdges F with hK
  have hjℓ : j < ℓ := by omega
  let Q : Finset V → Finset V → Prop := fun W Y =>
    Star.theta G.card ε' ρ * U.card ≤ W.card ∧ W ⊆ G.verts ∧ (W.card : ℝ) < 2 * (G.card : ℝ) / 3 ∧
      ((Aset K W Y).card : ℝ) < Star.g G.card ε' * W.card
  have hsub : {ω | ((Cset ℓ K U ω j).card : ℝ) < 2 * (G.card : ℝ) / 3 ∧
      ((Aset K (Cset ℓ K U ω j) (lay ℓ ω j)).card : ℝ) < Star.g G.card ε' * (Cset ℓ K U ω j).card} ⊆
      {ω | Q (Cset ℓ K U ω j) (ω ⟨j, hjℓ⟩)} := by
    intro ω hω
    obtain ⟨h1', h2'⟩ := hω
    have hlay : lay ℓ ω j = ω ⟨j, hjℓ⟩ := by unfold lay; rw [dif_pos hjℓ]
    refine ⟨?_, reach_subset_verts K U _ _, h1', by rw [← hlay]; exact h2'⟩
    refine hθ.trans ?_
    have : reach K U ∅ 1 ⊆ Cset ℓ K U ω j := reach_mono (Finset.empty_subset _) (by omega)
    exact_mod_cast Finset.card_le_card this
  refine (FinDist.prob_mono _ hsub).trans ?_
  unfold layLaw
  refine prob_pi_le_of_section _ (fun i : Fin ℓ => (i : ℕ) < j) ⟨j, hjℓ⟩ (by simp)
    (fun ω => Cset ℓ K U ω j) (fun ω ω' h => by
      unfold Cset; rw [pre_congr (fun i hi => h i hi)]) Q _ fun z => ?_
  have hrr : rr G.card ρ ⟨j, hjℓ⟩ = Star.p G.card ρ := by unfold rr; rw [if_pos hj]
  rw [rsubset_congr G.verts hrr _ _ (Star.p_pos hn h0 h1).le (Star.p_le_one h1)]
  by_cases hz : Star.theta G.card ε' ρ * U.card ≤ z.card ∧ z ⊆ G.verts ∧
      (z.card : ℝ) < 2 * (G.card : ℝ) / 3
  · have hsub2 : {Y | Q z Y} ⊆ {Y | ((Aset K z Y).card : ℝ) < Star.g G.card ε' * z.card} :=
      fun Y hY => hY.2.2.2
    refine (FinDist.prob_mono _ hsub2).trans ?_
    exact step2 hP13 hPar hS6 hCh hBBD hNumB hNumM hNumAσ hNumAE hNumBG hNumBE G hG hn hε1 hε2 h0
      h1 hs₁ F hFE U.card hu1 hFU z hz.2.1 hz.1 hz.2.2.le
  · refine le_trans (le_of_eq ?_) (Real.exp_pos _).le
    rw [FinDist.prob_eq_zero_iff]
    intro Y hY
    exact absurd ⟨hY.1, hY.2.1, hY.2.2.1⟩ hz

/-- Step 5, first event: "Condition on `V_1, …, V_{ℓ_*−1}` with `|𝓑_{ℓ_*}| ≥ 2n/3`. The set
`V_{ℓ_*}` is still `0.9ρ`-random, so `|𝓑_{ℓ_*} ∩ V_{ℓ_*}|` is binomial with mean at least
`0.6ρn`. The lower-tail Chernoff bound … with `δ=0.09` gives
`P(|𝓑_{ℓ_*} ∩ V_{ℓ_*}| < 0.546ρn) ≤ exp(−0.0081·0.6ρn/2)`." -/
theorem prob_E5a_le (hCh : Spec.ChernoffGenStatement.{u, u}) (G : FGraph V) {ρ : ℝ}
    (hn : 2 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (K : FGraph V) (U : Finset V)
    (hK : K.verts = G.verts) :
    (layLaw G hn h0 h1).prob {ω | 2 * (G.card : ℝ) / 3 ≤
        (Cset (Star.ell G.card) K U ω (Star.ell G.card - 1)).card ∧
      ((lay (Star.ell G.card) ω (Star.ell G.card - 1) ∩
        Cset (Star.ell G.card) K U ω (Star.ell G.card - 1)).card : ℝ) ≤
        (1 - 0.09) * (0.6 * (ρ * G.card))} ≤
      Real.exp (-(0.09 ^ 2 * (0.6 * (ρ * G.card)) / 2)) := by
  classical
  set ℓ := Star.ell G.card with hℓ
  have hℓ2 : 2 ≤ ℓ := Star.two_le_ell hn
  have hjℓ : ℓ - 1 < ℓ := by omega
  let Q : Finset V → Finset V → Prop := fun W Y =>
    W ⊆ G.verts ∧ 2 * (G.card : ℝ) / 3 ≤ W.card ∧
      ((Y ∩ W).card : ℝ) ≤ (1 - 0.09) * (0.6 * (ρ * G.card))
  have hsub : {ω | 2 * (G.card : ℝ) / 3 ≤ (Cset ℓ K U ω (ℓ - 1)).card ∧
      ((lay ℓ ω (ℓ - 1) ∩ Cset ℓ K U ω (ℓ - 1)).card : ℝ) ≤ (1 - 0.09) * (0.6 * (ρ * G.card))} ⊆
      {ω | Q (Cset ℓ K U ω (ℓ - 1)) (ω ⟨ℓ - 1, hjℓ⟩)} := by
    intro ω hω
    have hlay : lay ℓ ω (ℓ - 1) = ω ⟨ℓ - 1, hjℓ⟩ := by unfold lay; rw [dif_pos hjℓ]
    refine ⟨?_, hω.1, by rw [← hlay]; exact hω.2⟩
    rw [← hK]; exact reach_subset_verts K U _ _
  refine (FinDist.prob_mono _ hsub).trans ?_
  unfold layLaw
  refine prob_pi_le_of_section _ (fun i : Fin ℓ => (i : ℕ) < ℓ - 1) ⟨ℓ - 1, hjℓ⟩ (by simp)
    (fun ω => Cset ℓ K U ω (ℓ - 1)) (fun ω ω' h => by
      unfold Cset; rw [pre_congr (fun i hi => h i hi)]) Q _ fun z => ?_
  have hrr : rr G.card ρ ⟨ℓ - 1, hjℓ⟩ = Star.q ρ := by
    unfold rr; rw [if_neg (by simp only; omega)]
  have hq0 := Star.q_pos h0
  have hq1 : Star.q ρ ≤ 1 := by unfold Star.q; linarith
  rw [rsubset_congr G.verts hrr _ _ hq0.le hq1]
  by_cases hz : z ⊆ G.verts ∧ 2 * (G.card : ℝ) / 3 ≤ z.card
  · have hR := FinDist.isRSubset_rsubset (S := G.verts) hq0.le hq1
    have hμ : 0.6 * (ρ * G.card) ≤ Star.q ρ * z.card := by
      unfold Star.q; nlinarith
    have h := card_inter_le_tail hCh z hz.1 hR (δ := 0.09) (μ₀ := 0.6 * (ρ * G.card))
      (by norm_num) (by norm_num) (by positivity) hμ
    refine le_trans (FinDist.prob_mono _ fun Y hY => ?_) h
    exact hY.2.2
  · refine le_trans (le_of_eq ?_) (Real.exp_pos _).le
    rw [FinDist.prob_eq_zero_iff]
    intro Y hY
    exact absurd ⟨hY.1, hY.2.1⟩ hz

/-- Step 5, second event: "Since `V` is `ρ`-random, `|V| ∼ Bin(n,ρ)`, and
`P(|V| > 1.09ρn) ≤ exp(−0.0081ρn/3)`." -/
theorem prob_E5b_le (hCh : Spec.ChernoffGenStatement.{u, u})
    (hUnion : Spec.StarUnionLawStatement.{u, u}) (G : FGraph V) {ρ : ℝ}
    (hn : 2 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (layLaw G hn h0 h1).prob {ω | (1 + 0.09) * (ρ * G.card) ≤
        ((Finset.univ.biUnion ω ∩ G.verts).card : ℝ)} ≤
      Real.exp (-(0.09 ^ 2 * (ρ * G.card) / 3)) := by
  classical
  have hR : (layLaw G hn h0 h1).IsRSubset (fun ω => Finset.univ.biUnion ω) G.verts ρ :=
    hUnion V (Fin (Star.ell G.card) → Finset V) (layLaw G hn h0 h1) G.verts G.card ρ
      (fun ω => ω) hn h0 h1 (FinDist.iIndepFun_eval_pi _)
      (fun i => layLaw_isRSubset G hn h0 h1 i)
  exact card_inter_ge_tail hCh G.verts subset_rfl hR (by norm_num) (by norm_num)
    (by rw [FGraph.card_def])

/-- Lemma 17* on the layered space: for a well-expanding nonempty `U ⊆ V(G)` and `F ⊆ E(G)` with
`|F| ≤ |U|`, `P(|B^{ℓ_*}_{G−F}(U,V)| ≤ |V|/2) ≤ exp(−7|U|L)` for `V = V_1 ∪ ⋯ ∪ V_{ℓ_*}`. -/
theorem layered (hP13 : Spec.P13sStatement.{u}) (hPar : Spec.StarP13sParamsStatement)
    (hS6 : Spec.StarS6Statement) (hCh : Spec.ChernoffGenStatement.{u, u})
    (hBBD : Spec.BBDStatement.{u}) (hUnion : Spec.StarUnionLawStatement.{u, u})
    (hNumB : Spec.NumL17sBernsteinExponentStatement)
    (hNumM : Spec.NumL17sCaseBMeanStatement) (hNumAσ : Spec.NumL17sCaseASigmaStatement)
    (hNumAE : Spec.NumL17sCaseAExponentStatement) (hNumBG : Spec.NumL17sCaseBGrowthStatement)
    (hNumBE : Spec.NumL17sCaseBExponentStatement) (hNum0 : Spec.NumL17sStep0Statement)
    (hNum3 : Spec.NumL17sStep3Statement) (hNum4 : Spec.NumL17sStep4Statement)
    (hNum5 : Spec.NumL17sStep5Statement)
    (G : FGraph V) {ε' s₁ ρ : ℝ} (hG : G.IsExpander ε' s₁) (hn : 2 ≤ G.card)
    (hε1 : (2 : ℝ) ^ (-7 : ℤ) ≤ ε') (hε2 : ε' ≤ 1) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (hs₁ : 8 * (Star.d G.card ρ : ℝ) * (Star.lam G.card ρ : ℝ) ≤ s₁)
    (U : Finset V) (F : Finset (Sym2 V)) (hUV : U ⊆ G.verts) (hFE : F ⊆ G.edges)
    (hFU : F.card ≤ U.card) (hwe : G.IsWellExpanding (Star.theta G.card ε' ρ) U)
    (hU : U.Nonempty) :
    (layLaw G hn h0 h1).prob {ω | ((ball (G.deleteEdges F) (Star.ell G.card) U
        (Finset.univ.biUnion ω)).card : ℝ) ≤ ((Finset.univ.biUnion ω).card : ℝ) / 2} ≤
      Real.exp (-(7 * (U.card : ℝ) * Real.logb 2 (G.card : ℝ))) := by
  classical
  set n := G.card with hndef
  set ℓ := Star.ell n with hℓdef
  set K := G.deleteEdges F with hKdef
  set ν := layLaw G hn h0 h1 with hνdef
  set x : ℝ := ρ * n with hxdef
  set g := Star.g n ε' with hgdef
  have hℓ2 : 2 ≤ ℓ := Star.two_le_ell hn
  have hu1 : 1 ≤ U.card := Finset.card_pos.2 hU
  have hu1' : (1 : ℝ) ≤ U.card := by exact_mod_cast hu1
  have hKc : K.card = n := rfl
  have hKv : K.verts = G.verts := rfl
  rw [← Star.L_eq]
  -- Step 0
  have hNU : ((G.nbrSet U).card : ℝ) < n := by
    have hsub : G.nbrSet U ⊆ G.verts \ U := fun v hv => by
      rw [FGraph.mem_nbrSet] at hv; exact Finset.mem_sdiff.2 ⟨hv.1, hv.2.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hUV] at this
    have hUc := Finset.card_le_card hUV
    have hlt : (G.nbrSet U).card < G.verts.card := by omega
    have : ((G.nbrSet U).card : ℝ) < (G.verts.card : ℝ) := by exact_mod_cast hlt
    exact this
  have hθn : Star.theta n ε' ρ * U.card < n := lt_of_le_of_lt hwe hNU
  obtain ⟨hx39, h7⟩ := hNum0 n ε' ρ U.card hn hε1 hε2 h0 h1 hu1' hθn
  -- `θu ≤ |𝓑_1|`
  have hθ : Star.theta n ε' ρ * U.card ≤ (reach K U ∅ 1).card := by
    have h1' := card_nbrSet_le G U F
    have hdisj : Disjoint U (K.nbrSet U) := by
      rw [Finset.disjoint_left]; intro v hv hv'
      exact (FGraph.mem_nbrSet.1 hv').2.1 hv
    have hsub : U ∪ K.nbrSet U ⊆ reach K U ∅ 1 :=
      Finset.union_subset (subset_reach (hKv ▸ hUV) _ _) (nbrSet_subset_reach _ _ le_rfl)
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h2
    have h3 : ((G.nbrSet U).card : ℝ) ≤ (K.nbrSet U).card + F.card := by exact_mod_cast h1'
    have h4 : ((U.card + (K.nbrSet U).card : ℕ) : ℝ) ≤ (reach K U ∅ 1).card := by exact_mod_cast h2
    have h5 : (F.card : ℝ) ≤ U.card := by exact_mod_cast hFU
    have hw : Star.theta n ε' ρ * U.card ≤ ((G.nbrSet U).card : ℝ) := hwe
    push_cast at h4
    linarith
  -- the events
  let Ej : ℕ → Set (Fin ℓ → Finset V) := fun j => {ω | ((Cset ℓ K U ω j).card : ℝ) <
      2 * (n : ℝ) / 3 ∧ ((Aset K (Cset ℓ K U ω j) (lay ℓ ω j)).card : ℝ) < g * (Cset ℓ K U ω j).card}
  let E5a : Set (Fin ℓ → Finset V) := {ω | 2 * (n : ℝ) / 3 ≤ (Cset ℓ K U ω (ℓ - 1)).card ∧
      ((lay ℓ ω (ℓ - 1) ∩ Cset ℓ K U ω (ℓ - 1)).card : ℝ) ≤ (1 - 0.09) * (0.6 * x)}
  let E5b : Set (Fin ℓ → Finset V) := {ω | (1 + 0.09) * x ≤ ((Finset.univ.biUnion ω ∩ G.verts).card : ℝ)}
  let E0 : Set (Fin ℓ → Finset V) := {ω | ¬ Finset.univ.biUnion ω ⊆ G.verts}
  obtain ⟨hg8, -, -, -, hgn⟩ := hNum4 n ε' hn hε1 hε2
  have hg0 : 0 ≤ g := (Star.g_pos hn (lt_of_lt_of_le (by positivity) hε1)).le
  have hbad : {ω : Fin ℓ → Finset V | ((ball K ℓ U (Finset.univ.biUnion ω)).card : ℝ) ≤
      ((Finset.univ.biUnion ω).card : ℝ) / 2} ⊆
      (((⋃ j ∈ Finset.range (ℓ - 1), Ej j) ∪ E5a) ∪ E5b) ∪ E0 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hno
    obtain ⟨⟨⟨hnE, hn5a⟩, hn5b⟩, hn0⟩ := hno
    have hE : ∀ j < ℓ - 1, ¬ (((Cset ℓ K U ω j).card : ℝ) < 2 * (K.card : ℝ) / 3 ∧
        ((Aset K (Cset ℓ K U ω j) (lay ℓ ω j)).card : ℝ) < g * (Cset ℓ K U ω j).card) :=
      fun j hj => hnE j (Finset.mem_range.2 hj)
    have h23 := two_thirds_le_card K U (hKv ▸ hUV) hU ω (show 1 ≤ ℓ by omega) g hg0
      (by rw [hKc]; exact hgn) hE
    rw [hKc] at h23
    have h5a : (1 - 0.09) * (0.6 * x) < ((lay ℓ ω (ℓ - 1) ∩ Cset ℓ K U ω (ℓ - 1)).card : ℝ) := by
      by_contra h; push Not at h; exact hn5a ⟨h23, h⟩
    have h5b : ((Finset.univ.biUnion ω ∩ G.verts).card : ℝ) < (1 + 0.09) * x := by
      by_contra h; push Not at h; exact hn5b h
    have hVsub : Finset.univ.biUnion ω ⊆ G.verts := by
      by_contra h; exact hn0 h
    rw [Finset.inter_eq_left.2 hVsub] at h5b
    -- (O2)
    have hO2 : lay ℓ ω (ℓ - 1) ∩ Cset ℓ K U ω (ℓ - 1) ⊆ ball K ℓ U (Finset.univ.biUnion ω) := by
      intro v hv
      obtain ⟨hvl, hvC⟩ := Finset.mem_inter.1 hv
      have hpre : pre ℓ ω ℓ = Finset.univ.biUnion ω := pre_ell ω
      have := mem_ball_of_mem_reach (T := Finset.univ.biUnion ω) hvC
        (by rw [← hpre]; exact lay_subset_pre (by omega) hvl)
        (by rw [← hpre]; exact pre_mono (by omega))
      rwa [show ℓ - 1 + 1 = ℓ by omega] at this
    have hball := Finset.card_le_card hO2
    have hball' : ((lay ℓ ω (ℓ - 1) ∩ Cset ℓ K U ω (ℓ - 1)).card : ℝ) ≤
        ((ball K ℓ U (Finset.univ.biUnion ω)).card : ℝ) := by exact_mod_cast hball
    have hx0 : 0 < x := lt_trans (by positivity) hx39
    linarith
  -- the probabilities
  have hpE : ∀ j ∈ Finset.range (ℓ - 1), ν.prob (Ej j) ≤
      Real.exp (-(18 * (U.card : ℝ) * Star.L n)) := fun j hj =>
    prob_Ej_le hP13 hPar hS6 hCh hBBD hNumB hNumM hNumAσ hNumAE hNumBG hNumBE G hG hn hε1 hε2
      h0 h1 hs₁ U F hFE hu1 hFU hθ j (by
        have := Finset.mem_range.1 hj
        have e : ℓ = Star.ell G.card := rfl
        omega)
  have hp5a : ν.prob E5a ≤ Real.exp (-(0.09 ^ 2 * (0.6 * x) / 2)) :=
    prob_E5a_le hCh G hn h0 h1 K U hKv
  have hp5b : ν.prob E5b ≤ Real.exp (-(0.09 ^ 2 * x / 3)) := prob_E5b_le hCh hUnion G hn h0 h1
  have hp0 : ν.prob E0 = 0 := prob_not_subset G hn h0 h1
  have hsumE : ν.prob (⋃ j ∈ Finset.range (ℓ - 1), Ej j) ≤
      ((ℓ : ℝ) - 1) * Real.exp (-(18 * (U.card : ℝ) * Star.L n)) := by
    refine (ν.prob_biUnion_le _ _).trans ((Finset.sum_le_sum hpE).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
    simp
  -- numerics
  obtain ⟨-, -, hs3⟩ := hNum3
  obtain ⟨s31, s32⟩ := hs3 n U.card hn hu1'
  obtain ⟨-, -, -, n4, n5, n6, n7, -, -, n10, n11⟩ := hNum5
  obtain ⟨n10a, n10b⟩ := n10 x (7 * U.card * Star.L n) hx39 h7
  have hx0 : 0 < x := lt_trans (by positivity) hx39
  have ea : Real.exp (-(0.09 ^ 2 * (0.6 * x) / 2)) ≤ Real.exp (-(x / 412)) := by
    rw [Real.exp_le_exp]
    have : (0.09 : ℝ) ^ 2 * (0.6 * x) / 2 = 0.00243 * x := by norm_num; ring
    rw [this]; nlinarith
  have eb : Real.exp (-(0.09 ^ 2 * x / 3)) ≤ Real.exp (-(x / 412)) := by
    rw [Real.exp_le_exp]
    have : (0.09 : ℝ) ^ 2 * x / 3 = 0.0027 * x := by norm_num; ring
    rw [this]; nlinarith
  have htot := (ν.prob_mono hbad).trans ((ν.prob_union_le _ _).trans (add_le_add
    ((ν.prob_union_le _ _).trans (add_le_add ((ν.prob_union_le _ _).trans
      (add_le_add hsumE hp5a)) hp5b)) (le_of_eq hp0)))
  have hey := Real.exp_pos (-(7 * (U.card : ℝ) * Star.L n))
  linarith

universe v

/-- [s3:lemL17s] Lemma 17*, in the form of `Spec.L17sStatement`: "Since this event depends only
on `V`, the same bound holds for every `ρ`-random subset `V` of `V(G)`." -/
theorem l17s (hP13 : Spec.P13sStatement.{u}) (hPar : Spec.StarP13sParamsStatement)
    (hS6 : Spec.StarS6Statement) (hCh : Spec.ChernoffGenStatement.{u, u})
    (hBBD : Spec.BBDStatement.{u}) (hUnion : Spec.StarUnionLawStatement.{u, u})
    (hNumB : Spec.NumL17sBernsteinExponentStatement)
    (hNumM : Spec.NumL17sCaseBMeanStatement) (hNumAσ : Spec.NumL17sCaseASigmaStatement)
    (hNumAE : Spec.NumL17sCaseAExponentStatement) (hNumBG : Spec.NumL17sCaseBGrowthStatement)
    (hNumBE : Spec.NumL17sCaseBExponentStatement) (hNum0 : Spec.NumL17sStep0Statement)
    (hNum3 : Spec.NumL17sStep3Statement) (hNum4 : Spec.NumL17sStep4Statement)
    (hNum5 : Spec.NumL17sStep5Statement) : Spec.L17sStatement.{u, v} := by
  intro V _ G ε' s₁ ρ Ω μ R hG hn hε1 hε2 h0 h1 hs₁ hR U F hUV hFE hFU hwe
  classical
  by_cases hU : U.Nonempty
  · have hν : (layLaw G hn h0 h1).IsRSubset (fun ω => Finset.univ.biUnion ω) G.verts ρ :=
      hUnion V (Fin (Star.ell G.card) → Finset V) (layLaw G hn h0 h1) G.verts G.card ρ
        (fun ω => ω) hn h0 h1 (FinDist.iIndepFun_eval_pi _)
        (fun i => layLaw_isRSubset G hn h0 h1 i)
    have hmap : μ.map R = (layLaw G hn h0 h1).map (fun ω => Finset.univ.biUnion ω) :=
      hR.map_eq.trans hν.map_eq.symm
    have e1 : {ω | ((ball (G.deleteEdges F) (Star.ell G.card) U (R ω)).card : ℝ) ≤
        ((R ω).card : ℝ) / 2} = R ⁻¹' {T | ((ball (G.deleteEdges F) (Star.ell G.card) U T).card : ℝ) ≤
        (T.card : ℝ) / 2} := rfl
    rw [e1, ← FinDist.prob_map, hmap, FinDist.prob_map]
    exact layered hP13 hPar hS6 hCh hBBD hUnion hNumB hNumM hNumAσ hNumAE hNumBG hNumBE hNum0
      hNum3 hNum4 hNum5 G hG hn hε1 hε2 h0 h1 hs₁ U F hUV hFE hFU hwe hU
  · rw [Finset.not_nonempty_iff_eq_empty] at hU
    subst hU
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero]
    exact FinDist.prob_le_one _ _

end EG.L17sProof
