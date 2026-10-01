module

public import EG.Spec.Link.L9rho
public import EG.Spec.Ext.BMProp8
public import EG.Spec.Ext.Haxell
public import EG.Spec.Link.Multiset
public import EG.Lib.Link.Star
public import EG.Lib.Found.Graph
public import EG.Lib.Found.LogMono

/-!
# Lemma 9_ρ (manuscript s3:lemL9rho): the proof — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemL9rho]. The cited results enter as hypotheses
of the lemmas below (`Spec.BMProp8Statement` = [s1:citProp8], `Spec.HaxellStatement` =
[s1:citHaxell], `Spec.MultisetCountStatement` = [s3:remMultiset]); the stub
`EG/Proof/Todo/L9rho.lean` supplies them.

* `EG.L9rhoProof.card_W_ge`: "`|V| ≥ n/M_* + 2`";
* `EG.L9rhoProof.ell_le_card`: "`1 ≤ ℓ_* ≤ 2^{10}L^3 ≤ n` for `n ≥ 2^{30}`";
* `EG.L9rhoProof.exists_maximal`: a maximal subfamily `I' ⊆ I` of pairwise vertex-disjoint pairs;
* `EG.L9rhoProof.claim`: the Claim (a short path avoiding `F` for some `j ∈ I`);
* `EG.L9rhoProof.pathConnected`: the Haxell step.
-/

public section

namespace EG.L9rhoProof

open Finset

variable {V : Type*} [DecidableEq V]

/-- "`n/M_* ≤ ρn/2.1` and `ρn/2 − ρn/2.1 = ρn/42 ≥ 2`, so `|V| ≥ n/M_* + 2`." -/
theorem card_W_ge {n w ρ : ℝ} (h0 : 0 < ρ) (hn : 0 ≤ n) (hW : ρ * n / 2 ≤ w)
    (h84 : 84 ≤ ρ * n) : n / (Star.M ρ : ℝ) + 2 ≤ w := by
  have hM := Star.le_M ρ
  have hM0 : (0 : ℝ) < 21 / 10 / ρ := by positivity
  have h1 : n / (Star.M ρ : ℝ) ≤ n / (21 / 10 / ρ) := div_le_div_of_nonneg_left hn hM0 hM
  have h2 : n / (21 / 10 / ρ) = ρ * n / (21 / 10) := by field_simp
  rw [h2] at h1
  linarith

/-- "`1 ≤ ℓ_* ≤ 2^{10}L^3 ≤ n` for `n ≥ 2^{30}`." -/
theorem ell_le_card {n : ℕ} (hn : 2 ^ 30 ≤ n) :
    (2 : ℝ) ^ 10 * Star.L n ^ 3 ≤ n ∧ 1 ≤ Star.ell n ∧ Star.ell n ≤ n := by
  have hn' : (2 : ℝ) ^ 30 ≤ n := by exact_mod_cast hn
  have hmono := div_logb_pow_le_div_logb_pow (c := 2) (by norm_num) (k := 3)
    (a := (2 : ℝ) ^ 30) (b := n) (by positivity) (by
      rw [Real.log_pow]; push_cast
      have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num); norm_num at this; linarith)
      hn'
  have hl30 : Real.logb 2 ((2 : ℝ) ^ 30) = 30 := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
  rw [hl30] at hmono
  have hL : 30 ≤ Star.L n := by
    rw [Star.L, Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hn'
  have hL3 : 0 < Star.L n ^ 3 := by positivity
  have hkey : (2 : ℝ) ^ 30 * Star.L n ^ 3 ≤ 30 ^ 3 * n := by
    rw [← Star.L_eq, div_le_div_iff₀ (by norm_num) hL3] at hmono
    linarith
  have h1 : (2 : ℝ) ^ 10 * Star.L n ^ 3 ≤ n := by nlinarith
  have h2n : 2 ≤ n := le_trans (by norm_num) hn
  refine ⟨h1, le_trans (by norm_num) (Star.two_pow_ten_le_ell h2n), ?_⟩
  have := (Star.ell_le n).trans h1
  exact_mod_cast this

/-- A maximal subfamily of pairwise vertex-disjoint pairs ("Let `I' ⊆ I` be maximal such that the
pairs `{x_i,y_i}`, `i ∈ I'`, are pairwise vertex-disjoint; `I' ≠ ∅` because `I ≠ ∅`"). -/
theorem exists_maximal {ι : Type*} [DecidableEq ι] (P : ι → V × V) (I : Finset ι)
    (hI : I.Nonempty) :
    ∃ I' ⊆ I, I'.Nonempty ∧
      (I' : Set ι).PairwiseDisjoint (fun i => ({(P i).1, (P i).2} : Finset V)) ∧
      ∀ i ∈ I, i ∉ I' →
        ¬ (insert i (I' : Set ι)).PairwiseDisjoint (fun j => ({(P j).1, (P j).2} : Finset V)) := by
  classical
  set f : ι → Finset V := fun i => ({(P i).1, (P i).2} : Finset V)
  set C := I.powerset.filter (fun J : Finset ι => (J : Set ι).PairwiseDisjoint f) with hC
  have hCne : C.Nonempty := ⟨∅, by
    rw [hC, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨I', hI'C, hmax⟩ := Finset.exists_max_image C Finset.card hCne
  rw [hC, Finset.mem_filter, Finset.mem_powerset] at hI'C
  have hmax' : ∀ i ∈ I, i ∉ I' → ¬ (insert i (I' : Set ι)).PairwiseDisjoint f := by
    intro i hi hi' hpd
    have hmem : insert i I' ∈ C := by
      rw [hC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hi hI'C.1, ?_⟩
      rw [Finset.coe_insert]; exact hpd
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hi'] at this
    omega
  refine ⟨I', hI'C.1, ?_, hI'C.2, hmax'⟩
  obtain ⟨i, hi⟩ := hI
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply hmax' i hi (by rw [hne]; exact Finset.notMem_empty i)
  rw [hne, Finset.coe_empty, insert_empty_eq]
  exact Set.pairwiseDisjoint_singleton _ _

universe u

/-- The Claim of the proof of Lemma 9_ρ: "for every nonempty `I ⊆ [r]` and every `F ⊆ E(G)` with
`|F| < h^2|I|`, there are `j ∈ I` and `P ∈ 𝒴_j` with `E(P) ∩ F = ∅`" (`h = ⌊4ℓ_*L⌋`). -/
theorem claim (h8 : Spec.BMProp8Statement.{u}) (hMC : Spec.MultisetCountStatement.{u, 0})
    {V : Type u} [DecidableEq V] (G : FGraph V) (W : Finset V) (ρ t : ℝ)
    (hn : 2 ^ 30 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (hW : W ⊆ G.verts) (hWc : (G.card : ℝ) / (Star.M ρ : ℝ) + 2 ≤ W.card)
    (hball : ∀ U : Finset V, U.Nonempty → U ⊆ G.verts → ∀ F : Finset (Sym2 V), F ⊆ G.edges →
        (F.card : ℝ) ≤ Star.sbar G.card ρ t * (U.card : ℝ) →
        (W.card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell G.card) U W).card : ℝ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → V × V)
    (hP : ∀ i, (P i).1 ∈ G.verts ∧ (P i).2 ∈ G.verts ∧ (P i).1 ≠ (P i).2)
    (hPt : ∀ v : V, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ t)
    (I : Finset ι) (hI : I.Nonempty) (F : Finset (Sym2 V)) (hF : F ⊆ G.edges)
    (hFc : F.card < ⌊4 * (Star.ell G.card : ℝ) * Star.L G.card⌋₊ ^ 2 * I.card) :
    ∃ j ∈ I, ∃ p : List V, IsPathBetween G.edges (P j).1 (P j).2 p ∧ IsThrough W p ∧
      pathLength p ≤ ⌊4 * (Star.ell G.card : ℝ) * Star.L G.card⌋₊ ∧
      ∀ e ∈ walkEdges p, e ∉ F := by
  classical
  obtain ⟨hℓL, hℓ1, hℓn⟩ := ell_le_card hn
  have hn2 : 2 ≤ G.card := le_trans (by norm_num) hn
  have hL1 : 1 ≤ Star.L G.card := Star.one_le_L hn2
  set n := G.card with hndef
  set L := Star.L n with hLdef
  set ℓ := Star.ell n with hℓdef
  set M := Star.M ρ with hMdef
  set h := ⌊4 * (ℓ : ℝ) * L⌋₊ with hhdef
  -- `M_* ≥ 3` and `M_* ≤ 3.1/ρ`
  have hMr : (21 / 10 : ℝ) ≤ M := by
    have := Star.le_M ρ
    have : (21 / 10 : ℝ) ≤ 21 / 10 / ρ := by rw [le_div_iff₀ h0]; nlinarith
    linarith
  have hM3 : 3 ≤ M := by
    have : (2 : ℝ) < M := by linarith
    have : 2 < M := by exact_mod_cast this
    omega
  have hMle : (M : ℝ) ≤ 31 / 10 / ρ := by
    have := Star.M_lt h0
    have : (1 : ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ h0]; linarith
    have e : (31 / 10 : ℝ) / ρ = 21 / 10 / ρ + 1 / ρ := by ring
    linarith
  -- a maximal disjoint subfamily
  obtain ⟨I', hI'I, hI'ne, hpd, hmaxl⟩ := exists_maximal P I hI
  set k := I'.card with hkdef
  have hk1 : 1 ≤ k := Finset.card_pos.2 hI'ne
  have hIk : (I.card : ℝ) ≤ 2 * t * (k : ℝ) :=
    hMC V ι P t I I' (fun i => (hP i).2.2) hPt hI'I hpd hmaxl
  have h2k : 2 * k ≤ n := by
    have hc : (I'.biUnion (fun i => ({(P i).1, (P i).2} : Finset V))).card =
        ∑ i ∈ I', ({(P i).1, (P i).2} : Finset V).card :=
      Finset.card_biUnion (fun i hi j hj hij => hpd hi hj hij)
    have hc2 : ∑ i ∈ I', ({(P i).1, (P i).2} : Finset V).card = 2 * k := by
      rw [Finset.sum_congr rfl (fun i _ => Finset.card_pair (hP i).2.2), Finset.sum_const,
        smul_eq_mul, mul_comm]
    have hsub : I'.biUnion (fun i => ({(P i).1, (P i).2} : Finset V)) ⊆ G.verts := by
      intro v hv
      obtain ⟨i, -, hv⟩ := Finset.mem_biUnion.1 hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (hP i).1
      · exact (hP i).2.1
    have := Finset.card_le_card hsub
    rw [hc, hc2] at this
    exact this
  -- `t_{0*} := ⌈|I'|/(2M_*)⌉`
  set D := 2 * M with hDdef
  have hD : 6 ≤ D := by omega
  set t0 := (k + D - 1) / D with ht0def
  have hdm := Nat.div_add_mod (k + D - 1) D
  have hmod := Nat.mod_lt (k + D - 1) (show D > 0 by omega)
  rw [← ht0def] at hdm
  generalize hX : D * t0 = X at hdm
  have hXle : X ≤ k + D - 1 := by omega
  have hkX : k ≤ X := by omega
  have ht01 : 1 ≤ t0 := by
    by_contra hc
    have : t0 = 0 := Nat.lt_one_iff.1 (not_le.1 hc)
    rw [this, mul_zero] at hX
    omega
  have h2t0 : 2 * t0 - 1 ≤ k := by
    have h1' := Nat.mul_le_mul_right (t0 - 1) (show 2 ≤ D by omega)
    have e : D * (t0 - 1) = D * t0 - D := Nat.mul_sub_one D t0
    rw [e, hX] at h1'
    omega
  have ht0n : t0 ≤ n := by omega
  have h4t0 : 4 * t0 ≤ W.card + 2 := by
    have hXr : ((D * t0 : ℕ) : ℝ) ≤ (k : ℝ) + D - 1 := by
      rw [hX]
      have : X ≤ k + D - 1 := hXle
      have e : ((k + D - 1 : ℕ) : ℝ) = (k : ℝ) + D - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← e]; exact_mod_cast this
    push_cast at hXr
    have h2k' : 2 * (k : ℝ) ≤ n := by exact_mod_cast h2k
    have hM0 : (0 : ℝ) < M := by positivity
    have key : 4 * (t0 : ℝ) * M ≤ n + 4 * M := by rw [hDdef] at hXr; push_cast at hXr; nlinarith
    have key2 : 4 * (t0 : ℝ) ≤ n / M + 4 := by
      rw [div_add' _ _ _ hM0.ne', le_div_iff₀ hM0]; linarith
    have : (4 * t0 : ℝ) ≤ W.card + 2 := by linarith
    exact_mod_cast this
  -- `|F| ≤ s̄_* t_{0*}`
  have hFbound : (F.card : ℝ) ≤ Star.sbar n ρ t * (t0 : ℝ) := by
    have hFr : (F.card : ℝ) ≤ (h : ℝ) ^ 2 * I.card := by exact_mod_cast hFc.le
    have hh : (h : ℝ) ≤ 4 * ℓ * L := Nat.floor_le (by positivity)
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have hh2 : (h : ℝ) ^ 2 ≤ 16 * (ℓ : ℝ) ^ 2 * L ^ 2 := by nlinarith
    have hℓ2 : (ℓ : ℝ) ^ 2 * L ^ 2 ≤ 2 ^ 20 * L ^ 8 := by
      have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
      have := Star.ell_le n
      have h' : (ℓ : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 10 * L ^ 3) ^ 2 := pow_le_pow_left₀ hℓ0 this 2
      nlinarith [sq_nonneg L]
    have hkt : (k : ℝ) ≤ 2 * M * t0 := by
      have : (k : ℝ) ≤ ((D * t0 : ℕ) : ℝ) := by rw [hX]; exact_mod_cast hkX
      rw [hDdef] at this; push_cast at this; linarith
    have ht0' : (0 : ℝ) ≤ t0 := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg _) (hPt (P (hI.choose)).1)
    have hI0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
    have hL8 : (0 : ℝ) ≤ L ^ 8 := by positivity
    -- `|F| ≤ h^2 |I| ≤ 16ℓ^2L^2 · 2t · 2M t0 ≤ 2^26 L^8 t M t0`
    have s1 : (h : ℝ) ^ 2 * I.card ≤ (2 ^ 24 * L ^ 8) * (2 * t * (2 * M * t0)) := by
      have a1 : (h : ℝ) ^ 2 ≤ 2 ^ 24 * L ^ 8 := by linarith
      have a2 : (I.card : ℝ) ≤ 2 * t * (2 * M * t0) :=
        hIk.trans (mul_le_mul_of_nonneg_left hkt (by linarith))
      exact mul_le_mul a1 a2 hI0 (by positivity)
    have s2 : (2 ^ 24 * L ^ 8) * (2 * t * (2 * M * t0)) =
        2 ^ 26 * M * (t * L ^ 8 * t0) := by ring
    have s3 : (2 : ℝ) ^ 26 * M ≤ 2 ^ 28 / ρ := by
      have : (2 : ℝ) ^ 26 * (31 / 10 / ρ) ≤ 2 ^ 28 / ρ := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right h0]; norm_num
      have := mul_le_mul_of_nonneg_left hMle (by norm_num : (0 : ℝ) ≤ 2 ^ 26)
      linarith
    have s4 : (0 : ℝ) ≤ t * L ^ 8 * t0 := by positivity
    have s5 : Star.sbar n ρ t * (t0 : ℝ) = 2 ^ 28 / ρ * (t * L ^ 8 * t0) := by
      rw [Star.sbar]; ring
    rw [s5]
    calc (F.card : ℝ) ≤ (h : ℝ) ^ 2 * I.card := hFr
      _ ≤ 2 ^ 26 * M * (t * L ^ 8 * t0) := s1.trans (le_of_eq s2)
      _ ≤ 2 ^ 28 / ρ * (t * L ^ 8 * t0) := mul_le_mul_of_nonneg_right s3 s4
  -- the balls around any `t_{0*}` vertices
  have hU : ∀ U : Finset V, U ⊆ (G.deleteEdges F).verts → U.card = t0 →
      (W.card : ℝ) / 2 < ((ball (G.deleteEdges F) ℓ U W).card : ℝ) := by
    intro U hU hUc
    refine hball U (Finset.card_pos.1 (by omega)) hU F hF ?_
    rw [hUc]; exact hFbound
  -- `2t_{0*}-1` indices of `I'`
  have hle : 2 * t0 - 1 ≤ I'.card := h2t0
  set e : Fin (2 * t0 - 1) → ι := fun j => (I'.equivFin.symm (Fin.castLE hle j) : ι) with hedef
  have he_mem : ∀ j, e j ∈ I' := fun j => (I'.equivFin.symm (Fin.castLE hle j)).2
  have he_inj : Function.Injective e := by
    intro a b hab
    have := Subtype.ext hab
    exact Fin.castLE_injective hle (I'.equivFin.symm.injective this)
  -- distinct indices of `I'` have disjoint pairs
  have hdis : ∀ a b, e a ≠ e b → ∀ v, (v = (P (e a)).1 ∨ v = (P (e a)).2) →
      (v = (P (e b)).1 ∨ v = (P (e b)).2) → False := by
    intro a b hab v hva hvb
    have hd := hpd (he_mem a) (he_mem b) hab
    rw [Function.onFun, Finset.disjoint_left] at hd
    apply hd (a := v)
    · rcases hva with rfl | rfl <;> simp
    · rcases hvb with rfl | rfl <;> simp
  have hinj : Function.Injective (Sum.elim (fun j => (P (e j)).1) (fun j => (P (e j)).2)) := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · by_cases h' : e a = e b
      · rw [he_inj h']
      · exact (hdis a b h' _ (Or.inl rfl) (Or.inl hab)).elim
    · by_cases h' : e a = e b
      · exact ((hP (e a)).2.2 (by rw [hab, h'])).elim
      · exact (hdis a b h' _ (Or.inl rfl) (Or.inr hab)).elim
    · by_cases h' : e a = e b
      · exact ((hP (e a)).2.2 (by rw [hab, h'])).elim
      · exact (hdis a b h' _ (Or.inr rfl) (Or.inl hab)).elim
    · by_cases h' : e a = e b
      · rw [he_inj h']
      · exact (hdis a b h' _ (Or.inr rfl) (Or.inr hab)).elim
  obtain ⟨j, p, hp, hpW, hplen⟩ := h8 V (G.deleteEdges F) W ℓ t0 hℓ1 hℓn ht01 ht0n hW h4t0 hU
    (fun j => (P (e j)).1) (fun j => (P (e j)).2) (fun i => ⟨(hP (e i)).1, (hP (e i)).2.1⟩) hinj
  refine ⟨e j, hI'I (he_mem j), p, hp.mono Finset.sdiff_subset, hpW, ?_, ?_⟩
  · apply Nat.le_floor
    have e1 : ((G.deleteEdges F).card : ℝ) = (n : ℝ) := rfl
    rw [e1] at hplen
    exact hplen
  · intro x hx
    have := hp.1.edges_mem hx
    exact (Finset.mem_sdiff.1 this).2

/-- The Haxell step of the proof of Lemma 9_ρ: the hypergraph `ℋ` on `[r] ⊔ E(G)` with edges
`{i} ∪ E(P)`, `P ∈ 𝒴_i`, has a matching saturating `[r]`; its edges give pairwise edge-disjoint
`x_iy_i`-paths through `V` of length at most `h ≤ 4ℓ_*L ≤ 2^{12}L^4`. -/
theorem pathConnected (h8 : Spec.BMProp8Statement.{u}) (hMC : Spec.MultisetCountStatement.{u, 0})
    (hHax : Spec.HaxellStatement.{u})
    {V : Type u} [DecidableEq V] (G : FGraph V) (W : Finset V) (ρ t : ℝ)
    (hn : 2 ^ 30 ≤ G.card) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (hW : W ⊆ G.verts) (hWc : (G.card : ℝ) / (Star.M ρ : ℝ) + 2 ≤ W.card)
    (hball : ∀ U : Finset V, U.Nonempty → U ⊆ G.verts → ∀ F : Finset (Sym2 V), F ⊆ G.edges →
        (F.card : ℝ) ≤ Star.sbar G.card ρ t * (U.card : ℝ) →
        (W.card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell G.card) U W).card : ℝ)) :
    G.IsPathConnected ((2 : ℝ) ^ 12 * Real.logb 2 (G.card : ℝ) ^ 4) t W := by
  classical
  intro ι _ P hP hPt
  obtain ⟨hℓL, hℓ1, hℓn⟩ := ell_le_card hn
  have hn2 : 2 ≤ G.card := le_trans (by norm_num) hn
  have hL1 : 1 ≤ Star.L G.card := Star.one_le_L hn2
  set h := ⌊4 * (Star.ell G.card : ℝ) * Star.L G.card⌋₊ with hhdef
  have hℓ1' : (1 : ℝ) ≤ Star.ell G.card := by exact_mod_cast hℓ1
  have hh1 : 1 ≤ h := Nat.le_floor (by push_cast; nlinarith)
  have hhL : (h : ℝ) ≤ (2 : ℝ) ^ 12 * Real.logb 2 (G.card : ℝ) ^ 4 := by
    have := Nat.floor_le (show (0 : ℝ) ≤ 4 * (Star.ell G.card : ℝ) * Star.L G.card by positivity)
    rw [← hhdef] at this
    have hl := Star.ell_le G.card
    have hL0 : 0 ≤ Star.L G.card := by linarith
    rw [← Star.L_eq]
    nlinarith
  -- the hypergraph
  set X : Finset (ι ⊕ Sym2 V) := Finset.univ.map Function.Embedding.inl with hXdef
  set Y : Finset (ι ⊕ Sym2 V) := G.edges.map Function.Embedding.inr with hYdef
  set paths : ι → Finset (Finset (Sym2 V)) := fun i => G.edges.powerset.filter (fun Z =>
    ∃ p : List V, IsPathBetween G.edges (P i).1 (P i).2 p ∧ IsThrough W p ∧ pathLength p ≤ h ∧
      (walkEdges p).toFinset = Z) with hpaths
  set edge : ι → Finset (Sym2 V) → Finset (ι ⊕ Sym2 V) :=
    fun i Z => insert (Sum.inl i) (Z.map Function.Embedding.inr) with hedge
  set H : Finset (Finset (ι ⊕ Sym2 V)) :=
    Finset.univ.biUnion (fun i => (paths i).image (edge i)) with hHdef
  have mem_H : ∀ {e}, e ∈ H ↔ ∃ i, ∃ Z ∈ paths i, edge i Z = e := by
    intro e; simp [hHdef]
  have mem_edge_inl : ∀ {i j Z}, Sum.inl j ∈ edge i Z ↔ j = i := by
    intro i j Z; simp [hedge]
  have mem_edge_inr : ∀ {i Z x}, Sum.inr x ∈ edge i Z ↔ x ∈ Z := by
    intro i Z x; simp [hedge]
  have paths_sub : ∀ {i Z}, Z ∈ paths i → Z ⊆ G.edges := by
    intro i Z hZ; exact Finset.mem_powerset.1 (Finset.mem_filter.1 hZ).1
  have hmatch := hHax (ι ⊕ Sym2 V) X Y h H hh1
    (by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
      obtain ⟨x, -, hx⟩ := Finset.mem_map.1 hb
      cases hx)
    (by
      intro e he
      obtain ⟨i, Z, hZ, rfl⟩ := mem_H.1 he
      intro a ha
      rw [Finset.mem_union]
      rcases a with j | x
      · left; exact Finset.mem_map.2 ⟨j, Finset.mem_univ _, rfl⟩
      · right; exact Finset.mem_map.2 ⟨x, paths_sub hZ (mem_edge_inr.1 ha), rfl⟩)
    (by
      intro e he
      obtain ⟨i, Z, hZ, rfl⟩ := mem_H.1 he
      have : edge i Z ∩ X = {Sum.inl i} := by
        ext a
        rcases a with j | x
        · simp [hXdef, mem_edge_inl]
        · simp [hXdef]
      rw [this, Finset.card_singleton])
    (by
      intro e he
      obtain ⟨i, Z, hZ, rfl⟩ := mem_H.1 he
      have : edge i Z ∩ Y = Z.map Function.Embedding.inr := by
        ext a
        rcases a with j | x
        · simp [hYdef, hedge]
        · simp only [Finset.mem_inter, mem_edge_inr, hYdef, Finset.mem_map,
            Function.Embedding.inr_apply, Sum.inr.injEq, exists_eq_right]
          exact ⟨fun h => h.1, fun h => ⟨h, paths_sub hZ h⟩⟩
      rw [this, Finset.card_map]
      obtain ⟨p, -, -, hpl, rfl⟩ := (Finset.mem_filter.1 hZ).2
      exact (List.toFinset_card_le _).trans ((length_walkEdges p).le.trans hpl))
    (by
      intro X' hX' hne Z hZ hZc
      set I : Finset ι := Finset.univ.filter (fun i => Sum.inl i ∈ X') with hIdef
      have hIX : I.map Function.Embedding.inl = X' := by
        ext a
        constructor
        · intro ha
          obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 ha
          exact (Finset.mem_filter.1 hi).2
        · intro ha
          obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 (hX' ha)
          exact Finset.mem_map.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩, rfl⟩
      set F : Finset (Sym2 V) := G.edges.filter (fun x => Sum.inr x ∈ Z) with hFdef
      have hFZ : F.map Function.Embedding.inr = Z := by
        ext a
        constructor
        · intro ha
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
          exact (Finset.mem_filter.1 hx).2
        · intro ha
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 (hZ ha)
          exact Finset.mem_map.2 ⟨x, Finset.mem_filter.2 ⟨hx, ha⟩, rfl⟩
      have hIc : I.card = X'.card := by rw [← hIX, Finset.card_map]
      have hFc : F.card = Z.card := by rw [← hFZ, Finset.card_map]
      have hIne : I.Nonempty := by
        rw [← Finset.card_pos, hIc]; exact Finset.card_pos.2 hne
      obtain ⟨j, hj, p, hp, hpW, hpl, hpF⟩ := claim h8 hMC G W ρ t hn h0 h1 hW hWc hball P hP hPt
        I hIne F (Finset.filter_subset _ _) (by rw [hFc, hIc]; exact hZc)
      have hZp : (walkEdges p).toFinset ∈ paths j := by
        refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun x hx => ?_, p, hp, hpW, hpl, rfl⟩
        exact hp.1.edges_mem (List.mem_toFinset.1 hx)
      refine ⟨edge j (walkEdges p).toFinset, mem_H.2 ⟨j, _, hZp, rfl⟩, ?_, ?_⟩
      · intro a ha
        rw [Finset.mem_inter] at ha
        rcases a with i | x
        · have := mem_edge_inl.1 ha.1
          subst this
          exact (Finset.mem_filter.1 hj).2
        · obtain ⟨y, -, hy⟩ := Finset.mem_map.1 ha.2
          cases hy
      · rw [Finset.disjoint_left]
        intro a ha haZ
        rcases a with i | x
        · obtain ⟨y, -, hy⟩ := Finset.mem_map.1 (hZ haZ)
          cases hy
        · have hx := List.mem_toFinset.1 (mem_edge_inr.1 ha)
          apply hpF x hx
          rw [← hFZ] at haZ
          obtain ⟨y, hy, hyx⟩ := Finset.mem_map.1 haZ
          cases hyx
          exact hy)
  obtain ⟨Mt, hMH, hMdisj, hMcov⟩ := hmatch
  -- read off the paths
  have hex : ∀ i, ∃ Z ∈ paths i, edge i Z ∈ Mt := by
    intro i
    obtain ⟨e, heM, hie⟩ := hMcov (Sum.inl i) (Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩)
    obtain ⟨k, Z, hZ, rfl⟩ := mem_H.1 (hMH heM)
    have := mem_edge_inl.1 hie
    subst this
    exact ⟨Z, hZ, heM⟩
  choose Zf hZf hZfM using hex
  have hexp : ∀ i, ∃ p : List V, IsPathBetween G.edges (P i).1 (P i).2 p ∧ IsThrough W p ∧
      pathLength p ≤ h ∧ (walkEdges p).toFinset = Zf i := fun i => (Finset.mem_filter.1 (hZf i)).2
  choose Q hQ using hexp
  refine ⟨Q, fun i => ⟨(hQ i).1, (hQ i).2.1, ?_⟩, ?_⟩
  · have : (pathLength (Q i) : ℝ) ≤ h := by exact_mod_cast (hQ i).2.2.1
    linarith
  · intro i j hij x hxi hxj
    have hne : edge i (Zf i) ≠ edge j (Zf j) := by
      intro heq
      have : Sum.inl i ∈ edge j (Zf j) := by rw [← heq]; exact mem_edge_inl.2 rfl
      exact hij (mem_edge_inl.1 this)
    have hd := hMdisj (hZfM i) (hZfM j) hne
    rw [Function.onFun, id, id, Finset.disjoint_left] at hd
    apply hd (a := Sum.inr x)
    · rw [mem_edge_inr, ← (hQ i).2.2.2]; exact List.mem_toFinset.2 hxi
    · rw [mem_edge_inr, ← (hQ j).2.2.2]; exact List.mem_toFinset.2 hxj

end EG.L9rhoProof
