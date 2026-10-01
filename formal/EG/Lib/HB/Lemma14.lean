module

public import EG.Lib.HB.SEP
public import EG.Lib.HB.OVPotential
public import EG.Lib.Found.Constants

/-!
# Lemma 14^τ: counting at one split, the induction, termination (manuscript s2:lem14tau)

Unit P3A, proof round 1.

* `tau_count`: `Σ_{v ∈ H_out} deg_{F_0}(v) + Σ_{x ∈ H_in} deg_{F_1}(x) ≤ |F_0|` (for all
  `U`, `N`, `τ`), hence `τ (|H_out| + |H_in|) ≤ |F_0|`;
* `l14_split`: all inequalities of (a) at one split, at a node `K` with
  `128 s log² |K| ≤ τ` (`l14_split`);
* `STree.isTauRun_node_iff`: node decomposition of `IsTauRun`;
* `STree.l14_induction`: the induction of (a) (deletions `≤ 4 s m log m`, leaf size
  `≤ 2m - 2m/(2 + log m)`);
* `STree.tauBuild`: the recursion of a `τ`-run for a given witness rule, with fuel `|H_0|`
  (termination, (T2)).
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

/-! ### Logarithms of vertex counts -/

theorem logb_natCast_nonneg (n : ℕ) : 0 ≤ logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

theorem logb_natCast_mono {a b : ℕ} (h : a ≤ b) : logb 2 (a : ℝ) ≤ logb 2 (b : ℝ) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rw [ha, Nat.cast_zero, Real.logb_zero]
    exact logb_natCast_nonneg b
  · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast ha) (by exact_mod_cast h)

theorem logb_sq_natCast_mono {a b : ℕ} (h : a ≤ b) :
    logb 2 (a : ℝ) ^ 2 ≤ logb 2 (b : ℝ) ^ 2 :=
  pow_le_pow_left₀ (logb_natCast_nonneg a) (logb_natCast_mono h) 2

/-- `0.698 ≤ 2^{-2/5}`, i.e. `log₂ 0.698 ≤ -2/5`. -/
theorem le_two_rpow_neg_two_fifths : (0.698 : ℝ) ≤ (2 : ℝ) ^ (-(2 / 5 : ℝ)) := by
  rw [← pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (5 : ℕ) ≠ 0)]
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(2 / 5 : ℝ))) 5, ← Real.rpow_mul (by norm_num)]
  rw [show (-(2 / 5 : ℝ)) * ((5 : ℕ) : ℝ) = ((-2 : ℤ) : ℝ) by push_cast; ring,
    Real.rpow_intCast]
  norm_num

/-- `x ≤ 0.698 m` gives `log x ≤ log m - 2/5`. -/
theorem logb_le_sub_of_le {x m : ℝ} (hx : 0 < x) (hxm : x ≤ 0.698 * m) :
    logb 2 x ≤ logb 2 m - 2 / 5 := by
  have hm : 0 < m := by nlinarith
  have hle : x ≤ (2 : ℝ) ^ (-(2 / 5 : ℝ)) * m :=
    le_trans hxm (mul_le_mul_of_nonneg_right le_two_rpow_neg_two_fifths hm.le)
  calc logb 2 x ≤ logb 2 ((2 : ℝ) ^ (-(2 / 5 : ℝ)) * m) :=
        Real.logb_le_logb_of_le (by norm_num) hx hle
    _ = -(2 / 5) + logb 2 m := by
        rw [Real.logb_mul (by positivity) hm.ne', Real.logb_rpow (by norm_num) (by norm_num)]
    _ = logb 2 m - 2 / 5 := by ring

/-! ### Counting at one split -/

/-- Every edge of `F_0` has exactly one end in `U`; every edge of `F_1` exactly one end outside
`U' ∪ N'`; the edges of `F_0` at `H_out` avoid `F_1`. Hence
`Σ_{H_out} deg_{F_0} + Σ_{H_in} deg_{F_1} ≤ |F_0|`. -/
theorem tau_count (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    ∑ v ∈ tauHout H U N τ, degE (witF0 H U N) v + ∑ x ∈ tauHin H U N τ, degE (tauF1 H U N τ) x ≤
      (witF0 H U N).card := by
  set A := (tauHout H U N τ).biUnion (edgesAt (witF0 H U N))
  set B := (tauHin H U N τ).biUnion (edgesAt (tauF1 H U N τ))
  have hA : A.card = ∑ v ∈ tauHout H U N τ, degE (witF0 H U N) v := by
    apply Finset.card_biUnion
    intro v hv v' hv' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨heF, hve⟩ := FGraph.mem_edgesAt.1 he
    obtain ⟨-, hv'e⟩ := FGraph.mem_edgesAt.1 he'
    obtain ⟨-, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 heF
    have hbU : b ∉ U := fun h => (Finset.mem_sdiff.1 hb).2 (Finset.mem_union_left _ h)
    have hvU := tauHout_subset H U N τ hv
    have hv'U := tauHout_subset H U N τ hv'
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · rcases Sym2.mem_iff.1 hv'e with rfl | rfl
      · exact hne rfl
      · exact hbU hv'U
    · exact hbU hvU
  have hB : B.card = ∑ x ∈ tauHin H U N τ, degE (tauF1 H U N τ) x := by
    apply Finset.card_biUnion
    intro v hv v' hv' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨heF, hve⟩ := FGraph.mem_edgesAt.1 he
    obtain ⟨-, hv'e⟩ := FGraph.mem_edgesAt.1 he'
    obtain ⟨-, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 heF
    have hvo := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hv).1).2
    have hv'o := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hv').1).2
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · exact hvo (Finset.mem_union_left _ ha)
    · rcases Sym2.mem_iff.1 hv'e with rfl | rfl
      · exact hv'o (Finset.mem_union_left _ ha)
      · exact hne rfl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    obtain ⟨v, hv, hev⟩ := Finset.mem_biUnion.1 heA
    obtain ⟨x, -, hex⟩ := Finset.mem_biUnion.1 heB
    obtain ⟨heF1, -⟩ := FGraph.mem_edgesAt.1 hex
    obtain ⟨-, hve⟩ := FGraph.mem_edgesAt.1 hev
    have heF1' := heF1
    unfold tauF1 at heF1'
    rw [tauU1_union_tauN1] at heF1'
    obtain ⟨-, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 heF1'
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · exact (Finset.mem_sdiff.1 ha).2 hv
    · exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_union_left _ (tauHout_subset H U N τ hv))
  have hsub : A ∪ B ⊆ witF0 H U N := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨v, -, hev⟩ := Finset.mem_biUnion.1 he
      exact (FGraph.mem_edgesAt.1 hev).1
    · obtain ⟨x, -, hex⟩ := Finset.mem_biUnion.1 he
      exact tauF1_subset_witF0 H U N τ (FGraph.mem_edgesAt.1 hex).1
  rw [← hA, ← hB, ← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub

/-- `τ (|H_out| + |H_in|) ≤ |F_0|`. -/
theorem tau_mul_card_le (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    τ * ((tauHout H U N τ).card + (tauHin H U N τ).card : ℝ) ≤ (witF0 H U N).card := by
  have h1 : ((tauHout H U N τ).card : ℝ) * τ ≤
      ∑ v ∈ tauHout H U N τ, (degE (witF0 H U N) v : ℝ) := by
    have := Finset.card_nsmul_le_sum (tauHout H U N τ) (fun v => (degE (witF0 H U N) v : ℝ)) τ
      (fun v hv => (Finset.mem_filter.1 hv).2)
    simpa [nsmul_eq_mul] using this
  have h2 : ((tauHin H U N τ).card : ℝ) * τ ≤
      ∑ x ∈ tauHin H U N τ, (degE (tauF1 H U N τ) x : ℝ) := by
    have := Finset.card_nsmul_le_sum (tauHin H U N τ) (fun x => (degE (tauF1 H U N τ) x : ℝ)) τ
      (fun x hx => (Finset.mem_filter.1 hx).2)
    simpa [nsmul_eq_mul] using this
  have h3 : ((∑ v ∈ tauHout H U N τ, degE (witF0 H U N) v +
      ∑ x ∈ tauHin H U N τ, degE (tauF1 H U N τ) x : ℕ) : ℝ) ≤ (witF0 H U N).card := by
    exact_mod_cast tau_count H U N τ
  push_cast at h3
  linarith

/-! ### All inequalities of (a) at one split -/

section Split

variable {K : FGraph V} {s : ℕ} {τ : ℝ} {U : Finset V} {F : Finset (Sym2 V)}

/-- The facts of Lemma 14^τ (a) at one split: a node `K` with a witness `(U,F)` (parameter
`s ≥ 1`) and `128 s log²|K| ≤ τ`. -/
theorem l14_split (hw : IsWitness K epsC s U F) (hs : 1 ≤ s)
    (hτ : 128 * (s : ℝ) * logb 2 K.card ^ 2 ≤ τ) :
    (((tauHout K U (witN K U F) τ).card + (tauHin K U (witN K U F) τ).card : ℕ) : ℝ) ≤
        (witF0 K U (witN K U F)).card / τ ∧
      ((witF0 K U (witN K U F)).card : ℝ) / τ ≤ s * U.card / τ ∧
      (s : ℝ) * U.card / τ ≤ U.card / (128 * logb 2 K.card ^ 2) ∧
      ((tauN2 K U (witN K U F) τ).card : ℝ) < 1.25 * epsC * U.card / logb 2 K.card ^ 2 ∧
      1.25 * epsC * U.card / logb 2 K.card ^ 2 < 1.5 * epsC * U.card / logb 2 K.card ^ 2 ∧
      (127 / 128 : ℝ) * U.card ≤ (tauU1 K U (witN K U F) τ).card ∧
      0 < (tauU1 K U (witN K U F) τ).card ∧
      U ⊆ tauU1 K U (witN K U F) τ ∪ tauN2 K U (witN K U F) τ ∧
      ((tauU1 K U (witN K U F) τ ∪ tauN2 K U (witN K U F) τ).card : ℝ) ≤ 0.698 * K.card ∧
      0.698 * (K.card : ℝ) < 3 / 4 * K.card ∧
      K.card - (tauU1 K U (witN K U F) τ).card < K.card := by
  set N := witN K U F with hN
  have h2 := two_le_card_of_isWitness hw
  have hL : 1 ≤ logb 2 (K.card : ℝ) := one_le_logb_of_two_le (by exact_mod_cast h2)
  have hL2 : 1 ≤ logb 2 (K.card : ℝ) ^ 2 := by nlinarith
  set L2 := logb 2 (K.card : ℝ) ^ 2 with hL2def
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hτpos : 0 < τ := by nlinarith
  have hε := epsC_eq
  obtain ⟨hUK, hFK, h1, h23, hFs, hNb⟩ := hw
  have hU1 : (1 : ℝ) ≤ U.card := by exact_mod_cast h1
  have hF0F : ((witF0 K U N).card : ℝ) ≤ F.card := by
    exact_mod_cast Finset.card_le_card (witF0_witN_subset K U F)
  have hcnt := tau_mul_card_le K U N τ
  set hout := (tauHout K U N τ).card
  set hin := (tauHin K U N τ).card
  -- (1)–(3)
  have e1 : ((hout + hin : ℕ) : ℝ) ≤ (witF0 K U N).card / τ := by
    rw [le_div_iff₀ hτpos]
    push_cast
    linarith
  have e2 : ((witF0 K U N).card : ℝ) / τ ≤ s * U.card / τ :=
    div_le_div_of_nonneg_right (by linarith) hτpos.le
  have e3 : (s : ℝ) * U.card / τ ≤ U.card / (128 * L2) := by
    rw [div_le_div_iff₀ hτpos (by positivity)]
    have : (s : ℝ) * U.card * (128 * L2) = U.card * (128 * s * L2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hτ (by positivity)
  have hhh : ((hout + hin : ℕ) : ℝ) ≤ U.card / (128 * L2) := e1.trans (e2.trans e3)
  push_cast at hhh
  have hN'' : ((tauN2 K U N τ).card : ℝ) ≤ N.card + hout + hin := by
    have : (tauN2 K U N τ).card ≤ N.card + hout + hin := by
      unfold tauN2 tauN1
      exact le_trans (Finset.card_union_le _ _) (by
        have := Finset.card_union_le N (tauHout K U N τ)
        omega)
    exact_mod_cast this
  have hNb' : (N.card : ℝ) < epsC * U.card / L2 := hNb
  have e4 : ((tauN2 K U N τ).card : ℝ) < 1.25 * epsC * U.card / L2 := by
    have : (U.card : ℝ) / (128 * L2) = epsC * U.card / L2 / 4 := by
      rw [hε]; field_simp; ring
    have e : 1.25 * epsC * U.card / L2 = epsC * U.card / L2 + epsC * U.card / L2 / 4 := by ring
    rw [e]
    linarith
  have e5 : 1.25 * epsC * U.card / L2 < 1.5 * epsC * U.card / L2 := by
    apply div_lt_div_of_pos_right _ (by positivity)
    have := epsC_pos
    nlinarith
  -- `|U'| = |U| - |H_out|`
  have hU' : ((tauU1 K U N τ).card : ℝ) = U.card - hout := by
    have := Finset.card_sdiff_add_card_eq_card (tauHout_subset K U N τ)
    unfold tauU1
    have h' : (U \ tauHout K U N τ).card = U.card - hout := by omega
    rw [h', Nat.cast_sub (Finset.card_le_card (tauHout_subset K U N τ))]
  have hout_le : (hout : ℝ) ≤ U.card / 128 := by
    have hin0 : (0 : ℝ) ≤ hin := Nat.cast_nonneg _
    have : (U.card : ℝ) / (128 * L2) ≤ U.card / 128 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      nlinarith
    linarith
  have e6 : (127 / 128 : ℝ) * U.card ≤ (tauU1 K U N τ).card := by rw [hU']; linarith
  have e7 : 0 < (tauU1 K U N τ).card := by
    have : (0 : ℝ) < (tauU1 K U N τ).card := by linarith
    exact_mod_cast this
  have e8 := subset_tauU1_union_tauN2 K U N τ
  have e9 : ((tauU1 K U N τ ∪ tauN2 K U N τ).card : ℝ) ≤ 0.698 * K.card := by
    have hc : ((tauU1 K U N τ ∪ tauN2 K U N τ).card : ℝ) ≤
        (tauU1 K U N τ).card + (tauN2 K U N τ).card := by
      exact_mod_cast Finset.card_union_le _ _
    have hUU : ((tauU1 K U N τ).card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card (tauU1_subset K U N τ)
    have h4 : 1.25 * epsC * U.card / L2 ≤ 1.25 * epsC * U.card := by
      apply div_le_self (by have := epsC_pos; positivity) hL2
    have e4' := e4
    rw [hε] at h4 e4'
    linarith
  have e10 : 0.698 * (K.card : ℝ) < 3 / 4 * K.card := by
    have : (2 : ℝ) ≤ K.card := by exact_mod_cast h2
    linarith
  refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ?_⟩
  omega

/-- The children of a `τ`-rule split: `n_1 = |U' ∪ N''|`, `1 ≤ n_1 ≤ 0.698 m`,
`n_2 = m - |U'|`, `1 ≤ n_2 < m`, `|U| ≤ n_1`, `n_1 + n_2 = m + |N''|`. -/
theorem l14_children (hw : IsWitness K epsC s U F) (hs : 1 ≤ s)
    (hτ : 128 * (s : ℝ) * logb 2 K.card ^ 2 ≤ τ) :
    1 ≤ (splitFst K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card ∧
      ((splitFst K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card : ℝ) ≤
        0.698 * K.card ∧
      (splitFst K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card < K.card ∧
      1 ≤ (splitSnd K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card ∧
      (splitSnd K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card < K.card ∧
      U.card ≤ (splitFst K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card ∧
      (splitFst K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card +
          (splitSnd K (tauU1 K U (witN K U F) τ) (tauN2 K U (witN K U F) τ)).card =
        K.card + (tauN2 K U (witN K U F) τ).card := by
  obtain ⟨-, -, -, -, -, -, e7, e8, e9, e10, e11⟩ := l14_split hw hs hτ
  obtain ⟨hU, hN, hd⟩ := tau_split_wf (τ := τ) hw
  have h2 := two_le_card_of_isWitness hw
  rw [card_splitFst hU hN, card_splitSnd hU]
  have hUU : (tauU1 K U (witN K U F) τ).card ≤ (tauU1 K U (witN K U F) τ ∪
      tauN2 K U (witN K U F) τ).card := Finset.card_le_card Finset.subset_union_left
  have hUc : U.card ≤ (tauU1 K U (witN K U F) τ ∪ tauN2 K U (witN K U F) τ).card :=
    Finset.card_le_card e8
  have hUK : U.card ≤ K.card := Finset.card_le_card hw.1
  have hU23 : (U.card : ℝ) ≤ 2 * K.card / 3 := hw.2.2.2.1
  have hU'U : (tauU1 K U (witN K U F) τ).card ≤ U.card :=
    Finset.card_le_card (tauU1_subset K U _ τ)
  have hlt : (tauU1 K U (witN K U F) τ ∪ tauN2 K U (witN K U F) τ).card < K.card := by
    have : ((tauU1 K U (witN K U F) τ ∪ tauN2 K U (witN K U F) τ).card : ℝ) < K.card := by
      have : (0 : ℝ) < K.card := by exact_mod_cast (by omega : 0 < K.card)
      linarith
    exact_mod_cast this
  have hsnd : 1 ≤ K.card - (tauU1 K U (witN K U F) τ).card := by
    have : (U.card : ℝ) < K.card := by
      have : (2 : ℝ) ≤ K.card := by exact_mod_cast h2
      linarith
    have : U.card < K.card := by exact_mod_cast this
    omega
  have hsum := card_splitFst_add_card_splitSnd hU hN hd
  rw [card_splitFst hU hN, card_splitSnd hU] at hsum
  exact ⟨by omega, e9, hlt, hsnd, by omega, hUc, hsum⟩

end Split

/-! ### `τ`-runs: node decomposition -/

namespace STree

theorem isTauRun_node_iff {ε : ℝ} {s : ℕ} {τ : ℝ} (p : Finset V × Finset V) (l r : STree V)
    (K : FGraph V) :
    (STree.node p l r).IsTauRun ε s τ K ↔
      (p.1 ⊆ K.verts ∧ p.2 ⊆ K.verts ∧ Disjoint p.1 p.2) ∧ ¬ K.IsExpander ε s ∧
        (∃ (U : Finset V) (F : Finset (Sym2 V)), IsWitness K ε s U F ∧
          p = (tauU1 K U (witN K U F) τ, tauN2 K U (witN K U F) τ)) ∧
        l.IsTauRun ε s τ (splitFst K p.1 p.2) ∧ r.IsTauRun ε s τ (splitSnd K p.1 p.2) := by
  constructor
  · rintro ⟨hwf, hstop, hlab⟩
    obtain ⟨h0, hl, hr⟩ := (wf_node_iff p l r K).1 hwf
    refine ⟨h0, ?_, ?_, ⟨hl, ?_, ?_⟩, ⟨hr, ?_, ?_⟩⟩
    · have := (hstop [] (nil_mem_nodeAddrs _)).not.1 (by simp)
      simpa using this
    · obtain ⟨U, F, hw, h⟩ := hlab [] (by simp [internalAddrs_node])
      exact ⟨U, F, by simpa using hw, by simpa using h⟩
    · intro a ha
      simpa using hstop (false :: a) (by simpa using ha)
    · intro a ha
      obtain ⟨U, F, hw, h⟩ := hlab (false :: a) (by simpa using ha)
      exact ⟨U, F, by simpa using hw, by simpa using h⟩
    · intro a ha
      simpa using hstop (true :: a) (by simpa using ha)
    · intro a ha
      obtain ⟨U, F, hw, h⟩ := hlab (true :: a) (by simpa using ha)
      exact ⟨U, F, by simpa using hw, by simpa using h⟩
  · rintro ⟨h0, hexp, ⟨U, F, hw, hp⟩, hl, hr⟩
    refine ⟨(wf_node_iff p l r K).2 ⟨h0, hl.1, hr.1⟩, fun a ha => ?_, fun a ha => ?_⟩
    · cases a with
      | nil => simpa using hexp
      | cons c a =>
        rw [mem_nodeAddrs_node_cons] at ha
        cases c
        · simpa using hl.2.1 a ha
        · simpa using hr.2.1 a ha
    · cases a with
      | nil => exact ⟨U, F, by simpa using hw, by simpa using hp⟩
      | cons c a =>
        rw [mem_internalAddrs_node_cons] at ha
        cases c
        · obtain ⟨U', F', hw', h'⟩ := hl.2.2 a ha
          exact ⟨U', F', by simpa using hw', by simpa using h'⟩
        · obtain ⟨U', F', hw', h'⟩ := hr.2.2 a ha
          exact ⟨U', F', by simpa using hw', by simpa using h'⟩

end STree

end EG.HB
