module

public import EG.Lib.HB.Lemma14

/-!
# Lemma 14^τ: the induction and the construction of `τ`-runs (manuscript s2:lem14tau)

Unit P3A, proof round 1.

* `del_step`, `mass_step`: the real inequalities of one induction step ([BM, (8), (9)]);
* `STree.l14_induction`: a `τ`-run on `K` with `128 s log² |K| ≤ τ` deletes at most
  `4 s m log m` edges and has total leaf size at most `2m - 2m/(2 + log m)`, `m = |K|`;
* `STree.tauBuild`, `STree.tauBuild_spec`: the recursion of a `τ`-run that uses a given witness
  rule (fuel `n ≥ |K|`), for (T2) of "the recursion terminates".
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

/-! ### The numeric steps -/

/-- One step of the deletion bound ([BM, inequality (8)]). -/
theorem del_step {s m n1 n2 N L L1 L2 Fd D1 D2 : ℝ} (hs : 0 ≤ s) (hL : 1 ≤ L)
    (hL1 : L1 ≤ L - 2 / 5) (hL2 : L2 ≤ L) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hsum : n1 + n2 = m + N) (hN : 0 ≤ N) (hNb : N * L ^ 2 ≤ 1.5 * (1 / 32) * n1)
    (hF : Fd ≤ s * n1) (hD1 : D1 ≤ 4 * s * n1 * L1) (hD2 : D2 ≤ 4 * s * n2 * L2) :
    Fd + D1 + D2 ≤ 4 * s * m * L := by
  have a1 : 4 * s * n1 * L1 ≤ 4 * s * n1 * (L - 2 / 5) :=
    mul_le_mul_of_nonneg_left hL1 (by positivity)
  have a2 : 4 * s * n2 * L2 ≤ 4 * s * n2 * L := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have a3 : N * L ≤ 1.5 * (1 / 32) * n1 := by
    have : N * L ≤ N * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hN
    linarith
  have a4 : s * (4 * (N * L) - 0.6 * n1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs (by linarith)
  have e : s * n1 + 4 * s * n1 * (L - 2 / 5) + 4 * s * n2 * L =
      4 * s * m * L + s * (4 * (N * L) - 0.6 * n1) := by
    have : n2 = m + N - n1 := by linarith
    rw [this]
    ring
  linarith

/-- One step of the leaf-size bound ([BM, inequality (9)]). -/
theorem mass_step {m n1 n2 N L L1 L2 S1 S2 : ℝ} (hL : 1 ≤ L) (hL1 : 0 ≤ L1)
    (hL1' : L1 ≤ L - 2 / 5) (hL2 : 0 ≤ L2) (hL2' : L2 ≤ L) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hsum : n1 + n2 = m + N) (hN : 0 ≤ N) (hNb : N * L ^ 2 ≤ 1.5 * (1 / 32) * n1)
    (hS1 : S1 ≤ 2 * n1 - 2 * n1 / (2 + L1)) (hS2 : S2 ≤ 2 * n2 - 2 * n2 / (2 + L2)) :
    S1 + S2 ≤ 2 * m - 2 * m / (2 + L) := by
  have b2 : 2 * n2 / (2 + L) ≤ 2 * n2 / (2 + L2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have b1 : 2 * n1 / (8 / 5 + L) ≤ 2 * n1 / (2 + L1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hL2pos : 0 < L ^ 2 := by positivity
  have b3 : 2 * n1 / (2 + L) + n1 / (10 * L ^ 2) ≤ 2 * n1 / (8 / 5 + L) := by
    have hc : 1 / (10 * L ^ 2) ≤ 2 / (8 / 5 + L) - 2 / (2 + L) := by
      have e : 2 / (8 / 5 + L) - 2 / (2 + L) = (4 / 5) / ((8 / 5 + L) * (2 + L)) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_left hc hn1
    have e1 : n1 * (2 / (8 / 5 + L) - 2 / (2 + L)) = 2 * n1 / (8 / 5 + L) - 2 * n1 / (2 + L) := by
      ring
    have e2 : n1 * (1 / (10 * L ^ 2)) = n1 / (10 * L ^ 2) := by ring
    linarith
  have b5 : 2 * N ≤ n1 / (10 * L ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have f1 : 2 * n1 / (2 + L) + 2 * n2 / (2 + L) = 2 * m / (2 + L) + 2 * N / (2 + L) := by
    rw [← add_div, ← add_div]
    congr 1
    linarith
  have f2 : 0 ≤ 2 * N / (2 + L) := by positivity
  linarith

namespace STree

/-- [s2:lem14tau] (a), the induction: a `τ`-run on `K` with `128 s log²|K| ≤ τ` deletes at most
`4 s m log m` edges, and its leaves have total size at most `2m - 2m/(2 + log m)`. -/
theorem l14_induction {s : ℕ} {τ : ℝ} (hs : 1 ≤ s) (t : STree V) {K : FGraph V}
    (ht : t.IsTauRun epsC s τ K) (hτ : 128 * (s : ℝ) * logb 2 K.card ^ 2 ≤ τ) :
    ((t.deleted K).card : ℝ) ≤ 4 * s * K.card * logb 2 K.card ∧
      (t.leafMass K : ℝ) ≤ 2 * K.card - 2 * K.card / (2 + logb 2 K.card) := by
  induction t generalizing K with
  | nil =>
    have hL := logb_natCast_nonneg K.card
    refine ⟨by simp; positivity, ?_⟩
    simp only [leafMass_nil]
    have hm : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
    have : 2 * (K.card : ℝ) / (2 + logb 2 K.card) ≤ K.card := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  | node p l r ihl ihr =>
    obtain ⟨h0, -, ⟨U, F, hw, hp⟩, hl, hr⟩ := (isTauRun_node_iff p l r K).1 ht
    subst hp
    simp only at hl hr ⊢
    set N := witN K U F
    set U' := tauU1 K U N τ
    set N'' := tauN2 K U N τ
    obtain ⟨hn1, hn1le, hn1lt, hn2, hn2lt, hUn1, hsum⟩ := l14_children hw hs hτ
    obtain ⟨-, -, -, e4, -, -, -, -, -, -, -⟩ := l14_split hw hs hτ
    have hFst : 128 * (s : ℝ) * logb 2 (splitFst K U' N'').card ^ 2 ≤ τ :=
      le_trans (mul_le_mul_of_nonneg_left (logb_sq_natCast_mono hn1lt.le) (by positivity)) hτ
    have hSnd : 128 * (s : ℝ) * logb 2 (splitSnd K U' N'').card ^ 2 ≤ τ :=
      le_trans (mul_le_mul_of_nonneg_left (logb_sq_natCast_mono hn2lt.le) (by positivity)) hτ
    obtain ⟨dl, ml⟩ := ihl hl hFst
    obtain ⟨dr, mr⟩ := ihr hr hSnd
    have h2 := two_le_card_of_isWitness hw
    have hL : 1 ≤ logb 2 (K.card : ℝ) := one_le_logb_of_two_le (by exact_mod_cast h2)
    have hn1pos : (0 : ℝ) < (splitFst K U' N'').card := by exact_mod_cast hn1
    have hL1 : logb 2 ((splitFst K U' N'').card : ℝ) ≤ logb 2 (K.card : ℝ) - 2 / 5 :=
      logb_le_sub_of_le hn1pos hn1le
    have hL2 : logb 2 ((splitSnd K U' N'').card : ℝ) ≤ logb 2 (K.card : ℝ) :=
      logb_natCast_mono hn2lt.le
    have hsumR : ((splitFst K U' N'').card : ℝ) + (splitSnd K U' N'').card =
        K.card + N''.card := by exact_mod_cast hsum
    have hNb : (N''.card : ℝ) * logb 2 (K.card : ℝ) ^ 2 ≤
        1.5 * (1 / 32) * (splitFst K U' N'').card := by
      have hLp : 0 < logb 2 (K.card : ℝ) ^ 2 := by positivity
      have := (lt_div_iff₀ hLp).1 e4
      rw [epsC_eq] at this
      have hU : (U.card : ℝ) ≤ (splitFst K U' N'').card := by exact_mod_cast hUn1
      linarith
    constructor
    · -- deletions
      rw [deleted_node]
      have hc : ((splitDel K U' N'' ∪ (l.deleted (splitFst K U' N'') ∪
          r.deleted (splitSnd K U' N''))).card : ℝ) ≤ (splitDel K U' N'').card +
            (l.deleted (splitFst K U' N'')).card + (r.deleted (splitSnd K U' N'')).card := by
        have := Finset.card_union_le (splitDel K U' N'')
          (l.deleted (splitFst K U' N'') ∪ r.deleted (splitSnd K U' N''))
        have := Finset.card_union_le (l.deleted (splitFst K U' N''))
          (r.deleted (splitSnd K U' N''))
        exact_mod_cast (by omega)
      have hF : ((splitDel K U' N'').card : ℝ) ≤ s * (splitFst K U' N'').card := by
        have h1 : (splitDel K U' N'').card ≤ F.card :=
          Finset.card_le_card ((tauF2_subset_witF0 K U N τ).trans (witF0_witN_subset K U F))
        have h1' : ((splitDel K U' N'').card : ℝ) ≤ F.card := by exact_mod_cast h1
        have h2 : (F.card : ℝ) ≤ s * U.card := hw.2.2.2.2.1
        have hU : (U.card : ℝ) ≤ (splitFst K U' N'').card := by exact_mod_cast hUn1
        nlinarith
      exact le_trans hc (del_step (Nat.cast_nonneg s) hL hL1 hL2 (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hsumR (Nat.cast_nonneg _) hNb hF dl dr)
    · rw [leafMass_node]
      push_cast
      exact mass_step hL (logb_natCast_nonneg _) hL1 (logb_natCast_nonneg _) hL2
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsumR (Nat.cast_nonneg _) hNb ml mr

/-! ### Construction of a `τ`-run for a given witness rule -/

/-- The `τ`-run that uses the witness rule `W`, with fuel `n` (enough fuel: `n ≥ |K|`, since
both children of a split are smaller). -/
noncomputable def tauBuild (ε : ℝ) (s : ℕ) (τ : ℝ) (W : Addr → FGraph V → Finset V × Finset (Sym2 V)) :
    ℕ → Addr → FGraph V → STree V
  | 0, _, _ => .nil
  | n + 1, a, K =>
    haveI := Classical.dec (K.IsExpander ε s)
    if K.IsExpander ε s then .nil else
      .node (tauU1 K (W a K).1 (witN K (W a K).1 (W a K).2) τ,
          tauN2 K (W a K).1 (witN K (W a K).1 (W a K).2) τ)
        (tauBuild ε s τ W n (a ++ [false])
          (splitFst K (tauU1 K (W a K).1 (witN K (W a K).1 (W a K).2) τ)
            (tauN2 K (W a K).1 (witN K (W a K).1 (W a K).2) τ)))
        (tauBuild ε s τ W n (a ++ [true])
          (splitSnd K (tauU1 K (W a K).1 (witN K (W a K).1 (W a K).2) τ)
            (tauN2 K (W a K).1 (witN K (W a K).1 (W a K).2) τ)))

/-- A graph without vertices is an `(ε,s)`-expander (no witness). -/
theorem isExpander_of_card_eq_zero {K : FGraph V} (hK : K.card = 0) (ε s : ℝ) :
    K.IsExpander ε s := by
  by_contra h
  obtain ⟨U, F, hw⟩ := (not_isExpander_iff_exists_isWitness K ε s).1 h
  have := two_le_card_of_isWitness hw
  omega

/-- [s2:lem14tau] "The recursion terminates", (T2): the recursion that uses the witness rule
`W` is a `τ`-run whose labels are the `τ`-rule sets of `W`'s witnesses. -/
theorem tauBuild_spec {s : ℕ} {τ : ℝ} (hs : 1 ≤ s)
    (W : Addr → FGraph V → Finset V × Finset (Sym2 V))
    (hW : ∀ (a : Addr) (K : FGraph V), ¬ K.IsExpander epsC s →
      IsWitness K epsC s (W a K).1 (W a K).2) :
    ∀ (n : ℕ) (a : Addr) (K : FGraph V), K.card ≤ n →
      128 * (s : ℝ) * logb 2 K.card ^ 2 ≤ τ →
      (tauBuild epsC s τ W n a K).IsTauRun epsC s τ K ∧
        ∀ b ∈ (tauBuild epsC s τ W n a K).internalAddrs,
          (tauBuild epsC s τ W n a K).labelAt b = some
            (tauU1 ((tauBuild epsC s τ W n a K).graphAtD K b)
                (W (a ++ b) ((tauBuild epsC s τ W n a K).graphAtD K b)).1
                (witN ((tauBuild epsC s τ W n a K).graphAtD K b)
                  (W (a ++ b) ((tauBuild epsC s τ W n a K).graphAtD K b)).1
                  (W (a ++ b) ((tauBuild epsC s τ W n a K).graphAtD K b)).2) τ,
              tauN2 ((tauBuild epsC s τ W n a K).graphAtD K b)
                (W (a ++ b) ((tauBuild epsC s τ W n a K).graphAtD K b)).1
                (witN ((tauBuild epsC s τ W n a K).graphAtD K b)
                  (W (a ++ b) ((tauBuild epsC s τ W n a K).graphAtD K b)).1
                  (W (a ++ b) ((tauBuild epsC s τ W n a K).graphAtD K b)).2) τ) := by
  intro n
  induction n with
  | zero =>
    intro a K hK _
    have hK0 : K.card = 0 := by omega
    refine ⟨(isTauRun_nil_iff _ _ _ _).2 (isExpander_of_card_eq_zero hK0 _ _), ?_⟩
    intro b hb
    simp [tauBuild] at hb
  | succ n ih =>
    intro a K hK hτ
    by_cases hexp : K.IsExpander epsC s
    · have e : tauBuild epsC s τ W (n + 1) a K = .nil := by
        simp only [tauBuild]
        rw [if_pos hexp]
      rw [e]
      refine ⟨(isTauRun_nil_iff _ _ _ _).2 hexp, ?_⟩
      intro b hb
      simp at hb
    · set U := (W a K).1
      set F := (W a K).2
      have hw : IsWitness K epsC s U F := hW a K hexp
      set U' := tauU1 K U (witN K U F) τ
      set N'' := tauN2 K U (witN K U F) τ
      have e : tauBuild epsC s τ W (n + 1) a K =
          .node (U', N'') (tauBuild epsC s τ W n (a ++ [false]) (splitFst K U' N''))
            (tauBuild epsC s τ W n (a ++ [true]) (splitSnd K U' N'')) := by
        simp only [tauBuild]
        rw [if_neg hexp]
      rw [e]
      obtain ⟨-, -, hn1lt, -, hn2lt, -, -⟩ := l14_children hw hs hτ
      have hn1lt' : (splitFst K U' N'').card < K.card := hn1lt
      have hn2lt' : (splitSnd K U' N'').card < K.card := hn2lt
      have hFst : 128 * (s : ℝ) * logb 2 (splitFst K U' N'').card ^ 2 ≤ τ :=
        le_trans (mul_le_mul_of_nonneg_left (logb_sq_natCast_mono hn1lt.le) (by positivity)) hτ
      have hSnd : 128 * (s : ℝ) * logb 2 (splitSnd K U' N'').card ^ 2 ≤ τ :=
        le_trans (mul_le_mul_of_nonneg_left (logb_sq_natCast_mono hn2lt.le) (by positivity)) hτ
      obtain ⟨hl, hll⟩ := ih (a ++ [false]) (splitFst K U' N'') (by omega) hFst
      obtain ⟨hr, hrl⟩ := ih (a ++ [true]) (splitSnd K U' N'') (by omega) hSnd
      refine ⟨(isTauRun_node_iff _ _ _ K).2 ⟨tau_split_wf hw, hexp, ⟨U, F, hw, rfl⟩, hl, hr⟩, ?_⟩
      intro b hb
      cases b with
      | nil => simp [U', N'', U, F]
      | cons c b =>
        rw [mem_internalAddrs_node_cons] at hb
        cases c
        · have := hll b hb
          simp only [labelAt_node_false, graphAtD_node_false]
          rw [this]
          simp
        · have := hrl b hb
          simp only [labelAt_node_true, graphAtD_node_true]
          rw [this]
          simp

end STree

end EG.HB
