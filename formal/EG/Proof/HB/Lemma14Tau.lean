module

public import EG.Spec.HB.Lemma14Tau
public import EG.Lib.HB.Lemma14Ind
public import EG.Proof.HB.ThinCut

/-!
# Proof of Lemma 14^τ (manuscript s2:lem14tau)

Unit P3A, proof round 1. Design note `formal/work/p2b/P3A.md`. The generic arguments are in
`EG.Lib.HB.Lemma14` (counting at one split), `EG.Lib.HB.Lemma14Ind` (the induction, the
construction of `τ`-runs), `EG.Lib.HB.OVPotential` (Lemma OV) and `EG.Lib.HB.SEP` (thin cut).

* `EG.l14Split : EG.Spec.L14SplitStatement` ((a), one split);
* `EG.l14Term : EG.Spec.L14TermStatement` ((a), termination (T1), (T2));
* `EG.l14Global : EG.Spec.L14GlobalStatement` ((a), global part);
* `EG.l14OV : EG.Spec.L14OVStatement` ((b));
* `EG.l14Thin : EG.Spec.L14ThinStatement` ((c) with the T1 repair `0 < τ`, (d)).
-/

public section

namespace EG

open EG.HB EG.HB.STree

namespace HB

variable {V : Type*} [DecidableEq V]

/-- At a node of a `τ`-run on `H` with `128 s log² |H| ≤ τ`, the local threshold condition
`128 s log² |H_a| ≤ τ` holds. -/
theorem tau_local {s : ℕ} {τ : ℝ} {t : STree V} {H : FGraph V}
    (hτ : 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ) (a : Addr) :
    128 * (s : ℝ) * Real.logb 2 (t.graphAtD H a).card ^ 2 ≤ τ :=
  le_trans (mul_le_mul_of_nonneg_left
    (logb_sq_natCast_mono (Finset.card_le_card (graphAtD_verts_subset t H a)))
    (by positivity)) hτ

/-- [s2:lem14tau] (b) at one node: `|N''| ≤ 1.6 ε |U'|/log² m`, `U'` goes only to `G_1`,
`|G_1| ≤ (3/4) m`, `m ≥ 2`. -/
theorem l14_node {s : ℕ} {τ : ℝ} {t : STree V} {H : FGraph V} (hs : 1 ≤ s)
    (hτ : 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ) (ht : t.IsTauRun epsC s τ H)
    {a : Addr} (ha : a ∈ t.internalAddrs) :
    ((t.labelN a).card : ℝ) ≤
        1.6 * epsC * (t.labelU a).card / Real.logb 2 (t.graphAtD H a).card ^ 2 ∧
      (∀ v ∈ t.labelU a, v ∈ (t.graphAtD H (a ++ [false])).verts ∧
        v ∉ (t.graphAtD H (a ++ [true])).verts) ∧
      ((t.graphAtD H (a ++ [false])).card : ℝ) ≤ 3 / 4 * (t.graphAtD H a).card ∧
      2 ≤ (t.graphAtD H a).card := by
  obtain ⟨U, F, hw, hlab⟩ := ht.2.2 a ha
  set K := t.graphAtD H a with hK
  have hτK : 128 * (s : ℝ) * Real.logb 2 K.card ^ 2 ≤ τ := tau_local hτ a
  obtain ⟨-, -, -, e4, -, e6, -, -, e9, e10, -⟩ := l14_split hw hs hτK
  have hU : t.labelU a = tauU1 K U (witN K U F) τ := labelU_of_labelAt hlab
  have hN : t.labelN a = tauN2 K U (witN K U F) τ := labelN_of_labelAt hlab
  obtain ⟨hUK, hNK, -⟩ := ht.1 a ha
  have h2 := two_le_card_of_isWitness hw
  have hL : 1 ≤ Real.logb 2 (K.card : ℝ) := one_le_logb_of_two_le (by exact_mod_cast h2)
  refine ⟨?_, fun v hv => ?_, ?_, h2⟩
  · rw [hU, hN]
    refine le_trans e4.le ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := epsC_pos
    have hmul := mul_le_mul_of_nonneg_left e6 this.le
    nlinarith
  · rw [graphAtD_append_false ha, graphAtD_append_true ha]
    exact ⟨mem_splitFst_verts_of_mem_left hUK hv, not_mem_splitSnd_verts_of_mem_left hv⟩
  · rw [graphAtD_append_false ha, card_splitFst hUK hNK, hU, hN]
    linarith

end HB

/-- [s2:lem14tau] (a), local part: "at every split, at a node of size `m`,
`|H_out| + |H_in| ≤ |F_0|/τ ≤ s|U|/τ ≤ |U|/(128 log² m)`,
`|N''| < 1.25 ε|U|/log² m < 1.5 ε|U|/log² m`, `|U'| ≥ (127/128)|U| > 0`, `U ⊆ U' ∪ N''`,
`n_1 := |U' ∪ N''| ≤ 0.698 m < (3/4) m` and `n_2 := m - |U'| < m`." -/
theorem l14Split : EG.Spec.L14SplitStatement := by
  intro V _ H s τ t hs hτ _ a _ K U N F hK hw hN _
  subst hK hN
  exact l14_split hw hs (HB.tau_local hτ a)

/-- [s2:lem14tau] (a) "The recursion terminates", for every choice of witnesses: (T1) both
children of a split are smaller, (T2) the recursion with any witness rule is a finite `τ`-run. -/
theorem l14Term : EG.Spec.L14TermStatement := by
  intro V _ H s τ hs hτ
  refine ⟨fun K U N F _ hKn hw hN => ?_, fun W hW => ?_⟩
  · subst hN
    have hτK : 128 * (s : ℝ) * Real.logb 2 K.card ^ 2 ≤ τ :=
      le_trans (mul_le_mul_of_nonneg_left (logb_sq_natCast_mono hKn) (by positivity)) hτ
    obtain ⟨hn1, -, hn1lt, hn2, hn2lt, -, -⟩ := l14_children hw hs hτK
    exact ⟨hn1, hn1lt, hn2, hn2lt⟩
  · obtain ⟨h1, h2⟩ := tauBuild_spec hs W hW H.card [] H le_rfl hτ
    refine ⟨_, h1, fun a ha => ?_⟩
    have := h2 a ha
    rw [List.nil_append] at this
    exact this

/-- [s2:lem14tau] (a), global part: "at most `4 s n_0 log n_0` edges are deleted; the remaining
edges are partitioned into the leaves; every leaf is an `(ε,s)`-expander; and the total size of
the leaves is at most `2n_0 - 2n_0/(2 + log n_0)`." -/
theorem l14Global : EG.Spec.L14GlobalStatement := by
  intro V _ H s τ t hs hτ ht
  obtain ⟨hd, hm⟩ := l14_induction hs t ht hτ
  exact ⟨hd, fun e he => sep_count t he,
    fun L hL => (ht.2.1 L (leafAddrs_subset_nodeAddrs t hL)).1 hL, hm⟩

/-- [s2:lem14tau] (b) "(OV at `1.6ε`) at every split, `|N''| ≤ 1.6 ε|U'|/log² m`, the vertices of
`U'` go only to `G_1`, and `|G_1| ≤ (3/4)m`. Hence, by Lemma [s2:lemOVgeneric] with `c = 1.6`,
the total leaf size `S` satisfies `S ≤ n_0/(1 - 5.5ε) ≤ 1.21 n_0`, and for every `M ≥ 2` the
duplication at nodes of size at least `M` is `Δ_{≥M} ≤ 5.46 ε S / log M`." -/
theorem l14OV : EG.Spec.L14OVStatement := by
  intro V _ H s τ t hs hτ ht
  have hnode := fun a (ha : a ∈ t.internalAddrs) => HB.l14_node hs hτ ht ha
  have hov : t.OVHyp epsC 1.6 H :=
    ⟨ht.1, fun a ha => ⟨(hnode a ha).2.2.2, (hnode a ha).2.2.1, (hnode a ha).1⟩⟩
  have hε := epsC_eq
  have hεp := epsC_pos
  have hS : (t.leafMass H : ℝ) ≤ H.card / (1 - 3.42 * 1.6 * epsC) :=
    ov_c (by norm_num) hεp.le (by rw [hε]; norm_num) hov
  have hn0 : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
  refine ⟨hnode, hov, ?_, ?_, fun M hM => ?_⟩
  · refine le_trans hS ?_
    apply div_le_div_of_nonneg_left hn0 (by rw [hε]; norm_num) (by rw [hε]; norm_num)
  · rw [hε, div_le_iff₀ (by norm_num)]
    nlinarith
  · have ha := ov_a (c := 1.6) (by norm_num) hεp.le hM t hov
    have hC := ovC_le_sharp hM
    have hL := one_le_logb_of_two_le hM
    have hSn : (0 : ℝ) ≤ t.leafMass H := Nat.cast_nonneg _
    have h1 : 1.6 * epsC * ovC M * t.leafMass H ≤
        1.6 * epsC * (58 / 17 / Real.logb 2 M) * t.leafMass H := by
      apply mul_le_mul_of_nonneg_right _ hSn
      exact mul_le_mul_of_nonneg_left hC (by positivity)
    have h2 : 1.6 * epsC * (58 / 17 / Real.logb 2 M) * t.leafMass H ≤
        5.46 * epsC * t.leafMass H / Real.logb 2 M := by
      rw [show 1.6 * epsC * (58 / 17 / Real.logb 2 M) * t.leafMass H =
        (1.6 * (58 / 17)) * epsC * t.leafMass H / Real.logb 2 M by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ epsC * t.leafMass H := by positivity
      nlinarith
    linarith

/-- [s2:lem14tau] (c), (d) "(c) for every leaf `Leaf` and every vertex `h`,
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1` (`= τ - 1` for integer `τ`), and the number
is `0` if `h ∈ V(Leaf)`; (d) if `u ∉ Dup`, every edge at `u` is deleted or lies in the unique
leaf containing `u`." (With the T1 repair `0 < τ` on the two bounds.) -/
theorem l14Thin : EG.Spec.L14ThinStatement := by
  intro V _ H s τ t _ _ ht
  refine ⟨fun L hL h => ⟨fun hτ0 => ?_, fun hτ0 k hk => ?_, fun hh => thinCut_eq_zero hL hh⟩,
    fun u hu e he hue => thinCut_edge t hu he hue⟩
  · exact HB.natCast_le_ceil_sub_one (thinCut_lt hτ0 ht.tauLabels hL h)
  · exact HB.le_sub_one_of_cast_lt (thinCut_lt hτ0 ht.tauLabels hL h) hk

end EG
