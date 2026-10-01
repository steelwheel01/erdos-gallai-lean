module

public import EG.Spec.Ext.BMLemma25
public import EG.Lib.Ext.DFSCycle
public import EG.Lib.Found.LogMono
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bucić–Montgomery Lemma 25, explicit form (manuscript s1:citLem25)

* `EG.bmLemma25 : EG.Spec.BMLemma25Statement`: proved, with the constant `18` of the
  statement, by the depth-first-search proof of [BM, Lemma 25] sketched in s1:citLem25 (DFS as
  an invariant relation in `EG.Lib.Ext.DFS`, the `X, Y, Z` step in `EG.Lib.Ext.DFSCycle`;
  design note `formal/work/ext/lemma25.md`). The proof gives a cycle of length at least
  `⌈ε² m / (18 log⁴ m)⌉ + 2`.
* `EG.bmLemma25_literal_false`: the statement without the hypothesis `2 ≤ m` is false, in every
  universe (a one-vertex graph with `ε = 2^{15}`); this is why `EG.Spec.BMLemma25Statement` has
  it (a class T0 encoding deviation, PLAN §7; entry T0-cap-1 in `formal/work/p1b/cap.md`).
-/

public section


namespace EG

universe u

/-! ### Expansion with `F = ∅` -/

/-- Definition 11 with `s = 0` and `F = ∅`, for `U ⊆ V(G)` with `1 ≤ |U| ≤ 2|G|/3`. -/
theorem bm25_expand {V : Type*} [DecidableEq V] {G : FGraph V} {ε : ℝ}
    (hexp : G.IsExpander ε 0) {U : Finset V} (hU : U ⊆ G.verts) (h1 : 1 ≤ U.card)
    (h2 : 3 * U.card ≤ 2 * G.card) :
    ε * U.card / Real.logb 2 G.card ^ 2 ≤ (G.nbrSet U).card := by
  have h := hexp U ∅ hU (Finset.empty_subset _) h1 (by
    have : (3 * U.card : ℝ) ≤ 2 * G.card := by exact_mod_cast h2
    linarith) (by simp)
  simpa using h

/-- Non-vacuity of expansion: an `(ε,0)`-expander on `n ≥ 2` vertices has `ε ≤ log² n`
(apply Definition 11 to a set of `⌈n/2⌉` vertices). -/
theorem bm25_eps_le {V : Type*} [DecidableEq V] {G : FGraph V} {ε : ℝ}
    (hexp : G.IsExpander ε 0) (hn : 2 ≤ G.card) :
    ε / Real.logb 2 G.card ^ 2 ≤ 1 := by
  obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq (s := G.verts) (n := (G.card + 1) / 2)
    (by have : G.card = G.verts.card := rfl; omega)
  have h1 : 1 ≤ U.card := by omega
  have h := bm25_expand hexp hU h1 (by omega)
  have hN : (G.nbrSet U).card ≤ U.card := by
    have := Finset.card_le_card (FGraph.nbrSet_subset_sdiff (H := G) U)
    rw [Finset.card_sdiff_of_subset hU] at this
    simp only [FGraph.card] at hUc
    omega
  have hL : 0 < Real.logb 2 (G.card : ℝ) :=
    Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < G.card by omega))
  have hc : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have hN' : ((G.nbrSet U).card : ℝ) ≤ U.card := by exact_mod_cast hN
  rw [div_le_one (pow_pos hL 2)]
  have : ε * U.card / Real.logb 2 G.card ^ 2 = (ε / Real.logb 2 G.card ^ 2) * U.card := by
    ring
  rw [this] at h
  have h' : (ε / Real.logb 2 G.card ^ 2) * U.card ≤ 1 * U.card := by linarith
  have := le_of_mul_le_mul_right h' hc
  rwa [div_le_one (pow_pos hL 2)] at this

/-! ### The numerical inequality `24 log⁴ m ≤ ε² m` -/

/-- `log₂ (2^k) = k`. -/
theorem bm25_logb_two_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- For `m ≥ 2`, `max(2^{30}, m/2^{10}) ≥ 24 log⁴ m`: if `m < 2^{40}` then `log m < 40` and
`24 · 40⁴ < 2^{30}`; otherwise `m / log⁴ m ≥ 2^{40}/40⁴ ≥ 24 · 2^{10}` by monotonicity of
`y ↦ y / log⁴ y` (`EG.div_logb_pow_le_div_logb_pow`). -/
theorem bm25_numeric {m : ℝ} (hm : 2 ≤ m) :
    24 * Real.logb 2 m ^ 4 ≤ 2 ^ 30 ∨ 24 * Real.logb 2 m ^ 4 ≤ m / 2 ^ 10 := by
  have hL0 : 0 < Real.logb 2 m := Real.logb_pos one_lt_two (by linarith)
  by_cases h40 : m < 2 ^ 40
  · left
    have hL : Real.logb 2 m < 40 := by
      have := Real.logb_lt_logb one_lt_two (by linarith) h40
      rw [show ((2 : ℝ) ^ 40) = (2 : ℝ) ^ (40 : ℕ) by norm_num, bm25_logb_two_pow] at this
      exact_mod_cast this
    have : Real.logb 2 m ^ 4 ≤ 40 ^ 4 := pow_le_pow_left₀ hL0.le hL.le 4
    linarith
  · right
    push Not at h40
    have hk : ((4 : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ 40) := by
      rw [Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    have hmono := div_logb_pow_le_div_logb_pow one_lt_two (k := 4) (by norm_num) hk h40
    rw [show ((2 : ℝ) ^ 40) = (2 : ℝ) ^ (40 : ℕ) by norm_num, bm25_logb_two_pow] at hmono
    rw [div_le_div_iff₀ (by norm_num) (pow_pos hL0 4)] at hmono
    push_cast at hmono
    nlinarith [pow_pos hL0 4]

/-! ### The proof -/

/-- [s1:citLem25] Bucić–Montgomery Lemma 25, explicit form: "Let `ε ≥ 2^{-5}` and
`m ≥ max(2, 2^{30}/ε²)`. Every `m`-vertex `(ε,0)`-expander contains a cycle of length at least
`ε² m / (18 log⁴ m)`." Proof of [BM] (design note `formal/work/ext/lemma25.md`): a DFS state
with `|U| = |R|` (`EG.DFS.exists_balanced`) has a path `P ⊇ Nbr(U)` with
`|P| ≥ ε m / (3 log² m)`; the `X, Y, Z` argument (`EG.DFS.long_cycle_of_path`) with
`|Y| = ⌈ε² m / (18 log⁴ m)⌉` gives a cycle of length at least `|Y| + 2`. -/
theorem bmLemma25 : EG.Spec.BMLemma25Statement.{u} := by
  intro V _ G ε hε hm hn2 hexp
  set n : ℕ := G.card with hn
  set L : ℝ := Real.logb 2 (n : ℝ) with hL
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hL0 : 0 < L := Real.logb_pos one_lt_two (by linarith)
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  set β : ℝ := ε / L ^ 2 with hβ
  have hβ0 : 0 < β := div_pos hε0 (pow_pos hL0 2)
  have hβ1 : β ≤ 1 := bm25_eps_le hexp hn2
  have hexpβ : ∀ U : Finset V, U ⊆ G.verts → 1 ≤ U.card → 3 * U.card ≤ 2 * n →
      β * U.card ≤ (G.nbrSet U).card := by
    intro U hU h1 h2
    have := bm25_expand hexp hU h1 h2
    rw [hβ]
    calc ε / L ^ 2 * U.card = ε * U.card / L ^ 2 := by ring
      _ ≤ _ := this
  -- `24 log⁴ n ≤ ε² n`
  have hε2n : 2 ^ 30 ≤ ε ^ 2 * n := by
    have := (div_le_iff₀ (pow_pos hε0 2)).1 hm
    linarith
  have hε2 : (2 : ℝ) ^ (-10 : ℤ) ≤ ε ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hε 2
    rw [← zpow_natCast, ← zpow_mul] at this
    simpa using this
  have hε2n' : n / 2 ^ 10 ≤ ε ^ 2 * n := by
    have h0 : (0 : ℝ) ≤ n := by positivity
    have : (2 : ℝ) ^ (-10 : ℤ) = 1 / 2 ^ 10 := by norm_num
    rw [this] at hε2
    nlinarith
  have h24 : 24 * L ^ 4 ≤ ε ^ 2 * n := by
    rcases bm25_numeric hnR with h | h <;> linarith
  -- `a = ε² n / (18 L⁴) = β² n / 18 ≥ 4/3`
  set a : ℝ := ε ^ 2 * n / (18 * L ^ 4) with ha
  have haβ : a = β ^ 2 * n / 18 := by
    rw [ha, hβ]; field_simp
  have ha43 : 4 / 3 ≤ a := by
    rw [ha, le_div_iff₀ (by positivity)]
    linarith
  -- the DFS moment `|U| = |R|`
  obtain ⟨U, R, P, hinv, hUR⟩ := DFS.exists_balanced G
  have hcard := hinv.card_eq
  rw [← hUR] at hcard
  set p := P.length with hp
  have hpβ : β * n / 3 ≤ p := by
    by_cases h3 : n ≤ 3 * U.card
    · have h1 : 1 ≤ U.card := by omega
      have hN := hexpβ U hinv.U_sub h1 (by omega)
      have hNP : ((G.nbrSet U).card : ℝ) ≤ p := by exact_mod_cast hinv.card_nbrSet_le
      have h3' : (n : ℝ) ≤ 3 * U.card := by exact_mod_cast h3
      nlinarith
    · have h3' : (n : ℝ) < 3 * p := by
        have : n < 3 * p := by omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
  have hp6a : 6 * a ≤ β * p := by
    rw [haβ]
    have : β ^ 2 * n / 3 ≤ β * (β * n / 3) := by ring_nf; exact le_refl _
    nlinarith
  -- `|Y| = k = ⌈a⌉`, `|X| = x = (p - k)/2`
  set k : ℕ := ⌈a⌉₊ with hk
  have hk1 : a ≤ k := Nat.le_ceil a
  have hk2 : (k : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk0 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hβp : β * p ≤ p := by
    have : (0 : ℝ) ≤ p := by positivity
    nlinarith
  have hkp : k ≤ p := by
    have : (k : ℝ) ≤ p := by linarith
    exact_mod_cast this
  set x : ℕ := (p - k) / 2 with hx
  have hxk : x + k + x ≤ p := by omega
  have h2x : (p : ℝ) ≤ k + 2 * x + 1 := by
    have : p ≤ k + 2 * x + 1 := by omega
    exact_mod_cast this
  have hβx : (k : ℝ) < β * x := by
    have h1 : β * p ≤ β * (k + 2 * x + 1) := mul_le_mul_of_nonneg_left h2x hβ0.le
    have h2 : β * k ≤ k := by
      have : (0 : ℝ) ≤ k := by positivity
      nlinarith
    nlinarith
  -- expansion in the form needed by the `X, Y, Z` step
  have hexpS : ∀ S : Finset V, S ⊆ G.verts → x ≤ S.card → 2 * S.card ≤ G.card →
      k < (G.nbrSet S).card := by
    intro S hS hxS h2S
    have hx1 : 1 ≤ x := by
      by_contra h0
      have : x = 0 := by omega
      rw [this] at hβx
      simp at hβx
      linarith
    have hN := hexpβ S hS (le_trans hx1 hxS) (by omega)
    have hxS' : (x : ℝ) ≤ S.card := by exact_mod_cast hxS
    have : (k : ℝ) < (G.nbrSet S).card := by nlinarith
    exact_mod_cast this
  obtain ⟨c, hc1, hc2, hc3⟩ :=
    DFS.long_cycle_of_path P hinv.nodup hinv.chain hinv.P_sub x k hk0 (by omega) hexpS
  refine ⟨c, hc1, hc2, ?_⟩
  have : (k : ℝ) + 2 ≤ c.length := by exact_mod_cast hc3
  linarith

/-- The literal reading of [s1:citLem25] without the hypothesis `2 ≤ m` is false in Lean, in
every universe `u` (the statement below is `EG.Spec.BMLemma25Statement.{u}` with the hypothesis
`2 ≤ G.card` deleted): the one-vertex graph on `PUnit.{u+1}` is a `(2^{15}, 0)`-expander
(Definition 11 is vacuous), `2^{30}/(2^{15})² = 1`, the bound `ε² m / (18 log⁴ m)` is
`x / 0 = 0`, but there is no cycle. -/
theorem bmLemma25_literal_false :
    ¬ ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε : ℝ),
      (2 : ℝ) ^ (-5 : ℤ) ≤ ε → (2 : ℝ) ^ 30 / ε ^ 2 ≤ (G.card : ℝ) → G.IsExpander ε 0 →
      ∃ c : List V, (EG.Obj.cycle c).WF ∧ (∀ e ∈ EG.cycleEdges c, e ∈ G.edges) ∧
        ε ^ 2 * (G.card : ℝ) / (18 * Real.logb 2 (G.card : ℝ) ^ 4) ≤ (c.length : ℝ) := by
  intro h
  let G : EG.FGraph PUnit.{u+1} :=
    { verts := {PUnit.unit}, edges := ∅, edge_verts := by simp, loopless := by simp }
  have hcard : G.card = 1 := rfl
  have hexp : G.IsExpander ((2 : ℝ) ^ 15) 0 := by
    intro U F _ _ h1 h2 _
    rw [hcard] at h2
    have h1' : (1 : ℝ) ≤ U.card := by exact_mod_cast h1
    norm_num at h2
    linarith
  obtain ⟨c, ⟨hnd, hlen⟩, -, -⟩ :=
    h PUnit G ((2 : ℝ) ^ 15) (by norm_num) (by rw [hcard]; norm_num) hexp
  have := hnd.length_le_card
  simp at this
  omega

end EG
