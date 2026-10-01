module

public import EG.Lib.Quot.Pay
public import EG.Lib.Quot.UltraAux
public import EG.Lib.Quot.MultUniv
public import EG.Proof.Todo.CCCopies
public import EG.Proof.Todo.UltraSum

/-!
# The four kinds of vertices of `Q_l` (manuscript s7:lemUHsplit (ii)), round level

Proof of s7:lemUHsplit (ii) on an abstract valid round input: "Fix the past and the lists. The
vertices of `Q_l` are of four kinds." (universe-polymorphic):

* `copies_le_split`: `|V(Q_l)| ≤ #PAR copies + Σ_{h ∈ D_l} #copies of h + Σ_{κ<4M_l} Σ_{w ∈ Pool_l}
  max_h m_κ(h,w)`; the last term counts the junction copies in HUB sub-layers ("By Lemma
  s7:lemMULT, in colour `κ` the vertex `[w]` has `max_h m_κ(h,w)` copies"; `multSublayer_univ`);
* `hubCopies_le_three_kh`: "*Copies of non-ultra hubs* (deterministic given the lists). Let `h` be
  non-ultra. By Lemma s7:lemWellDef (iv) …, `m_κ(h,w) ≤ 1` for all `κ` and `w`. So by Lemma
  s7:lemMULT, `h` has exactly one copy in each colour that one of its items uses, and none in the
  other colours. The colours of its items lie in the union of its `k_h` lists, which has `3k_h`
  elements";
* `expect_copies_le`: (ii) at round level, `E[copies_l | Past_l] ≤ X_{V,l} + det_l` with the
  terms read from the round input (PAR copies: s7:lemCC (iii), `CCCopies_univ`; copies of ultra hubs:
  s7:lemUltra (iv), `UltraSum_univ`; "`Σ_{h:c^live_h≥1} 3k_h ≤ Σ_{h∈D_l} 3(1 + 8c^live_h/Hcd_l)
  ≤ 3|D_l| + 24·(nM_l)/Hcd_l`", with `Σ_h c^live_h ≤ |J_l| ≤ n(M_l − 1)`; junction copies
  `≤ 4M_l Σ_{w ∈ Pool_l} mult_{r(w)}(w)` by s7:lemMULT; "`44.7 + 32.9 ≤ 78` and `29.8 ≤ 30`";
  "Averaging over the lists gives (ii)").
-/

public section

namespace EG.Quot

open EG.FinDist Finset

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

/-- A list `{η(3i), η(3i+1), η(3i+2)}` has at most three elements. -/
theorem card_listOf_le {K : ℕ} (η : Equiv.Perm (Fin K)) (i : ℕ) : (listOf η i).card ≤ 3 := by
  classical
  unfold listOf
  refine card_image_le.trans (card_image_le.trans ?_)
  calc (univ.filter (fun a : Fin K => a.val / 3 = i)).card
      ≤ (Finset.Ico (3 * i) (3 * i + 3)).card := by
        refine card_le_card_of_injOn (fun a => a.val) ?_ ?_
        · intro a ha
          have h := (mem_filter.1 (mem_coe.1 ha)).2
          show a.val ∈ (Finset.Ico (3 * i) (3 * i + 3) : Set ℕ)
          rw [coe_Ico, Set.mem_Ico]
          omega
        · intro a _ b _ hab
          exact Fin.ext hab
    _ = 3 := by simp

/-- The junction copies `[w]` of colour `κ` in HUB sub-layers are `max_h m_κ(h,w)` in number. -/
theorem card_juncCopies (hI : I.Valid) (hR : R.Valid) (ξ : Xi I.G I.M) {κ : ℕ} (hκ : κ < 4 * I.M)
    {w : V} (hw : w ∈ I.pool) :
    ((R.Q ξ).verts.filter (fun q => q.1 = hubTag κ q.1.2.2.1 false ∧ q.2 = w)).card =
      I.hubs.sup (fun h => R.mHub ξ κ h w) := by
  classical
  rw [← ((EG.multSublayer_univ V I hI R hR ξ κ hκ).1 w hw)]
  unfold Spec.subLayerRanks
  rw [card_image_of_injOn]
  intro q hq q' hq' he
  simp only [coe_filter, Set.mem_ofPred_eq] at hq hq'
  obtain ⟨⟨t, v⟩⟩ := q
  obtain ⟨⟨t', v'⟩⟩ := q'
  simp only at hq hq' he
  rw [Prod.mk.injEq]
  refine ⟨?_, hq.2.2.trans hq'.2.2.symm⟩
  rw [hq.2.1, hq'.2.1, he]

/-- The vertices of `Q_l`: PAR copies, hub copies of hubs, junction copies in HUB sub-layers. -/
theorem copies_le_split (hI : I.Valid) (hR : R.Valid) (ξ : Xi I.G I.M) :
    R.copies ξ ≤ Spec.parCopies R ξ + ∑ h ∈ I.hubs, Spec.hubCopies R ξ h +
      ∑ κ ∈ range (4 * I.M), ∑ w ∈ I.pool, I.hubs.sup (fun h => R.mHub ξ κ h w) := by
  classical
  set A := (R.Q ξ).verts.filter (fun q => q.1.1 = false) with hA
  set B : V → Finset (QVert V) := fun h =>
    (R.Q ξ).verts.filter (fun q => q.1.1 = true ∧ q.1.2.2.2 = true ∧ q.2 = h) with hB
  set C : ℕ → V → Finset (QVert V) := fun κ w =>
    (R.Q ξ).verts.filter (fun q => q.1 = hubTag κ q.1.2.2.1 false ∧ q.2 = w) with hC
  have hsub : (R.Q ξ).verts ⊆ A ∪ I.hubs.biUnion B ∪
      (range (4 * I.M)).biUnion (fun κ => I.pool.biUnion (C κ)) := by
    intro x hx
    obtain ⟨e, -, q, hq, hxq⟩ := Quot.Rules.mem_Q_verts.1 hx
    rcases e with o | it
    · obtain ⟨κ, w₁, w₂, -, -, -, -, rfl⟩ := Rules.qEdge_par_iff.1 hq
      refine mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hx, ?_⟩))
      rcases Sym2.mem_iff.1 hxq with rfl | rfl <;> rfl
    · obtain ⟨κ, w, h1, h2, rfl⟩ := Rules.qEdge_hub_iff.1 hq
      have hit : it ∈ R.colouredHub ξ.1 := (Rules.hubColour_eq_some h1).1
      have hhub : it.1 ∈ I.hubs := RoundInput.hubItems_hub ((Rules.mem_colouredHub).1 hit).1
      rcases Sym2.mem_iff.1 hxq with rfl | rfl
      · refine mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨it.1, hhub, ?_⟩))
        exact mem_filter.2 ⟨hx, rfl, rfl, rfl⟩
      · refine mem_union_right _ (mem_biUnion.2 ⟨κ, mem_range.2 (Rules.hubColour_lt hR h1), ?_⟩)
        refine mem_biUnion.2 ⟨w, Rules.junction_pool h2, mem_filter.2 ⟨hx, rfl, rfl⟩⟩
  have h1 : (R.Q ξ).card ≤ A.card + ∑ h ∈ I.hubs, (B h).card +
      ∑ κ ∈ range (4 * I.M), ∑ w ∈ I.pool, (C κ w).card := by
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    refine add_le_add ((card_union_le _ _).trans (add_le_add le_rfl card_biUnion_le))
      (card_biUnion_le.trans (sum_le_sum fun κ _ => card_biUnion_le))
  refine h1.trans (le_of_eq ?_)
  congr 1
  refine sum_congr rfl fun κ hκ => sum_congr rfl fun w hw => ?_
  exact card_juncCopies hI hR ξ (mem_range.1 hκ) hw

/-- *Copies of non-ultra hubs*: at most `3k_h` (deterministic given the lists). -/
theorem hubCopies_le_three_kh (hI : I.Valid) (hR : R.Valid) (ξ : Xi I.G I.M) {h : V}
    (hh : h ∈ I.hubs) (hnu : ¬ I.ultra h) : Spec.hubCopies R ξ h ≤ 3 * I.kh h := by
  classical
  set Kh : Finset ℕ := (range (I.kh h)).biUnion (fun i => listOf (etaAt ξ.1 h) i) with hKh
  have hsup : ∀ κ, I.pool.sup (fun w => R.mHub ξ κ h w) ≤ if κ ∈ Kh then 1 else 0 := by
    intro κ
    refine Finset.sup_le fun w _ => ?_
    unfold Rules.mHub
    by_cases hK : κ ∈ Kh
    · rw [if_pos hK, card_le_one]
      intro it hit it' hit'
      obtain ⟨hc, hh1, hk1, hj1⟩ := by simpa only [mem_filter] using hit
      obtain ⟨hc', hh1', hk1', hj1'⟩ := by simpa only [mem_filter] using hit'
      by_contra hne
      have hnu' : ¬ I.ultra it.1 := hh1 ▸ hnu
      have hnu'' : ¬ I.ultra it'.1 := hh1' ▸ hnu
      have e1 : (R.e1State ξ.1).junc it = some w := by
        have := hj1
        simp only [Rules.junction, if_neg hnu'] at this
        exact this
      have e2 : (R.e1State ξ.1).junc it' = some w := by
        have := hj1'
        simp only [Rules.junction, if_neg hnu''] at this
        exact this
      exact (Rules.e1Inv_e1State (R := R) ξ.1).2.2 it it' w hne (hh1.trans hh1'.symm)
        (hk1.trans hk1'.symm) e1 e2
    · rw [if_neg hK, Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
      rintro it hit ⟨rfl, hk, -⟩
      apply hK
      obtain ⟨hcol, hsdr⟩ := Rules.hubColour_eq_some hk
      have hmem := Rules.sdr_mem_hubList hR hcol
      rw [hsdr] at hmem
      unfold Rules.hubList at hmem
      rw [if_neg hnu] at hmem
      have hgr : R.group it < I.kh it.1 :=
        (hR.group it.1 hnu).1 it ((Rules.mem_colouredHub).1 hcol).1 rfl
      exact mem_biUnion.2 ⟨R.group it, mem_range.2 hgr, hmem⟩
  refine (EG.Todo.hubCopies_le_sum hI hR ξ hh).trans ?_
  refine (sum_le_sum fun κ _ => hsup κ).trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
  refine (card_le_card (fun κ hκ => (mem_filter.1 hκ).2)).trans ?_
  exact (card_biUnion_le.trans (sum_le_sum fun i _ => card_listOf_le _ i)).trans
    (by rw [sum_const, card_range, smul_eq_mul, mul_comm])


/-- [s7:lemUHsplit] (ii) at round level: "For every past, `E[copies_l | Past_l] ≤ X_{V,l} + det_l`",
with `X_{V,l}` and `det_l` read from the round input. -/
theorem expect_copies_le (hI : I.Valid) (hR : R.Valid) :
    (roundLaw I.G I.M).expect (fun ξ => (R.copies ξ : ℝ)) ≤
      ((3 * I.M * (tCC I.M + 1) * I.pool.card +
          4 * I.M * ∑ w ∈ I.pool, I.multAt (I.poolRound w) w : ℕ) : ℝ) +
        (3 * (I.hubs.card : ℝ) + 78 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd +
          30 * (I.G.card : ℝ) / (I.M : ℝ) +
          320 * (I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8) / I.lam ^ 95) := by
  classical
  -- constants
  have hM40 : (2 : ℝ) ^ 40 ≤ (I.M : ℝ) := by exact_mod_cast hI.M_ge
  have hM1 : (1 : ℝ) ≤ (I.M : ℝ) := le_trans (by norm_num) hM40
  have hM0 : (0 : ℝ) < (I.M : ℝ) := by linarith
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  have hn : (0 : ℝ) ≤ (I.G.card : ℝ) := Nat.cast_nonneg _
  set D0 : ℕ := ∑ h ∈ I.hubs.filter (fun h => ¬ I.thult < I.clive h), 3 * I.kh h +
    4 * I.M * ∑ w ∈ I.pool, I.multAt (I.poolRound w) w with hD0
  -- pointwise split
  have hpt : ∀ ξ : Xi I.G I.M, (R.copies ξ : ℝ) ≤ (Spec.parCopies R ξ : ℝ) +
      ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), (Spec.hubCopies R ξ h : ℝ) +
      (D0 : ℝ) := by
    intro ξ
    have h1 := copies_le_split hI hR ξ
    have h2 : ∑ h ∈ I.hubs, Spec.hubCopies R ξ h ≤
        ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), Spec.hubCopies R ξ h +
          ∑ h ∈ I.hubs.filter (fun h => ¬ I.thult < I.clive h), 3 * I.kh h := by
      rw [← sum_filter_add_sum_filter_not I.hubs (fun h => I.thult < I.clive h)]
      refine add_le_add le_rfl (sum_le_sum fun h hh => ?_)
      obtain ⟨hh, hnu⟩ := mem_filter.1 hh
      exact hubCopies_le_three_kh hI hR ξ hh hnu
    have h3 : ∑ κ ∈ range (4 * I.M), ∑ w ∈ I.pool, I.hubs.sup (fun h => R.mHub ξ κ h w) ≤
        4 * I.M * ∑ w ∈ I.pool, I.multAt (I.poolRound w) w := by
      calc ∑ κ ∈ range (4 * I.M), ∑ w ∈ I.pool, I.hubs.sup (fun h => R.mHub ξ κ h w)
          ≤ ∑ κ ∈ range (4 * I.M), ∑ w ∈ I.pool, I.multAt (I.poolRound w) w :=
            sum_le_sum fun κ _ => sum_le_sum fun w _ =>
              Finset.sup_le fun h _ => Rules.mHub_le_multAt hI ξ κ h w
        _ = 4 * I.M * ∑ w ∈ I.pool, I.multAt (I.poolRound w) w := by
            rw [sum_const, card_range, smul_eq_mul]
    have h4 : R.copies ξ ≤ Spec.parCopies R ξ +
        ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), Spec.hubCopies R ξ h + D0 := by
      rw [hD0]
      omega
    have h5 : ((R.copies ξ : ℕ) : ℝ) ≤ ((Spec.parCopies R ξ +
        ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), Spec.hubCopies R ξ h + D0 : ℕ) : ℝ) := by
      exact_mod_cast h4
    push_cast at h5
    exact h5
  -- the deterministic part
  have hD0le : (D0 : ℝ) ≤ 3 * (I.hubs.card : ℝ) +
      24 * ((I.G.card : ℝ) * ((I.M : ℝ) - 1)) / I.Hcd +
      ((4 * I.M * ∑ w ∈ I.pool, I.multAt (I.poolRound w) w : ℕ) : ℝ) := by
    have hk : ∀ h, ((I.kh h : ℕ) : ℝ) ≤ 8 * (I.clive h : ℝ) / I.Hcd + 1 := fun h =>
      (Nat.ceil_lt_add_one (by positivity)).le
    have hs1 : ((∑ h ∈ I.hubs.filter (fun h => ¬ I.thult < I.clive h), 3 * I.kh h : ℕ) : ℝ) ≤
        ∑ h ∈ I.hubs, (3 * (8 * (I.clive h : ℝ) / I.Hcd + 1)) := by
      push_cast
      refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun h _ _ => by positivity).trans
        (sum_le_sum fun h _ => by linarith [hk h])
    have hs2 : ∑ h ∈ I.hubs, (3 * (8 * (I.clive h : ℝ) / I.Hcd + 1)) =
        3 * (I.hubs.card : ℝ) + 24 * (∑ h ∈ I.hubs, (I.clive h : ℝ)) / I.Hcd := by
      calc ∑ h ∈ I.hubs, (3 * (8 * (I.clive h : ℝ) / I.Hcd + 1))
          = ∑ h ∈ I.hubs, ((24 / I.Hcd) * (I.clive h : ℝ) + 3) :=
            sum_congr rfl fun h _ => by ring
        _ = (24 / I.Hcd) * ∑ h ∈ I.hubs, (I.clive h : ℝ) + (I.hubs.card : ℝ) * 3 := by
            rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        _ = 3 * (I.hubs.card : ℝ) + 24 * (∑ h ∈ I.hubs, (I.clive h : ℝ)) / I.Hcd := by ring
    have hs3 : ∑ h ∈ I.hubs, (I.clive h : ℝ) ≤ (I.G.card : ℝ) * ((I.M : ℝ) - 1) := by
      have h1 := RoundInput.sum_clive_le_card_J I hI.roles.2.1 I.hubs
      have h2 := hI.J2tot
      have h3 : ((∑ h ∈ I.hubs, I.clive h : ℕ) : ℝ) ≤ ((I.G.card * (I.M - 1) : ℕ) : ℝ) := by
        exact_mod_cast h1.trans h2
      rwa [Nat.cast_mul, Nat.cast_sub (by exact_mod_cast hM1 : 1 ≤ I.M), Nat.cast_one,
        Nat.cast_sum] at h3
    have hs4 : 24 * (∑ h ∈ I.hubs, (I.clive h : ℝ)) / I.Hcd ≤
        24 * ((I.G.card : ℝ) * ((I.M : ℝ) - 1)) / I.Hcd :=
      div_le_div_of_nonneg_right (by linarith) hH.le
    rw [hD0]
    push_cast
    push_cast at hs1
    linarith
  -- per lists
  have hL : ∀ L : Lists I.G I.M, (ordersLaw I.G).expect (fun O => (R.copies (L, O) : ℝ)) ≤
      (3 * (I.M : ℝ) * ((tCC I.M : ℝ) + 1) * (I.pool.card : ℝ) +
          44.7 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd + 29.8 * (I.G.card : ℝ) / (I.M : ℝ)) +
        320 * ((I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8)) / I.lam ^ 95 +
        (D0 : ℝ) := by
    intro L
    have hCC := EG.Todo.CCCopies_univ V I hI R hR L
    have hU := EG.Todo.UltraSum_univ V I hI R hR L
    refine (expect_mono _ fun O => hpt (L, O)).trans ?_
    rw [expect_add, expect_add, FinDist.expect_const]
    linarith
  -- averaging over the lists
  have hE : (roundLaw I.G I.M).expect (fun ξ => (R.copies ξ : ℝ)) ≤
      (3 * (I.M : ℝ) * ((tCC I.M : ℝ) + 1) * (I.pool.card : ℝ) +
          44.7 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd + 29.8 * (I.G.card : ℝ) / (I.M : ℝ)) +
        320 * ((I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8)) / I.lam ^ 95 +
        (D0 : ℝ) := by
    unfold roundLaw
    rw [expect_prod]
    exact expect_le_of_le _ hL
  refine hE.trans ?_
  -- the numerical step: `44.7 + 24 ≤ 78`, `29.8 ≤ 30`
  have hA : 44.7 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd +
      24 * ((I.G.card : ℝ) * ((I.M : ℝ) - 1)) / I.Hcd ≤
      78 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd := by
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ hH.le
    nlinarith
  have hB : 29.8 * (I.G.card : ℝ) / (I.M : ℝ) ≤ 30 * (I.G.card : ℝ) / (I.M : ℝ) :=
    div_le_div_of_nonneg_right (by nlinarith) hM0.le
  have hC : 320 * ((I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8)) / I.lam ^ 95 =
      320 * (I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8) / I.lam ^ 95 := by
    ring
  push_cast
  push_cast at hD0le
  linarith

end EG.Quot
