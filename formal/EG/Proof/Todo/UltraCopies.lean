module

public import EG.Spec.Quot.Ultra
public import EG.Proof.Todo.UltraMax
public import EG.Proof.Quot.MULT
public import EG.Lib.Quot.MultUniv
public import EG.Lib.Quot.Quotient
public import EG.Lib.Quot.Junction

/-!
# P3 stub: `EG.Spec.UltraCopiesStatement` (s7:lemUltra)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UltraCopies`; consumers import this module.

Proof (manuscript s7:lemUltra (iii)): "By Lemma s7:lemMULT, the number of copies of `h` in the
sub-layers of colour `κ` is `max_w m_κ(h,w)`" (`EG.multSublayer`; the copies of `h` in HUB
sub-layers have colours `κ < 4M_l`). "Let `N_κ` be the number of coloured items of `h` of colour
`κ`. Then `N_κ ≤ c^live_h` and `Σ_κ N_κ ≤ c^live_h`, and at most `4M_l` colours have `N_κ ≥ 1`. By
(ii) the expected number of copies of `h` is at most
`Σ_{κ:N_κ≥1} (log₂c^live_h + 8) + 2eΣ_κ 2N_κ/Hcd_l ≤ 4M_l(log₂c^live_h + 8) + 4e c^live_h/Hcd_l`"
(`EG.Todo.UltraMax`).
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist Finset

/-- The HUB-tagged vertices of `Q_l` have colours `κ < 4M_l`. -/
theorem hub_vert_colour_lt {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}
    (hR : R.Valid) (ξ : Xi I.G I.M) {x : QVert V} (hx : x ∈ (R.Q ξ).verts)
    (hk : x.1.1 = true) : x.1.2.1 < 4 * I.M := by
  obtain ⟨e, -, q, hq, hxq⟩ := Quot.Rules.mem_Q_verts.1 hx
  rcases e with o | it
  · obtain ⟨κ, w₁, w₂, -, -, -, -, rfl⟩ := Rules.qEdge_par_iff.1 hq
    rcases Sym2.mem_iff.1 hxq with rfl | rfl <;> simp [parTag] at hk
  · obtain ⟨κ, w, hκ, -, rfl⟩ := Rules.qEdge_hub_iff.1 hq
    have := Rules.hubColour_lt hR hκ
    rcases Sym2.mem_iff.1 hxq with rfl | rfl <;> simpa [hubTag] using this

/-- The copies of `h` in HUB sub-layers are at most `Σ_{κ<4M_l}` of the number of sub-layers of
colour `κ` in which `h` is not isolated. -/
theorem hubCopies_le_sum {V : Type*} [DecidableEq V] {I : RoundInput V} (hI : I.Valid)
    {R : Rules I} (hR : R.Valid) (ξ : Xi I.G I.M) {h : V} (hh : h ∈ I.hubs) :
    Spec.hubCopies R ξ h ≤ ∑ κ ∈ range (4 * I.M), I.pool.sup (fun w => R.mHub ξ κ h w) := by
  classical
  set F : ℕ → Finset (QVert V) := fun κ =>
    (R.Q ξ).verts.filter (fun q => q.1 = hubTag κ q.1.2.2.1 true ∧ q.2 = h) with hF
  have hsub : (R.Q ξ).verts.filter (fun q => q.1.1 = true ∧ q.1.2.2.2 = true ∧ q.2 = h) ⊆
      (range (4 * I.M)).biUnion F := by
    intro q hq
    obtain ⟨hqv, h1, h2, h3⟩ := by simpa only [mem_filter] using hq
    refine mem_biUnion.2 ⟨q.1.2.1, mem_range.2 (hub_vert_colour_lt hR ξ hqv h1), ?_⟩
    simp only [hF, mem_filter]
    refine ⟨hqv, ?_, h3⟩
    obtain ⟨⟨k, κ, ι, sd⟩, v⟩ := q
    simp only at h1 h2
    subst h1 h2
    rfl
  have hcard : ∀ κ < 4 * I.M, (F κ).card = I.pool.sup (fun w => R.mHub ξ κ h w) := by
    intro κ hκ
    rw [← ((EG.multSublayer_univ V I hI R hR ξ κ hκ).2 h hh)]
    unfold Spec.subLayerRanks
    rw [card_image_of_injOn]
    intro q hq q' hq' he
    simp only [hF, coe_filter, Set.mem_ofPred_eq] at hq hq'
    obtain ⟨⟨t, v⟩⟩ := q
    obtain ⟨⟨t', v'⟩⟩ := q'
    simp only at hq hq' he
    rw [Prod.mk.injEq]
    refine ⟨?_, hq.2.2.trans hq'.2.2.symm⟩
    rw [hq.2.1, hq'.2.1, he]
  calc Spec.hubCopies R ξ h
      ≤ ((range (4 * I.M)).biUnion F).card := card_le_card hsub
    _ ≤ ∑ κ ∈ range (4 * I.M), (F κ).card := card_biUnion_le
    _ = ∑ κ ∈ range (4 * I.M), I.pool.sup (fun w => R.mHub ξ κ h w) :=
        sum_congr rfl fun κ hκ => hcard κ (mem_range.1 hκ)

open EG.Spec in
/-- [s7:lemUltra] `EG.Spec.UltraCopiesStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem UltraCopies_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (h : V), h ∈ I.hubs → I.ultra h →
      (ordersLaw I.G).expect (fun O => (hubCopies R (L, O) h : ℝ)) ≤
        4 * (I.M : ℝ) * (Real.logb 2 (I.clive h : ℝ) + 8) +
          4 * Real.exp 1 * (I.clive h : ℝ) / I.Hcd := by
  intro V _ I hI R hR L h hh hult
  classical
  have hM : (0 : ℝ) < I.M := by exact_mod_cast lt_of_lt_of_le (by norm_num) hI.M_ge
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  set c := I.clive h with hc
  have hc1 : (1 : ℝ) ≤ c := by
    have : 1 ≤ c := lt_of_le_of_lt (Nat.zero_le _) hult
    exact_mod_cast this
  have hlogc : 0 ≤ Real.logb 2 (c : ℝ) := Real.logb_nonneg (by norm_num) hc1
  -- the items of `h` of colour `κ` lie among the live hub items of `h`
  have hsubItems : ∀ κ, Spec.ultraItems R L h κ ⊆ I.hubItems.filter (fun p => p.1 = h) := by
    intro κ it hit
    unfold Spec.ultraItems at hit
    rw [mem_filter] at hit ⊢
    exact ⟨(Rules.mem_colouredHub.1 hit.1).1, hit.2.1⟩
  have hNle : ∀ κ, (Spec.ultraItems R L h κ).card ≤ c := fun κ => card_le_card (hsubItems κ)
  -- `Σ_κ N_κ ≤ c^live_h`
  have hsumN : ∑ κ ∈ range (4 * I.M), (Spec.ultraItems R L h κ).card ≤ c := by
    rw [← card_biUnion]
    · exact card_le_card (biUnion_subset.2 fun κ _ => hsubItems κ)
    · intro κ _ κ' _ hne
      rw [Function.onFun, disjoint_left]
      intro it h1 h2
      unfold Spec.ultraItems at h1 h2
      rw [mem_filter] at h1 h2
      exact hne (Option.some.inj (h1.2.2.symm.trans h2.2.2))
  -- `m_κ(h,w) ≤ N_κ`
  have hmN : ∀ O : Orders I.G, ∀ κ w, R.mHub (L, O) κ h w ≤ (Spec.ultraItems R L h κ).card := by
    intro O κ w
    unfold Rules.mHub Spec.ultraItems
    apply card_le_card
    intro it hit
    rw [mem_filter] at hit ⊢
    exact ⟨hit.1, hit.2.1, hit.2.2.1⟩
  -- (ii) for each colour
  have hκb : ∀ κ ∈ range (4 * I.M), (ordersLaw I.G).expect
      (fun O => ((I.pool.sup fun w => R.mHub (L, O) κ h w : ℕ) : ℝ)) ≤
        Real.logb 2 (c : ℝ) + 8 + 4 * Real.exp 1 / I.Hcd * (Spec.ultraItems R L h κ).card := by
    intro κ hκ
    have he0 := Real.exp_pos 1
    rcases Nat.eq_zero_or_pos (Spec.ultraItems R L h κ).card with h0 | hpos
    · have hz : ∀ O : Orders I.G, ((I.pool.sup fun w => R.mHub (L, O) κ h w : ℕ) : ℝ) = 0 := by
        intro O
        have : I.pool.sup (fun w => R.mHub (L, O) κ h w) = 0 :=
          Nat.eq_zero_of_le_zero (Finset.sup_le fun w _ => (hmN O κ w).trans h0.le)
        simp [this]
      simp_rw [hz, FinDist.expect_const, h0]
      simp only [CharP.cast_eq_zero, mul_zero, add_zero]
      linarith
    · have hU := Todo.UltraMax_univ V I hI R hR L h κ hh hult (mem_range.1 hκ) hpos
      have hN1 : (1 : ℝ) ≤ (Spec.ultraItems R L h κ).card := by exact_mod_cast hpos
      have hlog : Real.logb 2 ((Spec.ultraItems R L h κ).card : ℝ) ≤ Real.logb 2 (c : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast hNle κ)
      have e : 2 * Real.exp 1 * (2 * ((Spec.ultraItems R L h κ).card : ℝ) / I.Hcd) =
          4 * Real.exp 1 / I.Hcd * (Spec.ultraItems R L h κ).card := by ring
      linarith
  -- sum over the colours
  have hle : ∀ O : Orders I.G, (Spec.hubCopies R (L, O) h : ℝ) ≤
      ∑ κ ∈ range (4 * I.M), ((I.pool.sup fun w => R.mHub (L, O) κ h w : ℕ) : ℝ) := by
    intro O
    exact_mod_cast hubCopies_le_sum hI hR (L, O) hh
  calc (ordersLaw I.G).expect (fun O => (Spec.hubCopies R (L, O) h : ℝ))
      ≤ (ordersLaw I.G).expect (fun O =>
          ∑ κ ∈ range (4 * I.M), ((I.pool.sup fun w => R.mHub (L, O) κ h w : ℕ) : ℝ)) :=
        expect_mono _ hle
    _ = ∑ κ ∈ range (4 * I.M), (ordersLaw I.G).expect
          (fun O => ((I.pool.sup fun w => R.mHub (L, O) κ h w : ℕ) : ℝ)) := expect_sum _ _ _
    _ ≤ ∑ κ ∈ range (4 * I.M),
          (Real.logb 2 (c : ℝ) + 8 + 4 * Real.exp 1 / I.Hcd * (Spec.ultraItems R L h κ).card) :=
        sum_le_sum hκb
    _ = 4 * (I.M : ℝ) * (Real.logb 2 (c : ℝ) + 8) +
          4 * Real.exp 1 / I.Hcd * ∑ κ ∈ range (4 * I.M), ((Spec.ultraItems R L h κ).card : ℝ) := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
        push_cast
        ring
    _ ≤ 4 * (I.M : ℝ) * (Real.logb 2 (c : ℝ) + 8) + 4 * Real.exp 1 / I.Hcd * c := by
        gcongr
        exact_mod_cast hsumN
    _ = 4 * (I.M : ℝ) * (Real.logb 2 (c : ℝ) + 8) + 4 * Real.exp 1 * (c : ℝ) / I.Hcd := by ring

/-- Proved in P3. [s7:lemUltra] see `EG.Spec.UltraCopiesStatement`. -/
theorem UltraCopies : EG.Spec.UltraCopiesStatement := UltraCopies_univ.{0}

end EG.Todo
