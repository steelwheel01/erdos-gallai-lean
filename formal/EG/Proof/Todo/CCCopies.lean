module

public import EG.Spec.Quot.CC
public import EG.Proof.Todo.CCMax
public import EG.Proof.Quot.MULT
public import EG.Lib.Quot.MultUniv
public import EG.Proof.Num.CC
public import EG.Lib.Prob.TotalExp
public import EG.Lib.Quot.Items
public import EG.Lib.Quot.Quotient
public import EG.Lib.Quot.Colour
public import EG.Lib.Quot.E2

/-!
# P3 stub: `EG.Spec.CCCopiesStatement` (s7:lemCC)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CCCopies`; consumers import this module.

Proof (manuscript s7:lemCC (iii)): "By the PAR-MULT identity, `[w]` is not isolated in exactly
`max_{w'} m_κ(w,w')` of the sub-layers `B^{P,(ι)}_κ`" (`EG.parMultSublayer`), so the number of PAR
copies is `Σ_{κ<3M_l} Σ_{w ∈ Pool_l} max_{w'} m_κ(w,w')`. Averaging (ii) (`EG.Todo.CCMax`) over the
indicators (`EG.FinDist.expect_le_of_cond_le`) with `t = t^CC_l` bounds each term by
`t + (6e/Hcd_l + 4e2^{-t})E|S_w|`; every PAR object lies in at most two sets `S_w` (one per end),
and there are at most `|J_l| ≤ n(M_l − 1)` PAR objects, so `Σ_{κ,w}|S_w| ≤ 2nM_l ≤ 2.74nM_l`. The
final computation is `EG.numCCCombine`.
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist Finset

/-- The PAR copies of `Q_l`: at most `Σ_{κ<3M_l} Σ_{w ∈ Pool_l} max_{w'} m_κ(w,w')`. -/
theorem parCopies_le_sum {V : Type*} [DecidableEq V] {I : RoundInput V} (hI : I.Valid)
    {R : Rules I} (hR : R.Valid) (ξ : Xi I.G I.M) :
    Spec.parCopies R ξ ≤ ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool,
      (I.pool.erase w).sup (fun w' => R.mPar ξ κ w w') := by
  classical
  set F : ℕ → V → Finset (QVert V) := fun κ w =>
    (R.Q ξ).verts.filter (fun q => q.1 = parTag κ q.1.2.2.1 ∧ q.2 = w) with hF
  have hsub : (R.Q ξ).verts.filter (fun q => q.1.1 = false) ⊆
      (range (3 * I.M)).biUnion (fun κ => I.pool.biUnion (F κ)) := by
    intro q hq
    rw [mem_filter] at hq
    obtain ⟨hqv, h1⟩ := hq
    obtain ⟨e, -, q', hq', hxq⟩ := Quot.Rules.mem_Q_verts.1 hqv
    rcases e with o | it
    · obtain ⟨κ, w₁, w₂, hc, hj1, hj2, -, rfl⟩ := Rules.qEdge_par_iff.1 hq'
      refine mem_biUnion.2 ⟨κ, mem_range.2 (Rules.parColour_lt' hI hR hc), ?_⟩
      rcases Sym2.mem_iff.1 hxq with rfl | rfl
      · exact mem_biUnion.2 ⟨w₁, Rules.junction_pool hj1, mem_filter.2 ⟨hqv, rfl, rfl⟩⟩
      · exact mem_biUnion.2 ⟨w₂, Rules.junction_pool hj2, mem_filter.2 ⟨hqv, rfl, rfl⟩⟩
    · obtain ⟨κ, w, -, -, rfl⟩ := Rules.qEdge_hub_iff.1 hq'
      rcases Sym2.mem_iff.1 hxq with rfl | rfl <;> simp [hubTag] at h1
  have hcard : ∀ κ < 3 * I.M, ∀ w ∈ I.pool,
      (F κ w).card = (I.pool.erase w).sup (fun w' => R.mPar ξ κ w w') := by
    intro κ hκ w hw
    rw [← EG.parMultSublayer_univ V I hI R hR ξ κ hκ w hw]
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
  unfold Spec.parCopies
  calc ((R.Q ξ).verts.filter (fun q => q.1.1 = false)).card
      ≤ ((range (3 * I.M)).biUnion (fun κ => I.pool.biUnion (F κ))).card := card_le_card hsub
    _ ≤ ∑ κ ∈ range (3 * I.M), (I.pool.biUnion (F κ)).card := card_biUnion_le
    _ ≤ ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool, (F κ w).card :=
        sum_le_sum fun κ _ => card_biUnion_le
    _ = ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool, (I.pool.erase w).sup (fun w' => R.mPar ξ κ w w') :=
        sum_congr rfl fun κ hκ => sum_congr rfl fun w hw => hcard κ (mem_range.1 hκ) w hw

/-- The value pattern of the indicators `I_x` of Lemma CC at the orders `O`: the end `(o, c)` of a
PAR object `o` of colour `κ` receives the junction `w` (and `false` off the objects of colour
`κ`). -/
noncomputable def ccPat {V : Type*} [DecidableEq V] {I : RoundInput V} (R : Rules I)
    (L : Lists I.G I.M) (κ : ℕ) (w : V) (O : Orders I.G) : ParObj V → Bool → Bool :=
  fun o c => decide (o ∈ Spec.parObjsOfColour R κ ∧ R.junction (L, O) (.par o c) = some w)

/-- A value of the pattern of positive probability: its fibre is the atom `ccAtom`. -/
theorem ccPat_fibre {V : Type*} [DecidableEq V] {I : RoundInput V} (R : Rules I)
    (L : Lists I.G I.M) (κ : ℕ) (w : V) (b : ParObj V → Bool → Bool)
    (hb : 0 < (ordersLaw I.G).prob (ccPat R L κ w ⁻¹' {b})) :
    ccPat R L κ w ⁻¹' {b} = Spec.ccAtom R L κ w b := by
  obtain ⟨O0, hO0, -⟩ := exists_of_prob_pos _ hb
  have hb0 : ccPat R L κ w O0 = b := hO0
  subst hb0
  ext O
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Spec.ccAtom, Set.mem_ofPred_eq]
  constructor
  · intro h o ho c
    rw [← h]
    simp [ccPat, ho]
  · intro h
    funext o c
    by_cases ho : o ∈ Spec.parObjsOfColour R κ
    · have := h o ho c
      rw [Bool.eq_iff_iff]
      simpa [ccPat, ho] using this
    · simp [ccPat, ho]

/-- (ii) averaged over the indicators: `E[max_{w'} m_κ(w,w')] ≤ E[t + (6e/Hcd + 4e2^{-t})|S_w|]`. -/
theorem expect_maxPar_le {V : Type*} [DecidableEq V] {I : RoundInput V} (hI : I.Valid)
    {R : Rules I} (hR : R.Valid) (L : Lists I.G I.M) {κ : ℕ} {w : V} (hκ : κ < 3 * I.M)
    (hw : w ∈ I.pool) {t : ℕ} (ht : 1 ≤ t) :
    (ordersLaw I.G).expect
        (fun O => (((I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') : ℕ) : ℝ)) ≤
      (ordersLaw I.G).expect (fun O => (t : ℝ) +
        (6 * Real.exp 1 / I.Hcd + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ))) *
          ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ)) := by
  classical
  refine expect_le_of_cond_le _ (ccPat R L κ w) fun b hb => ?_
  have hA := ccPat_fibre R L κ w b hb
  have hb' : 0 < (ordersLaw I.G).prob (Spec.ccAtom R L κ w b) := hA ▸ hb
  have key : ∀ (A B : Set (Orders I.G)) (_ : A = B) (hA : 0 < (ordersLaw I.G).prob A)
      (hB : 0 < (ordersLaw I.G).prob B), (ordersLaw I.G).cond A hA = (ordersLaw I.G).cond B hB := by
    rintro A B rfl _ _; rfl
  have hY : ((ordersLaw I.G).cond (ccPat R L κ w ⁻¹' {b}) hb).expect (fun O => (t : ℝ) +
        (6 * Real.exp 1 / I.Hcd + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ))) *
          ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ)) =
      (t : ℝ) + (6 * Real.exp 1 / I.Hcd + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ))) *
          ((Spec.ccS R κ b).card : ℝ) := by
    rw [← FinDist.expect_const ((ordersLaw I.G).cond (ccPat R L κ w ⁻¹' {b}) hb)
      ((t : ℝ) + (6 * Real.exp 1 / I.Hcd + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ))) *
          ((Spec.ccS R κ b).card : ℝ))]
    refine expect_congr _ fun O hO => ?_
    rw [cond_w_pos_iff] at hO
    have hO' : ccPat R L κ w O = b := hO.1
    rw [hO']
  rw [hY, key _ _ hA hb hb']
  refine (Todo.CCMax_univ V I hI R hR L κ w hκ hw b hb' t ht).trans ?_
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : (t : ℝ) * (if (Spec.ccS R κ b).Nonempty then 1 else 0) ≤ t := by
    split_ifs <;> simp [ht0]
  have e : 6 * Real.exp 1 * ((Spec.ccS R κ b).card : ℝ) / I.Hcd +
      4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) * ((Spec.ccS R κ b).card : ℝ) =
      (6 * Real.exp 1 / I.Hcd + 4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ))) *
        ((Spec.ccS R κ b).card : ℝ) := by ring
  linarith

/-- At most one pair `(κ, w)` matches the colour and a junction. -/
theorem sum_sum_ite_le_one {V : Type*} [DecidableEq V] (s : Finset ℕ) (P : Finset V)
    (a : Option ℕ) (x : Option V) :
    ∑ κ ∈ s, ∑ w ∈ P, (if a = some κ ∧ x = some w then 1 else 0 : ℕ) ≤ 1 := by
  rcases a with _ | κ0
  · simp
  rcases x with _ | w0
  · simp
  simp only [Option.some.injEq, ite_and]
  calc ∑ κ ∈ s, ∑ w ∈ P, (if κ0 = κ then (if w0 = w then 1 else 0) else 0 : ℕ)
      ≤ ∑ κ ∈ s, (if κ0 = κ then 1 else 0 : ℕ) := by
        refine sum_le_sum fun κ _ => ?_
        split_ifs
        · rw [sum_ite_eq]; split_ifs <;> simp
        · simp
    _ ≤ 1 := by rw [sum_ite_eq]; split_ifs <;> simp

/-- Every PAR object lies in at most two of the sets `S_w` (one per end). -/
theorem sum_card_ccS_le {V : Type*} [DecidableEq V] {I : RoundInput V} (R : Rules I)
    (L : Lists I.G I.M) (m : ℕ) (O : Orders I.G) :
    ∑ κ ∈ range m, ∑ w ∈ I.pool, (Spec.ccS R κ (ccPat R L κ w O)).card ≤ 2 * R.parObjs.card := by
  classical
  set A : ℕ → V → Bool → Finset (ParObj V) := fun κ w c =>
    R.parObjs.filter (fun o => R.parColour o = some κ ∧ R.junction (L, O) (.par o c) = some w)
    with hAdef
  have hsub : ∀ κ w, Spec.ccS R κ (ccPat R L κ w O) ⊆ A κ w false ∪ A κ w true := by
    intro κ w o ho
    rw [Spec.ccS, mem_filter] at ho
    obtain ⟨hK, hne⟩ := ho
    have hK' := hK
    rw [Spec.parObjsOfColour, mem_filter] at hK'
    rw [mem_union, hAdef, mem_filter, mem_filter]
    by_cases h0 : R.junction (L, O) (.par o false) = some w
    · exact Or.inl ⟨hK'.1, hK'.2, h0⟩
    by_cases h1 : R.junction (L, O) (.par o true) = some w
    · exact Or.inr ⟨hK'.1, hK'.2, h1⟩
    exfalso
    apply hne
    simp [ccPat, h0, h1]
  have hA : ∀ c, ∑ κ ∈ range m, ∑ w ∈ I.pool, (A κ w c).card ≤ R.parObjs.card := by
    intro c
    simp only [hAdef, card_filter]
    rw [sum_congr rfl fun κ _ => sum_comm]
    rw [sum_comm]
    calc ∑ o ∈ R.parObjs, ∑ κ ∈ range m, ∑ w ∈ I.pool,
          (if R.parColour o = some κ ∧ R.junction (L, O) (.par o c) = some w then 1 else 0)
        ≤ ∑ o ∈ R.parObjs, 1 := sum_le_sum fun o _ => sum_sum_ite_le_one _ _ _ _
      _ = R.parObjs.card := by simp
  calc ∑ κ ∈ range m, ∑ w ∈ I.pool, (Spec.ccS R κ (ccPat R L κ w O)).card
      ≤ ∑ κ ∈ range m, ∑ w ∈ I.pool, ((A κ w false).card + (A κ w true).card) :=
        sum_le_sum fun κ _ => sum_le_sum fun w _ =>
          (card_le_card (hsub κ w)).trans (card_union_le _ _)
    _ = ∑ κ ∈ range m, ∑ w ∈ I.pool, (A κ w false).card +
          ∑ κ ∈ range m, ∑ w ∈ I.pool, (A κ w true).card := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun κ _ => sum_add_distrib
    _ ≤ 2 * R.parObjs.card := by linarith [hA false, hA true]

/-- There are at most `|J_l| ≤ n(M_l − 1)` PAR objects (`o ↦` its J-edge at the end `false`). -/
theorem card_parObjs_le {V : Type*} [DecidableEq V] {I : RoundInput V} (hI : I.Valid)
    {R : Rules I} (hR : R.Valid) : R.parObjs.card ≤ I.G.card * (I.M - 1) := by
  refine le_trans ?_ hI.J2tot
  refine card_le_card_of_injOn (fun o => o.jAt false) ?_ ?_
  · intro o ho
    exact RoundInput.live_mem_J ((Rules.parObj_facts hI hR (mem_coe.1 ho)).1 false)
  · intro o ho o' ho' e
    exact Rules.parObj_eq_of_jAt hI hR (mem_coe.1 ho) (mem_coe.1 ho') e

theorem one_le_tCC {M : ℕ} (hM : 2 ≤ M) : 1 ≤ tCC M := by
  unfold tCC
  rw [Nat.one_le_ceil_iff]
  have : (1 : ℝ) < M := by exact_mod_cast hM
  have := Real.logb_pos (by norm_num : (1 : ℝ) < 2) this
  linarith

open EG.Spec in
/-- [s7:lemCC] `EG.Spec.CCCopiesStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem CCCopies_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ L : Lists I.G I.M,
      (ordersLaw I.G).expect (fun O => (parCopies R (L, O) : ℝ)) ≤
        3 * (I.M : ℝ) * ((tCC I.M : ℝ) + 1) * (I.pool.card : ℝ) +
          44.7 * (I.G.card : ℝ) * (I.M : ℝ) / I.Hcd + 29.8 * (I.G.card : ℝ) / (I.M : ℝ) := by
  intro V _ I hI R hR L
  classical
  have hM2 : 2 ≤ I.M := le_trans (by norm_num) hI.M_ge
  have hM1 : 1 ≤ I.M := le_trans (by norm_num) hM2
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  have ht := one_le_tCC hM2
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = 6 * Real.exp 1 / I.Hcd + 4 * Real.exp 1 * (2 : ℝ) ^ (-(tCC I.M : ℤ)) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hpt : ∀ O : Orders I.G, ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool,
      ((tCC I.M : ℝ) + c * ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ)) ≤
      3 * (I.M : ℝ) * (tCC I.M : ℝ) * (I.pool.card : ℝ) + c * (2 * (R.parObjs.card : ℝ)) := by
    intro O
    have hsum : ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool,
        ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ) ≤ 2 * (R.parObjs.card : ℝ) := by
      exact_mod_cast sum_card_ccS_le R L (3 * I.M) O
    have e : ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool,
        ((tCC I.M : ℝ) + c * ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ)) =
        3 * (I.M : ℝ) * (tCC I.M : ℝ) * (I.pool.card : ℝ) + c * ∑ κ ∈ range (3 * I.M),
          ∑ w ∈ I.pool, ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ) := by
      simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
      push_cast
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsum hc0
    linarith
  have hS : 2 * (R.parObjs.card : ℝ) ≤ 2.74 * (I.G.card : ℝ) * (I.M : ℝ) := by
    have h1 : R.parObjs.card ≤ I.G.card * I.M :=
      (card_parObjs_le hI hR).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h2 : (R.parObjs.card : ℝ) ≤ (I.G.card : ℝ) * (I.M : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ (I.G.card : ℝ) * (I.M : ℝ) := by positivity
    linarith
  have hfin := EG.numCCCombine I.M (I.G.card : ℝ) I.Hcd (I.pool.card : ℝ)
    (2 * (R.parObjs.card : ℝ)) hM1 hH (Nat.cast_nonneg _) (by positivity) hS
  rw [← hc] at hfin
  calc (ordersLaw I.G).expect (fun O => (Spec.parCopies R (L, O) : ℝ))
      ≤ (ordersLaw I.G).expect (fun O => ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool,
          (((I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') : ℕ) : ℝ)) := by
        refine expect_mono _ fun O => ?_
        exact_mod_cast parCopies_le_sum hI hR (L, O)
    _ = ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool, (ordersLaw I.G).expect (fun O =>
          (((I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') : ℕ) : ℝ)) := by
        rw [expect_sum]
        exact sum_congr rfl fun κ _ => expect_sum _ _ _
    _ ≤ ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool, (ordersLaw I.G).expect (fun O =>
          (tCC I.M : ℝ) + c * ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ)) := by
        refine sum_le_sum fun κ hκ => sum_le_sum fun w hw => ?_
        rw [hc]
        exact expect_maxPar_le hI hR L (mem_range.1 hκ) hw ht
    _ = (ordersLaw I.G).expect (fun O => ∑ κ ∈ range (3 * I.M), ∑ w ∈ I.pool,
          ((tCC I.M : ℝ) + c * ((Spec.ccS R κ (ccPat R L κ w O)).card : ℝ))) := by
        rw [expect_sum]
        exact sum_congr rfl fun κ _ => (expect_sum _ _ _).symm
    _ ≤ (ordersLaw I.G).expect (fun _ =>
          3 * (I.M : ℝ) * (tCC I.M : ℝ) * (I.pool.card : ℝ) + c * (2 * (R.parObjs.card : ℝ))) :=
        expect_mono _ hpt
    _ = 3 * (I.M : ℝ) * (tCC I.M : ℝ) * (I.pool.card : ℝ) + c * (2 * (R.parObjs.card : ℝ)) :=
        FinDist.expect_const _ _
    _ ≤ _ := hfin

/-- Proved in P3. [s7:lemCC] see `EG.Spec.CCCopiesStatement`. -/
theorem CCCopies : EG.Spec.CCCopiesStatement := CCCopies_univ.{0}

end EG.Todo
