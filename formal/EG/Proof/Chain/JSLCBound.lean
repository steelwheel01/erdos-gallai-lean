module

public import EG.Proof.Chain.JSLCAssembly

/-!
# JS-LC, Step 8: the count (manuscript s6:lemJSLC, proof, Step 8)

Probe unit P2J (probe P-2, part 2), proof round 1. The number of systems (each costing one cycle)
is at most `∑_Y |used Y| ≤ ∑_Y m_Y`, and the first-fit grouping gives
`m_Y K ≤ (m_{Y,l} + 2(M_l − 1) + 1) K + #cherries(Y)` with `K = K^JS_l = M_l²`.

Step 8 of the manuscript: "Each port has at most `M_l − 1` beads. So there are at most
`n(M_l − 1)` beads in total. … The number of ancestors `Y` of rounds `≤ l − 2` is
`ν_l ≤ 2.74n/P_{l−2}` (Lemma s2:lemTower(b) …). Moreover `γ_l ≤ P_{l−2}/M_l` and
`P_{l−2} ≥ M_l^{13}` (Lemma s2:lemTower(b)). … Since `15 ≤ 126`, the number of cycles is at most
`126n/M_l + 1.5 ∑_{(Y,l) giant} m_{Y,l}`."

Here (all components split into cherries, see `JSLCGroups.lean`): the number of cycles is at most
`∑_Y (m_{Y,l} + 2M_l) + (∑_Y |R_Y|)/K^JS_l`. For a non-giant `(Y,l)`, `m_{Y,l} ≤ 2γ_l`
(`JslcCtx.mY_le_of_not_isGiant`); so this is at most
`∑_{(Y,l) giant} m_{Y,l} + ν_l (2γ_l + 2M_l) + n(M_l − 1)/M_l² ≤ ∑_{giant} m_{Y,l} + 12 n/M_l`.
-/

public section

namespace EG.Chain.JSLC

open EG.HB EG.Chain EG.Chain.Cherry

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)} {J : Finset (Sym2 V)}
  {R : PartId → Finset (Sym2 V)} {m : PartId → ℕ} {col : PartId → V × V × V → ℕ}

theorem KJS_eq : Stage1.KJS G run l = run.M G l ^ 2 := rfl

theorem one_le_M' : 1 ≤ run.M G l :=
  le_trans (Nat.one_le_two_pow) (EG.Stage1.two_pow_le_M G run l)

/-- `|used Y| ≤ m_Y`. -/
theorem card_used_le (hg : GroupSpec run G l R δ m col) (Y : PartId) :
    (used run G R col Y).card ≤ m Y := by
  have : used run G R col Y ⊆ Finset.range (m Y) := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := mem_used.1 hi
    exact Finset.mem_range.2 ((hg Y).1 c hc)
  exact (Finset.card_le_card this).trans (by simp)

/-- The cost of one class in `ℝ`: `|used Y| ≤ m_{Y,l} + 2M_l + |R_Y|/K^JS_l`. -/
theorem card_used_le_real (C : JslcCtx run G δ S l B J R) (hg : GroupSpec run G l R δ m col)
    (Y : PartId) :
    ((used run G R col Y).card : ℝ) ≤ (mY run G δ Y l : ℝ) + 2 * (run.M G l : ℝ) +
      ((R Y).card : ℝ) / (Stage1.KJS G run l : ℝ) := by
  have hM := one_le_M' (run := run) (G := G) (l := l)
  have hK : 0 < Stage1.KJS G run l := by rw [KJS_eq]; positivity
  have hch : (chs run G R Y).card ≤ (R Y).card := card_cherries_le (C.cherryHyp Y)
  have h1 : m Y * Stage1.KJS G run l ≤
      (mY run G δ Y l + 2 * run.M G l) * Stage1.KJS G run l + (R Y).card := by
    refine ((hg Y).2.2.2).trans (Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) hch)
  have h2 : ((m Y : ℕ) : ℝ) * (Stage1.KJS G run l : ℝ) ≤
      ((mY run G δ Y l : ℝ) + 2 * (run.M G l : ℝ)) * (Stage1.KJS G run l : ℝ) +
        ((R Y).card : ℝ) := by
    exact_mod_cast h1
  have hKr : (0 : ℝ) < (Stage1.KJS G run l : ℝ) := by exact_mod_cast hK
  have h3 : (m Y : ℝ) ≤ (mY run G δ Y l : ℝ) + 2 * (run.M G l : ℝ) +
      ((R Y).card : ℝ) / (Stage1.KJS G run l : ℝ) := by
    have : ((m Y : ℝ) - ((mY run G δ Y l : ℝ) + 2 * (run.M G l : ℝ))) ≤
        ((R Y).card : ℝ) / (Stage1.KJS G run l : ℝ) := by
      rw [le_div_iff₀ hKr]; nlinarith
    linarith
  have h4 : ((used run G R col Y).card : ℝ) ≤ (m Y : ℝ) := by
    exact_mod_cast card_used_le hg Y
  linarith

/-- `∑_Y |R_Y| ≤ n(M_l − 1)`: the `R_Y` are pairwise disjoint subsets of `⋃_Z B_Z`. -/
theorem sum_card_R_le (C : JslcCtx run G δ S l B J R) :
    ∑ Y ∈ Step2.classes run G δ S l, (R Y).card ≤ G.card * (run.M G l - 1) := by
  classical
  rw [← Finset.card_biUnion (fun Y _ Y' _ h => C.disjRR Y Y' h)]
  refine (Finset.card_le_card ?_).trans C.card_Bu_le
  intro e he
  obtain ⟨Y, -, he⟩ := Finset.mem_biUnion.1 he
  exact C.R_sub Y he

/-- The classes of round `l` are ancestors of rounds `≤ l − 2`: at most `ν_l` of them. -/
theorem card_classes_le (C : JslcCtx run G δ S l B J R) :
    (Step2.classes run G δ S l).card ≤ run.nuAnc G l := by
  classical
  unfold Run.nuAnc
  refine Finset.card_le_card fun Y hY => ?_
  exact Finset.mem_filter.2 ⟨C.Ycl_ancestors hY, C.Ycl_round hY⟩

open Classical in
/-- `∑_Y m_{Y,l} ≤ ∑_{(Y,l) giant} m_{Y,l} + |classes| · 2γ_l`. -/
theorem sum_mY_le (C : JslcCtx run G δ S l B J R) :
    ∑ Y ∈ Step2.classes run G δ S l, (mY run G δ Y l : ℝ) ≤
      ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l), (mY run G δ Y l : ℝ) +
        ((Step2.classes run G δ S l).card : ℝ) * (2 * (gammaL run G l : ℝ)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Step2.classes run G δ S l)
    (fun Y => IsGiant run G δ Y l)]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
    intro Y hY
    obtain ⟨hY, hg⟩ := Finset.mem_filter.1 hY
    exact Finset.mem_filter.2 ⟨C.Ycl_ancestors hY, hg⟩
  · calc ∑ Y ∈ (Step2.classes run G δ S l).filter (fun Y => ¬ IsGiant run G δ Y l),
          (mY run G δ Y l : ℝ)
        ≤ ∑ Y ∈ (Step2.classes run G δ S l).filter (fun Y => ¬ IsGiant run G δ Y l),
          (2 * (gammaL run G l : ℝ)) := by
          refine Finset.sum_le_sum fun Y hY => ?_
          have := C.mY_le_of_not_isGiant (Finset.mem_filter.1 hY).2
          exact_mod_cast this
      _ ≤ ∑ Y ∈ Step2.classes run G δ S l, (2 * (gammaL run G l : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `γ_l ≤ P_{l−2}/M_l`. -/
theorem gammaL_le_real : (gammaL run G l : ℝ) ≤ (run.P G (l - 2) : ℝ) / (run.M G l : ℝ) :=
  Nat.floor_le (by positivity)

/-- The arithmetic of Step 8. -/
theorem step8_arith {n x p ν γ g : ℝ} (hn : 0 ≤ n) (hx : 1 ≤ x) (hp : x ^ 13 ≤ p)
    (hν : ν ≤ 2.74 * n / p) (hγ0 : 0 ≤ γ) (hγ : γ ≤ p / x) (hg : 0 ≤ g) :
    g + ν * (2 * γ + 2 * x) + n * x / x ^ 2 ≤ 126 * n / x + 1.5 * g := by
  have hx0 : 0 < x := by linarith
  have hx2 : x ^ 2 ≤ p := by
    have : x ^ 2 ≤ x ^ 13 := pow_le_pow_right₀ hx (by norm_num)
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hx2
  -- `ν γ ≤ 2.74 n / x`
  have t1 : ν * γ ≤ 2.74 * n / x := by
    calc ν * γ ≤ (2.74 * n / p) * (p / x) := mul_le_mul hν hγ hγ0 (by positivity)
      _ = 2.74 * n / x := by field_simp
  -- `ν x ≤ 2.74 n / x`
  have t2 : ν * x ≤ 2.74 * n / x := by
    calc ν * x ≤ (2.74 * n / p) * x := mul_le_mul_of_nonneg_right hν hx0.le
      _ = 2.74 * n * x / p := by ring
      _ ≤ 2.74 * n * x / x ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hx2
      _ = 2.74 * n / x := by field_simp
  have t3 : n * x / x ^ 2 = n / x := by field_simp
  have t4 : 0 ≤ n / x := by positivity
  have e1 : 126 * n / x = 126 * (n / x) := by ring
  have e2 : 2.74 * n / x = 2.74 * (n / x) := by ring
  rw [t3, e1]
  rw [e2] at t1 t2
  nlinarith

end EG.Chain.JSLC
