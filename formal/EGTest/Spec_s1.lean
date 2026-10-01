import EG.Spec.Found.FactAdd
import EG.Spec.Found.Chernoff
import EG.Spec.Found.Markov
import EG.Spec.Found.Hall
import EG.Spec.Ext.BMProp8
import EG.Spec.Ext.BMProp12
import EG.Spec.Ext.BMDef11
import EG.Spec.Ext.Lovasz
import EG.Spec.Gamma.Cond
import EG.Lib.Found.Fnum
import EG.Lib.Found.FGraphFnum
import EG.Lib.Found.Graph
import EG.Lib.Found.Gamma
import EG.Lib.Found.PathDecomp
import EG.Lib.Gamma.Full
import EG.Lib.Prob.Basic
import EG.Lib.Prob.Chernoff
import EG.Proof.Gamma.Sat
import Mathlib.Combinatorics.Hall.Basic

/-! Cheap non-vacuity checks for the s1 Specs written by the P2 s1 Spec unit
(`formal/work/p2s/s1.md`).

Where an existing Lib (or Mathlib) theorem already proves a new Spec, the check derives the Spec
from it: this shows that the hypotheses are the intended ones and that the statement is not
stronger than what the library proves. Where no such theorem exists (Propositions 8 and 12 of
[BM], Lovász), the check shows that the hypotheses are satisfiable, or that the conclusion is
satisfiable for a trivial instance.

Not checked: for `BMProp8Statement`, satisfiability of the ball hypothesis on a nontrivial
graph (it needs an explicit computation of `EG.ball`); the degenerate case `t = 0` is excluded
by the hypothesis `1 ≤ t`.
-/

open EG EG.Spec

/-! ### s1:factAdd -/

example : FactAddAStatement := fun _ F _ => fnum_le_card F

example : FactAddBStatement := fun _ _ _ _ _ _ hd => fnum_union_le hd

example : FactAddCStatement := fun _ _ H _ _ hdisj _ hE =>
  H.fnum_edges_eq_add_of_disjoint_verts hE hdisj

example : FactAddDStatement := fun _ _ _ _ hE => by rw [hE]

example : FactAddDMonoStatement := fmax_mono

/-! ### s1:citChernoffGen, s1:citMarkov (derived from the Lib theorems) -/

example : ChernoffGenStatement := by
  intro Ω P ι _ I δ μ hI hind hδ0 hδ1
  refine ⟨fun hm => ?_, fun hm0 hm => ?_⟩
  · exact FinDist.chernoffGen_upper hI hind Finset.univ hm hδ0 hδ1
  · exact FinDist.chernoffGen_lower hI hind Finset.univ hm0 hm hδ0

example : ChernoffGenTailStatement := by
  intro Ω P ι _ I μ hI hind hm j _
  exact FinDist.chernoffGen_tail_exp hI hind Finset.univ hm j

example : MarkovStatement := fun _ P _ _ hX ha => P.prob_le_expect_div hX ha

example : MarkovAStatement := fun _ P _ hX => P.two_thirds_le_prob_le_three_mul_expect hX

example : MarkovBStatement := fun _ P _ _ h₁ h₂ => P.half_le_prob_le_four_mul_expect_and h₁ h₂

example : MarkovCondStatement := fun _ P A hA _ _ _ hX h₁ h₂ =>
  ⟨(P.cond A hA).two_thirds_le_prob_le_three_mul_expect hX,
    (P.cond A hA).half_le_prob_le_four_mul_expect_and h₁ h₂⟩

/-! ### s1:citChernoff: hypotheses satisfiable (`n = 0` on a one-point space) -/

example : ∃ (P : FinDist Unit) (I : Fin 0 → Unit → ℝ),
    (∀ i ω, I i ω = 0 ∨ I i ω = 1) ∧ P.iIndepFun I ∧ ∀ i, P.prob {ω | I i ω = 1} = (1 / 2 : ℝ) := by
  refine ⟨FinDist.dirac (), fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, fun i => Fin.elim0 i⟩
  intro s A
  have hs : s = ∅ := Finset.eq_empty_of_forall_notMem fun i => Fin.elim0 i
  subst hs
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, Set.ofPred_true, Finset.prod_empty]
  exact FinDist.prob_univ _

/-! ### s1:citHall (derived from Mathlib) -/

example : HallStatement := by
  intro ι α _ J T hJ
  classical
  have key := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun a : J => T a)).1 (by
      intro s
      have h := hJ (s.map (Function.Embedding.subtype _)) (by
        intro x hx
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
        exact y.2)
      rw [Finset.card_map] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      ext b
      simp)
  exact key

/-! ### s1:citDef11 remark (derived from the Lib theorems) -/

example : ExpanderEpsZeroStatement := fun _ _ _ _ => FGraph.isExpander_of_nonpos le_rfl

example : ExpanderMinDegStatement := by
  intro V _ G ε s hG hε hn
  refine ⟨fun v hv => ?_, hG.lt_minDeg hε hn⟩
  rw [← FGraph.deg_eq_degE]
  exact hG.lt_deg hε hn hv

/-! ### s1:citProp12: hypotheses satisfiable (edgeless graph on three vertices, `ε = 0`) -/

example : ∃ (G : FGraph (Fin 3)) (U : Finset (Fin 3)) (F : Finset (Sym2 (Fin 3))),
    G.IsExpander 0 1 ∧ U ⊆ G.verts ∧ 1 ≤ U.card ∧ (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 ∧
    F ⊆ G.edges ∧ (F.card : ℝ) ≤ 1 * (U.card : ℝ) / 2 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 := by
  refine ⟨⟨Finset.univ, ∅, by simp, by simp⟩, {0}, ∅, FGraph.isExpander_of_nonpos le_rfl,
    Finset.subset_univ _, by simp, ?_, by simp, by simp, by norm_num, le_rfl⟩
  simp [FGraph.card]

/-! ### s1:citProp8: the premises other than the ball condition are satisfiable -/

example : ∃ (G : FGraph (Fin 2)) (W : Finset (Fin 2)) (x y : Fin (2 * 1 - 1) → Fin 2),
    1 ≤ 1 ∧ 1 ≤ G.card ∧ W ⊆ G.verts ∧ 4 * 1 ≤ W.card + 2 ∧
    (∀ i, x i ∈ G.verts ∧ y i ∈ G.verts) ∧ Function.Injective (Sum.elim x y) := by
  refine ⟨⟨Finset.univ, {s(0, 1)}, by simp, by simp⟩, Finset.univ, fun _ => 0, fun _ => 1,
    le_rfl, by simp [FGraph.card], Finset.subset_univ _, by simp, by simp, ?_⟩
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (Fin.ext (by have := a.isLt; have := b.isLt; omega))
  · simp at h
  · simp at h
  · exact congrArg Sum.inr (Fin.ext (by have := a.isLt; have := b.isLt; omega))

/-! ### s1:citThm21 (Lovász): the conclusion holds for the edgeless graph -/

example {V : Type} [DecidableEq V] (Z : Finset V) :
    let H : FGraph V := ⟨Z, ∅, by simp, by simp⟩
    ∃ P C : List (List V), IsPathCycleDecomp (H.edges : Set (Sym2 V)) P C ∧
      2 * (P.length + C.length) ≤ H.card := by
  intro H
  refine ⟨[], [], ?_, by simp⟩
  rw [isPathCycleDecomp_nil_right]
  simpa [H] using isPathDecomp_nil

/-! ### s1:condGamma consequences -/

example : Gamma2aOfGamma1Statement := fun _ h => h.gamma2a

example : Gamma1UpwardStatement := fun _ _ h hD => h.mono hD

/-- The hypothesis `Gamma1 D` of `Gamma1TransferStatement` is satisfiable. -/
example : ∃ D : ℝ, Gamma1 D :=
  let ⟨_, D, _, h⟩ := exists_gammaCond
  ⟨D, h.gamma1⟩

example : ∀ D : ℝ, Gamma1core D → (2 : ℝ) ^ 256 ≤ Real.logb 2 D :=
  fun _ h => h.two_pow_256_le_logb

example : ∀ D : ℝ, Gamma1core D → ∀ d : ℝ, D ≤ d → Gamma1Items (Real.logb 2 (Real.logb 2 d)) :=
  fun _ h _ hd => h.items_loglog hd

/-- `Gamma1dOfABStatement` holds; item (a) alone suffices: with `x = μ/2^8 ≥ 1`,
`log₂μ = log₂x + 8` and `log₂x ≤ 2(x - 1)` (as `ln x ≤ x - 1` and `ln 2 > 1/2`). -/
example : Gamma1dOfABStatement := by
  intro μ ha _
  unfold Gamma1a at ha
  unfold Gamma1d
  have hμ0 : 0 < μ := lt_of_lt_of_le (by norm_num) ha
  have hx1 : 1 ≤ μ / 2 ^ 8 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hx0 : 0 < μ / 2 ^ 8 := lt_of_lt_of_le one_pos hx1
  have hsplit : Real.logb 2 μ = Real.logb 2 (μ / 2 ^ 8) + 8 := by
    rw [Real.logb_div hμ0.ne' (by norm_num)]
    have : Real.logb 2 ((2 : ℝ) ^ (8 : ℕ)) = 8 := by
      rw [Real.logb_pow]; simp
    linarith
  have hlog : Real.log (μ / 2 ^ 8) ≤ μ / 2 ^ 8 - 1 := Real.log_le_sub_one_of_pos hx0
  have hlog0 : 0 ≤ Real.log (μ / 2 ^ 8) := Real.log_nonneg hx1
  have hl2 : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hb : Real.logb 2 (μ / 2 ^ 8) ≤ 2 * (μ / 2 ^ 8 - 1) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  rw [hsplit]
  have : μ / 2 ^ 8 = μ / 256 := by norm_num
  rw [this] at hb
  linarith
