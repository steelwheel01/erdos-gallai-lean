module

public import EG.Spec.Quot.Cand
public import EG.Lib.Quot.CandCount
public import EG.Lib.Lend.Standing
public import EG.Lib.Found.Gamma
public import EG.Lib.Prob.Chernoff
public import EG.Proof.Lend.COLJVCount
public import EG.Proof.HB.TowerA
public import EG.Proof.HB.TowerBM
public import EG.Proof.Todo.TowerD
public import EG.Proof.Todo.StructureExp

/-!
# P3 stub: `EG.Spec.CandCountStatement` (s7:lemCand)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CandCount`; consumers import this module.

Proof (manuscript s7:lemCand): (i) and the first equality of (ii) are
`EG/Lib/Quot/CandCount.lean` (the stage-1 law is a product of the colour and pool coordinates).
(ii) "`H_Y` has minimum degree larger than `s_Y ≥ s_r/2`, and `s_r ≥ λ_r^{100}`"
(Proposition s2:propStructure (i), `EG.Todo.StructureExp`); "`p_Y ≥ λ_r^{-4}`" (Lemma
s3:lemCOLJV, `EG.colJVCount`); "`λ_r ≥ λ_{l-2}`" (Lemma s2:lemTower (a), `EG.towerA`);
"`λ_r ≥ 2^{l-r}`" (Lemma s2:lemTower (d), `EG.Todo.TowerD`). (iii) the lower-tail Chernoff bound
with deviation `1/2` (Cited result s1:citChernoffGen, `EG.FinDist.chernoffGen_lower_half_on`).
(iv) from JV-goodness and (ii); `Hcd_l ≥ 2^{10}M_l^{10}` from `M_l ≤ λ_{l-2}^{1.6}` (Lemma
s2:lemTower (b), `EG.towerBM`). The pool labels form a probability law since
`Σ_{l,r} q_l π_{l,r} < 1` (`EG.Stage1.poolMass_lt_one`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot EG.Stage1 EG.FinDist

universe u

/-- [s7:lemCand], `EG.Spec.CandCountStatement` for vertex types of every universe (the Spec is
stated on `Type`; this form is used by the universe-polymorphic Lemma s7:lemEXprime). -/
theorem candCount_univ :
  ∀ (V : Type u) [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : Run V) (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ (Sω : Stage1.Outcome G run → StageData V),
      (∀ ω Y l, (Sω ω).ljv Y l = (Stage1.LJV G run Y (ω.colAt Y) l).edges) →
    ∀ (l : ℕ) (u : V), 3 ≤ l → u ∈ classedPorts run G l →
      -- (i) the sum of the indicators over `N_{H_Y}(u)`
      (∀ ω : Stage1.Outcome G run,
          ((cand G δ (Sω ω) ω.pool l u).card : ℝ) =
            ∑ w ∈ (run.ancGraph G (δ l u)).nbrs u,
              (if Stage1.plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
                (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) ∧
      -- (i) the summands are mutually independent
      (Stage1.law G run).iIndepFun
        (fun (w : ↥((run.ancGraph G (δ l u)).nbrs u)) (ω : Stage1.Outcome G run) =>
          (if Stage1.plabOf ω.pool (w : V) = some (l, (δ l u).1) then (1 : ℝ) else 0) *
            (if s(u, (w : V)) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) ∧
      -- (i) each is Bernoulli with success probability `q_l π_{l,r} p_Y`
      (∀ w ∈ (run.ancGraph G (δ l u)).nbrs u,
          (Stage1.law G run).prob {ω |
            (if Stage1.plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
              (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) = 1} =
            Stage1.qPool G run l * Stage1.piPool l (δ l u).1 * Stage1.pY G run (δ l u)) ∧
      -- (ii) `E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u) ≥ λ_r^{96} 2^{-(l-r)}/M_l^2 ≥ 2Hcd_l`
      (Stage1.law G run).expect (fun ω => ((cand G δ (Sω ω) ω.pool l u).card : ℝ)) =
        candMean run G δ l u ∧
      run.lam G (δ l u).1 ^ 96 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) / (run.M G l : ℝ) ^ 2 ≤
        candMean run G δ l u ∧
      2 * Hcd run G l ≤
        run.lam G (δ l u).1 ^ 96 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) / (run.M G l : ℝ) ^ 2 ∧
      -- (iii) `P(u is JV-bad) ≤ exp(−Hcd_l/4)`
      (Stage1.law G run).prob {ω | JVBad run G δ (Sω ω) ω.pool l u} ≤
        Real.exp (-(Hcd run G l) / 4) ∧
      -- (iv) JV-good ⇒ `|Cand_l(u)| ≥ Hcd_l`, and `Hcd_l ≥ 2^{10} M_l^{10}`
      (∀ (S : StageData V) (π : ↥G.verts → Option (ℕ × ℕ)),
          ¬ JVBad run G δ S π l u → Hcd run G l ≤ ((cand G δ S π l u).card : ℝ)) ∧
      (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ Hcd run G l := by
  intro V _ N0 Dstar G run δ hR hδ Sω hS l u hl hu
  obtain ⟨hΓ1, -, -, -, hd1, hrun⟩ := hR
  obtain ⟨a, ha, hua⟩ := (Chain.mem_classedPorts run G).1 hu
  have hY := hδ.mem_ancestors hl ha hua
  have hr1 := hδ.one_le_round hl ha hua
  have hr2 := hδ.round_add_two_le hl ha hua
  have huY := hδ.mem_ancVerts hl ha hua
  have hlR : l ≤ run.R := by
    by_contra h
    have h0 := Chain.classedPorts_eq_empty_of_not_isRound run G (l := l) (fun h' => h h'.2)
    rw [h0] at hu
    exact absurd hu (Finset.notMem_empty _)
  have hBM := EG.towerBM V G Dstar run hΓ1.1 hrun hd1
  have hm : poolMass G run ≤ 1 := (poolMass_lt_one G run hΓ1.1.two_lt hBM.2).le
  have hsub := fun ω => ljv_subset_ancGraph hS ω (δ l u) l
  have hE := expect_card_cand δ Sω hS hm l u hY hr1 hr2 hlR
  -- `λ_r`, `λ_{l-2}`, `M_l`
  have hRr : run.IsRound (δ l u).1 := ⟨hr1, by omega⟩
  obtain ⟨-, hLpos, -⟩ := Standing.lam_facts hΓ1 hrun hRr
  have hRl2 : run.IsRound (l - 2) := ⟨by omega, by omega⟩
  obtain ⟨-, hL'pos, -⟩ := Standing.lam_facts hΓ1 hrun hRl2
  have hlam_ge := Standing.lam_ge hΓ1 hrun hRl2
  have hM1 : (1 : ℝ) ≤ (run.M G l : ℝ) := by
    have := two_pow_le_M G run l
    exact_mod_cast le_trans Nat.one_le_two_pow this
  have hM0 : (0 : ℝ) < (run.M G l : ℝ) := by linarith
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) := zpow_pos (by norm_num) _
  -- (ii): `E|Cand_l(u)| ≥ λ_r^{96} 2^{-(l-r)}/M_l^2`
  have hq : qPool G run l = 1 / (run.M G l : ℝ) ^ 2 := by
    unfold qPool
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, one_div]
  have hπ : piPool l (δ l u).1 = 2 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) := by
    unfold piPool
    rw [← zpow_one_add₀ (by norm_num)]
    congr 1
    ring
  have hp : 1 / run.lam G (δ l u).1 ^ 4 ≤ pY G run (δ l u) := by
    have h := ((EG.colJVCount V G Dstar run hΓ1 hrun (δ l u) hY).2 (by omega)).2.2.2.2.2.2.2.2
    have e : run.lam G (δ l u).1 ^ (-4 : ℝ) = 1 / run.lam G (δ l u).1 ^ 4 := by
      rw [Real.rpow_neg hLpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        one_div]
    rw [← e]
    exact h
  have hSE := Todo.StructureExp V G Dstar run hΓ1.1.gamma2a hrun
  have hd : run.lam G (δ l u).1 ^ 100 / 2 ≤ ((run.ancGraph G (δ l u)).deg u : ℝ) := by
    have h3 := (hSE.2.2.1 (δ l u) hY).2 u (by rw [Run.ancGraph_verts]; exact huY)
    have h4 := (hSE.2.2.2 (δ l u).1 (Finset.mem_Icc.2 ⟨hr1, by omega⟩)).2
    have h5 : (run.s G (δ l u).1 : ℝ) / 2 ≤ run.ancS G (δ l u) := by
      have hs : (0 : ℝ) ≤ (run.s G (δ l u).1 : ℝ) := Nat.cast_nonneg _
      unfold Run.ancS
      split_ifs
      · exact le_rfl
      · linarith
    linarith
  have hmean_lb : run.lam G (δ l u).1 ^ 96 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) /
      (run.M G l : ℝ) ^ 2 ≤ candMean run G δ l u :=
    candMean_lower_arith hM0 hLpos ht0 hq hπ hp hd
  -- (ii): `λ_r^{96} 2^{-(l-r)}/M_l^2 ≥ 2Hcd_l`
  have hLL' : run.lam G (l - 2) ≤ run.lam G (δ l u).1 :=
    (EG.towerA V G Dstar run hΓ1.1 hrun hd1).2.2.2.2 (δ l u).1 l hr1 hr2 (by omega)
  have hLt : 1 ≤ run.lam G (δ l u).1 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) := by
    have hD := Todo.TowerD V G Dstar run hΓ1.1 hrun hd1 (δ l u).1 l hr1 (by omega) hlR
    have h2 : (2 : ℝ) ^ (l - (δ l u).1) ≤ run.lam G (δ l u).1 :=
      hD.2.2.trans (hD.2.1.trans hD.1)
    have e : (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) * (2 : ℝ) ^ (l - (δ l u).1) = 1 := by
      rw [show ((l : ℤ) - (δ l u).1) = ((l - (δ l u).1 : ℕ) : ℤ) by
        push_cast [Nat.cast_sub (by omega : (δ l u).1 ≤ l)]; ring, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (by positivity)]
    nlinarith
  have htwo : 2 * Hcd run G l ≤ run.lam G (δ l u).1 ^ 96 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) /
      (run.M G l : ℝ) ^ 2 :=
    twoHcd_le_arith hM0 hL'pos hLL' hLt
  -- (iv): `Hcd_l ≥ 2^{10} M_l^{10}`
  have hHcd : (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ Hcd run G l := by
    have hML := hBM.1 l (by omega) hlR
    exact Hcd_ge_arith hM1 (hML.1.trans hML.2) (le_trans (by norm_num) hlam_ge)
  have hmean0 : 0 ≤ candMean run G δ l u := le_trans (by positivity) hmean_lb
  refine ⟨fun ω => card_cand_eq_sum δ (Sω ω) ω.pool l u (hsub ω),
    iIndepFun_candSummand δ Sω hS l u hY,
    fun w hw => prob_candSummand_eq_one δ Sω hS hm l u hY hr1 hr2 hlR hw,
    hE, hmean_lb, htwo, ?_, ?_, hHcd⟩
  · -- (iii) the lower-tail Chernoff bound
    have hset : {ω | JVBad run G δ (Sω ω) ω.pool l u} =
        {ω | ∑ w ∈ (run.ancGraph G (δ l u)).nbrs u,
          (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
            (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) <
          candMean run G δ l u / 2} := by
      ext ω
      simp only [Set.mem_ofPred_eq, JVBad]
      rw [card_cand_eq_sum δ (Sω ω) ω.pool l u (hsub ω)]
      exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
    rw [hset]
    have hI : ∀ w ∈ (run.ancGraph G (δ l u)).nbrs u, ∀ ω : Outcome G run,
        (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) = 0 ∨
        (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) = 1 := by
      intro w _ ω
      by_cases h1 : plabOf ω.pool w = some (l, (δ l u).1) <;>
        by_cases h2 : s(u, w) ∈ (Sω ω).ljv (δ l u) l <;> simp [h1, h2]
    have hEs : candMean run G δ l u ≤ (law G run).expect (fun ω =>
        ∑ w ∈ (run.ancGraph G (δ l u)).nbrs u,
          (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
            (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) := by
      rw [← hE]
      exact le_of_eq (congrArg _ (funext fun ω =>
        (card_cand_eq_sum δ (Sω ω) ω.pool l u (hsub ω))))
    have hch := chernoffGen_lower_half_on (μ := law G run)
      ((run.ancGraph G (δ l u)).nbrs u) hI (iIndepFun_candSummand δ Sω hS l u hY) hmean0 hEs
    refine hch.trans (Real.exp_le_exp.2 ?_)
    linarith
  · -- (iv) a JV-good port has `|Cand_l(u)| ≥ ½E|Cand_l(u)| ≥ Hcd_l`
    intro S π hgood
    have h : ¬ (((cand G δ S π l u).card : ℝ) < candMean run G δ l u / 2) :=
      fun h => hgood ⟨hu, h⟩
    push Not at h
    linarith

/-- Proved in P3. [s7:lemCand] see `EG.Spec.CandCountStatement`. -/
theorem CandCount : EG.Spec.CandCountStatement := candCount_univ.{0}

end EG.Todo
