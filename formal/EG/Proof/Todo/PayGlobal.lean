module

public import EG.Spec.Quot.Pay
public import EG.Proof.Todo.Pay
public import EG.Proof.Todo.Fresh
public import EG.Proof.HB.TowerBM
public import EG.Lib.Found.Gamma

/-!
# P3 stub: `EG.Spec.PayGlobalStatement` (s7:lemPay)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.PayGlobal`; consumers import this module.

Proof (manuscript s7:lemPay (b), (d), run level): the per-round bounds of `EG.Todo.Pay`
("at most one unpaired fresh leg per fresh centre", "`pay^rd_l ≤ 2n/M_l`"), summed over the
rounds; "`Σ_{l,Z}|F_Z| ≤ 2n` by Proposition s2:propParentless(i)" (`EG.Todo.Fresh`); and
"`Σ_l pay^rd_l ≤ 2n Σ_l 1/M_l ≤ 4n/D_* ≤ 9n/D_*` by Lemma s2:lemTower(b)" (`EG.towerBM`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:lemPay] see `EG.Spec.PayGlobalStatement`. -/
theorem PayGlobal : EG.Spec.PayGlobalStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω Js hJs Rs hRs
  have hP := fun l (hl : l ∈ Finset.Icc 3 run.R) =>
    Todo.Pay V G N0 Dstar run δ hR hδ ω hω l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2
      (Js l) (hJs l hl) (pastOf run G δ ω l (Js l)) rfl (Rs l) (hRs l hl)
  obtain ⟨hΓ1, -, -, -, hd1, hrun⟩ := hR
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- (b): at most `Σ_{a ∈ Std_l} |F_Z|` unpaired fresh legs per round
    calc ∑ l ∈ Finset.Icc 3 run.R, (Rs l).unpairedLegs.card
        ≤ ∑ l ∈ Finset.Icc 3 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card :=
          Finset.sum_le_sum fun l hl => (hP l hl).2.2.2.2.1
      _ ≤ ∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card :=
          Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
  · -- "`Σ_{l,Z}|F_Z| ≤ 2n` by Proposition s2:propParentless(i)"
    exact_mod_cast (Todo.Fresh V G Dstar run hrun).2.2.2.2
  · -- (d): `pay^rd_l ≤ 2n/M_l`, and `Σ_l 1/M_l ≤ 2/D_*`
    intro ξs hξ
    have hD2 : 2 < Dstar := hΓ1.1.two_lt
    have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
    have hM := (EG.towerBM V G Dstar run hΓ1.1 hrun hd1).2
    have h1 : ∀ l ∈ Finset.Icc 3 run.R,
        ((Rs l).payrd (ξs l) : ℝ) ≤ 2 * (G.card : ℝ) * ((1 : ℝ) / (run.M G l : ℝ)) := by
      intro l hl
      have hd := (hP l hl).2.2.2.2.2.2.2.2.2
      have := (hd.1 (ξs l) (hξ l hl)).trans hd.2.1
      rw [mul_one_div]
      exact this
    have h2 : ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) ≤ 2 / Dstar :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
        (fun _ _ _ => by positivity)).trans hM
    calc ∑ l ∈ Finset.Icc 3 run.R, ((Rs l).payrd (ξs l) : ℝ)
        ≤ ∑ l ∈ Finset.Icc 3 run.R, 2 * (G.card : ℝ) * ((1 : ℝ) / (run.M G l : ℝ)) :=
          Finset.sum_le_sum h1
      _ = 2 * (G.card : ℝ) * ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (G.card : ℝ) * (2 / Dstar) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 9 * (G.card : ℝ) / Dstar := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right (by linarith)]
          nlinarith

end EG.Todo
