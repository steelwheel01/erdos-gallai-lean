module

public import EG.Spec.Quot.Ultra
public import EG.Proof.Todo.UltraIndep
public import EG.Lib.Prob.MaxLoad

/-!
# P3 stub: `EG.Spec.UltraMaxStatement` (s7:lemUltra)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UltraMax`; consumers import this module.

Proof (manuscript s7:lemUltra (ii)): `m_κ(h,w)` is the load of `w` among the junctions
`ω_1, …, ω_N` of the coloured hub items of `h` of colour `κ`; by (i) (`EG.Todo.UltraIndep`) these
are independent and each equals a given `w` with probability at most `1/(Hcd_l/2) = 2/Hcd_l`. The
bound `E[max_w m_w] ≤ log₂N + 2eμ* + 8`, `μ* = 2N/Hcd_l`, is `EG.FinDist.maxLoad_le`
(Chernoff tail bound s1:citChernoffGen, the tail-sum formula and the threshold
`T = max(⌈2eμ*⌉, ⌈log₂N⌉ + 1)`, `EG/Lib/Prob/MaxLoad.lean`).
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist

open EG.Spec in
/-- [s7:lemUltra] `EG.Spec.UltraMaxStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem UltraMax_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (h : V) (κ : ℕ), h ∈ I.hubs → I.ultra h → κ < 4 * I.M →
      1 ≤ (ultraItems R L h κ).card →
      (ordersLaw I.G).expect (fun O => ((I.pool.sup (fun w => R.mHub (L, O) κ h w) : ℕ) : ℝ)) ≤
        Real.logb 2 ((ultraItems R L h κ).card : ℝ) +
          2 * Real.exp 1 * (2 * ((ultraItems R L h κ).card : ℝ) / I.Hcd) + 8 := by
  intro V _ I hI R hR L h κ hh hult hκ hN
  classical
  obtain ⟨-, hind, hunif⟩ := Todo.UltraIndep_univ V I hI R hR L h κ hh hult hκ
  have hM : (0 : ℝ) < I.M := by exact_mod_cast lt_of_lt_of_le (by norm_num) hI.M_ge
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  have hp : ∀ it ∈ Spec.ultraItems R L h κ, ∀ w,
      (ordersLaw I.G).prob {O | R.junction (L, O) (.hub it.1 it.2) = some w} ≤ 2 / I.Hcd := by
    intro it hit w
    obtain ⟨hC, hP⟩ := hunif it hit
    rw [hP w]
    split_ifs
    · have hC0 : 0 < ((I.cand it.2 \ R.used L it.2).card : ℝ) := lt_of_lt_of_le (by positivity) hC
      rw [div_le_div_iff₀ hC0 hH]
      linarith
    · positivity
  have hload : ∀ O : Orders I.G, ∀ w, R.mHub (L, O) κ h w =
      load (Spec.ultraItems R L h κ)
        (fun it O => R.junction (L, O) (.hub it.1 it.2)) w O := by
    intro O w
    unfold Rules.mHub load Spec.ultraItems
    rw [Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun it _ => ?_
    simp only [and_assoc]
  have hmax := maxLoad_le (ordersLaw I.G) (Spec.ultraItems R L h κ) I.pool
    (fun it O => R.junction (L, O) (.hub it.1 it.2)) hind (by positivity) hp hN
  have e : (fun O : Orders I.G => ((I.pool.sup fun w => R.mHub (L, O) κ h w : ℕ) : ℝ)) =
      fun O => ((I.pool.sup fun w => load (Spec.ultraItems R L h κ)
        (fun it O => R.junction (L, O) (.hub it.1 it.2)) w O : ℕ) : ℝ) := by
    funext O
    simp only [hload O]
  rw [e]
  refine hmax.trans (le_of_eq ?_)
  ring

/-- Proved in P3. [s7:lemUltra] see `EG.Spec.UltraMaxStatement`. -/
theorem UltraMax : EG.Spec.UltraMaxStatement := UltraMax_univ.{0}

end EG.Todo
