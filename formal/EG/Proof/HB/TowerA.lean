module

public import EG.Spec.HB.TowerA
public import EG.Lib.HB.TowerDeg
public import EG.Proof.Todo.DegRec

/-!
# Declared-input stub of unit P3B: Lemma "tower facts" (a) (manuscript s2:lemTower (a))

[s6:thmCONC] (iii), [s6:thmCONCL] (iv) and (s6:eqTowerHalf) use [s2:lemTower] (a)
(`R - r ≤ 2 log* d_r + 2` for the number of rounds in which an ancestor is a class, and
`λ_r ≥ d_{r+1}^{1/A}` for the halving of the tower functions). Its proof (s2.tex, proof of
lemTower (a)) needs [s2:propDegRec] (`d_{r+1} ≤ λ_r^A`), [s2:propStructure] (iii) and the `log*`
induction; these are not nodes of probe P-3. Owner: the s2 tower unit; the full Tower Spec must
import `EG/Spec/HB/TowerA.lean` and must not restate (a). Justification: design note
`formal/work/p2b/P3B.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:lemTower] (a) "`λ_r ≥ d_{r+1}^{1/A}` for `r ≤ R`; `d_{r+2} ≤ λ_r` for
`r ≤ R-1`; `R - r ≤ 2 log* d_r - 1`, in particular `R - r ≤ 2 log* d_r + 2` (`r ≤ R`); and
`λ_r ≥ λ_{l-2}` whenever `r ≤ l-2 ≤ R`." Owner: s2 tower unit (blueprint s2b,
`TowerAStatement`). -/
theorem towerA : EG.Spec.TowerAStatement := by
  intro V _ G Dstar run hD hv _
  have hDR := EG.Todo.DegRec
  have h2 : ∀ r : ℕ, 1 ≤ r → r + 1 ≤ run.R → run.d G (r + 2) ≤ run.lam G r :=
    fun r hr1 hr => EG.HB.Run.d_add_two_le hDR hD hv hr1 hr
  -- `R - r ≤ 2 log* d_r - 1`
  have h3 : ∀ r ∈ Finset.Icc 1 run.R, run.R < r + 2 * logStar (run.d G r) := by
    intro r hr
    obtain ⟨hr1, hrR⟩ := Finset.mem_Icc.1 hr
    by_contra hcon
    push Not at hcon
    set k := logStar (run.d G r)
    have hind : ∀ i ≤ k, run.d G (r + 2 * i) ≤ logIter i (run.d G r) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have hi' := ih (by omega)
        have hri : r + 2 * i ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
        have hpos := (EG.HB.Run.paramHyp hD hv hri).d_pos
        have e : r + 2 * (i + 1) = r + 2 * i + 2 := by ring
        rw [e, logIter_succ']
        exact (h2 (r + 2 * i) (by omega) (by omega)).trans
          (Real.logb_le_logb_of_le (by norm_num) hpos hi')
    have hk := hind k le_rfl
    have hk1 := logIter_logStar_le_one (run.d G r)
    have hrk : r + 2 * k ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hcon⟩
    have := (EG.HB.Run.paramHyp hD hv hrk).two_lt
    linarith
  refine ⟨?_, h2, ?_, ?_, ?_⟩
  · intro r hr
    have h1 := EG.HB.Run.d_succ_le_lamA hDR hD hv hr
    have hl0 : 0 ≤ run.lam G r := (EG.HB.Run.paramHyp hD hv hr).lam_pos.le
    have hA : (Aexp : ℕ) ≠ 0 := by norm_num [Aexp]
    calc run.d G (r + 1) ^ ((1 : ℝ) / (Aexp : ℝ))
        ≤ (run.lam G r ^ Aexp) ^ ((1 : ℝ) / (Aexp : ℝ)) :=
          Real.rpow_le_rpow (EG.HB.Run.d_nonneg run G _) h1 (by positivity)
      _ = run.lam G r := by rw [one_div, Real.pow_rpow_inv_natCast hl0 hA]
  · intro r hr
    have := h3 r hr
    omega
  · intro r hr
    have := h3 r hr
    omega
  · intro r l hr1 hrl hl
    have hl2 : l - 2 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hpos := (EG.HB.Run.paramHyp hD hv hl2).d_pos
    exact Real.logb_le_logb_of_le (by norm_num) hpos (EG.HB.Run.d_anti run G (by omega))

end EG
