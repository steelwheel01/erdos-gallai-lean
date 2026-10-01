module

public import EG.Spec.HB.TowerBLate
public import EG.Lib.HB.TowerDeg
public import EG.Proof.Todo.DegRec
public import EG.Proof.HB.OVRunK

/-!
# Declared-input stub of unit P2J: Lemma "tower facts" (b), late-round clauses (manuscript
s2:lemTower (b))

One of the two `sorry`s of unit P2J (probe P-2, part 2; the other is `EG.capPrePart`
(`EG/Proof/HB/CapPrePart.lean`); Lemma EL, `EG.edgeLaminarity`, first a stub of unit P3A, is now
proved, and `EG.structureHY` (`EG/Proof/HB/StructureHY.lean`) was proved in fix round 1). Step 8 of
the proof of Lemma JS-LC [s6:lemJSLC] cites these clauses; their proof needs the (R2) parameter
algebra and the overlap count (K1) of s2:propOV, which are not nodes of probe P-2. Justification:
design note `formal/work/p2b/P2J.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:lemTower] (b) "For `3 ≤ l ≤ R`: … `P_{l−2} ≥ M_l^{13}` … Finally,
completing (K1) of Proposition s2:propOV, the number `ν_l` of ancestors of rounds at most `l − 2`
satisfies `ν_l ≤ 2.74 n/P_{l−2}` for `3 ≤ l ≤ R`." Owner: s2 tower unit (blueprint s2b). -/
theorem towerBLate : EG.Spec.TowerBLateStatement := by
  intro V _ G Dstar run hD hv _ l hl3 hl
  have hDR := EG.Todo.DegRec
  have hl2 : l - 2 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hp := EG.HB.Run.paramHyp hD hv hl2
  have hP := EG.HB.ParamHyp.P_ge (d := run.d G (l - 2))
  rw [EG.Cp_eq] at hP
  have hPpos : (0 : ℝ) < run.P G (l - 2) := lt_of_lt_of_le (pow_pos hp.lam_pos _) hP
  refine ⟨?_, ?_⟩
  · -- `M_l^{13} ≤ λ_{l-2}^{20.8} ≤ λ_{l-2}^{103} ≤ P_{l-2}`
    have hM := (EG.HB.Run.M_le_Amu hDR hD hv hl3 hl).trans hp.Amu_pow_2A_le_lam
    set x := run.lam G (l - 2)
    have hx1 : 1 ≤ x := hp.one_le_lam
    have h1 : (run.M G l : ℝ) ^ 13 ≤ (x ^ (1.6 : ℝ)) ^ 13 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hM 13
    have h2 : (x ^ (1.6 : ℝ)) ^ 13 ≤ x ^ 103 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast x 103]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have : ((run.M G l ^ 13 : ℕ) : ℝ) ≤ run.P G (l - 2) := by
      push_cast; exact h1.trans (h2.trans hP)
    exact_mod_cast this
  · have hK := (EG.ovK1 V G Dstar run hD.gamma2a hv).2 l
    have hset : (Finset.Icc 1 run.R).filter (fun r => r + 2 ≤ l) = Finset.Icc 1 (l - 2) := by
      ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hset] at hK
    have hs := EG.HB.Run.sum_inv_P_le hDR hD hv (k := l - 2) (by omega) (by omega)
    have hn : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
    calc (run.nuAnc G l : ℝ) ≤ 1.37 * (G.card : ℝ) *
          ∑ r ∈ Finset.Icc 1 (l - 2), 1 / (run.P G r : ℝ) := hK
      _ ≤ 1.37 * (G.card : ℝ) * (2 * (1 / (run.P G (l - 2) : ℝ))) := by gcongr
      _ = 2.74 * (G.card : ℝ) / (run.P G (l - 2) : ℝ) := by ring

end EG
