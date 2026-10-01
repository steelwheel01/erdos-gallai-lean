module

public import EG.Spec.HB.OVRunK
public import EG.Proof.Todo.OVRound

/-!
# Declared-input stubs of unit P3B: Proposition OV on runs, (K1) and (K3) (manuscript s2:propOV)

[s6:thmCONC] (iii) and [s6:thmCONCL] (iv) use (K1) (at most `1.37 n/P_r` ancestors of round `r`,
`Σ|Z^0| ≤ 1.37 n`) and (K3) (`Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n/log P_r`); [s2:propOrigin] (c) is (K3).
Their proof (s2.tex, proof of propOV: the composite tree, Lemma OV at `c = 1.6`, the LCA argument)
needs [s2:lemCap] (ii) and the OV transport along the graft; these are not nodes of probe P-3.
Owner: the s2 overlap unit; the full propOV Spec must import `EG/Spec/HB/OVRunK.lean` and must not
restate (K1), (K3). Justification: design note `formal/work/p2b/P3B.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:propOV] (K1) "`Σ|Z^0| ≤ 1.37 n`, the sum over the round-`r` pre-parts;
`|Std_r| ≤ 1.37 n/P_r`; the number of ancestors of round `r` is at most `1.37 n/P_r` …; hence the
number `ν_l` of ancestors of rounds at most `l-2` satisfies `ν_l ≤ 1.37 n Σ_{r ≤ l-2} P_r^{-1}`."
Owner: s2 overlap unit (blueprint s2b, `OVRunStatement`). -/
theorem ovK1 : EG.Spec.OVK1Statement := by
  classical
  intro V _ G Dstar run hD hv
  have hround : ∀ r ∈ Finset.Icc 1 run.R,
      ((∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a).card : ℕ) : ℝ) ≤ 1.37 * (G.card : ℝ) ∧
      ((run.Std G r).card : ℝ) ≤ 1.37 * (G.card : ℝ) / (run.P G r : ℝ) ∧
      (((run.ancestors G).filter (fun Y => Y.1 = r)).card : ℝ) ≤
        1.37 * (G.card : ℝ) / (run.P G r : ℝ) := by
    intro r hr
    have hR : run.IsRound r := Finset.mem_Icc.1 hr
    obtain ⟨-, -, -, hK1a, hK1b, hK1c, -⟩ :=
      EG.Todo.OVRound V (run.graph G r) (run.choice r) Dstar hD (hv.1 r hr).1 (hv.1 r hr).2
    have hn : ((run.graph G r).card : ℝ) = (G.card : ℝ) := by rw [EG.HB.Run.card_graph]
    have hP := EG.HB.Run.prePartAddrs_of_isRound run G hR
    rw [hn] at hK1a hK1b hK1c
    refine ⟨by rw [hP]; exact hK1a, ?_, ?_⟩
    · unfold EG.HB.Run.Std; rw [hP]; exact hK1b
    · rw [EG.HB.Run.card_ancestors_filter, hP]; exact hK1c
  refine ⟨hround, fun l => ?_⟩
  have h := EG.HB.Run.nuAnc_le_sum run G l
  have h' : (run.nuAnc G l : ℝ) ≤ ∑ r ∈ (Finset.Icc 1 run.R).filter (fun r => r + 2 ≤ l),
      (((run.ancestors G).filter (fun Y => Y.1 = r)).card : ℝ) := by exact_mod_cast h
  refine h'.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have := (hround r (Finset.mem_filter.1 hr).1).2.2
  rw [mul_one_div]; exact this

/-- Proved in P3. [s2:propOV] (K3) "the total size `Σ|Z^0|` of the round-`r` pre-parts failing
(L1) is at most `30.4 ε n / log P_r`, and `Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n / log P_r`, the sum over
all round-`r` pre-parts `Y`." Owner: s2 overlap unit (blueprint s2b, `OVRunStatement`). -/
theorem ovK3 : EG.Spec.OVK3Statement := by
  classical
  intro V _ G Dstar run hD hv r hr
  have hR : run.IsRound r := Finset.mem_Icc.1 hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hK3a, hK3b, -⟩ :=
    EG.Todo.OVRound V (run.graph G r) (run.choice r) Dstar hD (hv.1 r hr).1 (hv.1 r hr).2
  have hn : ((run.graph G r).card : ℝ) = (G.card : ℝ) := by rw [EG.HB.Run.card_graph]
  have hP := EG.HB.Run.prePartAddrs_of_isRound run G hR
  have hDS : run.DupStar G r = EG.HB.Round.DupStar (run.graph G r) (run.choice r) := if_pos hR
  rw [hn] at hK3a hK3b
  refine ⟨?_, ?_⟩
  · rw [hP]; exact hK3a
  · rw [hP, hDS]; exact hK3b

end EG
