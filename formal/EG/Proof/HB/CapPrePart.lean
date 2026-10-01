module

public import EG.Spec.HB.CapPrePart
public import EG.Proof.Todo.CapRound

/-!
# Declared-input stub of unit P2J: Lemma-25 size cap, part (ii) (manuscript s2:lemCap (ii))

One of the two `sorry`s of unit P2J (probe P-2, part 2; the other is `EG.towerBLate`
(`EG/Proof/HB/TowerBLate.lean`); Lemma EL, `EG.edgeLaminarity`, first a stub of unit P3A, is now
proved, and `EG.structureHY` (`EG/Proof/HB/StructureHY.lean`) was proved in fix round 1). Lemma
s2:lemCap (ii) is cited by the proofs of Lemma JS-LC [s6:lemJSLC] and Lemma J⁺ [s6:lemJplus] (J2);
its proof needs Cited result s1:citLem25 (`EG.bmLemma25`) and the (R2) parameter algebra, which are
not nodes of probe P-2. Justification: design note `formal/work/p2b/P2J.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:lemCap] (ii) "In every round `l ≤ R` of a valid `HB^tp` run, every
`s = 0` piece `𝒫` satisfies `|𝒫| ≤ M_l`. Hence every round-`l` pre-part has `|Z^0| ≤ M_l`; for
every round-`l` part `Z` (light or standalone) every vertex is incident with at most `M_l − 1`
edges of `E_l(Z)`". Owner: s2 structure unit (blueprint s2b). -/
theorem capPrePart : EG.Spec.CapPrePartStatement := by
  intro V _ G Dstar run hD hv l hl
  have hr : run.IsRound l := Finset.mem_Icc.1 hl
  obtain ⟨h1, h2, -⟩ := EG.Todo.CapRound V (run.graph G l) (run.choice l) Dstar hD
    (hv.1 l hl).1 (hv.1 l hl).2
  refine ⟨?_, ?_⟩
  · rw [EG.HB.Run.pieceAddrs_of_isRound run hr]; exact h1
  · rw [EG.HB.Run.prePartAddrs_of_isRound run G hr]
    intro a ha
    have hE : run.E G l a = EG.HB.Round.E (run.graph G l) (run.choice l) a := if_pos hr
    rw [hE]
    exact h2 a ha

end EG
