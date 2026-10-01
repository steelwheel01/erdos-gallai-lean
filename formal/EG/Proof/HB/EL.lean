module

public import EG.Spec.HB.EL
public import EG.Lib.HB.GC

/-!
# Proof of Lemma EL, edge laminarity (manuscript s2:lemEL)

Unit P3A. Until fix round 1 of the proof stage this file held a declared-input stub; the
statement `EG.Spec.ELStatement` (locked, `EG/Spec/HB/EL.lean`) is unchanged, and it is now
proved here with 0 `sorry` (design note `formal/work/p2b/P3A.md`, "Fix round 1 (proof stage)").
The module docstring of the Spec file still calls the statement a declared input of P3A; that
file is locked, so the remark is left as is.

Proof. Let `Y = (r, a)` be an ancestor (a round-`r` pre-part address) and `l > r`. Edges only
disappear, so `E(G_l) ⊆ E(G_{r+1})`, and `E(G_{r+1})` is the set of edges of `G'_r` that (R5)
does not assign. An edge with both ends in `V(Y)` is assigned: by (R5) step (2) (or an earlier
step) if `Y` is light, and by step (3) (or an earlier step) if `Y` is standalone
(`EG.HB.Round.assign_ne_none_of_mem_partVerts`, `EG/Lib/HB/GC.lean`).
-/

public section

namespace EG

open EG.HB

/-- [s2:lemEL] "For every ancestor `Y` of round `r` and every round `l > r`, no edge of `G_l` has
both ends in `V(Y)`." (For every valid run.) -/
theorem edgeLaminarity : EG.Spec.ELStatement := by
  intro V _ G Dstar run hv Y hY l hl e he hin
  obtain ⟨r, a⟩ := Y
  have ha : a ∈ run.prePartAddrs G r := (run.mem_ancestors G).1 hY
  have hR : run.IsRound r := Run.isRound_of_mem_prePartAddrs ha
  have hvr := Run.Valid.round run G hv hR
  have ha' : a ∈ Round.prePartAddrs (run.graph G r) (run.choice r) := by
    rw [← run.prePartAddrs_of_isRound G hR]; exact ha
  have he1 : e ∈ (run.graph G (r + 1)).edges := run.graph_edges_subset_of_le G hl he
  rw [run.graph_succ_of_isRound G hR, Round.next_edges] at he1
  obtain ⟨-, hnone⟩ := (Round.mem_passed _ _).1 he1
  exact Round.assign_ne_none_of_mem_partVerts hvr ha' hin hnone

end EG
