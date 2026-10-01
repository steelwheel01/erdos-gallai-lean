module

public import EG.Spec.Vortex.VX
public import EG.Lib.Vortex.VXProb

/-!
# P3 stub: `EG.Spec.VXStatement` (s4:thmVXp)

Generated at the P2→P3 transition (2026-09-30). Proved in P3 (unit P3-s4, round 1): labels in the
good event exist (`EG.VXProb.exists_good`: (G1) by Lemma 15⁺, (G2) by Theorem 16* and
observation (MC), (G3) by the Chernoff upper tail, (G4) by the Chernoff lower tail, with the sets
`A(w)` of Lemma HB), and for such labels the deterministic run decomposes `E(G)`
(`EG.VXRun.core`: steps `0, …, J-1` with parity, reserved and flexible edges, Corollary-22
decompositions, trail splitting (S), closing (C), and the finish by Fact EG0(b)). The bound
`f(G) ≤ 80N` follows from the decomposition (`EG.fnum_le_of_isDecomp`). Helper files:
`EG/Lib/Vortex/VX*.lean` and `EG/Lib/Vortex/TPV*.lean`.
Keep the name `EG.Todo.VX`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s4:thmVXp] see `EG.Spec.VXStatement`. Proved in P3. -/
theorem VX : EG.Spec.VXStatement := by
  intro V _ Z O εO s hsize hOZ hX hcase G hGZ hOG
  obtain ⟨J, R, M, lev, kap, A, ℓ, t, hg, h9, h3, hUJ⟩ :=
    VXProb.exists_good hsize hOZ hX hcase
  obtain ⟨D, hD, hlen, hcnt⟩ := VXRun.core hg h9 hsize.cond_i h3 hUJ hGZ hOG
  refine ⟨⟨D, hD, hlen, hcnt⟩, ?_⟩
  have hf := fnum_le_of_isDecomp hD
  have hf' : (fnum G.edges : ℝ) ≤ D.length := by exact_mod_cast hf
  have hN : (0 : ℝ) ≤ Z.card := by positivity
  have : (fnum G.edges : ℝ) ≤ 80 * Z.card := by linarith
  exact_mod_cast this

end EG.Todo
