module

public import EG.Spec.Vortex.PVCore
public import EG.Lib.Vortex.FinishCore
public import EG.Proof.Found.EG0
public import EG.Proof.Ext.Cor22

/-!
# The PV finish (manuscript s4:lemPV, proof, "Finish"; CR1-PV) — unit P4A

`EG.pvFinish : PVFinishStatement`. Fact s1:factEG0(b) (`EG.factEG0b`, proved) decomposes `E_1`;
every edge of `E_2` gets a phase avoiding the external phases of its ends (`EG.exists_phase`);
Corollary 22 (the declared input `EG.cor22`) decomposes each phase class `E_{2,c}`; stripping and
the counts are `EG.PVFin.finish_core`. Design note `formal/work/p2b/P4A.md`.
-/

public section

namespace EG

universe u

/-- [s4:lemPV] (proof, "Finish"; CR1-PV), with the finish count of (c) and the `Pl_J = ∅` case of
(d): "`E_1` decomposes into at most `64|Pl|` objects … Give every edge `xy ∈ E_2` a phase
`c ∈ [4] \ {ext(x), ext(y)}` … Take a Corollary-22 decomposition of each `E_{2,c}` … at most
`8|Pl_J|` … single edges in total"; "in the finish there are at most `|U_J| ≤ N` arcs per phase
by (E)". -/
theorem pvFinish : EG.Spec.PVFinishStatement.{u} := by
  intro V _ N Rt Pl PlJ HJ ext hL hPlN hPlJ hdis hG5 hloop hends
  have hdisJ : Disjoint Rt PlJ := hdis.mono_right hPlJ
  -- phases
  choose ph hph using exists_phase ext
  -- Corollary-22 decompositions of the phase classes
  have hc22 : ∀ c : Fin 4, ∃ P : List (List V),
      IsPathDecomp ((PVFin.E2c PlJ HJ ph c : Finset (Sym2 V)) : Set (Sym2 V)) P ∧
        ∀ v, pathEndCount P v ≤ 2 := fun c =>
    cor22 V _ fun e he => hloop e (PVFin.mem_E2.1 (PVFin.mem_E2c.1 he).1).1
  choose Pc hPc hPc2 using hc22
  -- Fact EG0(b) for `E_1`
  have hL' : (2 : ℝ) ^ 10 ≤ Real.logb 2 (N : ℝ) := hL
  have hN1 : (1 : ℝ) < N := by
    by_contra h
    push Not at h
    have : Real.logb 2 (N : ℝ) ≤ 0 := by
      rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).eq_or_lt with h0 | h0
      · rw [← h0, Real.logb_zero]
      · exact Real.logb_nonpos (by norm_num) h0.le h
    linarith
  obtain ⟨D1, hD1, hD1len, -⟩ := factEG0b V (N : ℝ) (Pl.card : ℝ) 64 (PVFin.E1 PlJ HJ) PlJ hN1
    (Nat.cast_nonneg _) (by exact_mod_cast hPlN) (by norm_num) (by linarith)
    (fun e he => hloop e (PVFin.mem_E1.1 he).1) (fun e he => (PVFin.mem_E1.1 he).2) hG5
  obtain ⟨Hobj, D, arcs, h1, h2, h3, h4, h5, h6, h7⟩ :=
    PVFin.finish_core hdisJ hloop hends hph hPc hPc2 hD1
  refine ⟨Hobj, D, arcs, h1, h2, ?_, h4, h5, h6, h7⟩
  have h3' : (D.length : ℝ) ≤ D1.length + 8 * PlJ.card := by exact_mod_cast h3
  linarith

end EG
