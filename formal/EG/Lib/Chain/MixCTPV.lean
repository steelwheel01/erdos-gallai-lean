module

public import EG.Defs.Chain.StageInst
public import EG.Defs.Gamma.Full
public import EG.Lib.Chain.Lending
public import EG.Lib.HB.TowerRun
public import EG.Lib.HB.Run
public import EG.Lib.Found.Graph
public import EG.Lib.Gamma.Full

/-!
# Helpers for the TPV bullet of Theorem MIX-C (manuscript s6:thmMIXC (a))

Unit P3-s6, round 1. Deterministic facts about a standalone pre-part `Z = (l, a) ∈ Std_l` used by
`EG.Todo.MixCTPVApplicable`:
* `n0_le_card_Z0`: "`|Z^0| ≥ P_l ≥ N_0` by (s1:condG3)" (`P_l = ⌈λ_l^{C'}⌉ ≥ (log₂ D_*)^{C'} ≥ 2N_0`,
  since `d_l ≥ D_*` on a valid run);
* `ancVerts_std`, `ancEps_std`, `ancS_std`, `ancGraph_verts_std`: for a standalone pre-part the
  ancestor data are `V(Z) = Z^0`, `ε_Z = 2^{-5}`, `s_Z = s_l` (s2:defAncestors);
* `ofEdges_own_std`: `Own_Z`, taken as a graph on `Z^0` (the form of `O_Z` in s6:defLending), is
  the graph `Own G run (l, a) c` of s3:defCOL.
-/

public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V]

/-- [s6:thmMIXC] (a) "`|Z^0| ≥ P_l ≥ N_0` by (s1:condG3)": under `RunHyp`, every pre-part of a
round has at least `N_0` vertices. -/
theorem n0_le_card_Z0 {N0 Dstar : ℝ} {G : FGraph V} {run : Run V}
    (h : RunHyp N0 Dstar G run) {l : ℕ} {a : Addr} (ha : a ∈ run.prePartAddrs G l) :
    N0 ≤ ((run.Z0 G l a).card : ℝ) := by
  have hR := Run.isRound_of_mem_prePartAddrs ha
  have hl : l ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  have hdl : Dstar ≤ run.d G l := (h.valid.1 l hl).1
  have hD2 : 2 < Dstar := h.gamma1core.two_lt
  have hN0 : (2 : ℝ) ^ 40 ≤ N0 := h.n0Cond.1
  have h3 : 2 * N0 ≤ Real.logb 2 Dstar ^ Cp := h.gamma3
  have hlog0 : 0 ≤ Real.logb 2 Dstar := Real.logb_nonneg (by norm_num) (by linarith)
  have hlog : Real.logb 2 Dstar ≤ Real.logb 2 (run.d G l) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hdl
  have hpow : Real.logb 2 Dstar ^ Cp ≤ Real.logb 2 (run.d G l) ^ Cp :=
    pow_le_pow_left₀ hlog0 hlog _
  have hP : Real.logb 2 (run.d G l) ^ Cp ≤ (run.P G l : ℝ) := by
    show Real.logb 2 (run.d G l) ^ Cp ≤ ((POf (run.d G l) : ℕ) : ℝ)
    unfold POf lamOf
    exact Nat.le_ceil _
  have hZ : (run.P G l : ℝ) ≤ ((run.Z0 G l a).card : ℝ) := by
    exact_mod_cast Run.P_le_card_Z0 ha
  linarith

variable (run : Run V) (G : FGraph V)

theorem ancVerts_std {l : ℕ} {a : Addr} (h : ¬ run.isLight G l a) :
    run.ancVerts G (l, a) = run.Z0 G l a := by
  classical
  show Round.partVerts (run.graph G l) (run.choice l) a = Round.Z0 (run.graph G l) (run.choice l) a
  unfold Round.partVerts
  exact if_neg h

theorem ancGraph_std {l : ℕ} {a : Addr} (h : ¬ run.isLight G l a) :
    run.ancGraph G (l, a) = run.X0 G l a := by
  classical
  show Round.partGraph (run.graph G l) (run.choice l) a = Round.X0 (run.graph G l) (run.choice l) a
  unfold Round.partGraph
  exact if_neg h

theorem ancGraph_verts_std {l : ℕ} {a : Addr} (h : ¬ run.isLight G l a) :
    (run.ancGraph G (l, a)).verts = run.Z0 G l a := by
  rw [ancGraph_std run G h]; rfl

theorem ancEps_std {l : ℕ} {a : Addr} (h : ¬ run.isLight G l a) :
    run.ancEps G (l, a) = (2 : ℝ) ^ (-5 : ℤ) := by
  classical
  unfold Run.ancEps
  rw [if_neg h]

theorem ancS_std {l : ℕ} {a : Addr} (h : ¬ run.isLight G l a) :
    run.ancS G (l, a) = (run.s G l : ℝ) := by
  classical
  unfold Run.ancS
  rw [if_neg h]

/-- `Own_Z` as a graph on `Z^0` (the lend-good `O_Z` of s6:defLending) is the graph `Own_Z` of
s3:defCOL, for a standalone pre-part. -/
theorem ofEdges_own_std {l : ℕ} {a : Addr} (h : ¬ run.isLight G l a)
    (c : Stage1.Colouring G run (l, a)) :
    FGraph.ofEdges (run.Z0 G l a) (Stage1.Own G run (l, a) c).edges = Stage1.Own G run (l, a) c := by
  have hv : (Stage1.Own G run (l, a) c).verts = run.Z0 G l a := by
    show (run.ancGraph G (l, a)).verts = _
    exact ancGraph_verts_std run G h
  rw [← hv]
  exact FGraph.ofEdges_self

end EG.Chain
