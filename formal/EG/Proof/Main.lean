module

public import EG.Spec.Main
public import EG.Proof.Quot.HIMain
public import EG.Proof.Todo.JVps
public import EG.Proof.Todo.ExistsRun
public import EG.Proof.Gamma.Sat
public import EG.Lib.Chain.Design
public import EG.Lib.Gamma.Full
public import EG.Lib.Main.Constants

/-!
# Proof of the internal main theorem (manuscript s1:thmMain via s7:thmMainProof)

Consumes only `EG/Spec` statements (PLAN_FORMALIZATION.md §4), through their theorems.

Manuscript v6.1, `s7.tex`, Corollary [s7:thmMainProof] (proof): "Let `D_*` be … a constant
satisfying Γ1–Γ4. Such constants exist by Lemma s7:lemGammaSat … We apply Theorem s7:thmHI with
`C := C_0` and `ϑ := θ_Q`. Its assumptions on the constants hold: `C_0 ≥ D_*/2`, since
`ε_1 ≥ 0`; and `0 ≤ θ_Q ≤ 1/4 < 1/2`. Let `G` be a graph without isolated vertices, with
`n ≥ N_0` vertices and `d_1 ≥ D_*`. By Proposition s2:propExists, `G` has a valid `HB^{τ+}` run.
A designation exists … (Definition s6:defDesign). With no VX-parts, Theorem s7:thmJVps gives
simple graphs `Q_3, …, Q_R` with `f(G) ≤ C_0 n + 2 Σ_l f(Q_l)` and `Σ_l |V(Q_l)| ≤ θ_Q n`. This
is the hypothesis of Theorem s7:thmHI, which therefore gives `f(G) ≤ c_EG |V(G)|` for every graph
`G`. In particular `f(n) ≤ c_EG n` for every `n`, so `f(n) = O(n)`."

Theorems used (record: `formal/work/p3/MAIN.md`):
* [s7:lemGammaSat] `EG.exists_gammaCond : Spec.GammaCondExistsStatement` (`N_0`, `D_*` exist);
* [s2:propExists] `EG.Todo.ExistsRun : Spec.ExistsRunStatement` (a valid run exists, under Γ1);
* [s6:defDesign] `EG.Chain.exists_isDesignation` (a designation exists);
* [s7:thmJVps] `EG.Todo.JVps : Spec.JVpsStatement`;
* [s7:thmHI] via `EG.mainInternal_of_hiHyp` (`EG/Proof/Quot/HIMain.lean`);
* constants: `EG.MainConst.half_le_C0`, `EG.MainConst.thetaQ_nonneg`,
  `EG.MainConst.thetaQ_lt_half`
  (`EG/Lib/Main/Constants.lean`), `EG.Gamma1core.gamma2a`, `EG.HB.Run.graph_one`.
-/

public section

namespace EG.Proof

open EG.HB EG.Chain

/-- Reindexing the quotients `Q_3, …, Q_R` of Theorem JV⁺* as `Q_1, …, Q_k` (`k = R − 2`) of
Theorem HI″: `Σ_{l=3}^{R} g(l) = Σ_{i < R+1-3} g(3 + i)`. -/
theorem sum_Icc_three_eq_sum_fin (R : ℕ) (g : ℕ → ℝ) :
    ∑ l ∈ Finset.Icc 3 R, g l = ∑ i : Fin (R + 1 - 3), g (3 + (i : ℕ)) := by
  rw [show Finset.Icc 3 R = Finset.Ico 3 (R + 1) from rfl, Finset.sum_Ico_eq_sum_range,
    Fin.sum_univ_eq_sum_range (fun i => g (3 + i))]

/-- [s7:thmMainProof] the hypothesis of Theorem HI″ (`EG.Spec.HIHyp`) with `C := C_0`,
`ϑ := θ_Q`, for `N_0`, `D_*` as in s1:defConstants: "Let `G` be a graph without isolated
vertices, with `n ≥ N_0` vertices and `d_1 ≥ D_*`. By Proposition s2:propExists, `G` has a valid
run. A designation exists … Theorem s7:thmJVps gives simple graphs `Q_3, …, Q_R` with
`f(G) ≤ C_0 n + 2 Σ_l f(Q_l)` and `Σ_l |V(Q_l)| ≤ θ_Q n`. This is the hypothesis of
Theorem s7:thmHI". -/
theorem hiHyp_of_gammaCond {N0 D : ℝ} (hN : N0Cond N0) (hΓ : GammaCond N0 D) :
    Spec.HIHyp D N0 (Quot.C0 D) (Quot.thetaQ D) := by
  classical
  intro V G _hiso hn hd
  obtain ⟨run, hrun⟩ := EG.Todo.ExistsRun V G D hΓ.gamma1core
  obtain ⟨δ, hδ⟩ := exists_isDesignation run G
  have hd1 : D ≤ run.d G 1 := by
    simpa [Run.d, Run.graph_one, Round.d] using hd
  obtain ⟨W, Q, -, h1, h2⟩ := EG.Todo.JVps V G N0 D run δ hN hΓ hn hd1 hrun hδ
  refine ⟨run.R + 1 - 3, fun i => W (3 + (i : ℕ)), fun i => Q (3 + (i : ℕ)), ?_, ?_⟩
  · rw [sum_Icc_three_eq_sum_fin run.R (fun l => (fnum (Q l).edges : ℝ))] at h1
    exact h1
  · rw [sum_Icc_three_eq_sum_fin run.R (fun l => ((Q l).card : ℝ))] at h2
    exact h2

/-- [s1:thmMain] via [s7:thmMainProof]: every finite simple graph on `n` vertices decomposes into
at most `c n` objects (with `c = ⌈c_EG⌉₊` for `N_0`, `D_*` given by s7:lemGammaSat). -/
theorem mainInternal : EG.Spec.MainInternal := by
  obtain ⟨N0, D, hN, hΓ⟩ := EG.exists_gammaCond
  have h4 : 4 ≤ D := MainConst.four_le_of_gamma2a hΓ.gamma1core.gamma2a
  exact mainInternal_of_hiHyp (MainConst.half_le_C0 h4) (MainConst.thetaQ_nonneg h4)
    (MainConst.thetaQ_lt_half hΓ.2.2.2) (hiHyp_of_gammaCond hN hΓ)

end EG.Proof
