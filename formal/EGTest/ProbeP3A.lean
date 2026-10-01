import EGTest.HB
import EG.Spec.HB.TauRules
import EG.Spec.HB.SEP
import EG.Spec.HB.ThinCut
import EG.Spec.HB.Overlap
import EG.Spec.HB.Lemma14Tau
import EG.Spec.HB.GC
import EG.Spec.HB.EL
import EG.Spec.HB.TowerC
import EG.Lib.Found.Gamma
import EG.Lib.HB.Split

/-! Non-vacuity checks for the statements of probe unit P3A (probe P-3, part 1; design note
`formal/work/p2b/P3A.md`): the hypotheses of the statements in `EG/Spec/HB/{TauRules, SEP,
ThinCut, Overlap, Lemma14Tau, GC, EL, TowerC}.lean` are satisfiable on small instances, reusing
the instances of `EGTest.HB`:
* `TauRunTest.t` on `H2` (two disjoint edges on `Fin 4`): a `τ`-run with three splits and two
  deleted edges; here re-checked at `s = 1`, `τ = 512 = 128 · 1 · log₂² 4`, the smallest `τ`
  allowed by Lemma 14^τ;
* `tree0` on `E3` (the empty graph on `Fin 3`): an `s = 0` recursion with two splits;
* `run1` on `K3`: a valid run with one round and three pre-parts;
* `GCPartTest` (fix round 1, review issue m2): a hand-built, not valid, round on `Fin 4` with a
  GC-part, on which the round-level forms of the GC-part clause of `GCStatement` (iii) are
  checked;
* `NonIdleTau` (fix round 2, review issue c1): a non-idle `τ`-rule split (`H_out ≠ ∅`, one
  deleted edge) on `Fin 6`, which is a `τ`-split tree and on which the thin-cut bound
  `⌈τ⌉ − 1` of `ThinCutStatement` is attained.
Also (proof-stage fix round 1, review issue c2) a check that the `WF` conjunct of `IsTauRun` is
implied by its label clause, and the Lean witness of the T1 finding `L14-C-TAU0` (the literal bound of s2:lem14tau (c) fails
at `n_0 = 1`, `τ = 0`). -/

namespace EGTest.ProbeP3A

open EG EG.HB EGTest.HB

/-! ## `τ`-rules ([s2:defTauRules]): the context is satisfiable -/

/-- The context of `TauFactAStatement` etc. (`0 ≤ s`, a witness, `s < τ`) holds for the root of
`H2`. -/
example : (0 : ℝ) ≤ 1 ∧ IsWitness (TauRunTest.t.graphAtD TauRunTest.H2 []) epsC 1 {0, 1} ∅ ∧
    (1 : ℝ) < 512 :=
  ⟨by norm_num, TauRunTest.wit_root, by norm_num⟩

/-! ## The `τ`-run of `H2` at `τ = 512` -/

section TauRun512

open TauRunTest

/-- With all degrees in `F₀` and `F₁` at most `1 < τ`, the `τ`-rules are idle (`EGTest.HB`'s
`tau_idle` at a general threshold `τ > 1`). -/
theorem tau_idle_of {W : Type} [DecidableEq W] (K : FGraph W) (U N : Finset W) {τ : ℝ}
    (hτ : 1 < τ) (h0 : ∀ v, degE (witF0 K U N) v ≤ 1)
    (h1 : ∀ v, degE (K.edgesBetween U (K.verts \ (U ∪ N))) v ≤ 1) :
    tauU1 K U N τ = U ∧ tauN2 K U N τ = N := by
  have hout : tauHout K U N τ = ∅ := by
    unfold tauHout
    apply Finset.filter_false_of_mem
    intro v _ hv
    have : ((degE (witF0 K U N) v : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h0 v
    linarith
  have hU : tauU1 K U N τ = U := by simp [tauU1, hout]
  have hN1 : tauN1 K U N τ = N := by simp [tauN1, hout]
  have hF1 : tauF1 K U N τ = K.edgesBetween U (K.verts \ (U ∪ N)) := by
    simp only [tauF1, hU, hN1]
  have hin : tauHin K U N τ = ∅ := by
    unfold tauHin
    apply Finset.filter_false_of_mem
    intro v _ hv
    rw [hF1] at hv
    have : ((degE (K.edgesBetween U (K.verts \ (U ∪ N))) v : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast h1 v
    linarith
  refine ⟨hU, ?_⟩
  simp [tauN2, hN1, hin]

/-- `t` is a `τ`-run of `H2` with `s = 1`, `τ = 512`. -/
theorem t_isTauRun_512 : t.IsTauRun epsC 1 512 H2 := by
  refine ⟨t_isTauRun.1, t_isTauRun.2.1, ?_⟩
  intro a ha
  rw [t_internal] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  have h512 : (1 : ℝ) < 512 := by norm_num
  rcases ha with rfl | rfl | rfl
  · refine ⟨{0, 1}, ∅, by rw [Nat.cast_one]; exact wit_root, ?_⟩
    have hN : witN (t.graphAtD H2 []) {0, 1} ∅ = ∅ := by decide
    obtain ⟨h1, h2⟩ := tau_idle_of (t.graphAtD H2 []) {0, 1} ∅ h512 (by decide) (by decide)
    rw [hN, h1, h2]; rfl
  · refine ⟨{0}, {s(0, 1)}, by rw [Nat.cast_one]; exact wit_F, ?_⟩
    have hN : witN (t.graphAtD H2 [false]) {0} {s(0, 1)} = ∅ := by decide
    obtain ⟨h1, h2⟩ := tau_idle_of (t.graphAtD H2 [false]) {0} ∅ h512 (by decide) (by decide)
    rw [hN, h1, h2]; rfl
  · refine ⟨{2}, {s(2, 3)}, by rw [Nat.cast_one]; exact wit_T, ?_⟩
    have hN : witN (t.graphAtD H2 [true]) {2} {s(2, 3)} = ∅ := by decide
    obtain ⟨h1, h2⟩ := tau_idle_of (t.graphAtD H2 [true]) {2} ∅ h512 (by decide) (by decide)
    rw [hN, h1, h2]; rfl

theorem H2_card : H2.card = 4 := rfl

theorem logb_two_four : Real.logb 2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- **Non-vacuity of the Lemma 14^τ statements** (`L14SplitStatement`, `L14GlobalStatement`,
`L14OVStatement`, `L14ThinStatement`): all hypotheses hold for `H2`, `s = 1`, `τ = 512`, `t`,
which has three splits. -/
theorem l14_hyps : 1 ≤ (1 : ℕ) ∧ 128 * ((1 : ℕ) : ℝ) * Real.logb 2 H2.card ^ 2 ≤ 512 ∧
    t.IsTauRun epsC 1 512 H2 ∧ t.internalAddrs.card = 3 := by
  refine ⟨le_rfl, ?_, t_isTauRun_512, by rw [t_internal]; rfl⟩
  rw [H2_card]
  push_cast
  rw [logb_two_four]
  norm_num

/-- The hypothesis of `L14SplitStatement` at the root: a witness with parameter `1` whose
`τ`-rules give the label. -/
example : IsWitness (t.graphAtD H2 []) epsC ((1 : ℕ) : ℝ) {0, 1} ∅ ∧
    t.labelAt [] = some (tauU1 (t.graphAtD H2 []) {0, 1} (witN (t.graphAtD H2 []) {0, 1} ∅) 512,
      tauN2 (t.graphAtD H2 []) {0, 1} (witN (t.graphAtD H2 []) {0, 1} ∅) 512) := by
  refine ⟨by rw [Nat.cast_one]; exact wit_root, ?_⟩
  have hN : witN (t.graphAtD H2 []) {0, 1} ∅ = ∅ := by decide
  obtain ⟨h1, h2⟩ := tau_idle_of (t.graphAtD H2 []) {0, 1} ∅ (by norm_num : (1 : ℝ) < 512)
    (by decide) (by decide)
  rw [hN, h1, h2]; rfl

/-- The `τ`-run deletes two edges, and the global objects are nontrivial. -/
example : t.deleted H2 = {s(0, 1), s(2, 3)} := by decide

/-! ## Split recursions (SEP), thin cut -/

/-- Hypothesis of the SEP statements: `t` is a split recursion on `H2`. -/
example : t.WF H2 := t_isTauRun.1

/-- **Non-vacuity of `ThinCutStatement` / `ThinCutEdgeStatement`**: `t` is a split recursion by
the `τ`-rules at `τ = 512` (witness parameter `1 < 512`), with deleted edges. -/
theorem t_isTauSplitTree : t.IsTauSplitTree epsC 512 H2 := by
  refine ⟨t_isTauRun_512.1, ?_⟩
  intro a ha
  obtain ⟨U, F, hw, hl⟩ := t_isTauRun_512.2.2 a ha
  exact ⟨1, U, F, by norm_num, by rw [Nat.cast_one] at hw; exact hw, hl⟩

end TauRun512

/-! ## Lemma OV: the `s = 0` recursion `tree0` on `E3` -/

/-- **Non-vacuity of `OVStatement`**: `0 < c`, `3.42 c ε < 1`, `n_0 ≥ 1` and `OVHyp` hold for
`tree0` on `E3` with `c = 1` (two splits). -/
theorem ov_hyps : (0 : ℝ) < 1 ∧ 3.42 * 1 * epsC < 1 ∧ 1 ≤ E3.card ∧ tree0.OVHyp epsC 1 E3 := by
  refine ⟨by norm_num, by unfold epsC; norm_num, by decide, wf_tree0, ?_⟩
  intro a ha
  have h2 := card_internal ha
  refine ⟨h2, ?_, ?_⟩
  · rw [tree0_internalAddrs] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [show ([] : Addr) ++ [false] = [false] from rfl]
      simp only [FGraph.card, verts_F, verts_root]
      norm_num
    · rw [show ([true] : Addr) ++ [false] = [true, false] from rfl]
      simp only [FGraph.card, verts_TF, verts_T]
      rw [show ({1, 2} : Finset (Fin 3)).card = 2 from rfl]
      norm_num
  · have : (0 : ℝ) < epsC := by unfold epsC; positivity
    have hl : (tree0.labelN a).card = 0 := by
      rw [tree0_internalAddrs] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> rfl
    rw [hl, Nat.cast_zero]
    positivity

/-- **Non-vacuity of `OVInstanceStatement`**: `tree0` is an `s = 0` recursion on `E3`. -/
example : tree0.IsS0Rec epsC E3 := isS0Rec_tree0

/-! ## Rule GC, EL, tower facts (c): valid runs -/

/-- **Non-vacuity of `GCDefStatement`, `GCStatement`, `ELStatement`**: `run1` is a valid run on
`K3` with one round and three pre-parts (all light; no GC-part: non-vacuity of the GC-part
clause of (iii) is not checked, see the design note). -/
example : run1.Valid K3 1 ∧ 1 ∈ Finset.Icc 1 run1.R ∧ (run1.prePartAddrs K3 1).card = 3 := by
  refine ⟨run1_valid, by decide, ?_⟩
  rw [show run1.prePartAddrs K3 1 = {[false], [true, false], [true, true]} by
    rw [Run.prePartAddrs_of_isRound run1 K3 (by decide), Run.graph_one]
    exact prePartAddrs_eq.trans tree0_leafAddrs]
  rfl

/-- The hypotheses `Gamma1core Dstar` and `run.Valid G Dstar` of `GCThetaStatement` and
`TowerCStatement` are jointly satisfiable (the run without rounds on `E2`; a run with a round
under `Γ1` needs `d_1 ≥ D_* ≥ 2^{2^{256}}` and is not built here). -/
example : ∃ D : ℝ, Gamma1core D ∧ (⟨[]⟩ : Run (Fin 2)).Valid E2 D := by
  obtain ⟨D, hD⟩ := exists_gamma1core
  refine ⟨D, hD, (Run.valid_nil_iff E2 D).2 ?_⟩
  have hE : E2.edges = ∅ := by decide
  have h2 : (2 : ℝ) < D := hD.1
  simp only [Round.d, hE, Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
  linarith

/-! ## Rule GC: a round-local GC-part (fix round 1, review issue m2)

No valid run has a GC-part at toy size (a GC-part is an `(ε,s_r)`-expander leaf with a guest, so
its minimum degree exceeds `s_r ≥ 40^{100}`; design note). Here the round-local functions of
(R3)–(R5) are exercised on a hand-built, **not valid**, `RoundChoice` with a failing (GC), and
the round-level forms of the conclusions of `GCStatement` (iii) are checked.

`H4` on `Fin 4` with edges `01, 23`, so `d = 2·2/4 = 1`. This is the junk regime of the
parameters: `λ = log₂ 1 = 0`, `P = ⌈0^{103}⌉ = 0`, and `θ^GC(z) = ⌈z · 0^{-1/2}⌉ = 0` (Lean's
`0 ^ (-1/2) = 0`; the manuscript never evaluates `θ^GC` at `λ ≤ 1`), so (GC) fails at every
pre-part that has a guest. The root split `({0}, {1})` gives the leaves `[false]` (vertices
`{0,1}`, edge `01`) and `[true]` (vertices `{1,2,3}`, edge `23`), overlapping in `1`. Home order
`[false], [true]`: `D = Dup* = {1}`, `S_{[true]} = {1}`; `[true]` satisfies (L1) (`2 ≤ 3`) and
(L2) (the guest `1` is isolated in `G'[{1,2,3}]`) and fails (GC): it is a GC-part. -/

namespace GCPartTest

def H4 : FGraph (Fin 4) := FGraph.ofEdges Finset.univ {s(0, 1), s(2, 3)}

def tr : STree (Fin 4) := .node ({0}, {1}) .nil .nil

def c : RoundChoice (Fin 4) := ⟨[], tr, fun _ => .nil, [[false], [true]]⟩

theorem H4_edges : H4.edges = {s(0, 1), s(2, 3)} := by decide

theorem d_H4 : Round.d H4 = 1 := by
  rw [Round.d, H4_edges, show H4.card = 4 from rfl]
  norm_num [show ({s(0, 1), s(2, 3)} : Finset (Sym2 (Fin 4))).card = 2 from by decide]

theorem POf_one : POf 1 = 0 := by simp [POf, lamOf, show Cp = 103 from rfl]

theorem thetaGC_one (z : ℕ) : thetaGC 1 z = 0 := by
  simp [thetaGC, lamOf]

theorem twoLevel_eq : Round.twoLevel H4 c = tr := by
  have h : (fun a => if POf (Round.d H4) ≤ (Round.piece H4 c a).card then c.tauRun a
      else (STree.nil : STree (Fin 4))) = fun _ => STree.nil :=
    funext fun a => by split_ifs <;> rfl
  unfold Round.twoLevel; rw [h]; exact STree.graft_nil_fun tr

theorem g'_eq : Round.graph' H4 c = H4 := by
  simp [Round.graph', Round.cycEdges, c]

theorem X0_eq (a : Addr) : Round.X0 H4 c a = tr.graphAtD H4 a := by
  rw [Round.X0, twoLevel_eq, g'_eq]

theorem pre_eq : Round.prePartAddrs H4 c = {[false], [true]} := by
  unfold Round.prePartAddrs
  rw [twoLevel_eq, d_H4, POf_one]
  simp only [X0_eq]
  decide

theorem Z0_F : Round.Z0 H4 c [false] = {0, 1} := by rw [Round.Z0, X0_eq]; decide

theorem Z0_T : Round.Z0 H4 c [true] = {1, 2, 3} := by rw [Round.Z0, X0_eq]; decide

theorem X0_T_edges : (Round.X0 H4 c [true]).edges = {s(2, 3)} := by rw [X0_eq]; decide

theorem D_eq : Round.D H4 c = {1} := by
  ext v
  rw [Round.mem_D]
  simp only [Round.mu, pre_eq]
  fin_cases v <;> simp [Finset.filter_insert, Finset.filter_singleton, Z0_F, Z0_T]

theorem DupStar_eq : Round.DupStar H4 c = {1} := by
  rw [Round.DupStar, twoLevel_eq, g'_eq]; decide

theorem home_eq (v : Fin 4) : Round.home H4 c v =
    if v = 0 ∨ v = 1 then some [false] else some [true] := by
  unfold Round.home
  rw [pre_eq, show c.homeOrder = [[false], [true]] from rfl]
  fin_cases v <;> simp [Z0_F, Z0_T]

theorem guests_F : Round.guests H4 c [false] = ∅ := by
  unfold Round.guests; rw [D_eq, Z0_F]; simp [home_eq]

theorem guests_T : Round.guests H4 c [true] = {1} := by
  unfold Round.guests; rw [D_eq, Z0_T]; simp [home_eq]

theorem light_F : Round.isLight H4 c [false] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guests_F]
  · intro u _
    rw [guests_F]
    simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  · intro x hx; rw [guests_F] at hx; simp at hx

/-- `[true]` is a **GC-part**: (L1) `2·1 ≤ 3`; (L2) no vertex of `Z^0 = {1,2,3}` has a guest
neighbour in `G'[Z^0]`; (GC) fails at the guest `1` (`0 < θ^GC = 0` is false). -/
theorem gcPart_T : Round.isGCPart H4 c [true] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guests_T, Z0_T]
  · intro u _
    rw [guests_T, Z0_T, g'_eq]
    have h : ∀ u : Fin 4, (H4.induce {1, 2, 3}).nbrs u ∩ {1} = ∅ := by decide
    rw [h u, Finset.card_empty, Nat.cast_zero]
    positivity
  · intro h
    have h1 := h 1 (by rw [guests_T]; simp)
    rw [d_H4, thetaGC_one] at h1
    exact Nat.not_lt_zero _ h1

theorem not_light_T : ¬ Round.isLight H4 c [true] := fun h => gcPart_T.2.2 h.2.2

theorem partGraph_F_edges : (Round.partGraph H4 c [false]).edges = {s(0, 1)} := by
  rw [Round.partGraph, if_pos light_F, Round.X, X0_eq, guests_F]; decide

theorem partGraph_T_edges : (Round.partGraph H4 c [true]).edges = {s(2, 3)} := by
  rw [Round.partGraph, if_neg not_light_T, X0_T_edges]

/-- (R5) step (1): `01` goes to the light part `[false]`. -/
theorem assign_01 : Round.assign H4 c s(0, 1) = some [false] := by
  unfold Round.assign
  rw [pre_eq, show c.homeOrder = [[false], [true]] from rfl]
  simp [partGraph_F_edges]

/-- (R5) step (1): `23` goes to the GC-part `[true]`. -/
theorem assign_23 : Round.assign H4 c s(2, 3) = some [true] := by
  unfold Round.assign
  rw [pre_eq, show c.homeOrder = [[false], [true]] from rfl]
  simp [partGraph_F_edges, partGraph_T_edges]

theorem passed_eq : Round.passed H4 c = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  rw [Round.mem_passed, g'_eq, H4_edges] at he
  obtain ⟨he, hn⟩ := he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · rw [assign_01] at hn; exact Option.some_ne_none _ hn
  · rw [assign_23] at hn; exact Option.some_ne_none _ hn

/-- **Round-local check of the GC-part clause of `GCStatement` (iii)** (review issue m2): the
pre-part `[true]` is a GC-part with a guest and an edge, and the round-level forms of the
conclusions hold: `[true] ∈ Std`; every edge of `G'` inside `Z^0` is assigned; `E(X^0) ⊆ E(Z)`
(here `= {23}`, nonempty); no edge of the next graph (`G_{r+1}` at run level) lies inside
`Z^0`; `S ⊆ D ⊆ Dup*` (here `{1} ⊆ {1} ⊆ {1}`, nonempty). The clause `V(Y) = Z^0` is about
the run-level ancestor and is not round-local. -/
example : [true] ∈ Round.prePartAddrs H4 c ∧ Round.isGCPart H4 c [true] ∧
    (Round.guests H4 c [true]).Nonempty ∧ (Round.X0 H4 c [true]).edges.Nonempty ∧
    [true] ∈ Round.Std H4 c ∧
    (∀ e ∈ (Round.graph' H4 c).edges, e ∈ (Round.Z0 H4 c [true]).sym2 →
      Round.assign H4 c e ≠ none) ∧
    (Round.X0 H4 c [true]).edges ⊆ Round.E H4 c [true] ∧
    (∀ e ∈ (Round.next H4 c).edges, e ∉ (Round.Z0 H4 c [true]).sym2) ∧
    Round.guests H4 c [true] ⊆ Round.D H4 c ∧ Round.D H4 c ⊆ Round.DupStar H4 c := by
  refine ⟨by rw [pre_eq]; simp, gcPart_T, by rw [guests_T]; simp,
    by rw [X0_T_edges]; simp, ?_, ?_, ?_, ?_, by rw [guests_T, D_eq],
    by rw [D_eq, DupStar_eq]⟩
  · simp only [Round.Std, Finset.mem_filter]
    exact ⟨by rw [pre_eq]; simp, not_light_T⟩
  · intro e he _
    rw [g'_eq, H4_edges] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [assign_01]; simp
    · rw [assign_23]; simp
  · rw [X0_T_edges, Finset.singleton_subset_iff, Round.mem_E, g'_eq, H4_edges]
    exact ⟨by simp, assign_23⟩
  · intro e he
    rw [Round.next_edges, passed_eq] at he
    simp at he

end GCPartTest

/-! ## A non-idle `τ`-rule split on which the thin-cut bound is attained (fix round 2, c1)

All `τ`-rule instances above are idle (`H_out = H_in = ∅`). Here `H6` on `Fin 6` has edges
`02, 03, 14`; the witness is `U = {0,1,5}`, `F = {02, 03, 14}` with `s = 1 < τ = 2`. Then
`N = ∅`, `F_0 = F`, `deg_{F_0}(0) = 2 ≥ τ`, so `H_out = {0}`, `U' = {1,5}`, `N' = {0}`,
`F_1 = {14}`, `H_in = ∅`, `N'' = {0}`, `F'' = {14}`. The one-split tree with label
`({1,5},{0})` is a `τ`-split tree ([s2:lemThinCut]'s hypothesis), `Dup = {0}`, and the count of
`ThinCutStatement` at the leaf `[false]` and `h = 4` is `1 = ⌈2⌉ − 1` (the bound is attained).
Instance found by the round-2 reviewer (`work/p2b/P3A.review2.md` §2). -/

namespace NonIdleTau

open TauRunTest

/-- The graph on `Fin 6` with edges `02, 03, 14`. -/
def H6 : FGraph (Fin 6) := FGraph.ofEdges Finset.univ {s(0, 2), s(0, 3), s(1, 4)}

/-- The witness set `U = {0,1,5}`. -/
def U : Finset (Fin 6) := {0, 1, 5}

/-- The witness edge set `F = {02, 03, 14}`. -/
def F : Finset (Sym2 (Fin 6)) := {s(0, 2), s(0, 3), s(1, 4)}

/-- One split, labelled `(U', N'') = ({1,5},{0})`. -/
def tr : STree (Fin 6) := .node ({1, 5}, {0}) .nil .nil

/-- At `τ = 2` the real comparison of `H_out` becomes a natural one (so `decide` applies). -/
theorem tauHout_two {W : Type} [DecidableEq W] (K : FGraph W) (U N : Finset W) :
    tauHout K U N 2 = U.filter (fun v => 2 ≤ degE (witF0 K U N) v) := by
  unfold tauHout
  apply Finset.filter_congr
  intro v _
  constructor <;> intro h <;> exact_mod_cast h

/-- At `τ = 2` the real comparison of `H_in` becomes a natural one. -/
theorem tauHin_two {W : Type} [DecidableEq W] (K : FGraph W) (U N : Finset W) :
    tauHin K U N 2 = (K.verts \ (tauU1 K U N 2 ∪ tauN1 K U N 2)).filter
      (fun x => 2 ≤ degE (tauF1 K U N 2) x) := by
  unfold tauHin
  apply Finset.filter_congr
  intro v _
  constructor <;> intro h <;> exact_mod_cast h

theorem root_eq : tr.graphAtD H6 [] = H6 := rfl

theorem wit : IsWitness H6 epsC 1 U F :=
  wit_of _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witN_eq : witN H6 U F = ∅ := by decide

/-- `H_out = {0}`: the rule is not idle. -/
theorem hout : tauHout H6 U ∅ 2 = {0} := by rw [tauHout_two]; decide

theorem hU1 : tauU1 H6 U ∅ 2 = {1, 5} := by unfold tauU1; rw [hout]; decide

theorem hN1 : tauN1 H6 U ∅ 2 = {0} := by unfold tauN1; rw [hout]; decide

theorem hF1 : tauF1 H6 U ∅ 2 = {s(1, 4)} := by unfold tauF1; rw [hU1, hN1]; decide

theorem hin : tauHin H6 U ∅ 2 = ∅ := by rw [tauHin_two, hU1, hN1, hF1]; decide

theorem hN2 : tauN2 H6 U ∅ 2 = {0} := by unfold tauN2; rw [hN1, hin]; decide

theorem hF2 : tauF2 H6 U ∅ 2 = {s(1, 4)} := by
  unfold tauF2; rw [hU1, hN2]; decide

/-- The non-idle split is a `τ`-split tree at `τ = 2` (witness parameter `1 < 2`). -/
theorem tst : tr.IsTauSplitTree epsC 2 H6 := by
  have hint : tr.internalAddrs = {[]} := by decide
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' : a = [] := by rw [hint] at ha; simpa using ha
    subst ha'
    refine ⟨?_, ?_, ?_⟩ <;> decide
  intro a ha
  have ha' : a = [] := by rw [hint] at ha; simpa using ha
  subst ha'
  refine ⟨1, U, F, by norm_num, wit, ?_⟩
  rw [root_eq, witN_eq, hU1, hN2]; rfl

theorem deleted_eq : tr.deleted H6 = {s(1, 4)} := by decide

theorem dup_eq : tr.dup H6 = {0} := by decide

/-- The hypotheses of `ThinCutStatement` hold, `H_out ≠ ∅`, an edge is deleted, and the count
at the leaf `[false]` and `h = 4` equals the bound `⌈2⌉ − 1 = 1` (also in the `k − 1` form,
`k = 2`). -/
example : (0 : ℝ) < 2 ∧ tr.IsTauSplitTree epsC 2 H6 ∧ tauHout H6 U ∅ 2 ≠ ∅ ∧
    tr.deleted H6 ≠ ∅ ∧ [false] ∈ tr.leafAddrs ∧
    (((tr.deleted H6).filter (fun e => ∃ u ∈ (tr.graphAtD H6 [false]).verts \ tr.dup H6,
      e = s((4 : Fin 6), u))).card : ℤ) = ⌈(2 : ℝ)⌉ - 1 ∧
    ((tr.deleted H6).filter (fun e => ∃ u ∈ (tr.graphAtD H6 [false]).verts \ tr.dup H6,
      e = s((4 : Fin 6), u))).card = 2 - 1 := by
  have h : ((tr.deleted H6).filter (fun e => ∃ u ∈ (tr.graphAtD H6 [false]).verts \ tr.dup H6,
      e = s((4 : Fin 6), u))).card = 1 := by decide
  refine ⟨by norm_num, tst, by rw [hout]; decide, by rw [deleted_eq]; decide, by decide, ?_,
    by rw [h]⟩
  rw [h]
  norm_num

/-- At the other leaf with `h = 1` (the `U'` end of the deleted edge) the count is also `1`. -/
example : ((tr.deleted H6).filter (fun e => ∃ u ∈ (tr.graphAtD H6 [true]).verts \ tr.dup H6,
      e = s((1 : Fin 6), u))).card = 1 := by decide

/-- `h = 0 ∈ V([false])`: the count is `0`, as the third clause claims. -/
example : (0 : Fin 6) ∈ (tr.graphAtD H6 [false]).verts ∧
    ((tr.deleted H6).filter (fun e => ∃ u ∈ (tr.graphAtD H6 [false]).verts \ tr.dup H6,
      e = s((0 : Fin 6), u))).card = 0 := by decide

end NonIdleTau

/-! ## T1 finding `L14-C-TAU0`: the literal bound of s2:lem14tau (c) at `n_0 = 1`, `τ = 0` -/

/-- The graph with one vertex and no edge. -/
def H1 : FGraph (Fin 1) := FGraph.ofEdges Finset.univ ∅

/-- The hypotheses of Lemma 14^τ hold for `H_0 = H1` (`n_0 = 1`), `s = 1`, `τ = 0`
(`128 s log² 1 = 0 ≤ 0`), with the one-leaf `τ`-run; but the literal bound of (c),
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1`, reads `0 ≤ -1`. This is why
`L14ThinStatement` adds `0 < τ` to that bound (design note, math finding `L14-C-TAU0`). -/
theorem lem14tau_c_literal_false :
    128 * ((1 : ℕ) : ℝ) * Real.logb 2 H1.card ^ 2 ≤ 0 ∧
    (STree.nil : STree (Fin 1)).IsTauRun epsC 1 0 H1 ∧
    [] ∈ (STree.nil : STree (Fin 1)).leafAddrs ∧
    ¬ (((((STree.nil : STree (Fin 1)).deleted H1).filter (fun e =>
        ∃ u ∈ ((STree.nil : STree (Fin 1)).graphAtD H1 []).verts \
          (STree.nil : STree (Fin 1)).dup H1, e = s((0 : Fin 1), u))).card : ℤ) ≤
      ⌈(0 : ℝ)⌉ - 1) := by
  refine ⟨?_, ?_, by simp, ?_⟩
  · have : H1.card = 1 := rfl
    rw [this, Nat.cast_one, Real.logb_one]
    norm_num
  · rw [STree.isTauRun_nil_iff]
    exact FGraph.isExpander_of_card_le_one (le_of_eq rfl)
  · simp

/-! ## `IsTauRun`: the `WF` conjunct is redundant (proof-stage fix round 1, review issue c2)

[s2:lem14tau] says "it is a split recursion" as a consequence. The locked predicate
`STree.IsTauRun` lists `WF` as a conjunct; this check shows that the conjunct follows from the
label clause (the `τ`-rule sets of a witness are disjoint subsets of `V(H_a)`,
`EG.HB.tau_split_wf`), so it does not restrict the class of `τ`-runs. -/

example {W : Type} [DecidableEq W] (ε : ℝ) (s : ℕ) (τ : ℝ) (t : STree W) (H : FGraph W)
    (hstop : t.StopsAt H (fun Q => Q.IsExpander ε s))
    (hlab : ∀ a ∈ t.internalAddrs, ∃ (U : Finset W) (F : Finset (Sym2 W)),
      IsWitness (t.graphAtD H a) ε s U F ∧
        t.labelAt a = some (tauU1 (t.graphAtD H a) U (witN (t.graphAtD H a) U F) τ,
          tauN2 (t.graphAtD H a) U (witN (t.graphAtD H a) U F) τ)) :
    t.IsTauRun ε s τ H := by
  refine ⟨fun a ha => ?_, hstop, hlab⟩
  obtain ⟨U, F, hw, hl⟩ := hlab a ha
  simp only [STree.labelU, STree.labelN, hl, Option.map_some, Option.getD_some]
  exact tau_split_wf hw

end EGTest.ProbeP3A
