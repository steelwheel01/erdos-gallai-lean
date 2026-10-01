module

public import EG.Spec.Chain.JSLCRouting
public import EG.Lib.Chain.JslcPairs
public import EG.Lib.Chain.StageInst
public import EG.Lib.Found.Graph
public import EG.Lib.HB.Run

/-!
# Proof of the joint-routing claims (a), (c), (d) of Step 6 of Lemma JS-LC
(manuscript s6:lemJSLC, proof, Step 6)

Probe unit P2J (probe P-2, part 2), proof round 1.
* `EG.jslcPairsBalance` (claim (a), "the bijections exist"): Lemma MED (b) gives
  `∑_{LayP_j} dem⁻ = Φ_j`, and `∑_{LayP_{j+1}} dem⁺ = Φ_{j+1}` by definition.
* `EG.jslcPairsDistinct` (claim (a), distinct pair ends): for `k ≥ 2` the layers `j`, `j+1` are
  disjoint by (D); for `k = 1`, `pad = 0`, so an out-unit has `exc < 0` and an in-unit `exc > 0`.
* `EG.jslcJointMult` (claim (c), the joint multiplicity): per system a vertex occurs in at most
  `|exc| + pad` pairs and in none if it is not a port; a port of `𝒮_0` is in no cherry system and
  gets `≤ (M−1) + ⌈M/2⌉ ≤ 2M − 2`; otherwise only cherry systems contribute, each `≤ 1 + 1`, and
  there are at most `M − 1` of them.
* `EG.jslcRouting` (claim (d)): Lemma COL(b) on the record (`StageData.Coherent.colB_conn`).
-/

public section

namespace EG

open EG.HB EG.Chain

/-- [s6:lemJSLC:proof-claim-a] "The bijections exist. … By Lemma s6:lemMED(b),
`Σ_{LayP_j} exc^- = Σ_{LayP_j} exc^+`. So the number of out-units of layer `j` equals its padded
load, which equals the padded load of layer `j+1`, which is the number of its in-units." -/
theorem jslcPairsBalance : EG.Spec.JslcPairsBalanceStatement := by
  intro V _ G S hS hPhi j
  rw [hS.sum_demMinus_eq_Phi j, hPhi j (S.succ j)]
  rfl

/-- [s6:lemJSLC:proof-claim-a] "The two vertices of a pair are distinct: for `k ≥ 2`, the layers
`j` and `j+1` consist of different, pairwise vertex-disjoint clusters …; for `k = 1`,
`X^out ∩ X^in = ∅`." -/
theorem jslcPairsDistinct : EG.Spec.JslcPairsDistinctStatement := by
  intro V _ G S hS j u hu v hv hu0 hv0 huv
  subst huv
  by_cases hk : S.k = 1
  · rw [S.succ_eq_self hk j] at hv
    have hp := hS.pad_k1 hk j u hu
    unfold HccpData.demMinus at hu0
    unfold HccpData.demPlus at hv0
    rw [hp] at hu0 hv0
    omega
  · have hne : S.succ j ≠ j := S.succ_ne_self (by have := hS.k_pos; omega) j
    exact Finset.disjoint_left.1 (hS.layP_disjoint hne.symm) hu hv

/-- `⌈M/2⌉ ≤ M − 1` for `M ≥ 2` ("For `M_l ≥ 2`, `⌈M_l/2⌉ ≤ M_l − 1`"). -/
theorem ceil_half_le_sub_one {M : ℕ} (hM : 2 ≤ M) : ⌈(M : ℝ) / 2⌉₊ ≤ M - 1 := by
  rw [Nat.ceil_le, Nat.cast_sub (by omega : 1 ≤ M)]
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  push_cast
  linarith

/-- [s6:lemJSLC:proof-claim-c] "(c) Every vertex lies in at most
`max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` pairs of `𝔓_j(Y,l)`. … So at a fixed junction
a port occurs in at most `max(dem⁻, dem⁺)` pairs of each system containing it. Centres occur in no
pair. By Steps 4 and 5 and part (b), a port occurs in at most `(M_l − 1) + ⌈M_l/2⌉` pairs (if it
belongs to `𝒮_0`) or at most `2(M_l − 1)` pairs (if it belongs to cherry systems). For `M_l ≥ 2`,
`⌈M_l/2⌉ ≤ M_l − 1`, so both are at most `2M_l − 2 < t = 2M_l + 2`." -/
theorem jslcJointMult : EG.Spec.JslcJointMultStatement := by
  classical
  intro V _ G M hM q Sys cherry hS h0uniq h0 hch h0ch hcnt j v
  refine ⟨?_, by omega⟩
  by_cases hv0 : ∃ s, cherry s = false ∧ (Sys s).IsPort v
  · -- `v` is a port of `𝒮_0`: no cherry system contains it
    obtain ⟨s0, hs0, hp0⟩ := hv0
    rw [Finset.sum_eq_single s0]
    · refine ((hS s0).junctionOcc_le j v).trans ?_
      obtain ⟨he, hpad⟩ := h0 s0 hs0 v hp0
      have := ceil_half_le_sub_one hM
      omega
    · intro s _ hne
      cases hcs : cherry s
      · exact absurd (h0uniq s s0 hcs hs0) hne
      · exact HccpData.junctionOcc_eq_zero_of_not_isPort (h0ch v s0 s hs0 hcs hp0) j
    · intro h; exact absurd (Finset.mem_univ s0) h
  · -- only cherry systems contribute, each at most `1 + 1`
    push Not at hv0
    have hle : ∀ s, (Sys s).junctionOcc j v ≤
        if cherry s = true ∧ (Sys s).IsPort v then 2 else 0 := by
      intro s
      split_ifs with hs
      · refine ((hS s).junctionOcc_le j v).trans ?_
        obtain ⟨he, hpad⟩ := hch s hs.1 v hs.2
        omega
      · rw [not_and_or] at hs
        rcases hs with hs | hs
        · have hf : cherry s = false := by simpa using hs
          exact (HccpData.junctionOcc_eq_zero_of_not_isPort (fun hp => hv0 s hf hp) j).le
        · exact (HccpData.junctionOcc_eq_zero_of_not_isPort hs j).le
    refine (Finset.sum_le_sum fun s _ => hle s).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have := hcnt v
    omega

/-- [s6:lemJSLC:proof-claim-d] "(d) There are pairwise edge-disjoint paths in `LJS_{Y,l,j}`, one
for each pair of `𝔓_j(Y,l)` and joining its two vertices. Each has length at most `2^{12}L_Y^4` and
all its interior vertices in `T_j(Y,l)`. … `Y` is lend-good. By Definition s6:defLending and Lemma
s3:lemCOL(b), `LJS_{Y,l,j}` is `(2^{12}L_Y^4, t)`-path connected through `T_j(Y,l)`, as a graph
on `V(Y)`." -/
theorem jslcRouting : EG.Spec.JslcRoutingStatement := by
  classical
  intro V _ G run S l Y j hS hY hlR hj ι _ P hP ht
  unfold lendGoodAnc at hY
  obtain ⟨-, hr, hgood⟩ := Finset.mem_filter.1 hY
  have hB : S.colB Y := by
    by_contra h
    exact hgood (Or.inr (Or.inr h))
  have hlate : l ∈ Stage1.lateRounds run Y.1 := by
    unfold Stage1.lateRounds
    exact Finset.mem_Icc.2 ⟨hr, hlR⟩
  have hconn := hS.colB_conn Y hB l hlate j hj
  obtain ⟨Q, hQ, hdisj⟩ := hconn.exists_paths P
    (fun i => by
      simp only [FGraph.restrictEdges, HB.Run.ancGraph_verts]
      exact hP i)
    (fun w => by exact_mod_cast ht w)
  refine ⟨Q, fun i => ⟨(hQ i).1.mono ?_, (hQ i).2⟩, hdisj⟩
  intro e he
  exact (Finset.mem_filter.1 he).2

end EG
