module

public import EG.Spec.Light.ParentRun
public import EG.Proof.HB.TowerBM
public import EG.Proof.HB.TowerA
public import EG.Proof.HB.StructureLight
public import EG.Proof.HB.CapPrePart
public import EG.Lib.Lend.Standing
public import EG.Lib.Light.Stages

/-!
# Proofs of the run-level Step 5 nodes of Lemma parent side (s5:lemParent, Step 5)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.mlTy` (`MlTyStatement`,
"`M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ t_Y`", refutation target) and `EG.bundleEndCount`
(`BundleEndCountStatement`, "every vertex is an end of at most `M_l − 1` arcs of `B_{l,c}`",
refutation target). Declared inputs used: `EG.towerBM` ([s2:lemTower] (b), `M_l` clauses),
`EG.towerA` ([s2:lemTower] (a)), `EG.capPrePart` ([s2:lemCap] (ii)), `EG.structureVertex`
(through `EG.structureLight`, [s2:propStructure] (iv)). Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemParent] Step 5, "Comparison with `t_Y`": "By Lemma s2:lemTower(b) (row 12 …) and Lemma
s2:lemTower(a), `M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ ⌈λ_r^{1.6}⌉ = t_Y`. So `v` lies in at most
`M_l − 1 < t_Y` pairs." -/
theorem mlTy : EG.Spec.MlTyStatement.{u} := by
  intro V _ G N0 Dstar run h Y hY l hl hlR
  obtain ⟨hΓ, -, -, -, hd1, hV⟩ := h
  have hY1 : 1 ≤ Y.1 := (Finset.mem_Icc.1 ((mem_lightParts_iff G run Y).1 hY).1).1
  have hl3 : 3 ≤ l := by omega
  obtain ⟨hBM, -⟩ := towerBM V G Dstar run hΓ.1 hV hd1
  have hM := hBM l hl3 hlR
  have hA := (towerA V G Dstar run hΓ.1 hV hd1).2.2.2.2 Y.1 l hY1 hl (by omega)
  have hpos : 0 < run.lam G (l - 2) :=
    (Standing.lam_facts hΓ hV (l := l - 2) ⟨by omega, by omega⟩).2.1
  have h1 : (run.M G l : ℝ) ≤ run.lam G (l - 2) ^ (1.6 : ℝ) := hM.1.trans hM.2
  have h2 : run.lam G (l - 2) ^ (1.6 : ℝ) ≤ run.lam G Y.1 ^ (1.6 : ℝ) :=
    Real.rpow_le_rpow hpos.le hA (by norm_num)
  have h3 : run.M G l ≤ tY G run Y := by
    unfold tY
    exact_mod_cast (h1.trans h2).trans (Nat.le_ceil _)
  have hposr : 0 < run.lam G Y.1 := hpos.trans_le hA
  have h4 : 1 ≤ tY G run Y := by
    unfold tY
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hposr _)).ne'
  exact ⟨h1, h2, h3, by omega⟩

/-- The phase-`c` arcs of `Z` have at most as many ends at `v` as all arcs of `Z`. -/
theorem pathEndCount_filter_le {V : Type*} [DecidableEq V] (as : List (Arc V)) (c : Fin 4)
    (v : V) :
    pathEndCount ((as.filter fun a => a.2 = c).map Prod.fst) v ≤
      pathEndCount (as.map Prod.fst) v := by
  unfold pathEndCount
  exact ((List.filter_sublist (l := as)).map Prod.fst).countP_le

/-- A vertex that is an end of some arc of an `ArcSys` family lies in `V(Z)`. -/
theorem mem_ancVerts_of_pathEndCount_pos {V : Type*} [DecidableEq V] {G : FGraph V}
    {run : Run V} {ω : Outcome G run} {Z : PartId} {H0 : Finset (Sym2 V)} {as : List (Arc V)}
    (hA : ArcSys ω Z H0 as) (c : Fin 4) (v : V)
    (hpos : 0 < pathEndCount ((as.filter fun a => a.2 = c).map Prod.fst) v) :
    v ∈ run.ancVerts G Z := by
  unfold pathEndCount at hpos
  obtain ⟨p, hp, hpv⟩ := List.countP_pos_iff.1 hpos
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
  have haZ : a ∈ as := (List.mem_filter.1 ha).1
  have hRt := (hA.2.1 a haZ).2.2.1 v (by simpa using hpv)
  exact (Finset.mem_filter.1 hRt).1

/-- [s5:lemParent] Step 5, "Counting": "the number of arcs of `B_{l,c}` having `v` as an end.
By (F-d) and (F-c), all of them are arcs of the unique round-`l` light part `Z(v)` containing `v`,
and there are at most `|Z(v)|−1 ≤ M_l−1` of them." (The bound `deg_{H_0(Z)}(v) ≤ M_l − 1` is
[s2:lemCap] (ii) for `H_0(Z) ⊆ E_l(Z)`, as in (F-d).) -/
theorem bundleEndCount : EG.Spec.BundleEndCountStatement.{u} := by
  intro V _ G N0 Dstar run h ω _ l hl3 hlR H0 arcs hArc c v
  have hSL := structureLight V G N0 Dstar run h
  obtain ⟨hΓ, -, -, -, -, hV⟩ := h
  -- the bound for one part
  have hone : ∀ Z ∈ childParts ω l,
      pathEndCount (((arcs Z).filter fun a => a.2 = c).map Prod.fst) v ≤ run.M G l - 1 := by
    intro Z hZ
    have hZ' := (mem_childParts ω).1 hZ
    obtain ⟨hZl, hZa, -⟩ := (mem_lightParts_iff G run Z).1 hZ'.1
    have hZ1 : Z.1 = l := hZ'.2.1
    obtain ⟨hH0, hAS⟩ := hArc Z hZ
    have hcap := (capPrePart V G Dstar run hΓ.1.gamma2a hV Z.1 hZl).2 Z.2 hZa
    refine (pathEndCount_filter_le _ c v).trans ((hAS.2.2.2.1 v).1.trans ?_)
    refine (FGraph.degE_mono hH0.2 v).trans ?_
    rw [← hZ1]
    exact hcap.2 v
  by_cases hex : ∃ Z ∈ childParts ω l, v ∈ run.ancVerts G Z
  · obtain ⟨Z0, hZ0, hvZ0⟩ := hex
    rw [Finset.sum_eq_single_of_mem Z0 hZ0]
    · exact hone Z0 hZ0
    · intro Z hZ hne
      by_contra hpos
      have hv := mem_ancVerts_of_pathEndCount_pos (hArc Z hZ).2 c v (Nat.pos_of_ne_zero hpos)
      have hZL := ((mem_childParts ω).1 hZ).1
      have hZ0L := ((mem_childParts ω).1 hZ0).1
      have hr : Z.1 = Z0.1 := (((mem_childParts ω).1 hZ).2.1).trans
        (((mem_childParts ω).1 hZ0).2.1).symm
      exact Finset.disjoint_left.1 (hSL Z hZL Z0 hZ0L hr hne) hv hvZ0
  · push Not at hex
    rw [Finset.sum_eq_zero]
    · exact Nat.zero_le _
    · intro Z hZ
      by_contra hpos
      exact hex Z hZ (mem_ancVerts_of_pathEndCount_pos (hArc Z hZ).2 c v (Nat.pos_of_ne_zero hpos))

end EG
