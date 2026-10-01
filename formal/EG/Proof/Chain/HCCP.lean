module

public import EG.Spec.Chain.HCCP
public import EG.Lib.Chain.HccpPot
public import EG.Proof.Chain.Gate

/-!
# Proof of Lemma HCC-P (manuscript s6:lemHCCP)

`EG.hccp : EG.Spec.HccpStatement`. Probe unit P2E (probe P-2, part 1), proof round 1. The proof
follows the manuscript step by step; the lemmas are in `EG.Lib.Chain.HccpPaths` (Step 1),
`EG.Lib.Chain.HccpAux` (Step 0, the length count of Step 4) and `EG.Lib.Chain.HccpPot` (Steps 2
and 3).
* Step 0: `Φ_j = |𝒫_j| = Φ_{j+1}` (uses Lemma MED (b), `∑ exc = 0`);
* Step 1: `D_j` orients `E(𝒫_j)`; cancelling a balanced `R_j ⊆ D_j` leaves an acyclic `D'_j`, and
  `R_j` lies inside `T_j`; `F_j` is the edge set of `D'_j`;
* Step 2: `F⃗ = ⋃_i O_i ∪ ⋃_j D'_j` orients `F = ⋃_𝒦 B_𝒦 ∪ ⋃_j F_j` and is balanced;
* Step 3: `Ψ` increases along every arc outside `𝒲` (the arcs of `D'_{k-1}` into `LayP_0`), and
  `|𝒲| ≤ |𝒫_{k-1}| = Φ`;
* Step 4: GATE (`EG.gate_with_cycles`) gives at most `|𝒲|` cycles of `G`, each of length `≥ 3`,
  each through an arc of `𝒲`, hence of length `≥ k` (`EG.le_length_of_blocks`).
-/

public section

namespace EG

open EG.Chain EG.Chain.HccpData

variable {V : Type*} [DecidableEq V]

/-- [s6:lemHCCP] (proof, Step 2) "Every port is balanced ... `d⁺(u) − d⁻(u) = exc(u) + dem⁻(u) −
dem⁺(u) = 0`": the integer identity behind the balance of `F⃗`, for any vertex. -/
theorem hccp_exc_sum_eq_zero {G : FGraph V} {S : HccpData V} (hS : S.Valid G) (v : V) :
    (∑ i, exc (S.O i) v) +
      ∑ j, ((((if v ∈ S.layP j then S.demMinus v else 0 : ℕ) : ℤ)) -
        ((if v ∈ S.layP (S.succ j) then S.demPlus v else 0 : ℕ) : ℤ)) = 0 := by
  rw [hS.sum_exc_O v, Finset.sum_sub_distrib]
  -- reindex the `dem⁺` sum along the bijection `succ`
  have hre : ∑ j, (((if v ∈ S.layP (S.succ j) then S.demPlus v else 0 : ℕ) : ℤ)) =
      ∑ j, (((if v ∈ S.layP j then S.demPlus v else 0 : ℕ) : ℤ)) :=
    (S.succ_bijective).sum_comp (fun j => (((if v ∈ S.layP j then S.demPlus v else 0 : ℕ) : ℤ)))
  rw [hre]
  have hind := hS.sum_layP_ind_le_one v
  have hm : ∑ j, (((if v ∈ S.layP j then S.demMinus v else 0 : ℕ) : ℤ)) =
      (∑ j, (if v ∈ S.layP j then (1 : ℤ) else 0)) * S.demMinus v := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hp : ∑ j, (((if v ∈ S.layP j then S.demPlus v else 0 : ℕ) : ℤ)) =
      (∑ j, (if v ∈ S.layP j then (1 : ℤ) else 0)) * S.demPlus v := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hm, hp]
  have hnn : 0 ≤ ∑ j, (if v ∈ S.layP j then (1 : ℤ) else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  rcases (show ∑ j, (if v ∈ S.layP j then (1 : ℤ) else 0) = 0 ∨
      ∑ j, (if v ∈ S.layP j then (1 : ℤ) else 0) = 1 by omega) with h0 | h1
  · -- `v` is no port
    have hall : ∀ j, v ∉ S.layP j := by
      intro j hj
      have := Finset.single_le_sum (f := fun j => if v ∈ S.layP j then (1 : ℤ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      simp only [hj, if_true] at this
      omega
    rw [h0, pexc_eq_zero_of_forall_not_mem hall]
    ring
  · rw [h1]
    unfold demMinus demPlus
    push_cast
    omega

/-- [s6:lemHCCP] (proof, Step 1) The sets `F_j`: for a balanced `R ⊆ D_j`, the edge set `F_j` of
`D'_j = D_j ∖ R` satisfies `F_j ⊆ E(𝒫_j)` and `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])` ("`E(𝒫_j) ∖ F_j ⊆
E(G[T_j])`"). -/
theorem hccp_F_props {G : FGraph V} {S : HccpData V} (hS : S.Valid G) (j : Fin S.k)
    {R : Finset (V × V)} (hR : R ⊆ S.pathArcs j) (hbal : IsBalanced R) :
    (S.pathArcs j \ R).image (fun a => s(a.1, a.2)) ⊆ S.pathEdges j ∧
      S.pathEdges j \ (S.pathArcs j \ R).image (fun a => s(a.1, a.2)) ⊆
        (G.induce (S.T j)).edges := by
  have hO := hS.isOrientation_pathArcs j
  constructor
  · intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
    exact hO.mem a (Finset.mem_sdiff.1 ha).1
  · intro e he
    obtain ⟨heP, heF⟩ := Finset.mem_sdiff.1 he
    obtain ⟨a, ha, rfl⟩ := hO.exists_mem heP
    have haR : a ∈ R := by
      by_contra haR
      exact heF (Finset.mem_image.2 ⟨a, Finset.mem_sdiff.2 ⟨ha, haR⟩, rfl⟩)
    obtain ⟨h1, h2⟩ := hS.cancel_arcs_mem_T j hR hbal haR
    have heG : s(a.1, a.2) ∈ G.edges := by
      obtain ⟨p, hp, hep⟩ := (S.mem_pathEdges).1 heP
      exact (hS.path_G j p hp).2.2 _ hep
    unfold FGraph.induce
    simp only [Finset.mem_filter, Finset.mem_sym2_iff]
    refine ⟨heG, fun v hv => ?_⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact h1
    · exact h2

/-- [s6:lemHCCP] "Let `k ≥ 1`, and suppose the following data are given. ... Assume: (D) ...;
(P) ...; (JC-P) ... Then:
(i) all `Φ_j` are equal to a common value `Φ`, and `Φ = |𝒫_j|` for every `j`;
(ii) there are sets `F_j ⊆ E(𝒫_j)` with `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])` such that
`⋃_𝒦 B_𝒦 ∪ ⋃_j F_j` decomposes into at most `Φ` cycles of `G`, each of length at least
`max(3,k)`." -/
theorem hccp : EG.Spec.HccpStatement := by
  intro V _ G S hS
  -- Step 0: the loads
  set Φ := S.Phi ⟨0, hS.k_pos⟩ with hΦ
  refine ⟨Φ, fun j => ⟨hS.Phi_eq_Phi_zero j,
    (hS.length_P_eq_Phi j).trans (hS.Phi_eq_Phi_zero j)⟩, ?_⟩
  -- Step 1: orient and cancel
  choose R hRsub hRbal hRac using fun j => exists_balanced_sdiff_acyclic (S.pathArcs j)
  set D' : Fin S.k → Finset (V × V) := fun j => S.pathArcs j \ R j with hD'
  set F : Fin S.k → Finset (Sym2 V) := fun j => (D' j).image (fun a => s(a.1, a.2)) with hF
  have hFprops := fun j => hccp_F_props hS j (hRsub j) (hRbal j)
  refine ⟨F, fun j => hFprops j, ?_⟩
  have hD'sub : ∀ j, D' j ⊆ S.pathArcs j := fun j => Finset.sdiff_subset
  have hOrD' : ∀ j, IsOrientation (F j) (D' j) := fun j =>
    (hS.isOrientation_pathArcs j).subset (hD'sub j)
  -- Step 2: the Eulerian digraph
  have hFdisj : ∀ j j', j ≠ j' → Disjoint (F j) (F j') := fun j j' h =>
    Finset.disjoint_of_subset_left (hFprops j).1
      (Finset.disjoint_of_subset_right (hFprops j').1 (hS.pp_disj j j' h))
  have hOrB : IsOrientation S.beads (Finset.univ.biUnion S.O) :=
    isOrientation_biUnion Finset.univ (fun i => (S.K i).beads) S.O
      (fun i _ => (hS.adm i).orient) (fun i _ i' _ h => hS.bb_disj i i' h)
  have hOrP : IsOrientation (Finset.univ.biUnion F) (Finset.univ.biUnion D') :=
    isOrientation_biUnion Finset.univ F D' (fun j _ => hOrD' j) (fun j _ j' _ h => hFdisj j j' h)
  have hBP : Disjoint S.beads (Finset.univ.biUnion F) := by
    rw [Finset.disjoint_biUnion_right]
    intro j _
    rw [HccpData.beads, Finset.disjoint_biUnion_left]
    intro i _
    exact Finset.disjoint_of_subset_right (hFprops j).1 (hS.pb_disj j i).symm
  set A := Finset.univ.biUnion S.O ∪ Finset.univ.biUnion D' with hA
  have hOr : IsOrientation (S.beads ∪ Finset.univ.biUnion F) A := hOrB.union hOrP hBP
  have hFG : S.beads ∪ Finset.univ.biUnion F ⊆ G.edges := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨i, hi⟩ := (S.mem_beads).1 he
      exact hS.beads_G i hi
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 he
      obtain ⟨p, hp, hep⟩ := (S.mem_pathEdges).1 ((hFprops j).1 hj)
      exact (hS.path_G j p hp).2.2 _ hep
  have hbal : IsBalanced A := by
    intro v
    have hdO : ∀ i ∈ (Finset.univ : Finset (Fin S.N)), ∀ i' ∈ (Finset.univ : Finset (Fin S.N)),
        i ≠ i' → Disjoint (S.O i) (S.O i') := fun i _ i' _ h =>
      (hS.adm i).orient.disjoint (hS.adm i').orient (hS.bb_disj i i' h)
    have hdD : ∀ j ∈ (Finset.univ : Finset (Fin S.k)), ∀ j' ∈ (Finset.univ : Finset (Fin S.k)),
        j ≠ j' → Disjoint (D' j) (D' j') := fun j _ j' _ h =>
      (hOrD' j).disjoint (hOrD' j') (hFdisj j j' h)
    have hdA : Disjoint (Finset.univ.biUnion S.O) (Finset.univ.biUnion D') :=
      hOrB.disjoint hOrP hBP
    have hexc : ∀ j, (outDeg (D' j) v : ℤ) - inDeg (D' j) v = exc (S.pathArcs j) v := by
      intro j
      have h1 := outDeg_sdiff (hRsub j) v
      have h2 := inDeg_sdiff (hRsub j) v
      have h3 := outDeg_mono (hRsub j) v
      have h4 := inDeg_mono (hRsub j) v
      have h5 := hRbal j v
      unfold exc
      simp only [hD']
      omega
    have key := hccp_exc_sum_eq_zero hS v
    have hsum : (outDeg A v : ℤ) - inDeg A v =
        (∑ i, exc (S.O i) v) + ∑ j, exc (S.pathArcs j) v := by
      rw [hA, outDeg_union hdA, inDeg_union hdA, outDeg_biUnion _ _ hdO, inDeg_biUnion _ _ hdO,
        outDeg_biUnion _ _ hdD, inDeg_biUnion _ _ hdD]
      push_cast
      rw [← Finset.sum_congr rfl (fun j _ => hexc j)]
      unfold exc
      simp only [Finset.sum_sub_distrib]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hS.exc_pathArcs j v)] at hsum
    have : (outDeg A v : ℤ) - inDeg A v = 0 := by rw [hsum]; exact key
    omega
  -- Step 3: the potential and `𝒲`
  choose pc hpc_inj hpc_rng hpc_inc using fun i =>
    (hS.adm i).acyclic.exists_potential (S.K i).verts
      (fun a ha => ⟨Cluster.fst_mem_verts_of_orient (hS.adm i).orient ha,
        Cluster.snd_mem_verts_of_orient (hS.adm i).orient ha⟩)
  choose tp htp_inj htp_rng htp_inc using fun j =>
    ((hRac j).mono (Finset.filter_subset (fun a => a.1 ∈ S.T j ∧ a.2 ∈ S.T j) _)).exists_potential
      (S.T j) (fun a ha => (Finset.mem_filter.1 ha).2)
  have hk1 : 1 ≤ S.k := hS.k_pos
  set jl : Fin S.k := ⟨S.k - 1, by omega⟩ with hjl
  set W := (D' jl).filter (fun a => a.2 ∈ S.layP (S.succ jl)) with hW
  have hWA : W ⊆ A := fun a ha =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨jl, Finset.mem_univ _,
      (Finset.mem_filter.1 ha).1⟩)
  have hacyc : IsAcyclic (A \ W) := by
    refine isAcyclic_of_potential (S.psi pc tp) fun a ha => ?_
    obtain ⟨haA, haW⟩ := Finset.mem_sdiff.1 ha
    rcases Finset.mem_union.1 haA with ha' | ha'
    · obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.1 ha'
      exact hS.psi_lt_O tp hpc_inc hai
    · obtain ⟨j, -, haj⟩ := Finset.mem_biUnion.1 ha'
      refine hS.psi_lt_pathArcs hpc_rng htp_rng (hD'sub j haj)
        (fun h1 h2 => htp_inc j a (Finset.mem_filter.2 ⟨haj, h1, h2⟩)) (fun h2 => ?_)
      by_contra hj
      have hjj : j = jl := Fin.ext (by simp only [hjl]; omega)
      subst hjj
      exact haW (Finset.mem_filter.2 ⟨haj, h2⟩)
  have hWcard : W.card ≤ Φ := by
    have h1 : W.card ≤ ((S.pathArcs jl).filter (fun a => a.2 ∈ S.layP (S.succ jl))).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (hD'sub jl))
    rw [← Cluster.sum_inDeg_eq_card_filter (S.pathArcs jl)] at h1
    have h2 : ∑ v ∈ S.layP (S.succ jl), inDeg (S.pathArcs jl) v ≤
        ∑ v ∈ S.layP (S.succ jl), S.demPlus v := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hvT : v ∉ S.T jl := by
        obtain ⟨i, -, hvi⟩ := mem_verts_of_mem_layP hv
        exact Finset.disjoint_left.1 (hS.D_KT i jl) hvi
      have := hS.inDeg_pathArcs_le jl hvT
      rwa [hS.countP_last_eq jl v, if_pos hv] at this
    have h3 : ∑ v ∈ S.layP (S.succ jl), S.demPlus v = Φ := by
      rw [hΦ, ← hS.Phi_eq_Phi_zero (S.succ jl)]
      rfl
    omega
  -- Step 4: GATE, count and length
  obtain ⟨cs, hdec, hlen, hcs⟩ := gate_with_cycles G _ A W hFG hOr hbal hWA hacyc
  refine ⟨cs.map Obj.cycle, hdec, by rw [List.length_map]; omega, ?_⟩
  intro o ho
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
  obtain ⟨hcyc, h3, hcG, w, hwW, hwc⟩ := hcs c hc
  refine ⟨c, rfl, max_le h3 ?_, hcG⟩
  refine le_length_of_blocks S.blk S.k (A := A) (W := W) ?_ ?_ hcyc.2.2 hwW hwc
  · intro a ha
    rcases Finset.mem_union.1 ha with ha' | ha'
    · obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.1 ha'
      rw [hS.blk_O hai]; omega
    · obtain ⟨j, -, haj⟩ := Finset.mem_biUnion.1 ha'
      exact hS.blk_pathArcs (hD'sub j haj)
  · intro a ha
    obtain ⟨haD, ha2⟩ := Finset.mem_filter.1 ha
    have hs0 : (S.succ jl).val = 0 := by
      rw [succ_val]
      simp only [hjl]
      rw [Nat.sub_add_cancel hk1, Nat.mod_self]
    refine ⟨?_, ?_⟩
    · rw [hS.blk_of_mem_layP ha2, hs0]
    · rw [hS.blk_fst_pathArcs (hD'sub jl haD)]
      simp only [hjl]
      omega

end EG
