module

public import EG.Proof.Chain.JSLCStep2Facts

/-!
# JS-LC Step 2: the partition `⋃_Z B_Z = J_l ⊔ ⨆_Y R_Y` and Lemma J⁺ for `J_l`
(manuscript s6:lemJSLC, proof, Steps 2–3; s6:lemJplus)

Probe unit P2J (probe P-2, part 2), proof round 1. Under `Step2Hyp`:
* the partition clauses of `EG.Spec.JslcStep2Statement` (`J_subset`, `R_subset`, `cover`,
  `disjoint_J_R`, `R_disjoint`);
* the structure of `R_Y` and `R_Y ⊆ Bead_{Y,l}` (Step 3: "Every edge `hu ∈ R_Y` lies in
  `Bead_{Y,l}`");
* `jPlusProps`: the fields of `JPlusProps` for `J_l` (the proof of Lemma J⁺: "Types", "(J1)",
  "(J2)", "(ii)"). In particular **(J1) at hubs, aggregated over all parts of round `l`**
  (`J1hub`): a `J^hub`-edge of class `Y` at the hub `h` is the moved edge `mv Y h`, since PAR
  deletions are port–port and the moves are made once per pair (centre, class) with the degree
  aggregated over all parts.
-/

public section

namespace EG.Chain.Step2

open EG.HB

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)}

namespace Step2Hyp

variable (H : Step2Hyp run G δ S l B)
include H

omit H in
theorem R0_subset (Y : PartId) : R0 run G δ S l B Y ⊆ (run.Std G l).biUnion B := by
  intro e he
  obtain ⟨a, ha, heB, -⟩ := mem_R0.1 he
  exact Finset.mem_biUnion.2 ⟨a, ha, heB⟩

omit H in
theorem Jpar_subset : Jpar run G δ S l B ⊆ (run.Std G l).biUnion B := by
  intro e he
  obtain ⟨a, ha, heB, -⟩ := mem_Jpar.1 he
  exact Finset.mem_biUnion.2 ⟨a, ha, heB⟩

theorem Jmov_subset : Jmov run G δ S l B ⊆ (run.Std G l).biUnion B := by
  intro e he
  obtain ⟨Y, -, h, hh, rfl⟩ := mem_Jmov.1 he
  exact R0_subset Y (H.mv_struct hh).1

/-- `J_l ⊆ ⋃_Z B_Z`. -/
theorem J_subset : J run G δ S l B ⊆ (run.Std G l).biUnion B := by
  intro e he
  rcases mem_J.1 he with h | h
  · exact Jpar_subset h
  · exact H.Jmov_subset h

omit H in
/-- `R_Y ⊆ ⋃_Z B_Z`. -/
theorem R_subset (Y : PartId) : R run G δ S l B Y ⊆ (run.Std G l).biUnion B :=
  (Finset.sdiff_subset).trans (R0_subset Y)

/-- `⋃_Z B_Z = J_l ∪ ⋃_Y R_Y`. -/
theorem cover : ∀ e ∈ (run.Std G l).biUnion B, e ∈ J run G δ S l B ∨ ∃ Y, e ∈ R run G δ S l B Y := by
  intro e he
  obtain ⟨a, ha, heB⟩ := Finset.mem_biUnion.1 he
  -- the class of `e`
  have hR0 : e ∈ Jpar run G δ S l B ∨
      ∃ Y ∈ classes run G δ S l, e ∈ R0 run G δ S l B Y := by
    by_cases hpp : IsPP run G δ S l a e
    · by_cases hJ : e ∈ parJ run G δ S l B a (e.map (δ l))
      · exact Or.inl (mem_Jpar.2 ⟨a, ha, heB, hpp, hJ⟩)
      · refine Or.inr ⟨parAsg run G δ S l B a (e.map (δ l)) e, ?_,
          mem_R0.2 ⟨a, ha, heB, Or.inr ⟨hpp, hJ, rfl⟩⟩⟩
        have hmem := H.parAsg_mem ha heB hpp
        induction e using Sym2.ind with
        | _ x w =>
          rw [Sym2.map_mk, Sym2.mem_iff] at hmem
          rcases hmem with h | h
          · rw [Sym2.map_mk, h]; exact mem_classes.2 ⟨a, ha, x, hpp x (by simp), rfl⟩
          · rw [Sym2.map_mk, h]; exact mem_classes.2 ⟨a, ha, w, hpp w (by simp), rfl⟩
    · obtain ⟨u, hu, hue⟩ := (H.hB a ha).2 e heB
      exact Or.inr ⟨δ l u, mem_classes.2 ⟨a, ha, u, hu, rfl⟩,
        mem_R0.2 ⟨a, ha, heB, Or.inl ⟨hpp, u, hu, hue, rfl⟩⟩⟩
  rcases hR0 with h | ⟨Y, hY, h⟩
  · exact Or.inl (mem_J.2 (Or.inl h))
  · by_cases hm : e ∈ Moved run G δ S l B Y
    · exact Or.inl (mem_J.2 (Or.inr (Finset.mem_biUnion.2 ⟨Y, hY, hm⟩)))
    · exact Or.inr ⟨Y, Finset.mem_sdiff.2 ⟨h, hm⟩⟩

/-- `J_l` is disjoint from every `R_Y`. -/
theorem disjoint_J_R (Y : PartId) : Disjoint (J run G δ S l B) (R run G δ S l B Y) := by
  rw [Finset.disjoint_left]
  intro e he heR
  obtain ⟨heR0, hnm⟩ := Finset.mem_sdiff.1 heR
  rcases mem_J.1 he with h | h
  · exact Finset.disjoint_left.1 (H.Jpar_disjoint_R0 Y) h heR0
  · obtain ⟨Y', -, h', hh', rfl⟩ := mem_Jmov.1 h
    have hmem' := (H.mv_struct hh').1
    by_cases hYY : Y' = Y
    · subst hYY
      exact hnm (Finset.mem_image.2 ⟨h', hh', rfl⟩)
    · exact Finset.disjoint_left.1 (H.R0_disjoint hYY) hmem' heR0

/-- The `R_Y` of distinct classes are disjoint. -/
theorem R_disjoint {Y Y' : PartId} (hYY : Y ≠ Y') :
    Disjoint (R run G δ S l B Y) (R run G δ S l B Y') :=
  Finset.disjoint_of_subset_left Finset.sdiff_subset
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (H.R0_disjoint hYY))

/-- The structure of the realized beads: `hu ∈ E_l(Z)` with port `u ∈ Q*_Z` of class `Y` and
centre `h ∉ V(Y)`. -/
theorem R_struct (Y : PartId) : ∀ e ∈ R run G δ S l B Y, ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
    ∃ h u, e = s(h, u) ∧ u ∈ qs run G δ S l a ∧ δ l u = Y ∧ h ∉ run.ancVerts G Y := by
  intro e he
  obtain ⟨a, ha, heB, h, u, heq, hu, hY, hh, -⟩ := H.R0_struct (Finset.mem_sdiff.1 he).1
  exact ⟨a, ha, H.mem_E ha heB, h, u, heq, hu, hY, hh⟩

/-- [s6:lemJSLC] (proof, Step 3) "Every edge `hu ∈ R_Y` lies in `Bead_{Y,l}`: `hu ∈ E_l(Z)`,
`u ∈ Q*_Z ⊆ Q_Z`, `Y(u) = Y`, and `h` is not a class-`Y` port of `Q_Z` (a class-`Y` vertex of
`Q_Z` lies in `V(Y)`, and `h ∉ V(Y)`)." -/
theorem R_subset_Bead (Y : PartId) : R run G δ S l B Y ⊆ Bead run G δ Y l := by
  classical
  intro e he
  obtain ⟨a, ha, heE, h, u, rfl, hu, hY, hh⟩ := H.R_struct Y e he
  unfold Bead
  refine Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2 ⟨heE, h, u, rfl, H.qs_classed hu, hY, ?_⟩⟩
  by_cases hc : h ∈ run.classed G l a
  · right
    intro hhY
    exact hh (hhY ▸ H.hδ.mem_ancVerts H.l3 ha hc)
  · exact Or.inl hc

/-! ### Lemma J⁺ for `J_l` -/

/-- A J-edge with an end `c ∉ Q*_Z` and an end `u ∈ Q*_Z` of class `Y` is the moved edge
`mv Y c` (PAR deletions are port–port). -/
theorem eq_mv_of_mem_J {e : Sym2 V} (he : e ∈ J run G δ S l B) {a : Addr}
    (ha : a ∈ run.Std G l) (heE : e ∈ run.E G l a) {c u : V} (heq : e = s(c, u))
    (hc : c ∉ qs run G δ S l a) (hu : u ∈ qs run G δ S l a) :
    c ∈ oddC run G δ S l B (δ l u) ∧ e = mv run G δ S l B (δ l u) c := by
  rcases mem_J.1 he with h | h
  · exfalso
    obtain ⟨a', ha', heB, hpp⟩ := Jpar_struct h
    obtain rfl := eq_of_mem_E run G (H.mem_E ha' heB) heE
    exact hc (hpp c (by rw [heq]; simp))
  · exact H.eq_mv_of_mem_Jmov h ha heE heq hc hu

/-- (J1) in the generic form: the J-edges `cu` of class `Y` (with `c ∉ Q*_Z`) at a fixed vertex
`c` are at most one. -/
theorem card_filter_le_one (c : V) (Y : PartId) (P : Sym2 V → Prop) [DecidablePred P]
    (hP : ∀ e, P e → ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧ ∃ u, e = s(c, u) ∧
      c ∉ qs run G δ S l a ∧ u ∈ qs run G δ S l a ∧ δ l u = Y) :
    ((J run G δ S l B).filter P).card ≤ 1 := by
  refine (Finset.card_le_card (t := {mv run G δ S l B Y c}) ?_).trans (Finset.card_singleton _).le
  intro e he
  obtain ⟨heJ, hPe⟩ := Finset.mem_filter.1 he
  obtain ⟨a, ha, heE, u, heq, hc, hu, rfl⟩ := hP e hPe
  rw [(H.eq_mv_of_mem_J heJ ha heE heq hc hu).2]
  exact Finset.mem_singleton_self _

/-- Every J-edge lies in `B_Z ⊆ E_l(Z)` for some `Z ∈ Std_l`. -/
theorem exists_B_of_mem_J {e : Sym2 V} (he : e ∈ J run G δ S l B) :
    ∃ a ∈ run.Std G l, e ∈ B a :=
  Finset.mem_biUnion.1 (H.J_subset he)

/-- The J-edges at a vertex outside `D_l` lie in one `E_l(Z)`. -/
theorem degE_J_le_of_notMem_D {v : V} (hv : v ∉ run.D G l) :
    degE (J run G δ S l B) v ≤ run.M G l - 1 := by
  by_cases hne : (edgesAt (J run G δ S l B) v).Nonempty
  · obtain ⟨e0, he0⟩ := hne
    rw [FGraph.mem_edgesAt] at he0
    obtain ⟨a0, ha0, he0B⟩ := H.exists_B_of_mem_J he0.1
    have hsub : edgesAt (J run G δ S l B) v ⊆ edgesAt (run.E G l a0) v := by
      intro e he
      rw [FGraph.mem_edgesAt] at he ⊢
      obtain ⟨a, ha, heB⟩ := H.exists_B_of_mem_J he.1
      have heE := H.mem_E ha heB
      have : a = a0 := eq_of_mem_Z0_of_notMem_D run G (Std_subset_prePartAddrs run G l ha)
        (Std_subset_prePartAddrs run G l ha0)
        (Run.partVerts_subset_Z0 run G l a (Run.mem_partVerts_of_mem_E run G heE he.2))
        (Run.partVerts_subset_Z0 run G l a0
          (Run.mem_partVerts_of_mem_E run G (H.mem_E ha0 he0B) he0.2)) hv
      subst this
      exact ⟨heE, he.2⟩
    exact (Finset.card_le_card hsub).trans (H.cap a0 ha0 v)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold degE; rw [hne]; exact Nat.zero_le _

/-- (J2) `|J_l| ≤ n (M_l − 1)`: charge every J-edge to an end in `Q*_Z`. -/
theorem card_J_le : (J run G δ S l B).card ≤ G.card * (run.M G l - 1) := by
  classical
  set Q := (qsRound run G δ S l).filter (fun u => u ∈ G.verts) with hQ
  have hsub : J run G δ S l B ⊆ Q.biUnion (edgesAt (J run G δ S l B)) := by
    intro e he
    obtain ⟨a, ha, heB⟩ := H.exists_B_of_mem_J he
    obtain ⟨u, hu, hue⟩ := (H.hB a ha).2 e heB
    have huG : u ∈ G.verts := G.edge_verts e (E_subset_edges run G l a (H.mem_E ha heB)) u hue
    refine Finset.mem_biUnion.2 ⟨u, Finset.mem_filter.2 ⟨(mem_qsRound run G δ S).2 ⟨a, ha, hu⟩,
      huG⟩, FGraph.mem_edgesAt.2 ⟨he, hue⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have h1 : ∀ u ∈ Q, (edgesAt (J run G δ S l B) u).card ≤ run.M G l - 1 := by
    intro u hu
    obtain ⟨a, -, hu⟩ := (mem_qsRound run G δ S).1 (Finset.mem_filter.1 hu).1
    exact H.degE_J_le_of_notMem_D (H.qs_notMem_D hu)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  unfold FGraph.card
  exact Finset.card_le_card (fun u hu => (Finset.mem_filter.1 hu).2)

/-- [s6:lemJplus] **Lemma J⁺** for the set `J_l` of Step 2: types (i), (J1) aggregated at hubs,
fresh and lost centres, (J2), (ii). -/
theorem jPlusProps : JPlusProps run G δ S l (J run G δ S l B) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, H.card_J_le, ?_⟩
  · -- (i) types
    intro e he
    rcases mem_J.1 he with h | h
    · obtain ⟨a, ha, heB, hpp⟩ := Jpar_struct h
      left
      induction e using Sym2.ind with
      | _ x w =>
        have hx := hpp x (by simp)
        have hw := hpp w (by simp)
        exact ⟨a, ha, H.mem_E ha heB, x, w, rfl, hx, hw,
          H.pp a ha x (H.qs_classed hx) w (H.qs_classed hw) (H.mem_E ha heB)⟩
    · obtain ⟨Y, -, c, hc, rfl⟩ := mem_Jmov.1 h
      obtain ⟨-, a, ha, heB, u, heq, hu, hY, hcr, -⟩ := H.mv_struct hc
      have heE := H.mem_E ha heB
      rw [heq]
      rw [heq] at heE
      unfold ret at hcr
      rcases Finset.mem_union.1 hcr with hcr | hcr
      · rcases Finset.mem_union.1 hcr with hcr | hcr
        · exact Or.inr (Or.inl ⟨c, Y, a, ha, heE, u, rfl, hcr, hu, hY⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨c, Y, a, ha, heE, u, rfl, hcr, hu, hY⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨c, Y, a, ha, heE, u, rfl, hcr, hu, hY⟩))
  · -- (J1) at hubs, aggregated
    intro h _ Y
    refine H.card_filter_le_one h Y _ fun e he => ?_
    obtain ⟨a, ha, heE, u, heq, hh, hu, hY⟩ := he
    exact ⟨a, ha, heE, u, heq,
      fun hq => Finset.disjoint_left.1 (disjoint_hubs_qs run G δ S l a a) hh hq, hu, hY⟩
  · -- (J1) at fresh centres
    intro x _ Y
    refine H.card_filter_le_one x Y _ fun e he => ?_
    obtain ⟨a, ha, heE, u, heq, hx, hu, hY⟩ := he
    exact ⟨a, ha, heE, u, heq,
      fun hq => Finset.disjoint_left.1 (disjoint_fresh_qs run G δ S l a) hx hq, hu, hY⟩
  · -- (J1) at lost centres
    intro v _ Y
    refine H.card_filter_le_one v Y _ fun e he => ?_
    obtain ⟨a, ha, heE, u, heq, hv, hu, hY⟩ := he
    exact ⟨a, ha, heE, u, heq,
      fun hq => Finset.disjoint_left.1 (disjoint_lost_qs run G δ S l a) hv hq, hu, hY⟩
  · -- (J2) an end in `Q*_Z`
    intro a ha e he heE
    obtain ⟨a', ha', heB⟩ := H.exists_B_of_mem_J he
    obtain rfl := eq_of_mem_E run G (H.mem_E ha' heB) heE
    exact (H.hB a' ha').2 e heB
  · -- (J2) per-part cap
    intro a ha v
    refine (Finset.card_le_card ?_).trans (H.cap a ha v)
    intro e he
    obtain ⟨-, heE, hv⟩ := Finset.mem_filter.1 he
    exact FGraph.mem_edgesAt.2 ⟨heE, hv⟩
  · -- (J2) outside `D_l`
    intro v hv
    exact H.degE_J_le_of_notMem_D hv
  · -- (ii)
    intro x hx
    obtain ⟨a, -, hxa⟩ := (mem_freshCentres run G).1 hx
    refine (Finset.card_le_card ?_).trans
      (H.degE_J_le_of_notMem_D (not_mem_D_of_mem_ports run G (fresh_subset_ports run G l a hxa)))
    intro e he
    obtain ⟨heJ, Y, a', -, -, u, rfl, -⟩ := Finset.mem_filter.1 he
    exact FGraph.mem_edgesAt.2 ⟨heJ, Sym2.mem_mk_left _ _⟩

end Step2Hyp

end EG.Chain.Step2
