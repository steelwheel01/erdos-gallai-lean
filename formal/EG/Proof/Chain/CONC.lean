module

public import EG.Spec.Chain.CONC
public import EG.Proof.HB.Origin
public import EG.Lib.Chain.Design

/-!
# Proof of Theorem CONC (i), (ii) (manuscript s6:thmCONC)

Unit P3B (probe P-3, part 2), proof round 1. Statements: `EG/Spec/Chain/CONC.lean`. Design note
`formal/work/p2b/P3B.md`.

* (i): by ORIGIN^τ (a) (`EG.originTypes`) a standalone pre-part has no (α)-edges, so every
  `G_l`-edge `hu` with `u ∈ Y^0 \ Dup*_r` is of type (β); ORIGIN^τ (b) (`EG.originThin`) bounds
  their number by `τ_r - 1`.
* (ii): the port-counting form of `d_{Y,l}(h)` (`EG.Chain.classDeg_eq_card_ports`); the counted
  ports in `Dup*_r` are counted by `d^*_{Y,l}`, the others by (i) (`classPort_facts`: a port of
  class `Y` lies in `V(Y) ⊆ Y^0`, `r(Y) + 2 ≤ l`, and `hu ∈ E_l(Z) ⊆ E(G_l)`).
The sums of (iii) are in `EG.Proof.Chain.ConcSums`.
-/

public section

namespace EG

open EG.HB EG.Chain

namespace Chain

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}

/-- `E_l(Z) ⊆ E(G_l)`. -/
theorem E_subset_graph_edges (l : ℕ) (a : Addr) : run.E G l a ⊆ (run.graph G l).edges :=
  (Run.E_subset_graph'_edges run G l a).trans (Round.graph'_le _ _).2

/-- The facts about a port counted in `d_{Y,l}(h)` (port-counting form): it is a classed port of
round `l ≥ 3` of class `Y(u) = δ l u`, `u ∈ V(Y(u))`, `r(Y(u)) + 2 ≤ l`, `Y(u)` is an ancestor,
and `hu ∈ E(G_l)`. -/
theorem classPort_facts (hδ : IsDesignation run G δ) {l : ℕ} {h u : V} {a : Addr}
    (ha : a ∈ run.Std G l) (hu : u ∈ run.classed G l a) (he : s(h, u) ∈ run.E G l a) :
    3 ≤ l ∧ u ∈ run.ancVerts G (δ l u) ∧ (δ l u).1 + 2 ≤ l ∧ δ l u ∈ run.ancestors G ∧
      s(h, u) ∈ (run.graph G l).edges := by
  have hl : 3 ≤ l := by
    by_contra hl
    rw [classed_eq_empty_of_le_two run G (by omega)] at hu
    exact Finset.notMem_empty u hu
  exact ⟨hl, hδ.mem_ancVerts hl ha hu, hδ.round_add_two_le hl ha hu, hδ.mem_ancestors hl ha hu,
    E_subset_graph_edges l a he⟩

/-- The port set of `d_{Y,l}(h)` splits into the ports in `Dup*_{r(Y)}` (counted by
`d^*_{Y,l}`) and the others. -/
theorem classDeg_le_dStar_add (Y : PartId) (l : ℕ) (h : V) (B : ℕ)
    (hB : (((classedPorts run G l).filter (fun u => δ l u = Y ∧
      ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ s(h, u) ∈ run.E G l a)).filter
        (fun u => u ∉ run.DupStar G Y.1)).card ≤ B) :
    classDeg run G δ Y l h ≤ B + dStar run G δ Y l := by
  classical
  rw [classDeg_eq_card_ports]
  set S := (classedPorts run G l).filter (fun u => δ l u = Y ∧
      ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ s(h, u) ∈ run.E G l a)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun u => u ∈ run.DupStar G Y.1)
  have hD : (S.filter (fun u => u ∈ run.DupStar G Y.1)).card ≤ dStar run G δ Y l := by
    unfold dStar
    refine Finset.card_le_card (fun u hu => ?_)
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    obtain ⟨hu3, hu4, -⟩ := Finset.mem_filter.1 hu1
    exact Finset.mem_filter.2 ⟨hu3, hu4, hu2⟩
  omega

end Chain

open Chain in
/-- [s6:thmCONC] (i) "for every `Y ∈ Std_r`, every `l ≥ r+1` and every vertex `h`:
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r - 1`." -/
theorem concI : EG.Spec.ConcIStatement := by
  classical
  intro V _ G Dstar run hv r a ha l hrl h
  obtain ⟨hpa, hnl⟩ := (Run.mem_Std_iff run G).1 ha
  have hR := Run.isRound_of_mem_prePartAddrs hpa
  have hr : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  refine le_trans (Finset.card_le_card ?_) (originThin V G Dstar run hv r hr a hpa h l (by omega))
  intro u hu
  obtain ⟨hu1, he⟩ := Finset.mem_filter.1 hu
  obtain ⟨-, -, -, -, hcl, -⟩ := originTypes V G Dstar run hv r hr a hpa u hu1
  have he' : s(u, h) ∈ (run.graph G l).edges := by rw [Sym2.eq_swap]; exact he
  rcases hcl l (by omega) h he' with ⟨hβ, -, -⟩ | ⟨hα, -, -⟩
  · exact Finset.mem_filter.2 ⟨hu1, he, hβ⟩
  · exact absurd hα.1 hnl

open Chain in
/-- [s6:thmCONC] (ii) "`m_{Y,l} ≤ τ_r - 1 + d^*_{Y,l}` for every `Y ∈ Std_r` and every `l`." -/
theorem concII : EG.Spec.ConcIIStatement := by
  classical
  intro V _ G Dstar run hv δ hδ r a ha l
  obtain ⟨hpa, hnl⟩ := (Run.mem_Std_iff run G).1 ha
  unfold mY
  refine Finset.sup_le (fun h _ => ?_)
  refine classDeg_le_dStar_add (r, a) l h _ ?_
  by_cases hrl : r + 1 ≤ l
  · refine le_trans (Finset.card_le_card ?_) (concI V G Dstar run hv r a ha l hrl h)
    intro u hu
    obtain ⟨hu1, hD⟩ := Finset.mem_filter.1 hu
    obtain ⟨-, hY, a', ha', hua', he⟩ := Finset.mem_filter.1 hu1
    obtain ⟨-, hV, -, -, hG⟩ := classPort_facts hδ ha' hua' he
    rw [hY] at hV
    have hV' : u ∈ run.Z0 G r a := Run.partVerts_subset_Z0 run G r a hV
    exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hV', hD⟩, hG⟩
  · have : ((classedPorts run G l).filter (fun u => δ l u = (r, a) ∧
        ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ s(h, u) ∈ run.E G l a)).filter
          (fun u => u ∉ run.DupStar G (r, a).1) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      obtain ⟨hu1, -⟩ := Finset.mem_filter.1 hu
      obtain ⟨-, hY, a', ha', hua', he⟩ := Finset.mem_filter.1 hu1
      obtain ⟨-, -, h2, -, -⟩ := classPort_facts hδ ha' hua' he
      rw [hY] at h2
      exact hrl (by simp only at h2; omega)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

end EG
