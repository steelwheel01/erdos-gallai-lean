module

public import EG.Lib.Found.Graph

/-!
# Depth-first search as an invariant relation (for manuscript s1:citLem25)

The proof of [BM, Lemma 25] ([s1:citLem25]) runs a depth-first search on an expander `G` and
stops "at the moment `|U| = |R|`". We model the search as an invariant on its states
(PLAN_FORMALIZATION §2, "the DFS proof, as an invariant relation"; design note
`formal/work/ext/lemma25.md`):

* a state is `(U, R, P)`: the unexplored vertices `U`, the processed vertices `R`, and the
  current DFS path `P`, a vertex list whose HEAD is the active end `t(P)`;
* `EG.DFS.Inv G U R P`: `U`, `R`, `P` partition `V(G)`, `P` is a path of `G`, and there is no
  edge between `U` and `R`;
* `EG.DFS.Inv.step`: while `U ≠ ∅` one DFS step (extend `P` into `U`, backtrack `t(P)` into
  `R`, or, if `P = []`, restart at a vertex of `U`) keeps the invariant and lowers `|U| - |R|`
  by exactly one;
* `EG.DFS.exists_balanced`: some state satisfying the invariant has `|U| = |R|` (a discrete
  intermediate value argument, by induction on `|U| - |R|`, starting from `(V(G), ∅, [])`);
* `EG.DFS.Inv.nbrSet_subset`: then `Nbr_G(U) ⊆ V(P)`.

Unlike [BM] we allow restarts when the path becomes empty; hence connectivity of `G` is never
needed.
-/

public section


namespace EG

namespace DFS

variable {V : Type*} [DecidableEq V]

/-- The DFS invariant on a state `(U, R, P)` of the search in `G`: unexplored set `U`,
processed set `R`, current path `P` (active end at the head). -/
structure Inv (G : FGraph V) (U R : Finset V) (P : List V) : Prop where
  U_sub : U ⊆ G.verts
  R_sub : R ⊆ G.verts
  P_sub : ∀ v ∈ P, v ∈ G.verts
  disj_UR : Disjoint U R
  P_notU : ∀ v ∈ P, v ∉ U
  P_notR : ∀ v ∈ P, v ∉ R
  nodup : P.Nodup
  card_eq : U.card + R.card + P.length = G.card
  chain : P.IsChain G.Adj
  noEdge : ∀ u ∈ U, ∀ r ∈ R, ¬ G.Adj u r

variable {G : FGraph V}

omit [DecidableEq V] in
/-- The initial state `(V(G), ∅, [])`. -/
theorem inv_init (G : FGraph V) : Inv G G.verts ∅ [] where
  U_sub := subset_rfl
  R_sub := Finset.empty_subset _
  P_sub := by simp
  disj_UR := Finset.disjoint_empty_right _
  P_notU := by simp
  P_notR := by simp
  nodup := List.nodup_nil
  card_eq := by simp [FGraph.card]
  chain := List.IsChain.nil
  noEdge := by simp

/-- One DFS step: if `U ≠ ∅`, there is a next state satisfying the invariant, with either
`|U|` lowered by one and `|R|` unchanged, or `|U|` unchanged and `|R|` raised by one. -/
theorem Inv.step {U R : Finset V} {P : List V} (h : Inv G U R P) (hU : U.Nonempty) :
    ∃ U' R' P', Inv G U' R' P' ∧
      ((U'.card + 1 = U.card ∧ R'.card = R.card) ∨ (U'.card = U.card ∧ R'.card = R.card + 1)) := by
  cases P with
  | nil =>
    -- restart at a vertex of `U`
    obtain ⟨u, hu⟩ := hU
    have huR : u ∉ R := Finset.disjoint_left.1 h.disj_UR hu
    refine ⟨U.erase u, R, [u], ?_, Or.inl ⟨Finset.card_erase_add_one hu, rfl⟩⟩
    have hc := h.card_eq
    have hc' := Finset.card_erase_add_one hu
    exact
      { U_sub := (Finset.erase_subset _ _).trans h.U_sub
        R_sub := h.R_sub
        P_sub := by simpa using h.U_sub hu
        disj_UR := Finset.disjoint_of_subset_left (Finset.erase_subset _ _) h.disj_UR
        P_notU := by simp
        P_notR := by simpa using huR
        nodup := List.nodup_singleton u
        card_eq := by simp at hc ⊢; omega
        chain := List.IsChain.singleton u
        noEdge := fun a ha r hr => h.noEdge a (Finset.mem_of_mem_erase ha) r hr }
  | cons t P' =>
    by_cases hext : ∃ v ∈ U, G.Adj t v
    · -- extend the path into `U`
      obtain ⟨v, hv, htv⟩ := hext
      have hvR : v ∉ R := Finset.disjoint_left.1 h.disj_UR hv
      have hvP : v ∉ t :: P' := fun hm => h.P_notU v hm hv
      refine ⟨U.erase v, R, v :: t :: P', ?_, Or.inl ⟨Finset.card_erase_add_one hv, rfl⟩⟩
      have hc := h.card_eq
      have hc' := Finset.card_erase_add_one hv
      exact
        { U_sub := (Finset.erase_subset _ _).trans h.U_sub
          R_sub := h.R_sub
          P_sub := by
            intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact h.U_sub hv
            · exact h.P_sub w hw
          disj_UR := Finset.disjoint_of_subset_left (Finset.erase_subset _ _) h.disj_UR
          P_notU := by
            intro w hw hwU
            rcases List.mem_cons.1 hw with rfl | hw
            · simp at hwU
            · exact h.P_notU w hw (Finset.mem_of_mem_erase hwU)
          P_notR := by
            intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact hvR
            · exact h.P_notR w hw
          nodup := List.nodup_cons.2 ⟨hvP, h.nodup⟩
          card_eq := by simp only [List.length_cons] at hc ⊢; omega
          chain := List.IsChain.cons_cons (htv.symm) h.chain
          noEdge := fun a ha r hr => h.noEdge a (Finset.mem_of_mem_erase ha) r hr }
    · -- backtrack: move `t` to `R`
      push Not at hext
      have htR : t ∉ R := h.P_notR t (List.mem_cons_self)
      have htU : t ∉ U := h.P_notU t (List.mem_cons_self)
      refine ⟨U, insert t R, P', ?_, Or.inr ⟨rfl, Finset.card_insert_of_notMem htR⟩⟩
      have hc := h.card_eq
      have hc' := Finset.card_insert_of_notMem htR
      have hnd := h.nodup
      rw [List.nodup_cons] at hnd
      exact
        { U_sub := h.U_sub
          R_sub := Finset.insert_subset (h.P_sub t List.mem_cons_self) h.R_sub
          P_sub := fun w hw => h.P_sub w (List.mem_cons_of_mem _ hw)
          disj_UR := Finset.disjoint_insert_right.2 ⟨htU, h.disj_UR⟩
          P_notU := fun w hw => h.P_notU w (List.mem_cons_of_mem _ hw)
          P_notR := by
            intro w hw hwR
            rcases Finset.mem_insert.1 hwR with rfl | hwR
            · exact hnd.1 hw
            · exact h.P_notR w (List.mem_cons_of_mem _ hw) hwR
          nodup := hnd.2
          card_eq := by simp only [List.length_cons] at hc; omega
          chain := h.chain.tail
          noEdge := by
            intro u hu r hr hur
            rcases Finset.mem_insert.1 hr with rfl | hr
            · exact hext u hu hur.symm
            · exact h.noEdge u hu r hr hur }

/-- The discrete intermediate value step: from a state with `|R| ≤ |U|`, the search reaches a
state with `|U| = |R|`. -/
theorem Inv.exists_balanced_of_le :
    ∀ (d : ℕ) {U R : Finset V} {P : List V}, Inv G U R P → R.card ≤ U.card →
      U.card - R.card = d → ∃ U' R' P', Inv G U' R' P' ∧ U'.card = R'.card := by
  intro d
  induction d with
  | zero =>
    intro U R P h hle hd
    exact ⟨U, R, P, h, by omega⟩
  | succ d ih =>
    intro U R P h hle hd
    have hU : U.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨U', R', P', h', hcard⟩ := h.step hU
    exact ih h' (by omega) (by omega)

/-- [s1:citLem25] (proof in [BM]) "at some point in the process, we must have `|U| = |R|`":
there is a DFS state satisfying the invariant with `|U| = |R|`. -/
theorem exists_balanced (G : FGraph V) :
    ∃ U R P, Inv G U R P ∧ U.card = R.card :=
  Inv.exists_balanced_of_le _ (inv_init G) (by simp) rfl

/-- "Since there are no edges between `U` and `R` we know that all the neighbours of `U` must
belong to `P`". -/
theorem Inv.nbrSet_subset {U R : Finset V} {P : List V} (h : Inv G U R P) :
    G.nbrSet U ⊆ P.toFinset := by
  intro v hv
  obtain ⟨hvV, hvU, u, hu, huv⟩ := FGraph.mem_nbrSet.1 hv
  have hvR : v ∉ R := fun hvR => h.noEdge u hu v hvR huv
  by_contra hvP
  rw [List.mem_toFinset] at hvP
  -- `V(G) = U ∪ R ∪ V(P)` by counting
  have hsub : insert v (U ∪ R ∪ P.toFinset) ⊆ G.verts := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hvV
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases Finset.mem_union.1 hw with hw | hw
      · exact h.U_sub hw
      · exact h.R_sub hw
    · exact h.P_sub w (List.mem_toFinset.1 hw)
  have hcard := Finset.card_le_card hsub
  have hnotin : v ∉ U ∪ R ∪ P.toFinset := by
    simp [hvU, hvR, hvP]
  rw [Finset.card_insert_of_notMem hnotin] at hcard
  have h1 : (U ∪ R ∪ P.toFinset).card = U.card + R.card + P.length := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint h.disj_UR,
      List.toFinset_card_of_nodup h.nodup]
    rw [Finset.disjoint_union_left]
    constructor
    · exact Finset.disjoint_left.2 fun w hw hwP => h.P_notU w (List.mem_toFinset.1 hwP) hw
    · exact Finset.disjoint_left.2 fun w hw hwP => h.P_notR w (List.mem_toFinset.1 hwP) hw
  have := h.card_eq
  simp only [FGraph.card] at this
  omega

theorem Inv.card_nbrSet_le {U R : Finset V} {P : List V} (h : Inv G U R P) :
    (G.nbrSet U).card ≤ P.length :=
  (Finset.card_le_card h.nbrSet_subset).trans (List.toFinset_card_le P)

end DFS

end EG
