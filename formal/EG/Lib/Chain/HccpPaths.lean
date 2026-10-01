module

public import EG.Lib.Chain.HccpEnds
public import EG.Lib.Found.Orient

/-!
# HCC-P, Step 1: the oriented path families `D_j` and their cancellation (manuscript s6:lemHCCP)

Probe unit P2E (probe P-2, part 1), proof round 1.

"Orient every path of `𝒫_j` from its first to its last vertex, and let `D_j` be the resulting set
of arcs." Here `D_j = HccpData.pathArcs S j` (the arcs of all walks `walkArcs p`, `p ∈ 𝒫_j`).
* degrees: `d⁺_{D_j}(v) + #{p : last(p) = v} = #{p : v ∈ p} = d⁻_{D_j}(v) + #{p : first(p) = v}`
  (`Valid.outDeg_pathArcs_add`, `Valid.inDeg_pathArcs_add`), since a path through `v` contributes
  one out-arc unless `v` is its last vertex and one in-arc unless `v` is its first vertex;
* `D_j` orients `E(𝒫_j)` (`Valid.isOrientation_pathArcs`);
* a vertex outside `T_j` lies on a path only as its first or last vertex, so it is a source or a
  sink of `D_j` (`Valid.source_or_sink`; "ports are sources or sinks of `D_j`", for `k = 1` via
  `X^out ∩ X^in = ∅`);
* every arc of `D_j` runs from `LayP_j ∪ T_j` to `T_j ∪ LayP_{j+1}` (`Valid.pathArcs_ends`);
* cancellation: `D'_j = D_j ∖ R_j` with `R_j` balanced and `D'_j` acyclic; the arcs of `R_j` lie
  inside `T_j` (`Valid.cancel_arcs_mem_T`), so `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])`.
-/

public section

namespace EG.Chain

namespace HccpData

variable {V : Type*} [DecidableEq V]

/-! ## One path -/

omit [DecidableEq V] in
/-- A vertex of a list is its first vertex, its last vertex, or an interior vertex. -/
theorem head_or_last_or_interior {p : List V} {v : V} (hv : v ∈ p) :
    p.head? = some v ∨ p.getLast? = some v ∨ v ∈ interior p := by
  match p, hv with
  | a :: t, hv =>
    rcases List.mem_cons.1 hv with rfl | hvt
    · exact Or.inl rfl
    · right
      have htne : t ≠ [] := List.ne_nil_of_mem hvt
      have hsplit := List.dropLast_append_getLast htne
      rw [← hsplit, List.mem_append, List.mem_singleton] at hvt
      rcases hvt with h | h
      · right; simpa [interior] using h
      · left
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a t)]
        rw [List.getLast_cons htne, h]

/-- In a duplicate-free walk, `v` is the tail of one arc unless it is the last vertex:
`#{arcs v → ·} + [last = v] = [v ∈ p]`. -/
theorem countP_walkArcs_fst (v : V) : ∀ {p : List V}, p.Nodup →
    (walkArcs p).countP (fun a => decide (a.1 = v)) + (if p.getLast? = some v then 1 else 0) =
      if v ∈ p then 1 else 0
  | [], _ => by simp
  | [x], _ => by
    by_cases h : x = v
    · subst h; simp
    · simp [h, Ne.symm h]
  | x :: y :: t, hnd => by
    have hx : x ∉ y :: t := (List.nodup_cons.1 hnd).1
    have ih := countP_walkArcs_fst v (List.nodup_cons.1 hnd).2
    have hlast : (x :: y :: t).getLast? = (y :: t).getLast? := by simp [List.getLast?_cons_cons]
    rw [walkArcs_cons_cons, List.countP_cons, hlast]
    generalize (walkArcs (y :: t)).countP (fun a => decide (a.1 = v)) = c at ih ⊢
    have hxv' : x = v → v ∉ y :: t := fun h => h ▸ hx
    by_cases h1 : x = v <;> by_cases h2 : v ∈ y :: t <;>
      by_cases h3 : (y :: t).getLast? = some v
    all_goals first
      | exact absurd h2 (hxv' h1)
      | (simp only [h1, h2, h3, if_true, if_false, decide_true, decide_false, List.mem_cons,
          true_or, or_true, or_false, false_or, Bool.false_eq_true] at ih ⊢; omega)
      | (simp_all; intro h; exact h1 h.symm)

/-- In a duplicate-free walk, `v` is the head of one arc unless it is the first vertex:
`#{arcs · → v} + [first = v] = [v ∈ p]`. -/
theorem countP_walkArcs_snd (v : V) : ∀ {p : List V}, p.Nodup →
    (walkArcs p).countP (fun a => decide (a.2 = v)) + (if p.head? = some v then 1 else 0) =
      if v ∈ p then 1 else 0
  | [], _ => by simp
  | [x], _ => by
    by_cases h : x = v
    · subst h; simp
    · simp [h, Ne.symm h]
  | x :: y :: t, hnd => by
    have hx : x ∉ y :: t := (List.nodup_cons.1 hnd).1
    have ih := countP_walkArcs_snd v (List.nodup_cons.1 hnd).2
    rw [walkArcs_cons_cons, List.countP_cons]
    generalize (walkArcs (y :: t)).countP (fun a => decide (a.2 = v)) = c at ih ⊢
    have hxv' : x = v → v ∉ y :: t := fun h => h ▸ hx
    have hyv' : y = v → v ∈ y :: t := fun h => h ▸ List.mem_cons_self
    simp only [List.head?_cons, Option.some.injEq] at ih ⊢
    by_cases h1 : x = v <;> by_cases h2 : v ∈ y :: t <;> by_cases h3 : y = v
    all_goals first
      | exact absurd h2 (hxv' h1)
      | exact absurd (hyv' h3) h2
      | (simp only [h1, h2, h3, if_true, if_false, decide_true, decide_false, List.mem_cons,
          true_or, or_true, or_false, false_or, Bool.false_eq_true] at ih ⊢; omega)
      | (simp_all; intro h; exact h1 h.symm)

/-! ## A family of paths -/

/-- Counting over a list of duplicate-free walks: tails. -/
theorem countP_flatMap_fst (v : V) : ∀ (Ps : List (List V)), (∀ p ∈ Ps, p.Nodup) →
    (Ps.flatMap walkArcs).countP (fun a => decide (a.1 = v)) +
        Ps.countP (fun p => decide (p.getLast? = some v)) =
      Ps.countP (fun p => decide (v ∈ p))
  | [], _ => by simp
  | p :: Ps, h => by
    have ih := countP_flatMap_fst v Ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := countP_walkArcs_fst v (h p List.mem_cons_self)
    rw [List.flatMap_cons, List.countP_append, List.countP_cons, List.countP_cons]
    by_cases h1 : p.getLast? = some v <;> by_cases h2 : v ∈ p <;>
      simp only [h1, h2, if_true, if_false, decide_true, decide_false,
        Bool.false_eq_true] at hp ⊢ <;> omega

/-- Counting over a list of duplicate-free walks: heads. -/
theorem countP_flatMap_snd (v : V) : ∀ (Ps : List (List V)), (∀ p ∈ Ps, p.Nodup) →
    (Ps.flatMap walkArcs).countP (fun a => decide (a.2 = v)) +
        Ps.countP (fun p => decide (p.head? = some v)) =
      Ps.countP (fun p => decide (v ∈ p))
  | [], _ => by simp
  | p :: Ps, h => by
    have ih := countP_flatMap_snd v Ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := countP_walkArcs_snd v (h p List.mem_cons_self)
    rw [List.flatMap_cons, List.countP_append, List.countP_cons, List.countP_cons]
    by_cases h1 : p.head? = some v <;> by_cases h2 : v ∈ p <;>
      simp only [h1, h2, if_true, if_false, decide_true, decide_false,
        Bool.false_eq_true] at hp ⊢ <;> omega

/-- The card of a filter of the `toFinset` of a duplicate-free list is a `countP`. -/
theorem card_filter_toFinset {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (P : α → Prop) [DecidablePred P] :
    (l.toFinset.filter P).card = l.countP (fun a => decide (P a)) := by
  rw [List.filter_toFinset, List.toFinset_card_of_nodup (hl.filter _),
    List.countP_eq_length_filter]

variable (S : HccpData V)

/-- [s6:lemHCCP] (proof, Step 1) "Orient every path of `𝒫_j` from its first to its last vertex,
and let `D_j` be the resulting set of arcs." -/
@[expose] def pathArcs (j : Fin S.k) : Finset (V × V) := ((S.P j).flatMap walkArcs).toFinset

theorem mem_pathArcs {j : Fin S.k} {a : V × V} :
    a ∈ S.pathArcs j ↔ ∃ p ∈ S.P j, a ∈ walkArcs p := by
  simp [pathArcs]

variable {G : FGraph V} {S}

omit [DecidableEq V] in
/-- The edge list of `𝒫_j` is the underlying edge list of the arc list. -/
theorem flatMap_walkEdges_eq (Ps : List (List V)) :
    Ps.flatMap walkEdges = (Ps.flatMap walkArcs).map (fun a => s(a.1, a.2)) := by
  induction Ps with
  | nil => rfl
  | cons p Ps ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih, walkEdges_eq_map_walkArcs]

theorem Valid.nodup_flatMap_walkArcs (hS : S.Valid G) (j : Fin S.k) :
    ((S.P j).flatMap walkArcs).Nodup := by
  have h := hS.nodup_flatMap_walkEdges j
  rw [flatMap_walkEdges_eq] at h
  exact h.of_map _

theorem Valid.path_nodup (hS : S.Valid G) {j : Fin S.k} {p : List V} (hp : p ∈ S.P j) :
    p.Nodup := (hS.path_G j p hp).nodup

/-- `d⁺_{D_j}(v) + #{p ∈ 𝒫_j : last(p) = v} = #{p ∈ 𝒫_j : v ∈ p}`. -/
theorem Valid.outDeg_pathArcs_add (hS : S.Valid G) (j : Fin S.k) (v : V) :
    outDeg (S.pathArcs j) v + (S.P j).countP (fun p => decide (p.getLast? = some v)) =
      (S.P j).countP (fun p => decide (v ∈ p)) := by
  unfold outDeg pathArcs
  rw [card_filter_toFinset (hS.nodup_flatMap_walkArcs j)]
  exact countP_flatMap_fst v (S.P j) (fun p hp => hS.path_nodup hp)

/-- `d⁻_{D_j}(v) + #{p ∈ 𝒫_j : first(p) = v} = #{p ∈ 𝒫_j : v ∈ p}`. -/
theorem Valid.inDeg_pathArcs_add (hS : S.Valid G) (j : Fin S.k) (v : V) :
    inDeg (S.pathArcs j) v + (S.P j).countP (fun p => decide (p.head? = some v)) =
      (S.P j).countP (fun p => decide (v ∈ p)) := by
  unfold inDeg pathArcs
  rw [card_filter_toFinset (hS.nodup_flatMap_walkArcs j)]
  exact countP_flatMap_snd v (S.P j) (fun p hp => hS.path_nodup hp)

/-- The excess of `D_j`: `d⁺(v) − d⁻(v) = #first(v) − #last(v)`, i.e. `dem⁻(v)` on `LayP_j`
minus `dem⁺(v)` on `LayP_{j+1}`. -/
theorem Valid.exc_pathArcs (hS : S.Valid G) (j : Fin S.k) (v : V) :
    exc (S.pathArcs j) v =
      ((if v ∈ S.layP j then S.demMinus v else 0 : ℕ) : ℤ) -
        ((if v ∈ S.layP (S.succ j) then S.demPlus v else 0 : ℕ) : ℤ) := by
  have h1 := hS.outDeg_pathArcs_add j v
  have h2 := hS.inDeg_pathArcs_add j v
  rw [hS.countP_head_eq j v] at h2
  rw [hS.countP_last_eq j v] at h1
  unfold exc
  omega

/-- [s6:lemHCCP] (proof, Step 1) "The paths are edge-disjoint, so every edge of `E(𝒫_j)` receives
exactly one direction": `D_j` is an orientation of `E(𝒫_j)`. -/
theorem Valid.isOrientation_pathArcs (hS : S.Valid G) (j : Fin S.k) :
    IsOrientation (S.pathEdges j) (S.pathArcs j) := by
  rw [isOrientation_iff]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · obtain ⟨p, hp, hap⟩ := (S.mem_pathArcs).1 ha
    exact walkArcs_loopless (hS.path_nodup hp) a hap
  · unfold pathArcs pathEdges
    rw [flatMap_walkEdges_eq]
    ext e
    simp
  · intro a ha b hb hab
    have hnd := hS.nodup_flatMap_walkEdges j
    rw [flatMap_walkEdges_eq] at hnd
    exact List.inj_on_of_nodup_map hnd (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb) hab

/-- A vertex outside `T_j` on a path of `𝒫_j` is its first or its last vertex. -/
theorem Valid.head_or_last_of_not_mem_T (hS : S.Valid G) {j : Fin S.k} {p : List V}
    (hp : p ∈ S.P j) {v : V} (hv : v ∈ p) (hvT : v ∉ S.T j) :
    p.head? = some v ∨ p.getLast? = some v := by
  rcases head_or_last_or_interior hv with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hS.path_T j p hp v h) hvT

theorem Valid.countP_mem_le (hS : S.Valid G) (j : Fin S.k) {v : V} (hvT : v ∉ S.T j) :
    (S.P j).countP (fun p => decide (v ∈ p)) ≤
      (S.P j).countP (fun p => decide (p.head? = some v)) +
        (S.P j).countP (fun p => decide (p.getLast? = some v)) := by
  refine le_trans (List.countP_mono_left fun p hp hv => ?_) (countP_or_le _ _ _)
  simp only [decide_eq_true_eq] at hv ⊢
  exact hS.head_or_last_of_not_mem_T hp hv hvT

/-- Outside `T_j`: `d⁺_{D_j}(v) ≤ #first(v)`. -/
theorem Valid.outDeg_pathArcs_le (hS : S.Valid G) (j : Fin S.k) {v : V} (hvT : v ∉ S.T j) :
    outDeg (S.pathArcs j) v ≤ (S.P j).countP (fun p => decide (p.head? = some v)) := by
  have h1 := hS.outDeg_pathArcs_add j v
  have h2 := hS.countP_mem_le j hvT
  omega

/-- Outside `T_j`: `d⁻_{D_j}(v) ≤ #last(v)`. -/
theorem Valid.inDeg_pathArcs_le (hS : S.Valid G) (j : Fin S.k) {v : V} (hvT : v ∉ S.T j) :
    inDeg (S.pathArcs j) v ≤ (S.P j).countP (fun p => decide (p.getLast? = some v)) := by
  have h1 := hS.inDeg_pathArcs_add j v
  have h2 := hS.countP_mem_le j hvT
  omega

/-- [s6:lemHCCP] (proof, Step 1) "ports are sources or sinks of `D_j`": a vertex outside `T_j` is
not both the first vertex of a path of `𝒫_j` and the last vertex of one ("last vertices lie in
`LayP_{j+1}`, which is disjoint from `LayP_j` by (D) when `k ≥ 2`; for `k = 1`,
`X^out ∩ X^in = ∅`"). -/
theorem Valid.source_or_sink (hS : S.Valid G) (j : Fin S.k) {v : V} (hvT : v ∉ S.T j) :
    outDeg (S.pathArcs j) v = 0 ∨ inDeg (S.pathArcs j) v = 0 := by
  have h1 := hS.outDeg_pathArcs_le j hvT
  have h2 := hS.inDeg_pathArcs_le j hvT
  rw [hS.countP_head_eq j v] at h1
  rw [hS.countP_last_eq j v] at h2
  by_contra hne
  push Not at hne
  split_ifs at h1 h2 with ha hb
  · by_cases hk : S.k = 1
    · have hsj : S.succ j = j := S.succ_eq_self hk j
      have hp := hS.pad_k1 hk j v ha
      simp only [demMinus, demPlus, hp] at h1 h2
      omega
    · have hne' : S.succ j ≠ j := S.succ_ne_self (by have := hS.k_pos; omega) j
      exact Finset.disjoint_left.1 (S.layP_disjoint hS.D_KK hne') hb ha
  · omega
  · omega
  · omega

/-- [s6:lemHCCP] (proof, Step 1) "All vertices of `D_j` lie in `LayP_j ∪ T_j ∪ LayP_{j+1}`":
every arc of `D_j` runs from `LayP_j ∪ T_j` to `T_j ∪ LayP_{j+1}`. -/
theorem Valid.pathArcs_ends (hS : S.Valid G) {j : Fin S.k} {a : V × V}
    (ha : a ∈ S.pathArcs j) :
    (a.1 ∈ S.T j ∨ a.1 ∈ S.layP j) ∧ (a.2 ∈ S.T j ∨ a.2 ∈ S.layP (S.succ j)) := by
  obtain ⟨p, hp, hap⟩ := (S.mem_pathArcs).1 ha
  have hnd := hS.path_nodup hp
  constructor
  · by_cases hT : a.1 ∈ S.T j
    · exact Or.inl hT
    · right
      rcases hS.head_or_last_of_not_mem_T hp (fst_mem_of_mem_walkArcs hap) hT with h | h
      · obtain ⟨u, hu, hpu⟩ := (hS.path_ends j p hp).1
        rw [h] at hpu
        exact (Option.some_inj.1 hpu) ▸ hu
      · -- the last vertex is the tail of no arc of the walk
        exfalso
        have hc := countP_walkArcs_fst a.1 hnd
        have hpos : 0 < (walkArcs p).countP (fun b => decide (b.1 = a.1)) :=
          List.countP_pos_iff.2 ⟨a, hap, by simp⟩
        simp only [h, if_true, fst_mem_of_mem_walkArcs hap] at hc
        omega
  · by_cases hT : a.2 ∈ S.T j
    · exact Or.inl hT
    · right
      rcases hS.head_or_last_of_not_mem_T hp (snd_mem_of_mem_walkArcs hap) hT with h | h
      · exfalso
        have hc := countP_walkArcs_snd a.2 hnd
        have hpos : 0 < (walkArcs p).countP (fun b => decide (b.2 = a.2)) :=
          List.countP_pos_iff.2 ⟨a, hap, by simp⟩
        simp only [h, if_true, snd_mem_of_mem_walkArcs hap] at hc
        omega
      · obtain ⟨u, hu, hpu⟩ := (hS.path_ends j p hp).2
        rw [h] at hpu
        exact (Option.some_inj.1 hpu) ▸ hu

/-- [s6:lemHCCP] (proof, Step 1) "Each deletion lowers in- and out-degree by one at the vertices
of a cycle inside `T_j`": a balanced set `R ⊆ D_j` of arcs has both ends of every arc in `T_j`
(outside `T_j` a vertex is a source or a sink of `D_j`). -/
theorem Valid.cancel_arcs_mem_T (hS : S.Valid G) (j : Fin S.k) {R : Finset (V × V)}
    (hR : R ⊆ S.pathArcs j) (hbal : IsBalanced R) {a : V × V} (ha : a ∈ R) :
    a.1 ∈ S.T j ∧ a.2 ∈ S.T j := by
  have key : ∀ v, 0 < outDeg R v → v ∈ S.T j := by
    intro v hv
    by_contra hvT
    have hin : 0 < inDeg R v := (hbal v) ▸ hv
    rcases hS.source_or_sink j hvT with h | h
    · have := outDeg_mono hR v; omega
    · have := inDeg_mono hR v; omega
  refine ⟨key _ (outDeg_pos_of_mem ha), key _ ?_⟩
  rw [hbal]
  exact inDeg_pos_of_mem ha

end HccpData

end EG.Chain
