module

public import EG.Defs.Graph
public import EG.Defs.Walk
public import EG.Defs.Orient
public import Mathlib.Data.List.Chain

/-!
# Orientations: basic lemmas, acyclicity, and the directed-cycle decomposition of balanced digraphs

Companion of `EG.Defs.Orient`.

* `EG.cycleArcs` / `EG.walkArcs` API: first and second coordinates, underlying edges
  (`EG.cycleEdges_eq_map_cycleArcs`, `EG.walkEdges_eq_map_walkArcs`), `Nodup`, rotation
  (`EG.cycleArcs_rotate`), a closed walk as a walk plus its closing arc (`EG.cycleArcs_cons`);
  directed paths as chains (`EG.isDirPathIn_iff_isChain`); directed paths are paths of the
  underlying edge set (`EG.IsDirPathIn.isPathIn`);
* degrees: sums, unions and differences of arc sets; the arcs of a directed cycle with distinct
  vertices have `d⁺ = d⁻` at every vertex, so deleting them from a balanced digraph keeps it
  balanced (`EG.IsBalanced.sdiff_cycleArcs`, `EG.isBalanced_flatMap_cycleArcs`,
  `EG.IsBalanced.sdiff`); a balanced subset has no arc at a source or a sink;
* orientations: no loops and no antiparallel pair of arcs (`EG.IsOrientation.not_mem_swap`);
  `d⁺(v) + d⁻(v) = deg_F(v)` (`EG.IsOrientation.outDeg_add_inDeg`); a characterisation without
  `∃!` (`EG.isOrientation_iff`); building orientations (`EG.IsOrientation.of_subset_edges`,
  `.union`, `.subset`, `.sdiff`; the orientation of a path from its first to its last vertex,
  `EG.isOrientation_walkArcs`);
* directed cycles: a directed cycle of a digraph without loops and antiparallel arcs has length at
  least `3` (`EG.IsDirCycle.three_le_length`); a directed cycle avoids sources and sinks; it may
  start at any vertex (`EG.IsDirCycle.rotate`), in particular at the head of any of its arcs
  (`EG.IsDirCycle.exists_rotate_eq_cons_of_mem`); its underlying edges form a cycle of `F`
  (`EG.IsDirCycle.wf_of_isOrientation`, `EG.IsDirCycle.forall_mem_cycleEdges`);
* `EG.exists_isDirCycle_of_forall_inDeg_pos`: a non-empty digraph in which every vertex with an
  out-arc has an in-arc contains a directed cycle (the maximal-path argument of [s6:lemGATE], run
  by extending a directed path backwards until it closes);
* acyclicity: monotonicity; a potential that increases strictly along every arc forces acyclicity
  (`EG.isAcyclic_of_potential`, used in [s6:lemMED] (a) and [s6:lemHCCP] Step 3); conversely an
  acyclic digraph has a source (`EG.IsAcyclic.exists_source`, used in s6, proof of the
  non-giant-component step) and a numbering `S → {1, …, |S|}` increasing along every arc
  (`EG.IsAcyclic.exists_potential`, the "topological order" of [s6:lemHCCP] Step 3);
* `EG.exists_dirCycle_decomp`: a balanced digraph without loops and antiparallel arcs is the
  arc-disjoint union of directed cycles of length at least `3` (the induction of [s6:lemGATE]);
* cancellation: deleting suitable arc-disjoint directed cycles from any digraph leaves an acyclic
  digraph (`EG.exists_cancel_dirCycles`, `EG.exists_balanced_sdiff_acyclic`, [s6:lemHCCP] Step 1);
* `EG.isDecomp_map_cycle_of_arcs`: arc-disjoint directed cycles covering an orientation of `F`
  give a decomposition of `F` into cycle objects.
-/

public section


namespace EG

variable {V : Type*}

/-! ## Arcs of a closed walk -/

theorem map_fst_cycleArcs (c : List V) : (cycleArcs c).map Prod.fst = c :=
  List.map_fst_zip (by simp)

theorem map_snd_cycleArcs (c : List V) : (cycleArcs c).map Prod.snd = c.rotate 1 :=
  List.map_snd_zip (by simp)

theorem cycleEdges_eq_map_cycleArcs (c : List V) :
    cycleEdges c = (cycleArcs c).map (fun a => s(a.1, a.2)) := by
  unfold cycleEdges cycleArcs
  rw [List.map_zip_eq_zipWith]
  rfl

theorem fst_mem_of_mem_cycleArcs {c : List V} {a : V × V} (h : a ∈ cycleArcs c) : a.1 ∈ c := by
  rw [← map_fst_cycleArcs c]
  exact List.mem_map_of_mem h

theorem snd_mem_of_mem_cycleArcs {c : List V} {a : V × V} (h : a ∈ cycleArcs c) : a.2 ∈ c := by
  rw [← List.mem_rotate (n := 1), ← map_snd_cycleArcs c]
  exact List.mem_map_of_mem h

theorem exists_mem_cycleArcs_fst {c : List V} {v : V} (h : v ∈ c) :
    ∃ w, (v, w) ∈ cycleArcs c := by
  rw [← map_fst_cycleArcs c, List.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a.2, ha⟩

theorem exists_mem_cycleArcs_snd {c : List V} {v : V} (h : v ∈ c) :
    ∃ u, (u, v) ∈ cycleArcs c := by
  rw [← List.mem_rotate (n := 1), ← map_snd_cycleArcs c, List.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a.1, ha⟩

theorem cycleArcs_nodup {c : List V} (h : c.Nodup) : (cycleArcs c).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [map_fst_cycleArcs]
  exact h

theorem cycleArcs_ne_nil {c : List V} (h : c ≠ []) : cycleArcs c ≠ [] := by
  intro h'
  apply h
  rw [← map_fst_cycleArcs c, h', List.map_nil]

/-- Rotating the vertex list of a closed walk rotates its arc list: the closed walk is the same,
only its starting vertex changes. -/
theorem cycleArcs_rotate (c : List V) (n : ℕ) :
    cycleArcs (c.rotate n) = (cycleArcs c).rotate n := by
  unfold cycleArcs
  show List.zipWith Prod.mk _ _ = (List.zipWith Prod.mk _ _).rotate n
  rw [List.zipWith_rotate_distrib _ _ _ _ (by simp), List.rotate_rotate, List.rotate_rotate,
    Nat.add_comm]

theorem mem_cycleArcs_rotate {c : List V} {n : ℕ} {a : V × V} :
    a ∈ cycleArcs (c.rotate n) ↔ a ∈ cycleArcs c := by
  rw [cycleArcs_rotate, List.mem_rotate]

/-- Every vertex of a cyclic list can be made its first vertex by a rotation. -/
theorem exists_rotate_eq_cons {c : List V} {v : V} (h : v ∈ c) :
    ∃ n t, c.rotate n = v :: t := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, c.drop (i + 1) ++ c.take i, by
    rw [List.rotate_eq_drop_append_take hi.le, List.drop_eq_getElem_cons hi, List.cons_append]⟩

/-- In a closed walk without repeated vertex, an arc is determined by its tail. -/
theorem eq_of_mem_cycleArcs_of_fst_eq {c : List V} (hc : c.Nodup) {a b : V × V}
    (ha : a ∈ cycleArcs c) (hb : b ∈ cycleArcs c) (h : a.1 = b.1) : a = b := by
  have hnd : ((cycleArcs c).map Prod.fst).Nodup := by rw [map_fst_cycleArcs]; exact hc
  exact List.inj_on_of_nodup_map hnd ha hb h

/-- In a closed walk without repeated vertex, an arc is determined by its head. -/
theorem eq_of_mem_cycleArcs_of_snd_eq {c : List V} (hc : c.Nodup) {a b : V × V}
    (ha : a ∈ cycleArcs c) (hb : b ∈ cycleArcs c) (h : a.2 = b.2) : a = b := by
  have hnd : ((cycleArcs c).map Prod.snd).Nodup := by
    rw [map_snd_cycleArcs]; exact List.nodup_rotate.2 hc
  exact List.inj_on_of_nodup_map hnd ha hb h

/-- The arcs `a → t₀ → … → t_m → y` (the list `zip (a :: t) (t ++ [y])`; just `a → y` if `t` is
empty) all satisfy `R` if `a t₀ … t_m` is an `R`-chain and `R t_m y` (resp. `R a y`). -/
private theorem forall_mem_zip_of_isChain {R : V → V → Prop} :
    ∀ (t : List V) (a y : V), List.IsChain R (a :: t) → R ((a :: t).getLast (by simp)) y →
      ∀ p ∈ List.zip (a :: t) (t ++ [y]), R p.1 p.2
  | [], a, y, _, hy, p, hp => by
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    simpa using hy
  | b :: t, a, y, hc, hy, p, hp => by
    rw [List.isChain_cons_cons] at hc
    rw [List.cons_append, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hc.1
    · refine forall_mem_zip_of_isChain t b y hc.2 ?_ p hp
      simpa using hy

/-- A directed path `a t₀ … t_m` of `A` together with the closing arc `t_m → a` gives a closed
directed walk all of whose arcs lie in `A`. -/
theorem forall_mem_cycleArcs_of_isChain {A : Finset (V × V)} {a : V} {t : List V}
    (hc : List.IsChain (fun x y => (x, y) ∈ A) (a :: t))
    (hlast : ((a :: t).getLast (by simp), a) ∈ A) : ∀ p ∈ cycleArcs (a :: t), p ∈ A := by
  intro p hp
  unfold cycleArcs at hp
  rw [List.rotate_cons_succ, List.rotate_zero] at hp
  exact forall_mem_zip_of_isChain (R := fun x y => (x, y) ∈ A) t a a hc hlast p hp

/-! ## Arcs of a walk; directed paths -/

@[simp] theorem walkArcs_nil : walkArcs ([] : List V) = [] := rfl

@[simp] theorem walkArcs_singleton (x : V) : walkArcs [x] = [] := rfl

@[simp] theorem walkArcs_cons_cons (x y : V) (t : List V) :
    walkArcs (x :: y :: t) = (x, y) :: walkArcs (y :: t) := rfl

/-- The underlying edges of the arcs of a directed walk are the edges of the walk. -/
theorem walkEdges_eq_map_walkArcs (p : List V) :
    walkEdges p = (walkArcs p).map (fun a => s(a.1, a.2)) := by
  unfold walkEdges walkArcs
  rw [List.map_zip_eq_zipWith]
  rfl

theorem forall_mem_walkArcs_iff_isChain {R : V → V → Prop} :
    ∀ p : List V, (∀ a ∈ walkArcs p, R a.1 a.2) ↔ List.IsChain R p
  | [] => by simp
  | [x] => by simp
  | x :: y :: t => by
    rw [walkArcs_cons_cons, List.isChain_cons_cons, ← forall_mem_walkArcs_iff_isChain (y :: t)]
    simp

/-- A directed path is a duplicate-free non-empty chain of arcs. -/
theorem isDirPathIn_iff_isChain {A : Finset (V × V)} {p : List V} :
    IsDirPathIn A p ↔ p ≠ [] ∧ p.Nodup ∧ List.IsChain (fun x y => (x, y) ∈ A) p := by
  unfold IsDirPathIn
  rw [← forall_mem_walkArcs_iff_isChain (R := fun x y => (x, y) ∈ A)]

theorem fst_mem_of_mem_walkArcs {p : List V} {a : V × V} (h : a ∈ walkArcs p) : a.1 ∈ p :=
  (List.of_mem_zip h).1

theorem snd_mem_of_mem_walkArcs {p : List V} {a : V × V} (h : a ∈ walkArcs p) : a.2 ∈ p :=
  List.mem_of_mem_tail (List.of_mem_zip h).2

private theorem zip_cons_append_singleton (y : V) : ∀ (a : V) (t : List V),
    List.zip (a :: t) (t ++ [y]) =
      List.zip (a :: t) t ++ [((a :: t).getLast (List.cons_ne_nil a t), y)]
  | a, [] => by simp
  | a, b :: t => by
    rw [List.cons_append, List.zip_cons_cons, zip_cons_append_singleton y b t, List.zip_cons_cons]
    simp

/-- The closed directed walk `v t₀ … t_m v` is the directed walk `v t₀ … t_m` followed by the
closing arc `t_m → v` (just the loop `v → v` if `t` is empty). -/
theorem cycleArcs_cons (v : V) (t : List V) :
    cycleArcs (v :: t) = walkArcs (v :: t) ++ [((v :: t).getLast (List.cons_ne_nil v t), v)] := by
  unfold cycleArcs walkArcs
  rw [List.rotate_cons_succ, List.rotate_zero, List.tail_cons]
  exact zip_cons_append_singleton v v t

/-- The arcs of a directed walk are arcs of the closed directed walk on the same vertex list. -/
theorem walkArcs_subset_cycleArcs (p : List V) : ∀ a ∈ walkArcs p, a ∈ cycleArcs p := by
  intro a ha
  match p with
  | [] => simp at ha
  | v :: t =>
    rw [cycleArcs_cons]
    exact List.mem_append_left _ ha

private theorem walkArcs_facts : ∀ {p : List V}, p.Nodup →
    ∀ a ∈ walkArcs p, a.1 ≠ a.2 ∧ (a.2, a.1) ∉ walkArcs p
  | [], _ => by simp
  | [_], _ => by simp
  | x :: y :: t, hnd => by
    have hx : x ∉ y :: t := (List.nodup_cons.1 hnd).1
    intro a ha
    rw [walkArcs_cons_cons, List.mem_cons] at ha
    rw [walkArcs_cons_cons, List.mem_cons]
    rcases ha with rfl | ha
    · have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
      refine ⟨hxy, ?_⟩
      rintro (h | h)
      · exact hxy (Prod.mk.inj h).1.symm
      · exact hx (snd_mem_of_mem_walkArcs h)
    · obtain ⟨h1, h2⟩ := walkArcs_facts (List.nodup_cons.1 hnd).2 a ha
      refine ⟨h1, ?_⟩
      rintro (h | h)
      · have h' : a.2 = x := (Prod.mk.inj h).1
        exact hx (h' ▸ snd_mem_of_mem_walkArcs ha)
      · exact h2 h

/-- The arcs of a walk without repeated vertex are not loops. -/
theorem walkArcs_loopless {p : List V} (hp : p.Nodup) : ∀ a ∈ walkArcs p, a.1 ≠ a.2 :=
  fun a ha => (walkArcs_facts hp a ha).1

/-- A walk without repeated vertex never uses both arcs `u → v` and `v → u`. -/
theorem walkArcs_not_mem_swap {p : List V} (hp : p.Nodup) {u v : V} (h : (u, v) ∈ walkArcs p) :
    (v, u) ∉ walkArcs p :=
  (walkArcs_facts hp _ h).2

/-- [s6:sec] (preamble) A directed path of a digraph obtained by orienting edges of `F` is a path
of `F` (it runs along the underlying edges of its arcs). Pass `hA.mem` for an orientation `hA`. -/
theorem IsDirPathIn.isPathIn {F : Finset (Sym2 V)} {A : Finset (V × V)} {p : List V}
    (hp : IsDirPathIn A p) (hF : ∀ a ∈ A, s(a.1, a.2) ∈ F) : IsPathIn F p := by
  obtain ⟨hne, hnd, hpA⟩ := hp
  refine ⟨hne, hnd, ?_⟩
  intro e he
  rw [walkEdges_eq_map_walkArcs, List.mem_map] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact hF a (hpA a ha)

/-! ## Degrees -/

section Deg

variable [DecidableEq V]

theorem outDeg_cycleArcs {c : List V} (hc : c.Nodup) (v : V) :
    outDeg (cycleArcs c).toFinset v = c.count v := by
  unfold outDeg
  rw [(cycleArcs_nodup hc).card_eq_countP, List.count_eq_countP]
  conv_rhs => rw [← map_fst_cycleArcs c]
  rw [List.countP_map]
  apply List.countP_congr
  intro a _
  simp [Function.comp]

theorem inDeg_cycleArcs {c : List V} (hc : c.Nodup) (v : V) :
    inDeg (cycleArcs c).toFinset v = c.count v := by
  unfold inDeg
  rw [(cycleArcs_nodup hc).card_eq_countP, ← (List.rotate_perm c 1).count_eq,
    List.count_eq_countP, ← map_snd_cycleArcs c, List.countP_map]
  apply List.countP_congr
  intro a _
  simp [Function.comp]

theorem outDeg_sdiff {A C : Finset (V × V)} (h : C ⊆ A) (v : V) :
    outDeg (A \ C) v = outDeg A v - outDeg C v := by
  unfold outDeg
  rw [← Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ h)]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem inDeg_sdiff {A C : Finset (V × V)} (h : C ⊆ A) (v : V) :
    inDeg (A \ C) v = inDeg A v - inDeg C v := by
  unfold inDeg
  rw [← Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ h)]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

/-- Degrees add over disjoint arc sets. -/
theorem outDeg_union {A B : Finset (V × V)} (h : Disjoint A B) (v : V) :
    outDeg (A ∪ B) v = outDeg A v + outDeg B v := by
  unfold outDeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

/-- Degrees add over disjoint arc sets. -/
theorem inDeg_union {A B : Finset (V × V)} (h : Disjoint A B) (v : V) :
    inDeg (A ∪ B) v = inDeg A v + inDeg B v := by
  unfold inDeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem outDeg_mono {A B : Finset (V × V)} (h : A ⊆ B) (v : V) : outDeg A v ≤ outDeg B v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem inDeg_mono {A B : Finset (V × V)} (h : A ⊆ B) (v : V) : inDeg A v ≤ inDeg B v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem outDeg_eq_zero_iff {A : Finset (V × V)} {v : V} : outDeg A v = 0 ↔ ∀ w, (v, w) ∉ A := by
  unfold outDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h w hw
    exact h hw rfl
  · rintro h ⟨x, w⟩ hw rfl
    exact h w hw

theorem inDeg_eq_zero_iff {A : Finset (V × V)} {v : V} : inDeg A v = 0 ↔ ∀ u, (u, v) ∉ A := by
  unfold inDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h u hu
    exact h hu rfl
  · rintro h ⟨u, x⟩ hu rfl
    exact h u hu

theorem exists_mem_of_inDeg_pos {A : Finset (V × V)} {v : V} (h : 0 < inDeg A v) :
    ∃ u, (u, v) ∈ A := by
  unfold inDeg at h
  obtain ⟨a, ha⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter] at ha
  exact ⟨a.1, by rw [← ha.2]; exact ha.1⟩

theorem exists_mem_of_outDeg_pos {A : Finset (V × V)} {v : V} (h : 0 < outDeg A v) :
    ∃ w, (v, w) ∈ A := by
  unfold outDeg at h
  obtain ⟨a, ha⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter] at ha
  exact ⟨a.2, by rw [← ha.2]; exact ha.1⟩

theorem outDeg_pos_of_mem {A : Finset (V × V)} {v w : V} (h : (v, w) ∈ A) : 0 < outDeg A v := by
  unfold outDeg
  exact Finset.card_pos.2 ⟨(v, w), Finset.mem_filter.2 ⟨h, rfl⟩⟩

theorem inDeg_pos_of_mem {A : Finset (V × V)} {u v : V} (h : (u, v) ∈ A) : 0 < inDeg A v := by
  unfold inDeg
  exact Finset.card_pos.2 ⟨(u, v), Finset.mem_filter.2 ⟨h, rfl⟩⟩

/-- Counting arcs by their tails: `∑_{v ∈ S} d⁺(v) = |A|` if `S` contains every tail. -/
theorem sum_outDeg_eq_card {A : Finset (V × V)} {S : Finset V} (hS : ∀ a ∈ A, a.1 ∈ S) :
    ∑ v ∈ S, outDeg A v = A.card :=
  (Finset.card_eq_sum_card_fiberwise hS).symm

/-- Counting arcs by their heads: `∑_{v ∈ S} d⁻(v) = |A|` if `S` contains every head. -/
theorem sum_inDeg_eq_card {A : Finset (V × V)} {S : Finset V} (hS : ∀ a ∈ A, a.2 ∈ S) :
    ∑ v ∈ S, inDeg A v = A.card :=
  (Finset.card_eq_sum_card_fiberwise hS).symm

/-- [s6:lemGATE] (proof) "Deleting the arcs of `C` lowers in- and out-degree by `1` at every vertex
of `C` and changes nothing elsewhere. So the remaining digraph is still balanced." -/
theorem IsBalanced.sdiff_cycleArcs {A : Finset (V × V)} (hA : IsBalanced A) {c : List V}
    (hc : c.Nodup) (hcA : ∀ a ∈ cycleArcs c, a ∈ A) :
    IsBalanced (A \ (cycleArcs c).toFinset) := by
  have hsub : (cycleArcs c).toFinset ⊆ A := fun a ha => hcA a (List.mem_toFinset.1 ha)
  intro v
  rw [outDeg_sdiff hsub, inDeg_sdiff hsub, outDeg_cycleArcs hc, inDeg_cycleArcs hc, hA v]

/-- The union of two balanced digraphs on disjoint arc sets is balanced. -/
theorem IsBalanced.union {A B : Finset (V × V)} (hA : IsBalanced A) (hB : IsBalanced B)
    (h : Disjoint A B) : IsBalanced (A ∪ B) := by
  intro v
  rw [outDeg_union h, inDeg_union h, hA v, hB v]

/-- A balanced set `R ⊆ A` of arcs has no arc at a source of `A` (a vertex with `d⁻_A(v) = 0`). -/
theorem IsBalanced.degs_eq_zero_of_source {R A : Finset (V × V)} (hR : IsBalanced R) (h : R ⊆ A)
    {v : V} (hv : inDeg A v = 0) : outDeg R v = 0 ∧ inDeg R v = 0 := by
  have := inDeg_mono h v
  have h0 : inDeg R v = 0 := by omega
  exact ⟨(hR v).trans h0, h0⟩

/-- A balanced set `R ⊆ A` of arcs has no arc at a sink of `A` (a vertex with `d⁺_A(v) = 0`). -/
theorem IsBalanced.degs_eq_zero_of_sink {R A : Finset (V × V)} (hR : IsBalanced R) (h : R ⊆ A)
    {v : V} (hv : outDeg A v = 0) : outDeg R v = 0 ∧ inDeg R v = 0 := by
  have := outDeg_mono h v
  have h0 : outDeg R v = 0 := by omega
  exact ⟨h0, (hR v).symm.trans h0⟩

/-- Deleting a balanced set of arcs from a balanced digraph leaves a balanced digraph. -/
theorem IsBalanced.sdiff {A B : Finset (V × V)} (hA : IsBalanced A) (hB : IsBalanced B)
    (h : B ⊆ A) : IsBalanced (A \ B) := by
  intro v
  rw [outDeg_sdiff h, inDeg_sdiff h, hA v, hB v]

/-- The union of the arcs of arc-disjoint directed cycles (each without repeated vertex) is
balanced: every cycle through `v` contributes one in-arc and one out-arc at `v`. -/
theorem isBalanced_flatMap_cycleArcs : ∀ {cs : List (List V)}, (∀ c ∈ cs, c.Nodup) →
    (cs.flatMap cycleArcs).Nodup → IsBalanced (cs.flatMap cycleArcs).toFinset
  | [], _, _ => by
    intro v
    simp [outDeg, inDeg]
  | c :: cs, h, hnd => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    rw [List.flatMap_cons, List.toFinset_append]
    refine IsBalanced.union ?_
      (isBalanced_flatMap_cycleArcs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hnd.2.1) ?_
    · intro v
      rw [outDeg_cycleArcs (h c List.mem_cons_self), inDeg_cycleArcs (h c List.mem_cons_self)]
    · rw [Finset.disjoint_left]
      intro a ha hb
      exact hnd.2.2 a (List.mem_toFinset.1 ha) a (List.mem_toFinset.1 hb) rfl

end Deg

/-! ## Orientations -/

/-- An orientation has no loops (a field of `EG.IsOrientation`, restated for arcs `(u, v)`). -/
theorem IsOrientation.ne {F : Finset (Sym2 V)} {A : Finset (V × V)} (hA : IsOrientation F A)
    {u v : V} (h : (u, v) ∈ A) : u ≠ v :=
  hA.loopless _ h

/-- Two arcs of an orientation with the same underlying edge are equal. -/
theorem IsOrientation.inj {F : Finset (Sym2 V)} {A : Finset (V × V)} (hA : IsOrientation F A)
    {a b : V × V} (ha : a ∈ A) (hb : b ∈ A) (h : s(a.1, a.2) = s(b.1, b.2)) : a = b := by
  obtain ⟨x, _, huniq⟩ := hA.existsUnique _ (hA.mem a ha)
  exact (huniq a ⟨ha, rfl⟩).trans (huniq b ⟨hb, h.symm⟩).symm

/-- [s6:lemGATE] (proof) An orientation contains no two antiparallel arcs `u → v`, `v → u`: they
would be two directions of the same edge `uv` (each edge receives exactly one direction). -/
theorem IsOrientation.not_mem_swap {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hA : IsOrientation F A) {u v : V} (h : (u, v) ∈ A) : (v, u) ∉ A := by
  intro h'
  have := hA.inj h h' Sym2.eq_swap
  exact hA.ne h (Prod.ext_iff.1 this).1

/-- Distinct arcs of an orientation have distinct underlying edges. -/
theorem IsOrientation.sym2_injOn {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hA : IsOrientation F A) : Set.InjOn (fun a : V × V => s(a.1, a.2)) (A : Set (V × V)) :=
  fun _ ha _ hb h => hA.inj ha hb h

/-- Every edge of `F` is the underlying edge of an arc of an orientation of `F`. -/
theorem IsOrientation.exists_mem {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hA : IsOrientation F A) {e : Sym2 V} (he : e ∈ F) : ∃ a ∈ A, s(a.1, a.2) = e := by
  obtain ⟨a, ⟨ha, hae⟩, -⟩ := hA.existsUnique e he
  exact ⟨a, ha, hae⟩

/-- Constructor for orientations of an edge set of a (simple) graph `G`: looplessness of the arcs
is automatic, since `G` has no loops. -/
theorem IsOrientation.of_subset_edges {G : FGraph V} {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hF : F ⊆ G.edges) (hmem : ∀ a ∈ A, s(a.1, a.2) ∈ F)
    (hex : ∀ e ∈ F, ∃! a, a ∈ A ∧ s(a.1, a.2) = e) : IsOrientation F A where
  loopless a ha h := G.loopless _ (hF (hmem a ha)) (Sym2.mk_isDiag_iff.2 h)
  mem := hmem
  existsUnique := hex

/-- The empty arc set orients the empty edge set. -/
theorem IsOrientation.empty : IsOrientation (∅ : Finset (Sym2 V)) (∅ : Finset (V × V)) where
  loopless := by simp
  mem := by simp
  existsUnique := by simp

/-- Two orientations of disjoint edge sets have disjoint arc sets. -/
theorem IsOrientation.disjoint {F F' : Finset (Sym2 V)} {A B : Finset (V × V)}
    (hA : IsOrientation F A) (hB : IsOrientation F' B) (h : Disjoint F F') : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact Finset.disjoint_left.1 h (hA.mem a ha) (hB.mem a hb)

section OrientDec

variable [DecidableEq V]

/-- The underlying edges of an orientation of `F` are exactly the edges of `F`. -/
theorem IsOrientation.image_eq {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hA : IsOrientation F A) : A.image (fun a => s(a.1, a.2)) = F := by
  ext e
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hA.mem a ha
  · intro he
    exact hA.exists_mem he

/-- An orientation of `F` has exactly `|F|` arcs. -/
theorem IsOrientation.card_eq {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hA : IsOrientation F A) : A.card = F.card := by
  rw [← hA.image_eq, Finset.card_image_of_injOn hA.sym2_injOn]

/-- A subset `B` of an orientation orients its set of underlying edges. -/
theorem IsOrientation.subset {F : Finset (Sym2 V)} {A B : Finset (V × V)}
    (hA : IsOrientation F A) (h : B ⊆ A) :
    IsOrientation (B.image (fun a => s(a.1, a.2))) B where
  loopless a ha := hA.loopless a (h ha)
  mem a ha := Finset.mem_image_of_mem _ ha
  existsUnique e he := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
    exact ⟨a, ⟨ha, rfl⟩, fun b hb => hA.inj (h hb.1) (h ha) hb.2⟩

/-- The union of orientations of two disjoint edge sets orients their union. -/
theorem IsOrientation.union {F F' : Finset (Sym2 V)} {A B : Finset (V × V)}
    (hA : IsOrientation F A) (hB : IsOrientation F' B) (h : Disjoint F F') :
    IsOrientation (F ∪ F') (A ∪ B) where
  loopless a ha := by
    rcases Finset.mem_union.1 ha with ha | ha
    · exact hA.loopless a ha
    · exact hB.loopless a ha
  mem a ha := by
    rcases Finset.mem_union.1 ha with ha | ha
    · exact Finset.mem_union_left _ (hA.mem a ha)
    · exact Finset.mem_union_right _ (hB.mem a ha)
  existsUnique e he := by
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨a, ha, hae⟩ := hA.exists_mem he
      refine ⟨a, ⟨Finset.mem_union_left _ ha, hae⟩, ?_⟩
      rintro b ⟨hb, hbe⟩
      rcases Finset.mem_union.1 hb with hb | hb
      · exact hA.inj hb ha (hbe.trans hae.symm)
      · exact absurd (hbe ▸ hB.mem b hb) (Finset.disjoint_left.1 h he)
    · obtain ⟨a, ha, hae⟩ := hB.exists_mem he
      refine ⟨a, ⟨Finset.mem_union_right _ ha, hae⟩, ?_⟩
      rintro b ⟨hb, hbe⟩
      rcases Finset.mem_union.1 hb with hb | hb
      · exact absurd (hbe ▸ hA.mem b hb) (Finset.disjoint_right.1 h he)
      · exact hB.inj hb ha (hbe.trans hae.symm)

/-- Deleting from an orientation `A` of `F` the arcs of an orientation `B ⊆ A` of `F'` leaves an
orientation of `F \ F'`. -/
theorem IsOrientation.sdiff {F F' : Finset (Sym2 V)} {A B : Finset (V × V)}
    (hA : IsOrientation F A) (hB : IsOrientation F' B) (h : B ⊆ A) :
    IsOrientation (F \ F') (A \ B) where
  loopless a ha := hA.loopless a (Finset.mem_sdiff.1 ha).1
  mem a ha := by
    obtain ⟨haA, haB⟩ := Finset.mem_sdiff.1 ha
    refine Finset.mem_sdiff.2 ⟨hA.mem a haA, fun hF' => haB ?_⟩
    obtain ⟨b, hb, hbe⟩ := hB.exists_mem hF'
    rw [hA.inj haA (h hb) hbe.symm]
    exact hb
  existsUnique e he := by
    obtain ⟨heF, heF'⟩ := Finset.mem_sdiff.1 he
    obtain ⟨a, ha, hae⟩ := hA.exists_mem heF
    refine ⟨a, ⟨Finset.mem_sdiff.2 ⟨ha, fun haB => heF' (hae ▸ hB.mem a haB)⟩, hae⟩, ?_⟩
    rintro b ⟨hb, hbe⟩
    exact hA.inj (Finset.mem_sdiff.1 hb).1 ha (hbe.trans hae.symm)

/-- Characterisation of orientations without the `∃!` bookkeeping: `A` orients `F` iff no arc is
a loop, the underlying edges of the arcs are exactly the edges of `F`, and distinct arcs have
distinct underlying edges (so `a ↦ s(a.1, a.2)` is a bijection `A → F`). -/
theorem isOrientation_iff {F : Finset (Sym2 V)} {A : Finset (V × V)} :
    IsOrientation F A ↔ (∀ a ∈ A, a.1 ≠ a.2) ∧ A.image (fun a => s(a.1, a.2)) = F ∧
      Set.InjOn (fun a : V × V => s(a.1, a.2)) (A : Set (V × V)) := by
  constructor
  · intro hA
    exact ⟨hA.loopless, hA.image_eq, hA.sym2_injOn⟩
  · rintro ⟨hloop, himg, hinj⟩
    refine ⟨hloop, fun a ha => by rw [← himg]; exact Finset.mem_image_of_mem _ ha, ?_⟩
    intro e he
    rw [← himg, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact ⟨a, ⟨ha, rfl⟩, fun b hb => hinj hb.1 ha hb.2⟩

/-- [s6:lemHCCP] (proof, Step 1) "Orient every path of `𝒫_j` from its first to its last vertex":
the arcs `v₀ → v₁ → … → v_k` of a walk without repeated vertex orient its edges. (For several
paths, combine with `EG.IsOrientation.union`, which needs the paths to be edge-disjoint.) -/
theorem isOrientation_walkArcs {p : List V} (hp : p.Nodup) :
    IsOrientation (walkEdges p).toFinset (walkArcs p).toFinset := by
  rw [isOrientation_iff]
  refine ⟨fun a ha => walkArcs_loopless hp a (List.mem_toFinset.1 ha), ?_, ?_⟩
  · ext e
    simp [walkEdges_eq_map_walkArcs]
  · intro a ha b hb h
    rw [Finset.mem_coe, List.mem_toFinset] at ha hb
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd ((Prod.ext h2 h1 : (a.2, a.1) = b) ▸ hb) (walkArcs_not_mem_swap hp ha)

/-- [s6:lemMED] (proof) For an orientation `A` of `F`, `d⁺(v) + d⁻(v) = deg_F(v)`: every edge of
`F` at `v` is oriented exactly once, either out of `v` or into `v` ("`exc(u)` is a sum of `±1`
over the `deg_{B_𝒦}(u)` beads at `u`"; "every hub of degree `2d` has exactly `d` in-arcs and `d`
out-arcs"). -/
theorem IsOrientation.outDeg_add_inDeg {F : Finset (Sym2 V)} {A : Finset (V × V)}
    (hA : IsOrientation F A) (v : V) : outDeg A v + inDeg A v = degE F v := by
  unfold outDeg inDeg degE edgesAt
  have hdisj : Disjoint (A.filter (fun a => a.1 = v)) (A.filter (fun a => a.2 = v)) := by
    rw [Finset.disjoint_filter]
    intro a ha h1 h2
    exact hA.loopless a ha (h1.trans h2.symm)
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_or]
  -- the arcs at `v` map bijectively onto the edges of `F` at `v`
  have himg : (A.filter (fun a => a.1 = v ∨ a.2 = v)).image (fun a => s(a.1, a.2)) =
      F.filter (fun e => v ∈ e) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, hv⟩, rfl⟩
      refine ⟨hA.mem a ha, ?_⟩
      rcases hv with h | h <;> simp [h]
    · rintro ⟨he, hv⟩
      obtain ⟨a, ha, rfl⟩ := hA.exists_mem he
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      rcases Sym2.mem_iff.1 hv with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [← himg, Finset.card_image_of_injOn]
  intro x hx y hy h
  exact hA.inj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 h

end OrientDec

/-! ## Directed cycles and acyclicity -/

theorem IsAcyclic.mono {A B : Finset (V × V)} (h : A ⊆ B) (hB : IsAcyclic B) : IsAcyclic A :=
  fun c ⟨hne, hnd, hc⟩ => hB c ⟨hne, hnd, fun a ha => h (hc a ha)⟩

theorem isAcyclic_empty : IsAcyclic (∅ : Finset (V × V)) := by
  rintro c ⟨hne, -, hc⟩
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (cycleArcs_ne_nil hne)
  simpa using hc a ha

/-- [s6:lemMED] (a), [s6:lemHCCP] (proof, Step 3) A digraph with a potential that strictly
increases along every arc is acyclic ("`pot` strictly increases along every arc, and `MED(≺)` has
no directed cycle"; "every arc outside `𝒲` increases `Ψ`, so `F⃗ - 𝒲` is acyclic"). -/
theorem isAcyclic_of_potential {β : Type*} [LinearOrder β] {A : Finset (V × V)} (pot : V → β)
    (h : ∀ a ∈ A, pot a.1 < pot a.2) : IsAcyclic A := by
  classical
  rintro c ⟨hne, -, hc⟩
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image c.toFinset pot (List.toFinset_nonempty_iff c |>.2 hne)
  rw [List.mem_toFinset] at hm
  obtain ⟨w, hw⟩ := exists_mem_cycleArcs_fst hm
  have hlt : pot m < pot w := h _ (hc _ hw)
  have hle : pot w ≤ pot m := hmax w (List.mem_toFinset.2 (snd_mem_of_mem_cycleArcs hw))
  exact absurd hle (not_le.2 hlt)

/-- [s6:lemGATE] (proof) "Since `G` has no loops, `i ≠ k`" and "Suppose the length were `2` ...
impossible since `G` is simple": a directed cycle of a digraph without loops and without
antiparallel arcs has length at least `3`. -/
theorem IsDirCycle.three_le_length {A : Finset (V × V)} {c : List V} (hc : IsDirCycle A c)
    (hloop : ∀ a ∈ A, a.1 ≠ a.2) (hanti : ∀ u v, (u, v) ∈ A → (v, u) ∉ A) : 3 ≤ c.length := by
  obtain ⟨hne, -, hcA⟩ := hc
  match c, hne, hcA with
  | [], hne, _ => exact absurd rfl hne
  | [x], _, hcA => exact absurd rfl (hloop _ (hcA (x, x) (by simp [cycleArcs])))
  | [x, y], _, hcA =>
    exact absurd (hcA (y, x) (by simp [cycleArcs])) (hanti _ _ (hcA (x, y) (by simp [cycleArcs])))
  | _ :: _ :: _ :: _, _, _ => simp

/-- A directed cycle of an orientation has length at least `3`. -/
theorem IsDirCycle.three_le_length_of_isOrientation {F : Finset (Sym2 V)} {A : Finset (V × V)}
    {c : List V} (hc : IsDirCycle A c) (hA : IsOrientation F A) : 3 ≤ c.length :=
  hc.three_le_length hA.loopless (fun _ _ h => hA.not_mem_swap h)

theorem IsDirCycle.mono {A B : Finset (V × V)} {c : List V} (hc : IsDirCycle A c) (h : A ⊆ B) :
    IsDirCycle B c :=
  ⟨hc.1, hc.2.1, fun a ha => h (hc.2.2 a ha)⟩

/-- A directed cycle may start at any of its vertices. -/
theorem IsDirCycle.rotate {A : Finset (V × V)} {c : List V} (hc : IsDirCycle A c) (n : ℕ) :
    IsDirCycle A (c.rotate n) :=
  ⟨by rw [Ne, List.rotate_eq_nil_iff]; exact hc.1, List.nodup_rotate.2 hc.2.1,
    fun a ha => hc.2.2 a (mem_cycleArcs_rotate.1 ha)⟩

/-- [s6:sec] (preamble) The underlying edges of a directed cycle of a digraph obtained by
orienting edges of `F` are edges of `F`. Pass `hA.mem` for an orientation `hA`. -/
theorem IsDirCycle.forall_mem_cycleEdges {F : Finset (Sym2 V)} {A : Finset (V × V)} {c : List V}
    (hc : IsDirCycle A c) (hF : ∀ a ∈ A, s(a.1, a.2) ∈ F) : ∀ e ∈ cycleEdges c, e ∈ F := by
  intro e he
  rw [cycleEdges_eq_map_cycleArcs, List.mem_map] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact hF a (hc.2.2 a ha)

/-- [s6:lemGATE] (proof) "its underlying edge set is a cycle of `G`": a directed cycle of an
orientation is a well-formed cycle object (together with
`EG.IsDirCycle.forall_mem_cycleEdges`, a cycle of `F`). -/
theorem IsDirCycle.wf_of_isOrientation {F : Finset (Sym2 V)} {A : Finset (V × V)} {c : List V}
    (hc : IsDirCycle A c) (hA : IsOrientation F A) : (Obj.cycle c).WF :=
  ⟨hc.2.1, hc.three_le_length_of_isOrientation hA⟩

/-- [s6:lemHCCP] (proof, Step 4) Starting a directed cycle at the head of one of its arcs `a`
("Take a maximal subpath of `C` that contains no arc of `𝒲`. It starts at the head of a `𝒲`-arc"):
some rotation of `c` is `a.2 t₀ … t_m` with `t_m = a.1` (the last vertex is the tail of `a`), its
arcs are those of the directed path `a.2 t₀ … t_m` followed by `a`, and that path is a directed
path of `A`. -/
theorem IsDirCycle.exists_rotate_eq_cons_of_mem {A : Finset (V × V)} {c : List V}
    (hc : IsDirCycle A c) {a : V × V} (ha : a ∈ cycleArcs c) :
    ∃ n t, c.rotate n = a.2 :: t ∧ (a.2 :: t).getLast (List.cons_ne_nil _ _) = a.1 ∧
      cycleArcs (a.2 :: t) = walkArcs (a.2 :: t) ++ [a] ∧ IsDirPathIn A (a.2 :: t) := by
  obtain ⟨n, t, hnt⟩ := exists_rotate_eq_cons (snd_mem_of_mem_cycleArcs ha)
  have hc' : IsDirCycle A (a.2 :: t) := hnt ▸ hc.rotate n
  have ha' : a ∈ cycleArcs (a.2 :: t) := hnt ▸ mem_cycleArcs_rotate.2 ha
  have hlast : ((a.2 :: t).getLast (List.cons_ne_nil _ _), a.2) ∈ cycleArcs (a.2 :: t) := by
    rw [cycleArcs_cons]
    exact List.mem_append_right _ List.mem_cons_self
  -- the closing arc and `a` are arcs of the cycle with the same head
  have heq := eq_of_mem_cycleArcs_of_snd_eq hc'.2.1 hlast ha' rfl
  refine ⟨n, t, hnt, (Prod.ext_iff.1 heq).1, ?_, ?_⟩
  · rw [cycleArcs_cons, heq]
  · exact ⟨List.cons_ne_nil _ _, hc'.2.1,
      fun b hb => hc'.2.2 b (walkArcs_subset_cycleArcs _ b hb)⟩

section Cycle

variable [DecidableEq V]

/-- [s6:lemHCCP] (proof, Step 1) "A directed cycle of `D_j` cannot pass through a port, since
ports are sources or sinks of `D_j`": every vertex of a directed cycle has an in-arc. -/
theorem IsDirCycle.inDeg_pos {A : Finset (V × V)} {c : List V} (hc : IsDirCycle A c) {v : V}
    (hv : v ∈ c) : 0 < inDeg A v := by
  obtain ⟨u, hu⟩ := exists_mem_cycleArcs_snd hv
  exact inDeg_pos_of_mem (hc.2.2 _ hu)

/-- Every vertex of a directed cycle has an out-arc (see `EG.IsDirCycle.inDeg_pos`). -/
theorem IsDirCycle.outDeg_pos {A : Finset (V × V)} {c : List V} (hc : IsDirCycle A c) {v : V}
    (hv : v ∈ c) : 0 < outDeg A v := by
  obtain ⟨w, hw⟩ := exists_mem_cycleArcs_fst hv
  exact outDeg_pos_of_mem (hc.2.2 _ hw)

/-- The vertices incident with an arc of `A`. -/
@[expose] def arcVerts (A : Finset (V × V)) : Finset V := A.image Prod.fst ∪ A.image Prod.snd

@[simp] theorem mem_arcVerts {A : Finset (V × V)} {v : V} :
    v ∈ arcVerts A ↔ ∃ a ∈ A, a.1 = v ∨ a.2 = v := by
  unfold arcVerts
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact ⟨a, ha, Or.inl h⟩
    · exact ⟨a, ha, Or.inr h⟩
  · rintro ⟨a, ha, h | h⟩
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨a, ha, h⟩

theorem fst_mem_arcVerts {A : Finset (V × V)} {a : V × V} (h : a ∈ A) : a.1 ∈ arcVerts A :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)

theorem snd_mem_arcVerts {A : Finset (V × V)} {a : V × V} (h : a ∈ A) : a.2 ∈ arcVerts A :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

private theorem length_le_card_of_nodup {S : Finset V} {q : List V} (hq : q.Nodup)
    (hS : ∀ y ∈ q, y ∈ S) : q.length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup hq]
  exact Finset.card_le_card (fun y hy => hS y (List.mem_toFinset.1 hy))

/-- One step of the path argument of [s6:lemGATE]. Let `u w t₀ … t_m` be a directed path of `A`
(no repeated vertex), in a digraph where every vertex with an out-arc has an in-arc (e.g. a
balanced one). Its first vertex `u` has an out-arc, hence an in-arc `x → u`. Either `x` is not on
the path (and the path extends backwards to `x u w t₀ …`), or `x` is on the path and closes a
directed cycle `u … x u`. -/
theorem dirCycle_or_extend {A : Finset (V × V)} (hin : ∀ v, 0 < outDeg A v → 0 < inDeg A v)
    (u w : V) (t : List V) (hnd : (u :: w :: t).Nodup)
    (hch : List.IsChain (fun x y => (x, y) ∈ A) (u :: w :: t)) :
    (∃ c : List V, IsDirCycle A c) ∨ ∃ x, x ∉ u :: w :: t ∧ (x, u) ∈ A := by
  have huw : (u, w) ∈ A := (List.isChain_cons_cons.1 hch).1
  obtain ⟨x, hx⟩ := exists_mem_of_inDeg_pos (hin u (outDeg_pos_of_mem huw))
  by_cases hxq : x ∈ u :: w :: t
  · left
    by_cases hxu : x = u
    · subst hxu
      refine ⟨[x], by simp, by simp, ?_⟩
      intro a ha
      simp only [cycleArcs, List.rotate_singleton, List.zip_cons_cons, List.zip_nil_right,
        List.mem_singleton] at ha
      subst ha
      exact hx
    have hx' : x ∈ w :: t := by
      rcases List.mem_cons.1 hxq with h | h
      · exact absurd h hxu
      · exact h
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hx'
    have hq : u :: w :: t = (u :: (l₁ ++ [x])) ++ l₂ := by
      rw [hl]; simp
    refine ⟨u :: (l₁ ++ [x]), by simp, ?_, ?_⟩
    · rw [hq] at hnd
      exact hnd.sublist (List.sublist_append_left _ _)
    · apply forall_mem_cycleArcs_of_isChain
      · rw [hq] at hch
        exact hch.left_of_append
      · simpa using hx
  · exact Or.inr ⟨x, hxq, hx⟩

/-- The iteration of `EG.dirCycle_or_extend` (the "maximal path" of [s6:lemGATE], by induction on
`n = |arcVerts A| - length`): a directed path `u w t₀ … t_m` of `A` (at least one arc, no
repeated vertex, all its vertices ends of arcs) in a digraph where every vertex with an out-arc has
an in-arc extends backwards until it closes a directed cycle. -/
theorem exists_dirCycle_aux {A : Finset (V × V)} (hin : ∀ v, 0 < outDeg A v → 0 < inDeg A v) :
    ∀ (n : ℕ) (u w : V) (t : List V), (arcVerts A).card - (u :: w :: t).length = n →
      (u :: w :: t).Nodup → List.IsChain (fun x y => (x, y) ∈ A) (u :: w :: t) →
      (∀ y ∈ u :: w :: t, y ∈ arcVerts A) → ∃ c : List V, IsDirCycle A c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w t hn hnd hch hS
    rcases dirCycle_or_extend hin u w t hnd hch with h | ⟨x, hxq, hx⟩
    · exact h
    · have hnd' : (x :: u :: w :: t).Nodup := List.nodup_cons.2 ⟨hxq, hnd⟩
      have hS' : ∀ y ∈ x :: u :: w :: t, y ∈ arcVerts A := by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact fst_mem_arcVerts hx
        · exact hS y hy
      have hlen := length_le_card_of_nodup hnd' hS'
      simp only [List.length_cons] at hlen hn
      refine ih _ ?_ x u (w :: t) rfl hnd' (List.IsChain.cons_cons hx hch) hS'
      simp only [List.length_cons]
      omega

/-- [s6:lemGATE] (proof, first step) A non-empty digraph in which every vertex with an out-arc has
an in-arc (in particular a non-empty balanced digraph) contains a directed cycle. -/
theorem exists_isDirCycle_of_forall_inDeg_pos {A : Finset (V × V)}
    (hin : ∀ v, 0 < outDeg A v → 0 < inDeg A v) (hne : A.Nonempty) : ∃ c : List V, IsDirCycle A c := by
  obtain ⟨⟨u, w⟩, h⟩ := hne
  by_cases huw : u = w
  · subst huw
    refine ⟨[u], by simp, by simp, ?_⟩
    intro a ha
    simp only [cycleArcs, List.rotate_singleton, List.zip_cons_cons, List.zip_nil_right,
      List.mem_singleton] at ha
    subst ha
    exact h
  refine exists_dirCycle_aux hin _ u w [] rfl ?_ ?_ ?_
  · simpa using huw
  · exact List.IsChain.cons_cons h (List.IsChain.singleton w)
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact fst_mem_arcVerts h
    · exact snd_mem_arcVerts h

/-- [s6:lemGATE] (proof, first step) A non-empty digraph with `d⁺ ≤ d⁻` everywhere (in
particular a balanced one), without loops and without antiparallel arcs, contains a directed
cycle with distinct vertices and of length at least `3`. -/
theorem exists_dirCycle_of_balanced {A : Finset (V × V)} (hloop : ∀ a ∈ A, a.1 ≠ a.2)
    (hanti : ∀ u v, (u, v) ∈ A → (v, u) ∉ A) (hbal : ∀ v, outDeg A v ≤ inDeg A v)
    (hne : A.Nonempty) : ∃ c : List V, c.Nodup ∧ 3 ≤ c.length ∧ ∀ a ∈ cycleArcs c, a ∈ A := by
  obtain ⟨c, hc⟩ :=
    exists_isDirCycle_of_forall_inDeg_pos (fun v hv => lt_of_lt_of_le hv (hbal v)) hne
  exact ⟨c, hc.2.1, hc.three_le_length hloop hanti, hc.2.2⟩

/-- s6, proof of the non-giant-component step: "an acyclic orientation with an arc has a source".
A non-empty acyclic digraph has a vertex with an out-arc and no in-arc. -/
theorem IsAcyclic.exists_source {A : Finset (V × V)} (hA : IsAcyclic A) (hne : A.Nonempty) :
    ∃ v, inDeg A v = 0 ∧ 0 < outDeg A v := by
  by_contra hno
  have hin : ∀ v, 0 < outDeg A v → 0 < inDeg A v := by
    intro v hv
    rcases Nat.eq_zero_or_pos (inDeg A v) with h0 | hpos
    · exact absurd ⟨v, h0, hv⟩ hno
    · exact hpos
  obtain ⟨c, hc⟩ := exists_isDirCycle_of_forall_inDeg_pos hin hne
  exact hA c hc

/-- [s6:lemHCCP] (proof, Step 3) "One exists because the orientation is acyclic: take the position
in a topological order"; "a numbering `tp_j : T_j → {1, …, |T_j|}` that increases along the arcs
of the acyclic digraph". For an acyclic digraph `A` and a finite vertex set `S` containing both
ends of every arc, there is a numbering `f`, injective on `S` with values in `{1, …, |S|}` on `S`
(hence a bijection `S → {1, …, |S|}`), that strictly increases along every arc. -/
theorem IsAcyclic.exists_potential {A : Finset (V × V)} (hA : IsAcyclic A) (S : Finset V)
    (hS : ∀ a ∈ A, a.1 ∈ S ∧ a.2 ∈ S) :
    ∃ f : V → ℕ, Set.InjOn f S ∧ (∀ v ∈ S, 1 ≤ f v ∧ f v ≤ S.card) ∧
      ∀ a ∈ A, f a.1 < f a.2 := by
  induction S using Finset.strongInduction generalizing A with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · refine ⟨fun _ => 0, by simp, by simp, ?_⟩
      intro a ha
      simpa using (hS a ha).1
    -- a vertex `v ∈ S` without in-arc: a source of `A`, or any vertex if `A` is empty
    obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S, ∀ u, (u, v) ∉ A := by
      rcases A.eq_empty_or_nonempty with rfl | hAne
      · obtain ⟨v, hv⟩ := hSne
        exact ⟨v, hv, by simp⟩
      · obtain ⟨v, hin, hout⟩ := hA.exists_source hAne
        obtain ⟨w, hw⟩ := exists_mem_of_outDeg_pos hout
        exact ⟨v, (hS _ hw).1, inDeg_eq_zero_iff.1 hin⟩
    have hv2 : ∀ a ∈ A, a.2 ≠ v := by
      rintro ⟨x, y⟩ ha rfl
      exact hv0 x ha
    -- number `v` first, then the rest (the arcs not leaving `v`) by induction
    set A' := A.filter (fun a => a.1 ≠ v) with hA'def
    have hS' : ∀ a ∈ A', a.1 ∈ S.erase v ∧ a.2 ∈ S.erase v := by
      intro a ha
      rw [Finset.mem_filter] at ha
      exact ⟨Finset.mem_erase.2 ⟨ha.2, (hS a ha.1).1⟩,
        Finset.mem_erase.2 ⟨hv2 a ha.1, (hS a ha.1).2⟩⟩
    obtain ⟨f, hinj, hrange, hinc⟩ :=
      ih (S.erase v) (Finset.erase_ssubset hvS) (hA.mono (Finset.filter_subset _ _)) hS'
    have hcard : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hvS
    have hf1 : ∀ x ∈ S, x ≠ v → 1 ≤ f x ∧ f x ≤ (S.erase v).card :=
      fun x hx hxv => hrange x (Finset.mem_erase.2 ⟨hxv, hx⟩)
    refine ⟨fun x => if x = v then 1 else f x + 1, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      simp only at hxy
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · rw [hxv, hyv]
      · rw [if_pos hxv, if_neg hyv] at hxy
        have := hf1 y hy hyv
        omega
      · rw [if_neg hxv, if_pos hyv] at hxy
        have := hf1 x hx hxv
        omega
      · rw [if_neg hxv, if_neg hyv] at hxy
        exact hinj (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hxv, hx⟩))
          (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyv, hy⟩)) (by omega)
    · intro x hx
      dsimp only
      by_cases hxv : x = v
      · rw [if_pos hxv]
        omega
      · rw [if_neg hxv]
        have := hf1 x hx hxv
        omega
    · intro a ha
      dsimp only
      have ha2 := hv2 a ha
      by_cases ha1 : a.1 = v
      · rw [if_pos ha1, if_neg ha2]
        have := hf1 a.2 (hS a ha).2 ha2
        omega
      · rw [if_neg ha1, if_neg ha2]
        have := hinc a (Finset.mem_filter.2 ⟨ha, ha1⟩)
        omega

/-- A digraph is acyclic iff it has a potential (with values in `ℕ`) increasing along every arc. -/
theorem isAcyclic_iff_exists_potential {A : Finset (V × V)} :
    IsAcyclic A ↔ ∃ f : V → ℕ, ∀ a ∈ A, f a.1 < f a.2 := by
  constructor
  · intro hA
    obtain ⟨f, -, -, hf⟩ :=
      hA.exists_potential (arcVerts A) (fun a ha => ⟨fst_mem_arcVerts ha, snd_mem_arcVerts ha⟩)
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact isAcyclic_of_potential f hf

/-- [s6:lemGATE] (proof) "We first show that `F⃗` is an arc-disjoint union of directed cycles of
length at least `3`, by induction on the number of arcs."  A balanced digraph without loops and
without antiparallel arcs is the arc-disjoint union of directed cycles with distinct vertices,
each of length at least `3`. -/
theorem exists_dirCycle_decomp (A : Finset (V × V)) (hloop : ∀ a ∈ A, a.1 ≠ a.2)
    (hanti : ∀ u v, (u, v) ∈ A → (v, u) ∉ A) (hbal : IsBalanced A) :
    ∃ cs : List (List V), (∀ c ∈ cs, c.Nodup ∧ 3 ≤ c.length ∧ ∀ a ∈ cycleArcs c, a ∈ A) ∧
      (cs.flatMap cycleArcs).Nodup ∧ ∀ a, a ∈ cs.flatMap cycleArcs ↔ a ∈ A := by
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], by simp, by simp, by simp⟩
    obtain ⟨c, hnd, hlen, hcA⟩ :=
      exists_dirCycle_of_balanced hloop hanti (fun v => (hbal v).le) hne
    set C := (cycleArcs c).toFinset with hC
    have hsub : C ⊆ A := fun a ha => hcA a (List.mem_toFinset.1 ha)
    have hCne : C.Nonempty := by
      rw [hC, List.toFinset_nonempty_iff]
      apply cycleArcs_ne_nil
      rintro rfl
      simp at hlen
    obtain ⟨cs, hcs, hcsnd, hcsmem⟩ := ih (A \ C) (Finset.sdiff_ssubset hsub hCne)
      (fun a ha => hloop a (Finset.mem_sdiff.1 ha).1)
      (fun u v h h' => hanti u v (Finset.mem_sdiff.1 h).1 (Finset.mem_sdiff.1 h').1)
      (hbal.sdiff_cycleArcs hnd hcA)
    refine ⟨c :: cs, ?_, ?_, ?_⟩
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨hnd, hlen, hcA⟩
      · obtain ⟨h1, h2, h3⟩ := hcs c' hc'
        exact ⟨h1, h2, fun a ha => (Finset.mem_sdiff.1 (h3 a ha)).1⟩
    · rw [List.flatMap_cons, List.nodup_append]
      refine ⟨cycleArcs_nodup hnd, hcsnd, ?_⟩
      intro a ha b hb hab
      subst hab
      have := (Finset.mem_sdiff.1 ((hcsmem a).1 hb)).2
      exact this (List.mem_toFinset.2 ha)
    · intro a
      rw [List.flatMap_cons, List.mem_append, hcsmem a, Finset.mem_sdiff]
      constructor
      · rintro (h | h)
        · exact hcA a h
        · exact h.1
      · intro h
        by_cases haC : a ∈ C
        · exact Or.inl (List.mem_toFinset.1 haC)
        · exact Or.inr ⟨h, haC⟩

/-- [s6:lemHCCP] (proof, Step 1) "Delete directed cycles from `D_j` one at a time until no directed
cycle remains." Every digraph `A` contains arc-disjoint directed cycles `c ∈ cs` whose deletion
leaves an acyclic digraph. (The deleted arc set is balanced, `EG.isBalanced_flatMap_cycleArcs`,
see `EG.exists_balanced_sdiff_acyclic`.) -/
theorem exists_cancel_dirCycles (A : Finset (V × V)) :
    ∃ cs : List (List V), (∀ c ∈ cs, IsDirCycle A c) ∧ (cs.flatMap cycleArcs).Nodup ∧
      IsAcyclic (A \ (cs.flatMap cycleArcs).toFinset) := by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hA : IsAcyclic A
    · exact ⟨[], by simp, by simp, by simpa using hA⟩
    obtain ⟨c, hc⟩ : ∃ c, IsDirCycle A c := by
      unfold IsAcyclic at hA
      push Not at hA
      exact hA
    set C := (cycleArcs c).toFinset with hC
    have hsub : C ⊆ A := fun a ha => hc.2.2 a (List.mem_toFinset.1 ha)
    have hCne : C.Nonempty := by
      rw [hC, List.toFinset_nonempty_iff]
      exact cycleArcs_ne_nil hc.1
    obtain ⟨cs, hcs, hnd, hac⟩ := ih (A \ C) (Finset.sdiff_ssubset hsub hCne)
    refine ⟨c :: cs, ?_, ?_, ?_⟩
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hc
      · exact (hcs c' hc').mono Finset.sdiff_subset
    · rw [List.flatMap_cons, List.nodup_append]
      refine ⟨cycleArcs_nodup hc.2.1, hnd, ?_⟩
      intro a ha b hb hab
      subst hab
      obtain ⟨c', hc', hb'⟩ := List.mem_flatMap.1 hb
      exact (Finset.mem_sdiff.1 ((hcs c' hc').2.2 a hb')).2 (List.mem_toFinset.2 ha)
    · have hset : A \ ((c :: cs).flatMap cycleArcs).toFinset =
          (A \ C) \ (cs.flatMap cycleArcs).toFinset := by
        ext a
        simp only [List.flatMap_cons, List.toFinset_append, Finset.mem_sdiff, Finset.mem_union, hC]
        tauto
      rw [hset]
      exact hac

/-- [s6:lemHCCP] (proof, Step 1) Cancellation, as an arc set: every digraph `A` has a balanced
set `R ⊆ A` of arcs whose deletion leaves an acyclic digraph ("Each deletion lowers in- and
out-degree by one at the vertices of a cycle"). Since `R ⊆ A` is balanced, `R` has no arc at a
source or a sink of `A`, so deleting it changes no degree there. -/
theorem exists_balanced_sdiff_acyclic (A : Finset (V × V)) :
    ∃ R ⊆ A, IsBalanced R ∧ IsAcyclic (A \ R) := by
  obtain ⟨cs, hcs, hnd, hac⟩ := exists_cancel_dirCycles A
  refine ⟨(cs.flatMap cycleArcs).toFinset, ?_,
    isBalanced_flatMap_cycleArcs (fun c hc => (hcs c hc).2.1) hnd, hac⟩
  intro a ha
  obtain ⟨c, hc, hac⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 ha)
  exact (hcs c hc).2.2 a hac

end Cycle

/-! ## From directed cycles to a decomposition -/

/-- The edges of the cycle objects of a list `cs` of vertex lists are the underlying edges of the
concatenated arc lists `cycleArcs c`, `c ∈ cs`, in the same order. -/
theorem Obj.flatMap_edges_map_cycle (cs : List (List V)) :
    (cs.map Obj.cycle).flatMap Obj.edges =
      (cs.flatMap cycleArcs).map (fun a => s(a.1, a.2)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    rw [Obj.edges, cycleEdges_eq_map_cycleArcs]

/-- [s6:lemGATE] (proof) "Their underlying cycles partition `F`, so they form a decomposition of
`F` into cycles in the sense of Definition [s1:defObject]." Let `A` be an orientation of `F`, and
let the directed cycles `c ∈ cs` (well-formed cycle objects) have pairwise disjoint duplicate-free
arc lists whose union is `A`. Then the cycle objects `Obj.cycle c` form a decomposition of `F`. -/
theorem isDecomp_map_cycle_of_arcs {F : Finset (Sym2 V)} {A : Finset (V × V)}
    {cs : List (List V)} (hA : IsOrientation F A) (hnd : (cs.flatMap cycleArcs).Nodup)
    (hmem : ∀ a, a ∈ cs.flatMap cycleArcs ↔ a ∈ A) (hwf : ∀ c ∈ cs, (Obj.cycle c).WF) :
    IsDecomp (F : Set (Sym2 V)) (cs.map Obj.cycle) := by
  refine ⟨?_, ?_, ?_⟩
  · intro o ho
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    exact hwf c hc
  · -- distinct arcs have distinct underlying edges
    rw [Obj.flatMap_edges_map_cycle]
    exact hnd.map_on (fun x hx y hy h => hA.inj ((hmem x).1 hx) ((hmem y).1 hy) h)
  · intro e
    rw [Obj.flatMap_edges_map_cycle, List.mem_map, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hA.mem a ((hmem a).1 ha)
    · intro he
      obtain ⟨a, ha, rfl⟩ := hA.exists_mem he
      exact ⟨a, (hmem a).2 ha, rfl⟩

end EG
