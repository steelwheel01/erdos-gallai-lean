module

public import EG.Spec.Found.EG0
public import EG.Lib.Found.Fnum
public import EG.Lib.Found.Graph
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.Exponential

/-!
# Fact EG0, the long-cycle bound (manuscript s1:factEG0)

Proofs of `EG.Spec.FactEG0aStatement`, `EG.Spec.FactEG0aFnumStatement` and
`EG.Spec.FactEG0bStatement` (the Erdős–Gallai `O(n log n)` argument, as written in s1.tex):

* `EG.EG0.exists_core`: deleting vertices of degree `≤ d - 1` one at a time from a vertex set `S`
  with `(|S| - 1)(d - 1) < e(H[S])` stops at a non-empty `T ⊆ S` with `δ(H[T]) ≥ d`;
* `EG.EG0.exists_long_cycle_of_deg`: a longest path `v₀ … v_r` of a graph of minimum degree
  `d ≥ 2`, closed at the neighbour of `v₀` of largest index, is a cycle of length `≥ d + 1`;
* `EG.EG0.exists_cycle_of_card_le` (the Claim): a graph with `h ≥ 1` vertices and `m' ≥ h` edges
  has a cycle of length `ℓ` with `m' < hℓ`;
* `EG.EG0.block`, `EG.EG0.decomp_of_card_lt`: removal of long cycles; `h` removals at least halve
  the number of edges (`(1 - 1/h)^h ≤ e⁻¹ ≤ 1/2`), so an edge set with fewer than `2^q h` edges is
  decomposed into at most `q h` cycles and at most `h - 1` single edges;
* `EG.EG0.exists_decomp_log`: the bound `h(log h + 1)` for an edge set with ends in `W`, `|W| = h`.
-/

public section


namespace EG

namespace EG0

variable {V : Type*}

/-! ### A prefix ending at the last element with a property -/

/-- If some element of `p` satisfies `q`, then `p` has a prefix `c ++ [u]` with `q u` that
contains every element of `p` satisfying `q`. -/
theorem exists_prefix_last (q : V → Prop) [DecidablePred q] :
    ∀ (p : List V), (∃ x ∈ p, q x) →
      ∃ c u, (c ++ [u]) <+: p ∧ q u ∧ ∀ x ∈ p, q x → x ∈ c ++ [u]
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ht : ∃ x ∈ t, q x
    · obtain ⟨c, u, hpre, hu, hall⟩ := exists_prefix_last q t ht
      refine ⟨a :: c, u, ?_, hu, fun x hx hqx => ?_⟩
      · simpa using hpre
      · rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · have := hall x hx hqx
          simp only [List.mem_append, List.mem_singleton] at this
          simp only [List.cons_append, List.mem_cons, List.mem_append]
          tauto
    · push Not at ht
      have ha : q a := by
        obtain ⟨x, hx, hqx⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hqx
        · exact absurd hqx (ht x hx)
      refine ⟨[], a, by simp, ha, fun x hx hqx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact absurd hqx (ht x hx)

/-! ### Closing a chain into a cycle -/

/-- A duplicate-free list, all of whose consecutive pairs and whose last and first vertices are
adjacent in `G`, has all its cycle edges in `E(G)`. -/
theorem cycleEdges_subset_of_chain {G : FGraph V} {c : List V}
    (hch : c.IsChain G.Adj) (hclose : ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) :
    ∀ e ∈ cycleEdges c, e ∈ G.edges := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := mem_cycleEdges.1 he
  by_cases h1 : i + 1 < c.length
  · have h2 := hch.getElem i h1
    simp only [Nat.mod_eq_of_lt h1]
    exact h2
  · have hi' : i + 1 = c.length := by omega
    have hmod : (i + 1) % c.length = 0 := by rw [hi', Nat.mod_self]
    simp only [hmod]
    have hlast : c.getLast? = some c[i] := by
      rw [List.getLast?_eq_getElem?]
      simp only [show c.length - 1 = i by omega]
      exact List.getElem?_eq_getElem hi
    have hhead : c.head? = some c[0] := by
      rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)
    exact hclose c[i] (by rw [hlast]; rfl) c[0] (by rw [hhead]; rfl)

/-! ### A long cycle in a graph of large minimum degree -/

/-- A path of `G` (as a vertex list inside `V(G)`). -/
def IsPth [DecidableEq V] (G : FGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain G.Adj ∧ ∀ x ∈ p, x ∈ G.verts

theorem IsPth.length_le [DecidableEq V] {G : FGraph V} {p : List V} (hp : IsPth G p) : p.length ≤ G.verts.card := by
  rw [← List.toFinset_card_of_nodup hp.2.1]
  exact Finset.card_le_card (fun x hx => hp.2.2.2 x (List.mem_toFinset.1 hx))

/-- A longest path exists in a graph with at least one vertex. -/
theorem exists_longest [DecidableEq V] {G : FGraph V} (hne : G.verts.Nonempty) :
    ∃ p, IsPth G p ∧ ∀ q, IsPth G q → q.length ≤ p.length := by
  classical
  let S : Set ℕ := {n | ∃ p, IsPth G p ∧ p.length = n}
  obtain ⟨v, hv⟩ := hne
  have hS : S.Nonempty := ⟨1, [v], ⟨by simp, by simp, by simp, by simpa using hv⟩, rfl⟩
  have hbdd : BddAbove S := ⟨G.verts.card, fun n ⟨p, hp, hn⟩ => hn ▸ hp.length_le⟩
  obtain ⟨p, hp, hn⟩ := Nat.sSup_mem hS hbdd
  exact ⟨p, hp, fun q hq => hn ▸ le_csSup hbdd ⟨q, hq, rfl⟩⟩

/-- [s1:factEG0] (a), end of the Claim: "Let `v₀v₁⋯v_r` be a longest path in `H*`. Every
neighbour of `v₀` in `H*` is one of `v₁, …, v_r` … the largest index `i` with `v₀vᵢ ∈ E(H*)`
satisfies `i ≥ d ≥ 2`, so `v₀v₁⋯vᵢv₀` is a cycle … of length `i + 1 > d`." -/
theorem exists_long_cycle_of_deg [DecidableEq V] (G : FGraph V) (d : ℕ) (hd : 2 ≤ d) (hne : G.verts.Nonempty)
    (hdeg : ∀ v ∈ G.verts, d ≤ G.deg v) :
    ∃ c : List V, c.Nodup ∧ d + 1 ≤ c.length ∧ ∀ e ∈ cycleEdges c, e ∈ G.edges := by
  classical
  obtain ⟨p, hp, hmax⟩ := exists_longest hne
  obtain ⟨v₀, rest, rfl⟩ : ∃ v₀ rest, p = v₀ :: rest := by
    rcases p with _ | ⟨a, t⟩
    · exact absurd rfl hp.1
    · exact ⟨a, t, rfl⟩
  have hv₀ : v₀ ∈ G.verts := hp.2.2.2 v₀ (by simp)
  -- every neighbour of `v₀` lies on the path
  have hnb : ∀ u ∈ G.nbrs v₀, u ∈ v₀ :: rest := by
    intro u hu
    by_contra hnot
    have hadj : G.Adj v₀ u := FGraph.mem_nbrs.1 hu
    have hq : IsPth G (u :: v₀ :: rest) := by
      refine ⟨by simp, List.nodup_cons.2 ⟨hnot, hp.2.1⟩, ?_, ?_⟩
      · exact List.IsChain.cons_cons hadj.symm hp.2.2.1
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hadj.mem_verts_right
        · exact hp.2.2.2 x hx
    have := hmax _ hq
    simp at this
  have hcard : d ≤ (G.nbrs v₀).card := hdeg v₀ hv₀
  obtain ⟨w, hw⟩ : (G.nbrs v₀).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨c, u, hpre, hu, hall⟩ :=
    exists_prefix_last (G.Adj v₀) (v₀ :: rest) ⟨w, hnb w hw, FGraph.mem_nbrs.1 hw⟩
  -- the prefix starts with `v₀`
  obtain ⟨c', rfl⟩ : ∃ c', c = v₀ :: c' := by
    rcases c with _ | ⟨a, c'⟩
    · exfalso
      have : u = v₀ := by simpa using hpre.head
      exact hu.ne this.symm
    · have : a = v₀ := by simpa using hpre.head
      exact ⟨c', by rw [this]⟩
  refine ⟨v₀ :: c' ++ [u], hpre.sublist.nodup hp.2.1, ?_, ?_⟩
  · -- length: the neighbours of `v₀` lie in the cycle minus `v₀`
    have hsub : G.nbrs v₀ ⊆ (v₀ :: c' ++ [u]).toFinset.erase v₀ := by
      intro x hx
      rw [Finset.mem_erase, List.mem_toFinset]
      exact ⟨fun h => G.self_not_mem_nbrs v₀ (h ▸ hx), hall x (hnb x hx) (FGraph.mem_nbrs.1 hx)⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp)] at h1
    have h2 := List.toFinset_card_le (v₀ :: c' ++ [u])
    omega
  · have hpch : (v₀ :: rest).IsChain G.Adj := hp.2.2.1
    apply cycleEdges_subset_of_chain (hpch.infix hpre.isInfix)
    intro a ha b hb
    simp only [List.cons_append, List.getLast?_cons, List.getLast?_append,
      Option.some_or, Option.getD_some, Option.mem_def, Option.some.injEq] at ha
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst ha hb
    exact hu.symm

/-! ### Peeling vertices of small degree -/

/-- Deleting one vertex `v` from `S` loses at most `d_{H[S]}(v)` edges of `H[S]`. -/
theorem card_induce_edges_le_erase [DecidableEq V] (H : FGraph V) (S : Finset V) (v : V) :
    (H.induce S).edges.card ≤ (H.induce (S.erase v)).edges.card + (H.induce S).deg v := by
  rw [FGraph.deg_eq_degE, degE]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro e he
  rw [Finset.mem_union, FGraph.mem_induce_edges, FGraph.mem_edgesAt]
  by_cases hv : v ∈ e
  · exact Or.inr ⟨he, hv⟩
  · left
    rw [FGraph.mem_induce_edges] at he
    refine ⟨he.1, fun w hw => Finset.mem_erase.2 ⟨fun h => hv (h ▸ hw), he.2 w hw⟩⟩

/-- [s1:factEG0] (a), in the Claim: "Delete from `H'`, one at a time, a vertex whose degree in the
current graph is at most `d − 1`, as long as such a vertex exists. … So the deletions stop at a
subgraph `H*` of `H'` with at least one vertex and minimum degree at least `d`."
Here the current graph is `H[S]`, and the hypothesis `(|S| - 1)(d - 1) < e(H[S])` is what rules
out the deletion of all vertices. -/
theorem exists_core [DecidableEq V] (H : FGraph V) (d : ℕ) :
    ∀ n, ∀ S ⊆ H.verts, S.card = n → S.Nonempty → (n - 1) * (d - 1) < (H.induce S).edges.card →
      ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T, d ≤ (H.induce T).deg v := by
  intro n
  induction n with
  | zero =>
    intro S _ hS hne _
    rw [Finset.card_eq_zero] at hS
    exact absurd hS hne.ne_empty
  | succ n ih =>
    intro S hSH hS hne hlt
    by_cases hall : ∀ v ∈ S, d ≤ (H.induce S).deg v
    · exact ⟨S, subset_rfl, hne, hall⟩
    push Not at hall
    obtain ⟨v, hvS, hvd⟩ := hall
    have hcard := card_induce_edges_le_erase H S v
    have hS' : (S.erase v).card = n := by rw [Finset.card_erase_of_mem hvS, hS]; rfl
    by_cases hne' : (S.erase v).Nonempty
    · obtain ⟨T, hTS, hTne, hT⟩ := ih (S.erase v) ((Finset.erase_subset v S).trans hSH) hS' hne'
        (by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by
            have := hne'.card_pos; omega⟩
          have hmul : (k + 1) * (d - 1) = k * (d - 1) + (d - 1) := by ring
          simp only [Nat.add_sub_cancel] at hlt ⊢
          omega)
      exact ⟨T, hTS.trans (Finset.erase_subset v S), hTne, hT⟩
    · -- `S = {v}`: `H[S]` has no edges, contradicting `0 < e(H[S])`
      exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hne'
      have hn : n = 0 := by rw [← hS', hne', Finset.card_empty]
      subst hn
      have hempty : (H.induce S).edges = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rw [FGraph.mem_induce_edges] at he
        have hloop := H.loopless e he.1
        apply hloop
        induction e using Sym2.ind with
        | h a b =>
          have ha := he.2 a (Sym2.mem_mk_left a b)
          have hb := he.2 b (Sym2.mem_mk_right a b)
          have ha' : a = v := by
            by_contra hav
            have : a ∈ S.erase v := Finset.mem_erase.2 ⟨hav, ha⟩
            rw [hne'] at this
            simp at this
          have hb' : b = v := by
            by_contra hbv
            have : b ∈ S.erase v := Finset.mem_erase.2 ⟨hbv, hb⟩
            rw [hne'] at this
            simp at this
          rw [Sym2.mk_isDiag_iff, ha', hb']
      rw [hempty] at hlt
      simp at hlt

/-- [s1:factEG0] (a), the Claim: "If a graph `H'` with vertex set `V(H)` has `m' ≥ h` edges, then
`H'` contains a cycle of length at least `m'/h`." (Here with the strict bound `m' < h ℓ` that the
proof gives, `ℓ > d ≥ ⌈m'/h⌉`; `d` is taken as `max(2, ⌊m'/h⌋)`.) -/
theorem exists_cycle_of_card_le [DecidableEq V] (H : FGraph V) (h1 : 1 ≤ H.card)
    (hm : H.card ≤ H.edges.card) :
    ∃ c : List V, c.Nodup ∧ 3 ≤ c.length ∧ (∀ e ∈ cycleEdges c, e ∈ H.edges) ∧
      H.edges.card < H.card * c.length := by
  set h := H.card with hh
  set m := H.edges.card with hmdef
  set d := max 2 (m / h) with hd
  have hd2 : 2 ≤ d := le_max_left _ _
  have hind : (H.induce H.verts).edges = H.edges := by
    ext e
    rw [FGraph.mem_induce_edges]
    exact ⟨fun h => h.1, fun he => ⟨he, H.edge_verts e he⟩⟩
  have hqm : m / h * h ≤ m := Nat.div_mul_le_self m h
  have hlt : (h - 1) * (d - 1) < (H.induce H.verts).edges.card := by
    rw [hind]
    rcases le_total (m / h) 2 with hq | hq
    · have : d = 2 := by rw [hd]; exact max_eq_left hq
      rw [this]
      omega
    · have : d = m / h := by rw [hd]; exact max_eq_right hq
      rw [this]
      obtain ⟨a, ha⟩ : ∃ a, h = a + 1 := ⟨h - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, m / h = b + 1 := ⟨m / h - 1, by omega⟩
      rw [hb] at hqm ⊢
      rw [ha] at hqm ⊢
      simp only [Nat.add_sub_cancel]
      nlinarith
  obtain ⟨v, hv⟩ : H.verts.Nonempty := Finset.card_pos.1 (show 0 < H.card by omega)
  obtain ⟨T, hTS, hTne, hT⟩ := exists_core H d h H.verts subset_rfl rfl ⟨v, hv⟩ hlt
  have hTv : (H.induce T).verts = T := FGraph.induce_verts_of_subset hTS
  obtain ⟨c, hnd, hlen, hedges⟩ := exists_long_cycle_of_deg (H.induce T) d hd2 (by rw [hTv]; exact hTne)
    (fun w hw => hT w (by rw [hTv] at hw; exact hw))
  refine ⟨c, hnd, by omega, fun e he => (FGraph.induce_le (H := H) T).2 (hedges e he), ?_⟩
  have h3 : m < m / h * h + h := Nat.lt_div_mul_add (by omega)
  have h4 : m / h + 1 ≤ c.length := by
    have : m / h ≤ d := le_max_right _ _
    omega
  calc m < m / h * h + h := h3
    _ = h * (m / h + 1) := by ring
    _ ≤ h * c.length := Nat.mul_le_mul_left h h4

/-! ### Removal of long cycles -/

/-- The Claim for an edge set `E` without loops, with all ends in `W`: if `1 ≤ |W| ≤ |E|`, then
`E` contains the edges of a cycle of length `ℓ` with `|E| < |W| ℓ`. -/
theorem exists_cycle_of_edges [DecidableEq V] {W : Finset V} {E : Finset (Sym2 V)}
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hEW : ∀ e ∈ E, ∀ v ∈ e, v ∈ W) (h1 : 1 ≤ W.card)
    (hm : W.card ≤ E.card) :
    ∃ c : List V, c.Nodup ∧ 3 ≤ c.length ∧ (∀ e ∈ cycleEdges c, e ∈ E) ∧
      E.card < W.card * c.length := by
  have hed := FGraph.ofEdges_edges_of_subset hE hEW
  have hc : (FGraph.ofEdges W E).card = W.card := rfl
  have := exists_cycle_of_card_le (FGraph.ofEdges W E) (by rw [hc]; exact h1)
    (by rw [hc, hed]; exact hm)
  rw [hed, hc] at this
  exact this

/-- `(1 - 1/h)^h ≤ 1/2` for `h ≥ 1` (via `(1 - 1/h)^h ≤ e⁻¹` and `e ≥ 2`). -/
theorem one_sub_inv_pow_le_half {h : ℕ} (hh : 1 ≤ h) : (1 - 1 / (h : ℝ)) ^ h ≤ 1 / 2 := by
  have h1 : (1 - 1 / (h : ℝ)) ^ h ≤ Real.exp (-1) :=
    Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hh)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- [s1:factEG0] (a), "Removal of long cycles", `j` steps: from an edge set `E` (no loops, ends in
`W`, `|W| = h ≥ 1`) at most `j` cycles can be removed, leaving `E' ⊆ E` with `|E'| < h` (the
removal stopped) or `|E'| ≤ (1 - 1/h)^j |E|` (each step: `m_{i+1} ≤ (1 - 1/h) m_i`). -/
theorem block [DecidableEq V] (W : Finset V) (hW : 1 ≤ W.card) :
    ∀ j : ℕ, ∀ E : Finset (Sym2 V), (∀ e ∈ E, ¬ e.IsDiag) → (∀ e ∈ E, ∀ v ∈ e, v ∈ W) →
      ∃ E' ⊆ E, ∃ C : List (Obj V), IsDecomp ((E \ E' : Finset (Sym2 V)) : Set (Sym2 V)) C ∧
        C.countP Obj.isEdge = 0 ∧ C.length ≤ j ∧
        (E'.card < W.card ∨ (E'.card : ℝ) ≤ (1 - 1 / (W.card : ℝ)) ^ j * E.card) := by
  intro j
  induction j with
  | zero =>
    intro E _ _
    refine ⟨E, subset_rfl, [], ?_, rfl, le_rfl, Or.inr (by simp)⟩
    rw [Finset.sdiff_self, Finset.coe_empty]
    exact isDecomp_nil
  | succ j ih =>
    intro E hE hEW
    obtain ⟨E', hE'E, C, hC, hC0, hClen, hbd⟩ := ih E hE hEW
    by_cases hsmall : E'.card < W.card
    · exact ⟨E', hE'E, C, hC, hC0, by omega, Or.inl hsmall⟩
    push Not at hsmall
    have hbd' : (E'.card : ℝ) ≤ (1 - 1 / (W.card : ℝ)) ^ j * E.card :=
      hbd.resolve_left (by omega)
    obtain ⟨c, hnd, h3, hcE, hlt⟩ := exists_cycle_of_edges (fun e he => hE e (hE'E he))
      (fun e he => hEW e (hE'E he)) hW hsmall
    set K := (cycleEdges c).toFinset with hK
    have hKE : K ⊆ E' := fun e he => hcE e (List.mem_toFinset.1 he)
    have hKcard : K.card = c.length := by
      rw [hK, List.toFinset_card_of_nodup (nodup_cycleEdges hnd h3), length_cycleEdges]
    refine ⟨E' \ K, Finset.sdiff_subset.trans hE'E, C ++ [Obj.cycle c], ?_, ?_, ?_, Or.inr ?_⟩
    · have h2 : IsDecomp ((K : Finset (Sym2 V)) : Set (Sym2 V)) [Obj.cycle c] :=
        (isDecomp_cycle hnd h3).congr (by ext; simp [hK])
      refine (hC.append h2 ?_).congr ?_
      · rw [Finset.disjoint_coe]
        exact Finset.disjoint_of_subset_right hKE Finset.sdiff_disjoint
      · ext e
        simp only [Set.mem_union, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
        have := @hKE e
        have := @hE'E e
        tauto
    · simp [List.countP_append, hC0]
    · simp only [List.length_append, List.length_singleton]
      omega
    · have hh : (1 : ℝ) ≤ W.card := by exact_mod_cast hW
      have hr0 : 0 ≤ 1 - 1 / (W.card : ℝ) := by
        rw [sub_nonneg, div_le_one (by linarith)]
        exact hh
      have hsum : ((E' \ K).card : ℝ) + c.length = E'.card := by
        have := Finset.card_sdiff_add_card_eq_card hKE
        rw [hKcard] at this
        exact_mod_cast this
      have hlt' : (E'.card : ℝ) ≤ W.card * c.length := by exact_mod_cast hlt.le
      have hdiv : (E'.card : ℝ) / W.card ≤ c.length := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      calc ((E' \ K).card : ℝ) ≤ (1 - 1 / (W.card : ℝ)) * E'.card := by
            have : (1 - 1 / (W.card : ℝ)) * E'.card = E'.card - E'.card / W.card := by ring
            rw [this]
            linarith
        _ ≤ (1 - 1 / (W.card : ℝ)) * ((1 - 1 / (W.card : ℝ)) ^ j * E.card) :=
            mul_le_mul_of_nonneg_left hbd' hr0
        _ = (1 - 1 / (W.card : ℝ)) ^ (j + 1) * E.card := by ring

/-- [s1:factEG0] (a), "Removal of long cycles", counted: an edge set `E` (no loops, ends in `W`,
`|W| = h ≥ 1`) with `|E| < 2^q h` has a decomposition into at most `q h` cycles and at most
`h - 1` single edges (`h` removals halve the number of edges, as `(1 - 1/h)^h ≤ 1/2`). -/
theorem decomp_of_card_lt [DecidableEq V] (W : Finset V) (hW : 1 ≤ W.card) :
    ∀ q : ℕ, ∀ E : Finset (Sym2 V), (∀ e ∈ E, ¬ e.IsDiag) → (∀ e ∈ E, ∀ v ∈ e, v ∈ W) →
      E.card < 2 ^ q * W.card →
      ∃ D : List (Obj V), IsDecomp (E : Set (Sym2 V)) D ∧ D.countP Obj.isEdge ≤ W.card - 1 ∧
        D.length ≤ q * W.card + (W.card - 1) := by
  intro q
  induction q with
  | zero =>
    intro E hE _ hlt
    simp only [pow_zero, one_mul] at hlt
    refine ⟨E.toList.map Obj.edge, isDecomp_singletons E hE, ?_, ?_⟩
    · rw [countP_isEdge_singletons]
      omega
    · rw [length_singletons]
      omega
  | succ q ih =>
    intro E hE hEW hlt
    obtain ⟨E', hE'E, C, hC, hC0, hClen, hbd⟩ := block W hW W.card E hE hEW
    have hE'lt : E'.card < 2 ^ q * W.card := by
      rcases hbd with h | h
      · have : 1 ≤ 2 ^ q := Nat.one_le_two_pow
        nlinarith
      · have hhalf := one_sub_inv_pow_le_half hW
        have hE0 : (0 : ℝ) ≤ E.card := by positivity
        have hltR : (E.card : ℝ) < 2 ^ (q + 1) * W.card := by exact_mod_cast hlt
        have : (E'.card : ℝ) < 2 ^ q * W.card := by
          calc (E'.card : ℝ) ≤ (1 - 1 / (W.card : ℝ)) ^ W.card * E.card := h
            _ ≤ 1 / 2 * E.card := mul_le_mul_of_nonneg_right hhalf hE0
            _ < 2 ^ q * W.card := by rw [pow_succ] at hltR; linarith
        exact_mod_cast this
    obtain ⟨D', hD', hD'0, hD'len⟩ := ih E' (fun e he => hE e (hE'E he))
      (fun e he => hEW e (hE'E he)) hE'lt
    refine ⟨C ++ D', (hC.append hD' ?_).congr ?_, ?_, ?_⟩
    · rw [Finset.disjoint_coe]
      exact Finset.sdiff_disjoint
    · ext e
      simp only [Set.mem_union, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      have := @hE'E e
      tauto
    · rw [List.countP_append, hC0]
      omega
    · rw [List.length_append]
      have : (q + 1) * W.card = q * W.card + W.card := by ring
      omega

/-- [s1:factEG0] (a) for an edge set: an edge set `E` without loops, all of whose edges have both
ends in `W`, `h = |W| ≥ 1`, has a decomposition into at most `h(log h + 1)` objects, at most
`h − 1` of which are single edges. (With `q = ⌊log h⌋`: `|E| < |W^{(2)}| = (h+1)h/2 ≤ 2^q h`.) -/
theorem exists_decomp_log [DecidableEq V] {W : Finset V} (hW : 1 ≤ W.card)
    {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag) (hEW : ∀ e ∈ E, ∀ v ∈ e, v ∈ W) :
    ∃ D : List (Obj V), IsDecomp (E : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ (W.card : ℝ) * (Real.logb 2 (W.card : ℝ) + 1) ∧
      D.countP Obj.isEdge ≤ W.card - 1 := by
  have hsub : E ⊂ W.sym2 := by
    obtain ⟨v, hv⟩ : W.Nonempty := Finset.card_pos.1 (by omega)
    refine (Finset.ssubset_iff_of_subset (fun e he => Finset.mem_sym2_iff.2 (hEW e he))).2
      ⟨s(v, v), Finset.mk_mem_sym2_iff.2 ⟨hv, hv⟩, fun he => hE _ he (Sym2.mk_isDiag_iff.2 rfl)⟩
  have hlt1 : E.card < (W.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    exact Finset.card_lt_card hsub
  have hpow : W.card + 1 ≤ 2 * 2 ^ Nat.log 2 W.card := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) W.card
    rw [Nat.pow_succ] at this
    omega
  have hchoose : (W.card + 1).choose 2 ≤ 2 ^ Nat.log 2 W.card * W.card := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    apply Nat.div_le_of_le_mul
    nlinarith
  obtain ⟨D, hD, hD0, hDlen⟩ := decomp_of_card_lt W hW (Nat.log 2 W.card) E hE hEW (by omega)
  refine ⟨D, hD, ?_, hD0⟩
  have hqlog : ((Nat.log 2 W.card : ℕ) : ℝ) ≤ Real.logb 2 W.card := by
    have := Real.natLog_le_logb W.card 2
    simpa using this
  have hh : (1 : ℝ) ≤ W.card := by exact_mod_cast hW
  have hlen : (D.length : ℝ) ≤ (Nat.log 2 W.card : ℕ) * (W.card : ℝ) + W.card := by
    have : D.length ≤ Nat.log 2 W.card * W.card + W.card := by omega
    exact_mod_cast this
  nlinarith


end EG0

universe u

/-- [s1:factEG0] (a) "Every graph `H` with `h ≥ 1` vertices has a decomposition into at most
`h(log h + 1)` objects, at most `h − 1` of which are single edges." -/
theorem factEG0a : EG.Spec.FactEG0aStatement.{u} := by
  intro V _ H hH
  obtain ⟨D, hD, hlen, hcnt⟩ := EG0.exists_decomp_log (W := H.verts) hH H.loopless H.edge_verts
  refine ⟨D, hD, hlen, le_trans (le_of_eq ?_) hcnt⟩
  exact List.countP_congr (q := Obj.isEdge) fun o _ => by cases o <;> exact Iff.rfl

/-- [s1:factEG0] (a) "In particular `f(H) ≤ h(log h + 1)`." -/
theorem factEG0aFnum : EG.Spec.FactEG0aFnumStatement.{u} := by
  intro V _ H hH
  obtain ⟨D, hD, hlen, -⟩ := factEG0a V H hH
  exact le_trans (by exact_mod_cast fnum_le_of_isDecomp hD) hlen

/-- [s1:factEG0] (b) "Let `N > 1` and `L := log N`, and let `α` and `β` be real numbers with
`0 ≤ α ≤ N`, `β > 0` and `4β ≤ L`. If `F` is the edge set of a (simple) graph … and every edge of
`F` has both ends in a set `W` with `|W| ≤ βα/L`, then `F` has a decomposition into at most `βα`
objects, at most `|W|` of which are single edges." -/
theorem factEG0b : EG.Spec.FactEG0bStatement.{u} := by
  intro V _ N α β F W hN hα0 hαN hβ h4β hF hFW hWcard
  have hLpos : 0 < Real.logb 2 N := Real.logb_pos (by norm_num) hN
  rcases Nat.eq_zero_or_pos W.card with hW0 | hW1
  · have hWe : W = ∅ := Finset.card_eq_zero.1 hW0
    have hFe : F = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have := hFW _ he a (Sym2.mem_mk_left a b)
        simp [hWe] at this
    refine ⟨[], by rw [hFe, Finset.coe_empty]; exact isDecomp_nil, ?_, by simp⟩
    simp only [List.length_nil, Nat.cast_zero]
    positivity
  · obtain ⟨D, hD, hlen, hcnt⟩ := EG0.exists_decomp_log hW1 hF hFW
    refine ⟨D, hD, ?_, le_trans (le_of_eq ?_) (hcnt.trans (Nat.sub_le _ _))⟩
    swap
    · exact List.countP_congr (q := Obj.isEdge) fun o _ => by cases o <;> exact Iff.rfl
    have hh1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW1
    have hhL : (W.card : ℝ) * Real.logb 2 N ≤ β * α := by rwa [le_div_iff₀ hLpos] at hWcard
    have hN0 : 0 < N := by linarith
    have hhN : (W.card : ℝ) ≤ N / 4 := by
      have h1 : β * α ≤ β * N := mul_le_mul_of_nonneg_left hαN hβ.le
      have h2 : 4 * β * N ≤ Real.logb 2 N * N := mul_le_mul_of_nonneg_right h4β hN0.le
      refine le_of_mul_le_mul_right (a := Real.logb 2 N) ?_ hLpos
      nlinarith
    have hlog : Real.logb 2 (W.card : ℝ) ≤ Real.logb 2 N - 2 := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) hhN
      rw [Real.logb_div (by linarith) (by norm_num)] at this
      have h4 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        norm_num
      linarith
    have := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ W.card)
    nlinarith

end EG
