module

public import EG.Lib.Ext.LovaszCons

/-!
# Lovász's path-and-cycle theorem (manuscript s1:citThm21)

`EG.LovaszC.lovasz : EG.Spec.LovaszStatement`: every graph with `n` vertices decomposes into at most
`n/2` paths and cycles (L. Lovász, *On covering of graphs*, 1968). Proof as in L. Yan, *On path
decompositions of graphs* (PhD thesis, Arizona State University, 1998), §2.1 and the proof of
Lovász's theorem cited there, by strong induction on the number of edges
(`formal/work/p3/lovasz.md`):

* Case 0 (`case0`): some vertex `a` has even positive degree. Let `x` be a neighbour of `a` and `Z` the
  set of neighbours of `x` of even degree. In `F = E(H) \ xZ` every neighbour of `x` has odd degree,
  hence ends a path of any decomposition of `F` (parity); the induction hypothesis for `F` and the
  Lovász construction (`lovasz_construction`) give the decomposition of `H`.
* Case 1 (`case1`): every vertex has odd degree or degree `0`. A matching is decomposed into its
  edges; otherwise we move one end of an edge `xy` (`deg x ≥ 3`) to a new pendant vertex
  `none` on `Option V`, apply Case 0 there, delete the leaf `none` and add `xy` back.
-/

public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EG

namespace LovaszC

universe u

/-- The conclusion of Lovász's theorem for `H`. -/
def Concl {V : Type u} [DecidableEq V] (H : FGraph V) : Prop :=
  ∃ P C : List (List V), IsPathCycleDecomp (H.edges : Set (Sym2 V)) P C ∧
    2 * (P.length + C.length) ≤ H.card

/-- The induction hypothesis: the conclusion for all graphs with fewer than `m` edges. -/
def IH (m : ℕ) : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V), H.edges.card < m → Concl H

section Helpers

variable {V : Type*} [DecidableEq V]

/-- Parity: a vertex of odd degree ends a path of every path-and-cycle decomposition. -/
theorem exists_end_of_odd {E : Finset (Sym2 V)} {P C : List (List V)}
    (hD : IsPathCycleDecomp (E : Set (Sym2 V)) P C) {v : V} (hv : Odd (degE E v)) :
    ∃ p ∈ P, p.head? = some v ∨ p.getLast? = some v := by
  have h1 := Cor22.even_degE_add_pathEndCount hD v
  have hpos : 0 < pathEndCount P v := by
    rcases Nat.even_or_odd (pathEndCount P v) with he | ho
    · exact absurd (Nat.even_add.1 h1 |>.2 he) (Nat.not_even_iff_odd.2 hv)
    · exact ho.pos
  unfold pathEndCount at hpos
  obtain ⟨p, hp, hpv⟩ := List.countP_pos_iff.1 hpos
  exact ⟨p, hp, by simpa using hpv⟩

/-- Degrees after deleting the edges `s(x, z)`, `z ∈ Z`. -/
theorem degE_sdiff_star (E : Finset (Sym2 V)) (x : V) (Z : Finset V) {v : V} (hvx : v ≠ x) :
    degE E v = degE (E \ Z.image (fun z => s(x, z))) v +
      (if v ∈ Z ∧ s(x, v) ∈ E then 1 else 0) := by
  set R := Z.image (fun z => s(x, z)) with hR
  have hsplit : edgesAt E v = edgesAt (E \ R) v ∪ edgesAt (E ∩ R) v := by
    unfold edgesAt
    rw [← Finset.filter_union, Finset.sdiff_union_inter]
  have hdisj : Disjoint (edgesAt (E \ R) v) (edgesAt (E ∩ R) v) := by
    unfold edgesAt
    exact Finset.disjoint_filter_filter (Finset.disjoint_sdiff_inter E R)
  have hinter : edgesAt (E ∩ R) v = if v ∈ Z ∧ s(x, v) ∈ E then {s(x, v)} else ∅ := by
    ext e
    simp only [FGraph.mem_edgesAt, Finset.mem_inter, hR, Finset.mem_image]
    split_ifs with hv
    · rw [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, z, hz, rfl⟩, hve⟩
        rcases Sym2.mem_iff.1 hve with h1 | h1
        · exact absurd h1 hvx
        · rw [h1]
      · rintro rfl
        exact ⟨⟨hv.2, v, hv.1, rfl⟩, Sym2.mem_mk_right _ _⟩
    · simp only [Finset.notMem_empty, iff_false]
      intro hcon
      obtain ⟨⟨heE, z, hz, hze⟩, hve⟩ := hcon
      subst hze
      rcases Sym2.mem_iff.1 hve with h1 | h1
      · exact hvx h1
      · subst h1; exact hv ⟨hz, heE⟩
  unfold degE
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hinter]
  split_ifs <;> simp

end Helpers

/-! ### Deleting a pendant vertex `none` -/

section Leaf

variable {V : Type*} [DecidableEq V]

/-- Forget the `some`s (and drop `none`s). -/
def unmap (l : List (Option V)) : List V := l.filterMap id

theorem unmap_map_some : ∀ {l : List (Option V)}, none ∉ l → (unmap l).map some = l
  | [], _ => rfl
  | none :: l, h => absurd (List.mem_cons_self ..) h
  | some a :: l, h => by
    have ih := unmap_map_some (l := l) (fun h' => h (List.mem_cons_of_mem _ h'))
    show some a :: (unmap l).map some = some a :: l
    rw [ih]

/-- The list `l` if it has an edge, nothing otherwise. -/
def piece (l : List V) : List (List V) := if 2 ≤ l.length then [l] else []

theorem flatMap_piece (l : List V) : (piece l).flatMap walkEdges = walkEdges l := by
  unfold piece
  split_ifs with h
  · simp
  · rw [Cor22.walkEdges_eq_nil_of_length_lt (by omega)]; rfl

theorem unmap_length {l : List (Option V)} (h : none ∉ l) : (unmap l).length = l.length := by
  rw [← unmap_map_some h, List.length_map, unmap_map_some h]

theorem unmap_nodup {l : List (Option V)} (h : none ∉ l) (hl : l.Nodup) : (unmap l).Nodup := by
  rw [← unmap_map_some h] at hl
  exact List.Nodup.of_map _ hl

theorem walkEdges_unmap {l : List (Option V)} (h : none ∉ l) :
    (walkEdges (unmap l)).map (Sym2.map some) = walkEdges l := by
  rw [← Cor22.walkEdges_map, unmap_map_some h]

theorem cycleEdges_unmap {l : List (Option V)} (h : none ∉ l) :
    (cycleEdges (unmap l)).map (Sym2.map some) = cycleEdges l := by
  rw [← cycleEdges_map, unmap_map_some h]

theorem none_notMem_map_some (e : Sym2 V) : none ∉ Sym2.map some e := by
  intro h
  obtain ⟨a, -, ha⟩ := Sym2.mem_map.1 h
  simp at ha

/-- **Deleting the pendant vertex `none`.** Let `(P', C')` decompose `E ⊔ {s(none, some y)}` (on
`Option V`). Then `E` has a decomposition on `V` with at most as many members, which either has one
member fewer or has a path ending at `y`. -/
theorem drop_leaf {E : Finset (Sym2 V)} {y : V} {P' C' : List (List (Option V))}
    (hD : IsPathCycleDecomp
      ((E.image (Sym2.map some) ∪ {s(none, some y)} : Finset (Sym2 (Option V))) :
        Set (Sym2 (Option V))) P' C') :
    ∃ Q C'' : List (List V), IsPathCycleDecomp (E : Set (Sym2 V)) Q C'' ∧
      ((Q.length + C''.length ≤ P'.length + C'.length ∧
          ∃ q ∈ Q, q.head? = some y ∨ q.getLast? = some y) ∨
        Q.length + C''.length + 1 ≤ P'.length + C'.length) := by
  obtain ⟨hP, hC, hnd, hmem⟩ := hD
  set e₀ : Sym2 (Option V) := s(none, some y) with he₀
  -- the only edge at `none` is `e₀`
  have hat : ∀ e, e ∈ P'.flatMap walkEdges ++ C'.flatMap cycleEdges → none ∈ e → e = e₀ := by
    intro e he hne
    have := (hmem e).1 he
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_singleton, Set.mem_union,
      Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff] at this
    rcases this with ⟨e', -, rfl⟩ | h'
    · exact absurd hne (none_notMem_map_some e')
    · exact h'
  have he₀mem : e₀ ∈ P'.flatMap walkEdges ++ C'.flatMap cycleEdges :=
    (hmem e₀).2 (by simp [he₀])
  -- no cycle contains `none`
  have hCnone : ∀ c ∈ C', none ∉ c := by
    intro c hc hn
    obtain ⟨hcn, h3⟩ := hC c hc
    have h2 := Cor22.countP_mem_cycleEdges none hcn h3
    rw [if_pos hn] at h2
    have hsub : (cycleEdges c).countP (fun e => none ∈ e) ≤ (cycleEdges c).count e₀ := by
      rw [List.count_eq_countP]
      apply List.countP_mono_left
      intro e he hne
      have := hat e (List.mem_append_right _ (List.mem_flatMap.2 ⟨c, hc, he⟩)) (by simpa using hne)
      simp [this]
    have hc1 : (cycleEdges c).count e₀ ≤ 1 :=
      List.nodup_iff_count_le_one.1 (nodup_cycleEdges hcn h3) e₀
    omega
  -- the path containing `e₀`
  have he₀P : e₀ ∈ P'.flatMap walkEdges := by
    rcases List.mem_append.1 he₀mem with h' | h'
    · exact h'
    · obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 h'
      exact absurd (mem_of_mem_cycleEdges hec (Sym2.mem_mk_left _ _)) (hCnone c hc)
  obtain ⟨p₀, hp₀, hep₀⟩ := List.mem_flatMap.1 he₀P
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hp₀
  have hndP := (List.nodup_append.1 hnd).1
  -- the other paths avoid `none`
  have hLnone : ∀ p ∈ L₁ ++ L₂, none ∉ p := by
    intro p hp hn
    have hpP : 2 ≤ p.length ∧ p.Nodup :=
      hP p (by rw [hsplit]; rcases List.mem_append.1 hp with h' | h' <;> simp [h'])
    obtain ⟨e, he, hne⟩ := exists_mem_walkEdges_of_mem hpP.1 hn
    have heq := hat e (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, by
      rw [hsplit]; rcases List.mem_append.1 hp with h' | h' <;> simp [h'], he⟩)) hne
    subst heq
    rw [hsplit, List.flatMap_append, List.flatMap_cons] at hndP
    rcases List.mem_append.1 hp with h' | h'
    · have := List.nodup_append.1 hndP
      exact this.2.2 e₀ (List.mem_flatMap.2 ⟨p, h', he⟩) e₀
        (List.mem_append_left _ hep₀) rfl
    · have := (List.nodup_append.1 (List.nodup_append.1 hndP).2.1)
      exact this.2.2 e₀ hep₀ e₀ (List.mem_flatMap.2 ⟨p, h', he⟩) rfl
  -- `none` is an end of `p₀`: orient `p₀` to start with `none`
  obtain ⟨h2p₀, hndp₀⟩ := hP p₀ hp₀
  have hnp₀ : none ∈ p₀ := mem_of_mem_walkEdges hep₀ (Sym2.mem_mk_left _ _)
  obtain ⟨q, hq⟩ : ∃ q : List (Option V), p₀ = none :: q ∨ p₀.reverse = none :: q := by
    have h2 := Cor22.countP_mem_walkEdges_add none hndp₀ (by rintro rfl; simp at h2p₀)
    rw [if_pos hnp₀] at h2
    have hcnt : (walkEdges p₀).countP (fun e => none ∈ e) ≤ 1 := by
      calc (walkEdges p₀).countP (fun e => none ∈ e) ≤ (walkEdges p₀).count e₀ := by
            rw [List.count_eq_countP]
            apply List.countP_mono_left
            intro e he hne
            have := hat e (List.mem_append_left _ (List.mem_flatMap.2 ⟨p₀, hp₀, he⟩))
              (by simpa using hne)
            simp [this]
        _ ≤ 1 := List.nodup_iff_count_le_one.1 (nodup_walkEdges hndp₀) e₀
    by_cases hh : p₀.head? = some none
    · obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (by rintro rfl; simp at h2p₀ : p₀ ≠ [])
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨t, Or.inl (by rw [hh])⟩
    · have hl : p₀.getLast? = some none := by
        by_contra hl
        rw [if_neg hh, if_neg hl] at h2
        omega
      obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil
        (by rw [Ne, List.reverse_eq_nil_iff]; rintro rfl; simp at h2p₀ : p₀.reverse ≠ [])
      have : a = none := by
        have h' : p₀.reverse.head? = some a := by rw [ht]; rfl
        rw [List.head?_reverse, hl, Option.some.injEq] at h'
        exact h'.symm
      subst this
      exact ⟨t, Or.inr ht⟩
  -- properties of `q`
  have hq' : (walkEdges p₀).Perm (e₀ :: walkEdges q) ∧ none ∉ q ∧ q.Nodup ∧ q.length + 1 = p₀.length := by
    rcases hq with hq | hq
    · subst hq
      have hqne : q ≠ [] := by rintro rfl; simp at h2p₀
      obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hqne
      have hb : s(none, b) = e₀ := hat _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨_, hp₀, by simp⟩)) (Sym2.mem_mk_left _ _)
      refine ⟨by rw [walkEdges_cons_cons, hb], (List.nodup_cons.1 hndp₀).1,
        (List.nodup_cons.1 hndp₀).2, by simp⟩
    · have hndr : p₀.reverse.Nodup := List.nodup_reverse.2 hndp₀
      rw [hq] at hndr
      have hqne : q ≠ [] := by
        rintro rfl
        have := congrArg List.length hq
        simp at this; omega
      obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hqne
      have hbe : s(none, b) ∈ walkEdges p₀ := by
        rw [← mem_walkEdges_reverse, hq]; simp
      have hb : s(none, b) = e₀ := hat _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨_, hp₀, hbe⟩)) (Sym2.mem_mk_left _ _)
      refine ⟨?_, (List.nodup_cons.1 hndr).1, (List.nodup_cons.1 hndr).2, ?_⟩
      · have h1 : (walkEdges p₀).Perm (walkEdges p₀.reverse) := by
          rw [walkEdges_reverse]; exact (List.reverse_perm _).symm
        rw [hq, walkEdges_cons_cons, hb] at h1
        exact h1
      · have := congrArg List.length hq
        simp only [List.length_reverse, List.length_cons] at this ⊢
        omega
  obtain ⟨hperm₀, hnq, hndq, hlenq⟩ := hq'
  -- the new decomposition
  refine ⟨L₁.map unmap ++ piece (unmap q) ++ L₂.map unmap, C'.map unmap, ?_, ?_⟩
  · -- the edges, mapped to `Option V`
    have hmapped : ((L₁.map unmap ++ piece (unmap q) ++ L₂.map unmap).flatMap walkEdges ++
        (C'.map unmap).flatMap cycleEdges).map (Sym2.map some) =
        L₁.flatMap walkEdges ++ walkEdges q ++ L₂.flatMap walkEdges ++ C'.flatMap cycleEdges := by
      simp only [List.flatMap_append, List.map_append]
      rw [flatMap_piece, walkEdges_unmap hnq]
      simp only [List.map_flatMap, List.flatMap_map]
      have h1 : L₁.flatMap (fun a => (walkEdges (unmap a)).map (Sym2.map some)) =
          L₁.flatMap walkEdges := by
        apply List.flatMap_congr
        intro p hp
        exact walkEdges_unmap (hLnone p (List.mem_append_left _ hp))
      have h2 : L₂.flatMap (fun a => (walkEdges (unmap a)).map (Sym2.map some)) =
          L₂.flatMap walkEdges := by
        apply List.flatMap_congr
        intro p hp
        exact walkEdges_unmap (hLnone p (List.mem_append_right _ hp))
      have h3 : C'.flatMap (fun a => (cycleEdges (unmap a)).map (Sym2.map some)) =
          C'.flatMap cycleEdges := by
        apply List.flatMap_congr
        intro c hc
        exact cycleEdges_unmap (hCnone c hc)
      rw [h1, h2, h3]
    have hperm : (P'.flatMap walkEdges ++ C'.flatMap cycleEdges).Perm
        (e₀ :: (L₁.flatMap walkEdges ++ walkEdges q ++ L₂.flatMap walkEdges ++
          C'.flatMap cycleEdges)) := by
      rw [hsplit, List.flatMap_append, List.flatMap_cons]
      simp only [List.append_assoc]
      refine (List.Perm.append_left _ (hperm₀.append_right _)).trans ?_
      simp only [List.cons_append]
      exact List.perm_middle
    have hnd' : ((L₁.flatMap walkEdges ++ walkEdges q ++ L₂.flatMap walkEdges ++
        C'.flatMap cycleEdges)).Nodup := (List.nodup_cons.1 (hperm.nodup_iff.1 hnd)).2
    have hmem' : ∀ e, e ∈ L₁.flatMap walkEdges ++ walkEdges q ++ L₂.flatMap walkEdges ++
        C'.flatMap cycleEdges ↔ e ≠ e₀ ∧ e ∈ P'.flatMap walkEdges ++ C'.flatMap cycleEdges := by
      intro e
      rw [hperm.mem_iff, List.mem_cons]
      have hnot : e₀ ∉ L₁.flatMap walkEdges ++ walkEdges q ++ L₂.flatMap walkEdges ++
          C'.flatMap cycleEdges := (List.nodup_cons.1 (hperm.nodup_iff.1 hnd)).1
      constructor
      · intro h'
        exact ⟨fun h'' => hnot (h'' ▸ h'), Or.inr h'⟩
      · rintro ⟨hne, h' | h'⟩
        · exact absurd h' hne
        · exact h'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
          have hn := hLnone p' (List.mem_append_left _ hp')
          have hv := hP p' (by rw [hsplit]; simp [hp'])
          exact ⟨by rw [unmap_length hn]; exact hv.1, unmap_nodup hn hv.2⟩
        · unfold piece at hp
          split_ifs at hp with hl
          · rw [List.mem_singleton] at hp; subst hp; exact ⟨hl, unmap_nodup hnq hndq⟩
          · simp at hp
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        have hn := hLnone p' (List.mem_append_right _ hp')
        have hv := hP p' (by rw [hsplit]; simp [hp'])
        exact ⟨by rw [unmap_length hn]; exact hv.1, unmap_nodup hn hv.2⟩
    · intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      have hn := hCnone c' hc'
      obtain ⟨hv1, hv2⟩ := hC c' hc'
      exact ⟨unmap_nodup hn hv1, by rw [unmap_length hn]; exact hv2⟩
    · rw [← hmapped] at hnd'
      exact List.Nodup.of_map _ hnd'
    · intro e
      rw [← List.mem_map_of_injective Cor22.sym2Map_some_injective, hmapped, hmem', hmem]
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_singleton, Set.mem_union,
        Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, ⟨e', he', heq⟩ | h'⟩
        · rwa [← Cor22.sym2Map_some_injective heq]
        · exact absurd h' (fun h'' => none_notMem_map_some e (h'' ▸ Sym2.mem_mk_left _ _))
      · intro he
        exact ⟨fun h'' => none_notMem_map_some e (h'' ▸ Sym2.mem_mk_left _ _),
          Or.inl ⟨e, he, rfl⟩⟩
  · -- the count
    have hlenP : P'.length = L₁.length + L₂.length + 1 := by
      rw [hsplit]; simp; omega
    by_cases hql : 2 ≤ (unmap q).length
    · left
      have hpc : piece (unmap q) = [unmap q] := by simp [piece, hql]
      refine ⟨by simp [hpc, hlenP]; omega, unmap q, by simp [hpc], ?_⟩
      left
      -- `q` starts with `some y`
      rcases hq with hq | hq
      · subst hq
        obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil
          (by rintro rfl; simp at h2p₀ : q ≠ [])
        have hb : s(none, b) = e₀ := hat _ (List.mem_append_left _ (List.mem_flatMap.2
          ⟨_, hp₀, by simp⟩)) (Sym2.mem_mk_left _ _)
        have hb' : b = some y := by
          rw [he₀] at hb
          rcases Sym2.eq_iff.1 hb with ⟨-, h'⟩ | ⟨h', -⟩
          · exact h'
          · exact absurd h' (by simp)
        subst hb'
        simp [unmap]
      · have hqne : q ≠ [] := by
          rintro rfl
          have := congrArg List.length hq
          simp at this; omega
        obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hqne
        have hbe : s(none, b) ∈ walkEdges p₀ := by
          rw [← mem_walkEdges_reverse, hq]; simp
        have hb : s(none, b) = e₀ := hat _ (List.mem_append_left _ (List.mem_flatMap.2
          ⟨_, hp₀, hbe⟩)) (Sym2.mem_mk_left _ _)
        have hb' : b = some y := by
          rw [he₀] at hb
          rcases Sym2.eq_iff.1 hb with ⟨-, h'⟩ | ⟨h', -⟩
          · exact h'
          · exact absurd h' (by simp)
        subst hb'
        simp [unmap]
    · right
      have hpc : piece (unmap q) = [] := by simp [piece, hql]
      simp [hpc, hlenP]

end Leaf

/-- **Case 0.** If some vertex has even positive degree, the conclusion follows from the induction
hypothesis for graphs with fewer edges. -/
theorem case0 {m : ℕ} (ih : IH.{u} m) {V : Type u} [DecidableEq V] (H : FGraph V)
    (hm : H.edges.card = m) {a : V} (ha : Even (degE H.edges a)) (ha0 : degE H.edges a ≠ 0) :
    Concl H := by
  -- a neighbour `x` of `a`
  obtain ⟨e, he⟩ : (edgesAt H.edges a).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero ha0)
  rw [FGraph.mem_edgesAt] at he
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 he.2
  have hax : s(x, a) ∈ H.edges := by rw [Sym2.eq_swap]; exact he.1
  set Z := (H.nbrs x).filter (fun z => Even (degE H.edges z)) with hZ
  set R := Z.image (fun z => s(x, z)) with hR
  set F := H.edges \ R with hF
  have hmemZ : ∀ {z}, z ∈ Z ↔ s(x, z) ∈ H.edges ∧ Even (degE H.edges z) := by
    intro z
    rw [hZ, Finset.mem_filter, FGraph.mem_nbrs, FGraph.adj_iff]
  have haZ : a ∈ Z := hmemZ.2 ⟨hax, ha⟩
  have hxZ : x ∉ Z := fun hx => H.loopless _ (hmemZ.1 hx).1 (Sym2.mk_isDiag_iff.2 rfl)
  have hRE : R ⊆ H.edges := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 he
    exact (hmemZ.1 hz).1
  have hlt : F.card < m := by
    rw [← hm]
    apply Finset.card_lt_card
    refine ⟨Finset.sdiff_subset, fun h' => ?_⟩
    have : s(x, a) ∈ F := h' hax
    exact (Finset.mem_sdiff.1 this).2 (Finset.mem_image_of_mem _ haZ)
  obtain ⟨P, C, hD, hc⟩ := ih V (H.deleteEdges R) (by simpa [hF] using hlt)
  rw [FGraph.deleteEdges_edges] at hD
  rw [FGraph.deleteEdges_card] at hc
  have hZF : ∀ z ∈ Z, s(x, z) ∉ F := fun z hz hzF =>
    (Finset.mem_sdiff.1 hzF).2 (Finset.mem_image_of_mem _ hz)
  have hends : ∀ v, (v ∈ Z ∨ s(x, v) ∈ F) → ∃ p ∈ P, p.head? = some v ∨ p.getLast? = some v := by
    intro v hv
    apply exists_end_of_odd hD
    have hvx : v ≠ x := by
      rintro rfl
      rcases hv with hv | hv
      · exact hxZ hv
      · exact H.loopless _ (Finset.mem_sdiff.1 hv).1 (Sym2.mk_isDiag_iff.2 rfl)
    have hdeg := degE_sdiff_star H.edges x Z hvx
    rw [← hR, ← hF] at hdeg
    rcases hv with hv | hv
    · have h1 := hmemZ.1 hv
      rw [if_pos ⟨hv, h1.1⟩] at hdeg
      rw [hdeg] at h1
      rcases Nat.even_or_odd (degE F v) with h2 | h2
      · exact absurd h1.2 (by rw [Nat.even_add_one]; exact not_not_intro h2)
      · exact h2
    · have hvE : s(x, v) ∈ H.edges := (Finset.mem_sdiff.1 hv).1
      have hvZ : v ∉ Z := fun hvZ => hZF v hvZ hv
      rw [if_neg (fun h' => hvZ h'.1), add_zero] at hdeg
      rw [← hdeg]
      rcases Nat.even_or_odd (degE H.edges v) with h2 | h2
      · exact absurd (hmemZ.2 ⟨hvE, h2⟩) hvZ
      · exact h2
  obtain ⟨P', C', hD', hc'⟩ := lovasz_construction hD hxZ hZF hends
  refine ⟨P', C', ?_, ?_⟩
  · have hFR : F ∪ R = H.edges := by
      rw [hF]; exact Finset.sdiff_union_of_subset hRE
    rw [← hR, hFR] at hD'
    exact hD'
  · rw [hc']; exact hc

/-! ### Case 1 -/

section Case1Helpers

variable {V : Type*} [DecidableEq V]

/-- Adding a single edge as a new path. -/
theorem add_edge_path {F : Finset (Sym2 V)} {Q C : List (List V)}
    (hD : IsPathCycleDecomp (F : Set (Sym2 V)) Q C) {x y : V} (hxy : x ≠ y)
    (hF : s(x, y) ∉ F) :
    IsPathCycleDecomp ((insert s(x, y) F : Finset (Sym2 V)) : Set (Sym2 V)) ([x, y] :: Q) C := by
  obtain ⟨hP, hC, hnd, hmem⟩ := hD
  refine ⟨?_, hC, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨by simp, by simp [hxy]⟩
    · exact hP p hp
  · rw [List.flatMap_cons, walkEdges_cons_cons, walkEdges_singleton, List.singleton_append,
      List.cons_append, List.nodup_cons]
    exact ⟨fun h => hF (by exact_mod_cast (hmem _).1 h), hnd⟩
  · intro e
    rw [List.flatMap_cons, walkEdges_cons_cons, walkEdges_singleton, List.singleton_append,
      List.cons_append, List.mem_cons, hmem, Finset.coe_insert, Set.mem_insert_iff]

theorem degE_erase (E : Finset (Sym2 V)) (e : Sym2 V) (v : V) :
    degE E v = degE (E.erase e) v + (if e ∈ E ∧ v ∈ e then 1 else 0) := by
  unfold degE edgesAt
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.2 h)]
    have : 0 < (E.filter (fun e => v ∈ e)).card := Finset.card_pos.2 ⟨e, Finset.mem_filter.2 h⟩
    omega
  · rw [Finset.erase_eq_of_notMem (fun h' => h (Finset.mem_filter.1 h')), add_zero]

open Classical in
/-- A graph whose degrees are at most `1` (a matching) is decomposed into its edges. -/
theorem matching_concl {V : Type u} [DecidableEq V] (H : FGraph V)
    (h1 : ∀ v, degE H.edges v ≤ 1) : Concl H := by
  let pr : Sym2 V → List V := fun e => [(Quot.out e).1, (Quot.out e).2]
  have hpr : ∀ e : Sym2 V, s((Quot.out e).1, (Quot.out e).2) = e := fun e => Quot.out_eq e
  have hwe : ∀ e, walkEdges (pr e) = [e] := by
    intro e
    simp only [pr, walkEdges_cons_cons, walkEdges_singleton, hpr]
  have hflat : ∀ l : List (Sym2 V), (l.map pr).flatMap walkEdges = l := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih => rw [List.map_cons, List.flatMap_cons, ih, hwe]; rfl
  refine ⟨H.edges.toList.map pr, [], ⟨?_, by simp, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    have hne : (Quot.out e).1 ≠ (Quot.out e).2 := by
      intro h
      apply H.loopless e (Finset.mem_toList.1 he)
      rw [← hpr e, h]
      exact Sym2.mk_isDiag_iff.2 rfl
    exact ⟨by simp [pr], by simp [pr, hne]⟩
  · rw [hflat, List.flatMap_nil, List.append_nil]
    exact Finset.nodup_toList _
  · intro e
    rw [hflat, List.flatMap_nil, List.append_nil, Finset.mem_toList, Finset.mem_coe]
  · simp only [List.length_map, Finset.length_toList, List.length_nil, add_zero]
    have hs := H.sum_deg_eq_two_mul_card_edges
    rw [← hs]
    calc ∑ v ∈ H.verts, H.deg v ≤ ∑ _v ∈ H.verts, 1 :=
          Finset.sum_le_sum fun v _ => by rw [FGraph.deg_eq_degE]; exact h1 v
      _ = H.card := by simp

end Case1Helpers

/-- **Case 1.** If every vertex has odd degree or degree `0`, the conclusion follows from the
induction hypothesis (through Case 0 on a graph with one more vertex). -/
theorem case1 {m : ℕ} (ih : IH.{u} m) {V : Type u} [DecidableEq V] (H : FGraph V)
    (hm : H.edges.card = m) (hodd : ∀ v, degE H.edges v ≠ 0 → Odd (degE H.edges v)) :
    Concl H := by
  classical
  by_cases hmatch : ∀ v, degE H.edges v ≤ 1
  · exact matching_concl H hmatch
  simp only [not_forall, not_le] at hmatch
  obtain ⟨x, hx2⟩ := hmatch
  have hxodd := hodd x (by omega)
  -- a neighbour `y` of `x`
  obtain ⟨e, he⟩ : (edgesAt H.edges x).Nonempty := Finset.card_pos.1 (by unfold degE at hx2; omega)
  rw [FGraph.mem_edgesAt] at he
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 he.2
  have hxyE : s(x, y) ∈ H.edges := he.1
  have hxy : x ≠ y := fun h => H.loopless _ hxyE (Sym2.mk_isDiag_iff.2 h)
  -- the non-isolated vertices
  set V₀ := H.verts.filter (fun v => degE H.edges v ≠ 0) with hV₀
  have hV₀mem : ∀ {v e}, e ∈ H.edges → v ∈ e → v ∈ V₀ := by
    intro v e he hv
    refine Finset.mem_filter.2 ⟨H.edge_verts e he v hv, ?_⟩
    have : 0 < degE H.edges v := Finset.card_pos.2 ⟨e, FGraph.mem_edgesAt.2 ⟨he, hv⟩⟩
    omega
  have hV₀even : Even V₀.card := by
    have hs := H.sum_deg_eq_two_mul_card_edges
    simp_rw [FGraph.deg_eq_degE] at hs
    rw [← Finset.sum_filter_ne_zero] at hs
    rw [← hV₀] at hs
    have hmod := Finset.sum_nat_mod V₀ 2 (fun v => degE H.edges v)
    have h1 : ∀ v ∈ V₀, degE H.edges v % 2 = 1 := by
      intro v hv
      exact Nat.odd_iff.1 (hodd v (Finset.mem_filter.1 hv).2)
    rw [Finset.sum_congr rfl h1, hs] at hmod
    simp at hmod
    exact Nat.even_iff.2 (by omega)
  -- the graph `T'` on `Option V`: move the end `x` of `xy` to a new pendant vertex `none`
  set F := H.edges.erase s(x, y) with hF
  set E₁ : Finset (Sym2 (Option V)) := F.image (Sym2.map some) with hE₁
  set E₂ : Finset (Sym2 (Option V)) := {s(none, some y)} with hE₂
  set W' : Finset (Option V) := insert none (V₀.image some) with hW'
  have hdisj : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨e₁, -, rfl⟩ := Finset.mem_image.1 h1
    rw [hE₂, Finset.mem_singleton] at h2
    exact none_notMem_map_some e₁ (h2 ▸ Sym2.mem_mk_left _ _)
  have hloop : ∀ e ∈ E₁ ∪ E₂, ¬ e.IsDiag := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 h
      rw [Sym2.isDiag_map (Option.some_injective V)]
      exact H.loopless e₁ (Finset.mem_of_mem_erase he₁)
    · rw [hE₂, Finset.mem_singleton] at h
      subst h
      simp
  have hverts : ∀ e ∈ E₁ ∪ E₂, ∀ w ∈ e, w ∈ W' := by
    intro e he w hw
    rcases Finset.mem_union.1 he with h | h
    · obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.1 hw
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (hV₀mem (Finset.mem_of_mem_erase he₁) hv))
    · rw [hE₂, Finset.mem_singleton] at h
      subst h
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
          (hV₀mem hxyE (Sym2.mem_mk_right _ _)))
  set T' := FGraph.ofEdges W' (E₁ ∪ E₂) with hT'
  have hT'e : T'.edges = E₁ ∪ E₂ := FGraph.ofEdges_edges_of_subset hloop hverts
  have hT'c : T'.card = V₀.card + 1 := by
    rw [FGraph.card_def, hT', FGraph.ofEdges_verts, hW', Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective V)]
  have hT'm : T'.edges.card = m := by
    rw [hT'e, Finset.card_union_of_disjoint hdisj, hE₁,
      Finset.card_image_of_injective _ Cor22.sym2Map_some_injective, hF,
      Finset.card_erase_of_mem hxyE, hE₂, Finset.card_singleton, ← hm]
    have : 0 < H.edges.card := Finset.card_pos.2 ⟨_, hxyE⟩
    omega
  -- `some x` has even positive degree in `T'`
  have hdegx : degE T'.edges (some x) + 1 = degE H.edges x := by
    rw [hT'e, Cor22.degE_union_of_disjoint hdisj, hE₁, Cor22.degE_image_some]
    have h2 : degE E₂ (some x) = 0 := by
      rw [hE₂]
      unfold degE edgesAt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hxe
      rw [Finset.mem_singleton] at he
      subst he
      rcases Sym2.mem_iff.1 hxe with h | h
      · simp at h
      · exact hxy (Option.some.inj h)
    rw [h2, add_zero, degE_erase H.edges s(x, y) x, if_pos ⟨hxyE, Sym2.mem_mk_left _ _⟩]
  have hTeven : Even (degE T'.edges (some x)) := by
    rcases Nat.even_or_odd (degE T'.edges (some x)) with h | h
    · exact h
    · exfalso
      rw [← hdegx] at hxodd
      exact Nat.not_even_iff_odd.2 hxodd (h.add_one)
  obtain ⟨P', C', hD', hc'⟩ := case0 ih T' hT'm hTeven (by omega)
  rw [hT'e, hT'c] at *
  -- back to `V`
  obtain ⟨Q, C'', hDQ, hQ⟩ := drop_leaf (E := F) (y := y) hD'
  have hcount : 2 * (P'.length + C'.length) ≤ V₀.card := by
    obtain ⟨k, hk⟩ := hV₀even
    omega
  have hV₀le : V₀.card ≤ H.card := Finset.card_filter_le _ _
  have hins : insert s(x, y) F = H.edges := Finset.insert_erase hxyE
  have hxyF : s(x, y) ∉ F := Finset.notMem_erase _ _
  rcases hQ with ⟨hle, q, hq, hqy⟩ | hle
  · -- `y` ends a path: the Lovász construction with `Z = {y}`
    have hends : ∀ v, (v ∈ ({y} : Finset V) ∨ s(x, v) ∈ F) →
        ∃ p ∈ Q, p.head? = some v ∨ p.getLast? = some v := by
      intro v hv
      rcases hv with hv | hv
      · rw [Finset.mem_singleton] at hv; subst hv; exact ⟨q, hq, hqy⟩
      · apply exists_end_of_odd hDQ
        have hvE : s(x, v) ∈ H.edges := Finset.mem_of_mem_erase hv
        have hvy : v ≠ y := by rintro rfl; exact hxyF hv
        have hvx : v ≠ x := fun h => H.loopless _ hvE (Sym2.mk_isDiag_iff.2 h.symm)
        have hd := degE_erase H.edges s(x, y) v
        rw [if_neg (fun h => by
          rcases Sym2.mem_iff.1 h.2 with h' | h'
          · exact hvx h'
          · exact hvy h')] at hd
        rw [← hF, add_zero] at hd
        rw [← hd]
        refine hodd v ?_
        have : 0 < degE H.edges v := Finset.card_pos.2 ⟨_, FGraph.mem_edgesAt.2
          ⟨hvE, Sym2.mem_mk_right _ _⟩⟩
        omega
    obtain ⟨P₂, C₂, hD₂, hc₂⟩ := lovasz_construction hDQ (by simpa using hxy) (by simpa using hxyF)
      hends
    refine ⟨P₂, C₂, ?_, ?_⟩
    · have : (F ∪ ({y} : Finset V).image (fun z => s(x, z))) = H.edges := by
        rw [Finset.image_singleton, Finset.union_comm, ← Finset.insert_eq, hins]
      rw [this] at hD₂
      exact hD₂
    · omega
  · -- the pendant path was a single edge: add `xy` as a new path
    refine ⟨[x, y] :: Q, C'', ?_, ?_⟩
    · have := add_edge_path hDQ hxy hxyF
      rw [hins] at this
      exact this
    · simp only [List.length_cons]
      omega

/-- The conclusion for every graph with `m` edges, by strong induction on `m`. -/
theorem concl_of_card : ∀ (m : ℕ) (V : Type u) [DecidableEq V] (H : FGraph V),
    H.edges.card = m → Concl H := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro V _ H hm
    have ih : IH.{u} m := fun V' _ H' hlt => ihm _ hlt V' H' rfl
    by_cases hev : ∃ a, Even (degE H.edges a) ∧ degE H.edges a ≠ 0
    · obtain ⟨a, ha, ha0⟩ := hev
      exact case0 ih H hm ha ha0
    · simp only [not_exists, not_and, not_not] at hev
      refine case1 ih H hm fun v hv => ?_
      rcases Nat.even_or_odd (degE H.edges v) with h | h
      · exact absurd (hev v h) hv
      · exact h

/-- **Lovász's theorem** ([s1:citThm21], Lovász 1968): every graph with `n` vertices decomposes into
at most `n/2` paths and cycles. -/
theorem lovasz : Spec.LovaszStatement.{u} :=
  fun V _ H => concl_of_card _ V H rfl

end LovaszC

end EG
