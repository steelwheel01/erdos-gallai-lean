module

public import EG.Lib.Light.Trail
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Visit capping of closed trails (s5:lemParent, Step 4): list machinery

Library for probe unit P4B (probe P-4, part 2), proof round 1. The split of a closed trail at a
node (manuscript: "Rotate the cyclic sequence so that its last transition (position `k`) is at
`Y` … cut `𝒲` into `vis` consecutive segments … Group consecutive segments into `⌈vis/T^sl_Y⌉`
blocks of at most `T^sl_Y` segments"):
* `segs q L`: the consecutive segments of `L` each ending with an element satisfying `q`;
* `chunksS k L`: consecutive chunks of `k + 1` elements (the last one possibly shorter);
* closure of a cyclic list as a chain (`closed_iff_chain`) and rotation invariance.
Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG.MTrail

variable {α : Type*}

/-! ### Segments ending with a marked element -/

/-- The consecutive segments of `L`, each ending with an element satisfying `q` (the last segment
may end without one if `L` does). -/
def segs (q : α → Bool) : List α → List (List α)
  | [] => []
  | x :: xs =>
    if q x then [x] :: segs q xs
    else match segs q xs with
      | [] => [[x]]
      | s :: ss => (x :: s) :: ss

theorem flatten_segs (q : α → Bool) : ∀ L : List α, (segs q L).flatten = L
  | [] => rfl
  | x :: xs => by
    have ih := flatten_segs q xs
    unfold segs
    split_ifs
    · simp [ih]
    · split
      · rename_i h; rw [h] at ih; simp at ih; simp [ih]
      · rename_i s ss h; rw [h] at ih; simp [← ih]

theorem ne_nil_of_mem_segs (q : α → Bool) : ∀ (L : List α), ∀ s ∈ segs q L, s ≠ []
  | [] => by simp [segs]
  | x :: xs => by
    have ih := ne_nil_of_mem_segs q xs
    unfold segs
    split_ifs
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · simp
      · exact ih s hs
    · split
      · intro s hs; simp at hs; rw [hs]; simp
      · rename_i s0 ss h
        intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · simp
        · exact ih s (by rw [h]; exact List.mem_cons_of_mem _ hs)

/-- If `L` ends with a marked element, every segment contains exactly one marked element and ends
with it. -/
theorem segs_spec (q : α → Bool) : ∀ (L : List α), (∀ y ∈ L.getLast?, q y = true) →
    ∀ s ∈ segs q L, s.countP q = 1 ∧ ∀ y ∈ s.getLast?, q y = true
  | [] => by simp [segs]
  | x :: xs => by
    intro hlast
    have hlast' : ∀ y ∈ xs.getLast?, q y = true := by
      intro y hy
      apply hlast
      cases xs with
      | nil => simp at hy
      | cons z zs => rw [List.getLast?_cons_cons]; exact hy
    have ih := segs_spec q xs hlast'
    unfold segs
    split_ifs with hx
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · simp [hx]
      · exact ih s hs
    · have hxs : xs ≠ [] := by
        rintro rfl
        simp at hlast
        exact absurd hlast (by simp [hx])
      split
      · rename_i h
        have := flatten_segs q xs
        rw [h] at this
        exact absurd this.symm hxs
      · rename_i s0 ss h
        have hs0 := ih s0 (by rw [h]; exact List.mem_cons_self)
        have hs0ne := ne_nil_of_mem_segs q xs s0 (by rw [h]; exact List.mem_cons_self)
        intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · refine ⟨by simp [List.countP_cons, hx, hs0.1], ?_⟩
          intro y hy
          apply hs0.2
          obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hs0ne
          rw [List.getLast?_cons_cons] at hy
          exact hy
        · exact ih s (by rw [h]; exact List.mem_cons_of_mem _ hs)

theorem length_segs (q : α → Bool) (L : List α) (hlast : ∀ y ∈ L.getLast?, q y = true) :
    (segs q L).length = L.countP q := by
  conv_rhs => rw [← flatten_segs q L]
  rw [List.countP_flatten]
  have : (segs q L).map (List.countP q) = (segs q L).map fun _ => 1 :=
    List.map_congr_left fun s hs => (segs_spec q L hlast s hs).1
  rw [this, List.map_const', List.sum_replicate]
  simp

/-! ### Chunks -/

/-- Consecutive chunks of `k + 1` elements, with fuel `f` (structural recursion). -/
def chunksF (k : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, x :: xs => (x :: xs.take k) :: chunksF k f (xs.drop k)

/-- Consecutive chunks of `k + 1` elements (the last one possibly shorter). -/
def chunksS (k : ℕ) (L : List α) : List (List α) := chunksF k L.length L

theorem flatten_chunksF (k : ℕ) : ∀ (f : ℕ) (L : List α), L.length ≤ f →
    (chunksF k f L).flatten = L
  | 0, L, h => by simp at h; subst h; rfl
  | f + 1, [], _ => rfl
  | f + 1, x :: xs, h => by
    simp only [chunksF, List.flatten_cons]
    rw [flatten_chunksF k f (xs.drop k) (by simp at h ⊢; omega)]
    simp

theorem flatten_chunksS (k : ℕ) (L : List α) : (chunksS k L).flatten = L :=
  flatten_chunksF k _ L le_rfl

theorem mem_chunksF (k : ℕ) : ∀ (f : ℕ) (L : List α), ∀ ch ∈ chunksF k f L,
    ch ≠ [] ∧ ch.length ≤ k + 1
  | 0, L => by simp [chunksF]
  | f + 1, [] => by simp [chunksF]
  | f + 1, x :: xs => by
    intro ch hch
    simp only [chunksF] at hch
    rcases List.mem_cons.1 hch with rfl | hch
    · simp
    · exact mem_chunksF k f (xs.drop k) ch hch

theorem mem_chunksS (k : ℕ) (L : List α) : ∀ ch ∈ chunksS k L, ch ≠ [] ∧ ch.length ≤ k + 1 :=
  mem_chunksF k _ L

theorem length_chunksF (k : ℕ) : ∀ (f : ℕ) (L : List α),
    ((chunksF k f L).length - 1) * (k + 1) ≤ L.length
  | 0, L => by simp [chunksF]
  | f + 1, [] => by simp [chunksF]
  | f + 1, x :: xs => by
    simp only [chunksF, List.length_cons]
    have ih := length_chunksF k f (xs.drop k)
    rw [List.length_drop] at ih
    rcases Nat.eq_zero_or_pos (chunksF k f (xs.drop k)).length with h0 | hpos
    · rw [h0]; simp
    · simp only [Nat.add_sub_cancel]
      have hlen : k < xs.length := by
        by_contra hc
        have : xs.drop k = [] := List.drop_eq_nil_of_le (by omega)
        rw [this] at hpos
        cases f <;> simp [chunksF] at hpos
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hm] at ih ⊢
      simp only [Nat.succ_sub_one] at ih
      have : (m + 1) * (k + 1) = m * (k + 1) + (k + 1) := by ring
      rw [this]
      omega

theorem length_chunksS (k : ℕ) (L : List α) : ((chunksS k L).length - 1) * (k + 1) ≤ L.length :=
  length_chunksF k _ L


/-! ### Closure of a cyclic list as a chain -/

section Closure

variable {ι β : Type*} (E : ι → β × β)

/-- Consecutive oriented edges meet: the end of `p` is the start of `p'`. -/
def Meets (p p' : ι × Bool) : Prop := oTgt E p = oSrc E p'

theorem closed_aux : ∀ (a : ι × Bool) (t : List (ι × Bool)) (z : ι × Bool),
    (∀ x ∈ List.zipWith (fun p q => (oTgt E p, oSrc E q)) (a :: t) (t ++ [z]), x.1 = x.2) ↔
      List.IsChain (Meets E) (a :: t) ∧ ∀ x ∈ (a :: t).getLast?, Meets E x z
  | a, [], z => by simp [Meets]
  | a, b :: t, z => by
    have ih := closed_aux b t z
    simp only [List.cons_append, List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih, List.isChain_cons_cons, List.getLast?_cons_cons]
    simp only [Meets]
    tauto

/-- The transitions of a nonempty cyclic list are all closed iff consecutive oriented edges meet
and the last meets the first. -/
theorem trans_closed_iff (W : List (ι × Bool)) (hW : W ≠ []) :
    (∀ x ∈ transitions E W, x.1 = x.2) ↔
      List.IsChain (Meets E) W ∧ ∀ x ∈ W.getLast?, ∀ y ∈ W.head?, Meets E x y := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hW
  have hrot : (a :: t).rotate 1 = t ++ [a] := by rw [List.rotate_cons_succ, List.rotate_zero]
  unfold transitions
  rw [hrot, closed_aux]
  simp

theorem transitions_rotate (W : List (ι × Bool)) (m : ℕ) :
    transitions E (W.rotate m) = (transitions E W).rotate m := by
  unfold transitions
  rw [List.zipWith_rotate_distrib _ _ _ _ (by simp), List.rotate_rotate, List.rotate_rotate,
    add_comm]

theorem IsClosedTrail.rotate_closed {W : List (ι × Bool)} (h : IsClosedTrail E W) (m : ℕ) :
    IsClosedTrail E (W.rotate m) := by
  obtain ⟨hne, hnd, hcl⟩ := h
  refine ⟨fun h' => hne (by simpa using congrArg List.length h'), ?_, ?_⟩
  · rw [List.map_rotate]; exact List.nodup_rotate.2 hnd
  · intro t ht
    rw [transitions_rotate, List.mem_rotate] at ht
    exact hcl t ht

/-- Blocks of a chain, each ending at the node `Y`, following an element that ends at `Y`, are
closed. -/
theorem blocks_wrap (Y : β) : ∀ (Bs : List (List (ι × Bool))) (x : ι × Bool), oTgt E x = Y →
    List.IsChain (Meets E) (x :: Bs.flatten) →
    (∀ B ∈ Bs, B ≠ [] ∧ ∀ y ∈ B.getLast?, oTgt E y = Y) →
    ∀ B ∈ Bs, List.IsChain (Meets E) B ∧ ∀ u ∈ B.getLast?, ∀ v ∈ B.head?, Meets E u v
  | [], _, _, _, _ => by simp
  | B :: rest, x, hx, hch, hB => by
    rw [List.flatten_cons, ← List.cons_append, List.isChain_append] at hch
    obtain ⟨hxB, hrest, hlink⟩ := hch
    rw [List.isChain_cons] at hxB
    obtain ⟨hne, hlast⟩ := hB B List.mem_cons_self
    cases hBl : B.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hBl) hne
    | some x' =>
      have hx' : oTgt E x' = Y := hlast x' hBl
      have hxBl : (x :: B).getLast? = some x' := by rw [List.getLast?_cons, hBl]; rfl
      intro B' hB'
      rcases List.mem_cons.1 hB' with rfl | hB'
      · refine ⟨hxB.2, fun u hu v hv => ?_⟩
        have hu' := hlast u hu
        have hxv := hxB.1 v hv
        unfold Meets at hxv ⊢
        rw [hu', ← hxv, hx]
      · refine blocks_wrap Y rest x' hx' ?_
          (fun B'' h => hB B'' (List.mem_cons_of_mem _ h)) B' hB'
        rw [List.isChain_cons]
        exact ⟨fun y hy => hlink x' hxBl y hy, hrest⟩

end Closure


/-! ### Splitting one closed trail at a node -/

section Split

variable {ι β : Type*} [DecidableEq β] (E : ι → β × β)

theorem getLast?_flatten_of_forall {P : α → Prop} : ∀ (ch : List (List α)),
    (∀ s ∈ ch, s ≠ [] ∧ ∀ y ∈ s.getLast?, P y) → ∀ y ∈ ch.flatten.getLast?, P y
  | [], _ => by simp
  | s :: rest, h => by
    intro y hy
    rw [List.flatten_cons, List.getLast?_append] at hy
    cases hr : rest.flatten.getLast? with
    | none =>
      rw [hr] at hy
      exact (h s List.mem_cons_self).2 y (by simpa using hy)
    | some z =>
      rw [hr, Option.some_or, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact getLast?_flatten_of_forall rest (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) _ hr

/-- From `(L - 1) c ≤ m` in `ℕ`: `L ≤ 1 + m/c` in `ℝ`. -/
theorem real_le_of_pred_mul_le {L m c : ℕ} (hc : 1 ≤ c) (h : (L - 1) * c ≤ m) :
    (L : ℝ) ≤ 1 + (m : ℝ) / c := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp; positivity
  · have h' : ((L - 1 : ℕ) : ℝ) * c ≤ m := by exact_mod_cast h
    rw [Nat.cast_sub hL, Nat.cast_one] at h'
    rw [← sub_le_iff_le_add', le_div_iff₀ hc0]
    exact h'

/-- [s5:lemParent] Step 4, one split: "If `vis_Y(𝒲) > T^sl_Y`, *split* `𝒲` at `Y` … A block
`(a_p, …, a_q)` is again a closed trail of the same kind … The block has as many transitions at `Y`
as it has segments, hence at most `T^sl_Y`; … So a split at `Y` replaces `𝒲` by
`⌈vis/T^sl_Y⌉ ≤ 1 + vis/T^sl_Y` closed trails, partitions the arcs of `𝒲` among them". Here the
transitions at `Y` of a trail are counted as its oriented edges ending at `Y`. -/
theorem split_one {W : List (ι × Bool)} (hW : IsClosedTrail E W) (Y : β) {c : ℕ} (hc : 1 ≤ c) :
    ∃ Bs : List (List (ι × Bool)), Bs.flatten.Perm W ∧ (∀ B ∈ Bs, IsClosedTrail E B) ∧
      (∀ B ∈ Bs, B.countP (fun p => decide (oTgt E p = Y)) ≤ c) ∧
      (Bs.length : ℝ) ≤ 1 + (W.countP (fun p => decide (oTgt E p = Y)) : ℝ) / c := by
  set q : ι × Bool → Bool := fun p => decide (oTgt E p = Y) with hq
  by_cases hle : W.countP q ≤ c
  · refine ⟨[W], by simp, by simpa using hW, by simpa using hle, ?_⟩
    simp only [List.length_singleton, Nat.cast_one, le_add_iff_nonneg_right]
    positivity
  push Not at hle
  obtain ⟨x, hxW, hqx⟩ := List.countP_pos_iff.1 (show 0 < W.countP q by omega)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxW
  set W' := W.rotate (j + 1) with hW'
  have hlast : W'.getLast? = some W[j] := by
    rw [List.getLast?_eq_getElem?, List.length_rotate, List.getElem?_rotate (by omega)]
    have : (W.length - 1 + (j + 1)) % W.length = j := by
      rw [show W.length - 1 + (j + 1) = j + W.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hj]
    rw [this, List.getElem?_eq_getElem hj]
  have hYj : oTgt E W[j] = Y := by simpa [hq] using hqx
  have hW'c := hW.rotate_closed E (j + 1)
  rw [← hW'] at hW'c
  obtain ⟨hne', hnd', hcl'⟩ := hW'c
  rw [trans_closed_iff E W' hne'] at hcl'
  obtain ⟨hchain, hwrap⟩ := hcl'
  have hss := segs_spec q W' (fun y hy => by
    rw [hlast, Option.mem_def, Option.some.injEq] at hy; subst hy; exact hqx)
  set ss := segs q W' with hssdef
  set chs := chunksS (c - 1) ss with hchs
  have hflat : (chs.map List.flatten).flatten = W' := by
    rw [← List.flatten_flatten, flatten_chunksS, flatten_segs]
  have hmem : ∀ ch ∈ chs, ∀ s ∈ ch, s ∈ ss := fun ch hch s hs => by
    have := (List.sublist_flatten_of_mem hch).subset hs
    rwa [flatten_chunksS] at this
  have hblk : ∀ B ∈ chs.map List.flatten, B ≠ [] ∧ ∀ y ∈ B.getLast?, oTgt E y = Y := by
    intro B hB
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hB
    obtain ⟨hchne, -⟩ := mem_chunksS (c - 1) ss ch hch
    obtain ⟨s0, ss0, hs0⟩ := List.exists_cons_of_ne_nil hchne
    refine ⟨?_, ?_⟩
    · rw [hs0, List.flatten_cons]
      have := ne_nil_of_mem_segs q W' s0 (hmem ch hch s0 (by rw [hs0]; exact List.mem_cons_self))
      simp [this]
    · refine getLast?_flatten_of_forall ch (fun s hs => ⟨ne_nil_of_mem_segs q W' s (hmem ch hch s hs),
        fun y hy => ?_⟩)
      have := (hss s (hmem ch hch s hs)).2 y hy
      simpa [hq] using this
  have hwrapB := blocks_wrap E Y (chs.map List.flatten) W[j] hYj
    (by
      rw [hflat, List.isChain_cons]
      exact ⟨fun y hy => hwrap W[j] hlast y hy, hchain⟩) hblk
  refine ⟨chs.map List.flatten, ?_, ?_, ?_, ?_⟩
  · rw [hflat]; exact List.rotate_perm W (j + 1)
  · intro B hB
    have hBne := (hblk B hB).1
    refine ⟨hBne, ?_, (trans_closed_iff E B hBne).2 (hwrapB B hB)⟩
    have hsub : List.Sublist B W' := by rw [← hflat]; exact List.sublist_flatten_of_mem hB
    exact hnd'.sublist (hsub.map _)
  · intro B hB
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hB
    obtain ⟨-, hlen⟩ := mem_chunksS (c - 1) ss ch hch
    rw [List.countP_flatten]
    have : ch.map (List.countP q) = ch.map fun _ => 1 :=
      List.map_congr_left fun s hs => (hss s (hmem ch hch s hs)).1
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
    omega
  · rw [List.length_map]
    have h1 := length_chunksS (c - 1) ss
    rw [show c - 1 + 1 = c by omega, hssdef, length_segs q W' (fun y hy => by
      rw [hlast, Option.mem_def, Option.some.injEq] at hy; subst hy; exact hqx),
      (List.rotate_perm W (j + 1)).countP_eq] at h1
    exact real_le_of_pred_mul_le hc h1

end Split


/-! ### Splitting all trails at one node, then at every node of a list -/

section Iterate

variable {ι β : Type*} [DecidableEq β] (E : ι → β × β)

theorem split_all (Y : β) {c : ℕ} (hc : 1 ≤ c) : ∀ (Ws : List (List (ι × Bool))),
    (∀ W ∈ Ws, IsClosedTrail E W) →
    ∃ Ws1 : List (List (ι × Bool)), (∀ W1 ∈ Ws1, IsClosedTrail E W1) ∧
      Ws1.flatten.Perm Ws.flatten ∧ (∀ W1 ∈ Ws1, ∃ W ∈ Ws, W1.Subperm W) ∧
      (∀ W1 ∈ Ws1, W1.countP (fun p => decide (oTgt E p = Y)) ≤ c) ∧
      (Ws1.length : ℝ) ≤ Ws.length +
        (Ws.flatten.countP (fun p => decide (oTgt E p = Y)) : ℝ) / c
  | [], _ => ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | W :: Ws, h => by
    obtain ⟨Bs, hBf, hBc, hBq, hBl⟩ := split_one E (h W List.mem_cons_self) Y hc
    obtain ⟨Ws1, h1c, h1f, h1s, h1q, h1l⟩ := split_all Y hc Ws (fun W' hW' => h W' (List.mem_cons_of_mem _ hW'))
    refine ⟨Bs ++ Ws1, ?_, ?_, ?_, ?_, ?_⟩
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · exact hBc B hB
      · exact h1c B hB
    · rw [List.flatten_append, List.flatten_cons]
      exact hBf.append h1f
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · exact ⟨W, List.mem_cons_self, ((List.sublist_flatten_of_mem hB).subperm).trans hBf.subperm⟩
      · obtain ⟨W', hW', hs⟩ := h1s B hB
        exact ⟨W', List.mem_cons_of_mem _ hW', hs⟩
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · exact hBq B hB
      · exact h1q B hB
    · rw [List.length_append, List.flatten_cons, List.countP_append, List.length_cons]
      push_cast
      have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
      rw [add_div]
      linarith

theorem iterate (cap : β → ℕ) : ∀ (Ys : List β) (Ws : List (List (ι × Bool))),
    (∀ W ∈ Ws, IsClosedTrail E W) → (∀ Y ∈ Ys, 1 ≤ cap Y) →
    ∃ Ws' : List (List (ι × Bool)), (∀ W' ∈ Ws', IsClosedTrail E W') ∧
      Ws'.flatten.Perm Ws.flatten ∧ (∀ W' ∈ Ws', ∃ W ∈ Ws, W'.Subperm W) ∧
      (∀ W' ∈ Ws', ∀ Y ∈ Ys, W'.countP (fun p => decide (oTgt E p = Y)) ≤ cap Y) ∧
      (Ws'.length : ℝ) ≤ Ws.length +
        (Ys.map fun Y => (Ws.flatten.countP (fun p => decide (oTgt E p = Y)) : ℝ) / cap Y).sum
  | [], Ws, h, _ => ⟨Ws, h, List.Perm.refl _, fun W hW => ⟨W, hW, List.Subperm.refl W⟩,
      by simp, by simp⟩
  | Y :: Ys, Ws, h, hcap => by
    obtain ⟨Ws1, h1c, h1f, h1s, h1q, h1l⟩ := split_all E Y (hcap Y List.mem_cons_self) Ws h
    obtain ⟨Ws', h2c, h2f, h2s, h2q, h2l⟩ := iterate cap Ys Ws1 h1c
      (fun Y' hY' => hcap Y' (List.mem_cons_of_mem _ hY'))
    refine ⟨Ws', h2c, h2f.trans h1f, ?_, ?_, ?_⟩
    · intro W' hW'
      obtain ⟨W1, hW1, hs1⟩ := h2s W' hW'
      obtain ⟨W, hW, hs⟩ := h1s W1 hW1
      exact ⟨W, hW, hs1.trans hs⟩
    · intro W' hW' Y' hY'
      rcases List.mem_cons.1 hY' with rfl | hY'
      · obtain ⟨W1, hW1, hs1⟩ := h2s W' hW'
        exact (hs1.countP_le _).trans (h1q W1 hW1)
      · exact h2q W' hW' Y' hY'
    · have hsum : (Ys.map fun Y => (Ws1.flatten.countP (fun p => decide (oTgt E p = Y)) : ℝ) /
          cap Y).sum = (Ys.map fun Y => (Ws.flatten.countP (fun p => decide (oTgt E p = Y)) : ℝ) /
          cap Y).sum := by
        congr 1
        refine List.map_congr_left fun Y' _ => ?_
        rw [h1f.countP_eq]
      rw [hsum] at h2l
      rw [List.map_cons, List.sum_cons]
      linarith

end Iterate

end EG.MTrail
