module

public import EG.Lib.Chain.HccpPaths
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# HCC-P: auxiliary lemmas (manuscript s6:lemHCCP)

Probe unit P2E (probe P-2, part 1), proof round 1.
* orientations and degrees of a union of arc sets over a finite index set
  (`EG.isOrientation_biUnion`, `EG.outDeg_biUnion`, `EG.inDeg_biUnion`);
* `HccpData.succ` is a bijection of `Fin k` (`HccpData.succ_bijective`);
* Step 0, the loads: `|𝒫_j| = ∑_{LayP_j} dem⁻ = Φ_j` and `|𝒫_j| = ∑_{LayP_{j+1}} dem⁺ = Φ_{j+1}`
  (`Valid.length_P_eq_Phi`, `Valid.length_P_eq_Phi_succ`), hence all `Φ_j` are equal
  (`Valid.Phi_eq_Phi_zero`);
* Step 4, the length bound through blocks (`EG.le_length_of_blocks`): along a closed directed
  walk the block index goes up by at most `1` per arc and drops by `k − 1` on an arc of `𝒲`, so the
  walk has at least `k` arcs.
-/

public section

namespace EG

variable {V : Type*} [DecidableEq V]

/-- The union of orientations of pairwise disjoint edge sets orients the union. -/
theorem isOrientation_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → Finset (Sym2 V)) (A : ι → Finset (V × V)) (hA : ∀ i ∈ s, IsOrientation (F i) (A i))
    (hd : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (F i) (F i')) :
    IsOrientation (s.biUnion F) (s.biUnion A) := by
  induction s using Finset.induction_on with
  | empty => simpa using (IsOrientation.empty (V := V))
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.biUnion_insert]
    refine (hA a (Finset.mem_insert_self _ _)).union
      (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
        (fun i hi i' hi' h => hd i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi') h))
      ?_
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hd a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
      (fun h => ha (h ▸ hi))

/-- Degrees add over a union of pairwise disjoint arc sets. -/
theorem outDeg_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Finset (V × V))
    (hd : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (A i) (A i')) (v : V) :
    outDeg (s.biUnion A) v = ∑ i ∈ s, outDeg (A i) v := by
  unfold outDeg
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i hi i' hi' h
  exact Finset.disjoint_filter_filter (hd i hi i' hi' h)

theorem inDeg_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Finset (V × V))
    (hd : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (A i) (A i')) (v : V) :
    inDeg (s.biUnion A) v = ∑ i ∈ s, inDeg (A i) v := by
  unfold inDeg
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i hi i' hi' h
  exact Finset.disjoint_filter_filter (hd i hi i' hi' h)

/-- A list sum of terms `≤ 1` with one distinguished term `f w`. -/
theorem sum_map_le_of_mem {α : Type*} [DecidableEq α] (f : α → ℤ) :
    ∀ (l : List α) {w : α}, w ∈ l → (∀ a ∈ l, f a ≤ 1) →
      (l.map f).sum ≤ ((l.length : ℤ) - 1) + f w
  | [], _, hw, _ => absurd hw List.not_mem_nil
  | a :: l, w, hw, h => by
    have hle : ∀ (l : List α), (∀ a ∈ l, f a ≤ 1) → (l.map f).sum ≤ l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons b l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        have := hl b List.mem_cons_self
        have := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        linarith
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rcases List.mem_cons.1 hw with rfl | hw'
    · have := hle l (fun x hx => h x (List.mem_cons_of_mem _ hx))
      linarith
    · have := sum_map_le_of_mem f l hw' (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have := h a List.mem_cons_self
      linarith

omit [DecidableEq V] in
theorem length_cycleArcs (c : List V) : (cycleArcs c).length = c.length := by
  unfold cycleArcs
  rw [List.length_zip, List.length_rotate, min_self]

omit [DecidableEq V] in
/-- Telescoping along a closed walk: `∑_{arcs} (g(head) − g(tail)) = 0`. -/
theorem sum_cycleArcs_sub (g : V → ℤ) (c : List V) :
    ((cycleArcs c).map (fun a => g a.2 - g a.1)).sum = 0 := by
  have h1 : ((cycleArcs c).map (fun a => g a.2)).sum = (c.map g).sum := by
    have : (cycleArcs c).map (fun a => g a.2) = ((cycleArcs c).map Prod.snd).map g := by
      rw [List.map_map]; rfl
    rw [this, map_snd_cycleArcs]
    exact ((List.rotate_perm c 1).map g).sum_eq
  have h2 : ((cycleArcs c).map (fun a => g a.1)).sum = (c.map g).sum := by
    have : (cycleArcs c).map (fun a => g a.1) = ((cycleArcs c).map Prod.fst).map g := by
      rw [List.map_map]; rfl
    rw [this, map_fst_cycleArcs]
  have hsub : ∀ l : List (V × V),
      (l.map (fun a => g a.2 - g a.1)).sum = (l.map (fun a => g a.2)).sum - (l.map (fun a => g a.1)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hsub, h1, h2, sub_self]

/-- [s6:lemHCCP] (proof, Step 4) "For the bound `k` on the length, call `[3j,3j+3)` the `j`-th
block. Every arc of `F⃗ - 𝒲` either has both ends in the same block, or is an arc ... from block
`j` to block `j+1` ... Together with the `𝒲`-arc that follows it, `C` has at least `k` arcs."
With a block index `blk`: if every arc of `A` raises `blk` by at most `1` and every arc of `W`
goes from block `k − 1` to block `0`, then a closed directed walk of `A` through an arc of `W` has
at least `k` arcs. -/
theorem le_length_of_blocks {A W : Finset (V × V)} (blk : V → ℕ) (k : ℕ)
    (hA : ∀ a ∈ A, blk a.2 ≤ blk a.1 + 1) (hW : ∀ a ∈ W, blk a.2 = 0 ∧ blk a.1 + 1 = k)
    {c : List V} (hc : ∀ a ∈ cycleArcs c, a ∈ A) {w : V × V} (hwW : w ∈ W)
    (hwc : w ∈ cycleArcs c) : k ≤ c.length := by
  have h0 := sum_cycleArcs_sub (fun v => (blk v : ℤ)) c
  have hle := sum_map_le_of_mem (fun a => (blk a.2 : ℤ) - blk a.1) (cycleArcs c) hwc
    (fun a ha => by have := hA a (hc a ha); omega)
  rw [h0, length_cycleArcs] at hle
  obtain ⟨h1, h2⟩ := hW w hwW
  simp only [h1] at hle
  omega

namespace Chain

namespace HccpData

variable {S : HccpData V}

omit [DecidableEq V] in
/-- For `k ≥ 1`, `j ↦ j + 1 mod k` is a bijection of `Fin k`. -/
theorem succ_injective (S : HccpData V) : Function.Injective S.succ := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [succ_val] at h'
  apply Fin.ext
  have ha := a.2
  have hb := b.2
  rcases Nat.lt_or_ge (a.val + 1) S.k with ha' | ha' <;>
    rcases Nat.lt_or_ge (b.val + 1) S.k with hb' | hb'
  · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h'; omega
  · have : b.val + 1 = S.k := by omega
    rw [Nat.mod_eq_of_lt ha', this, Nat.mod_self] at h'; omega
  · have : a.val + 1 = S.k := by omega
    rw [Nat.mod_eq_of_lt hb', this, Nat.mod_self] at h'; omega
  · omega

omit [DecidableEq V] in
theorem succ_bijective (S : HccpData V) : Function.Bijective S.succ :=
  Finite.injective_iff_bijective.1 S.succ_injective

/-- Counting a list by the first vertices of its members, when every member starts in `L`. -/
theorem length_eq_sum_countP {α : Type*} (l : List α) (f : α → Option V) (L : Finset V)
    (h : ∀ p ∈ l, ∃ u ∈ L, f p = some u) :
    l.length = ∑ u ∈ L, l.countP (fun p => decide (f p = some u)) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.length_cons, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp only [List.countP_cons, Finset.sum_add_distrib]
    congr 1
    obtain ⟨u, hu, hpu⟩ := h p List.mem_cons_self
    rw [Finset.sum_eq_single_of_mem u hu]
    · simp [hpu]
    · intro u' _ hne
      simp [hpu, Ne.symm hne]

variable {G : FGraph V}

/-- [s6:lemHCCP] (proof, Step 0) "`∑_{u∈LayP_j} exc(u)^- = ∑_{u∈LayP_j} exc(u)^+`": for an
admissible orientation, `∑_{u∈U_𝒦} exc(u)^- = Φ(𝒦)` (Lemma MED (b), `∑ exc = 0`). -/
theorem sum_excNeg_eq_load {K : Cluster V} {O : Finset (V × V)} (hO : K.IsAdmissible O) :
    ∑ u ∈ K.ports, excNeg O u = K.load O := by
  have h := Cluster.sum_ports_exc hO
  have h' : ∑ u ∈ K.ports, ((excPos O u : ℤ) - excNeg O u) = 0 := by
    rw [← h]; exact Finset.sum_congr rfl fun u _ => (exc_eq_excPos_sub_excNeg O u).symm
  rw [Finset.sum_sub_distrib, sub_eq_zero] at h'
  unfold Cluster.load
  exact_mod_cast h'.symm

/-- [s6:lemHCCP] (proof, Step 0) "Counting first vertices ... `|𝒫_j| = ∑_{u∈LayP_j} dem⁻(u)
= ∑_{u∈LayP_j} (exc(u)^+ + pad(u)) = Φ_j`". -/
theorem Valid.length_P_eq_Phi (hS : S.Valid G) (j : Fin S.k) : (S.P j).length = S.Phi j := by
  rw [length_eq_sum_countP (S.P j) List.head? (S.layP j) (fun p hp => (hS.path_ends j p hp).1),
    Finset.sum_congr rfl (fun u hu => hS.starts j u hu), hS.sum_demMinus_eq,
    hS.Phi_eq_sum_load_add_pad]
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_excNeg_eq_load (hS.adm i)

/-- [s6:lemHCCP] (proof, Step 0) "`|𝒫_j| = ∑_{v∈LayP_{j+1}} dem⁺(v) = Φ_{j+1}`". -/
theorem Valid.length_P_eq_Phi_succ (hS : S.Valid G) (j : Fin S.k) :
    (S.P j).length = S.Phi (S.succ j) := by
  rw [length_eq_sum_countP (S.P j) List.getLast? (S.layP (S.succ j))
    (fun p hp => (hS.path_ends j p hp).2),
    Finset.sum_congr rfl (fun v hv => hS.ends j v hv)]
  rfl

/-- [s6:lemHCCP] (i) "Hence `Φ_j = Φ_{j+1}` for all `j` modulo `k`, and all padded loads equal
`Φ := |𝒫_j|`." -/
theorem Valid.Phi_eq_Phi_zero (hS : S.Valid G) (j : Fin S.k) :
    S.Phi j = S.Phi ⟨0, hS.k_pos⟩ := by
  obtain ⟨n, hn⟩ := j
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < S.k := by omega
    have hs : S.succ ⟨n, hn'⟩ = ⟨n + 1, hn⟩ := by
      apply Fin.ext
      simp only [succ_val]
      exact Nat.mod_eq_of_lt hn
    rw [← hs, ← hS.length_P_eq_Phi_succ, hS.length_P_eq_Phi, ih hn']

end HccpData

end Chain

end EG
