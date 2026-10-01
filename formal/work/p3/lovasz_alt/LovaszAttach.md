# LovaszAttach.lean (archived, unused alternative Lovász route; not built)

```lean
module

public import EG.Lib.Ext.LovaszForest

/-!
# Lovász's theorem: attaching edges at a vertex (manuscript s1:citThm21)

Helper file for `EG.Spec.LovaszStatement` (proof outline: `formal/work/p3/s1.md`, Round 2,
step 3, "Rebuild"). Given chains `l b` (from a root `b` down along arms to a live vertex
`leaf b`) and paths `q b` avoiding `x` ending at `leaf b`, the new family reverses every arm
attached at a non-root chain vertex (`newX`) and appends `x` to each `q b` at `leaf b`
(`psi`). `rebuild`: the result decomposes `F ∪ {xb : b ∈ B}` and has the same size.
-/

public section

namespace EG

namespace Lov

open Cor22

variable {V : Type*} [DecidableEq V]

/-! ### Flipping arms -/

/-- `L` reversed if its last vertex lies in `U`. -/
@[expose] def flipL (U : Multiset V) (L : List V) : List V :=
  if L.getLast?.any (fun u => decide (u ∈ U)) then L.reverse else L

/-- `R` reversed if its first vertex lies in `U`. -/
@[expose] def flipR (U : Multiset V) (R : List V) : List V :=
  if R.head?.any (fun u => decide (u ∈ U)) then R.reverse else R

/-- The last vertex of `L`, if it lies in `U`. -/
@[expose] def attL (U : Multiset V) (L : List V) : List V :=
  L.getLast?.toList.filter (fun u => decide (u ∈ U))

/-- The first vertex of `R`, if it lies in `U`. -/
@[expose] def attR (U : Multiset V) (R : List V) : List V :=
  R.head?.toList.filter (fun u => decide (u ∈ U))

/-- The new path through `x`: arms attached in `U` are reversed. -/
@[expose] def newX (U : Multiset V) (x : V) (p : List V) : List V :=
  flipL U (lpart x p) ++ x :: flipR U (rpart x p)

theorem flipL_perm (U : Multiset V) (L : List V) : (flipL U L).Perm L := by
  unfold flipL; split_ifs
  · exact List.reverse_perm L
  · exact List.Perm.refl L

theorem flipR_perm (U : Multiset V) (R : List V) : (flipR U R).Perm R := by
  unfold flipR; split_ifs
  · exact List.reverse_perm R
  · exact List.Perm.refl R

theorem ms_walkEdges_flipL (U : Multiset V) (L : List V) :
    (walkEdges (flipL U L) : Multiset (Sym2 V)) = walkEdges L := by
  unfold flipL; split_ifs
  · exact ms_walkEdges_reverse L
  · rfl

theorem ms_walkEdges_flipR (U : Multiset V) (R : List V) :
    (walkEdges (flipR U R) : Multiset (Sym2 V)) = walkEdges R := by
  unfold flipR; split_ifs
  · exact ms_walkEdges_reverse R
  · rfl

theorem side_L (U : Multiset V) (x : V) (f : V → V) (L : List V)
    (hf : ∀ u h, L.getLast? = some u → L.head? = some h → u ∈ U → f u = h) :
    ((((flipL U L).getLast?.map fun a => s(a, x)).toList : List _) : Multiset (Sym2 V)) +
        (((attL U L).map fun u => s(x, u) : List _) : Multiset (Sym2 V)) =
      (((L.getLast?.map fun a => s(a, x)).toList : List _) : Multiset (Sym2 V)) +
        (((attL U L).map fun u => s(x, f u) : List _) : Multiset (Sym2 V)) := by
  cases hl : L.getLast? with
  | none =>
    have : L = [] := List.getLast?_eq_none_iff.1 hl
    subst this
    simp [flipL, attL]
  | some u =>
    have hne : L ≠ [] := by rintro rfl; simp at hl
    obtain ⟨h, hh⟩ : ∃ h, L.head? = some h := ⟨L.head hne, List.head?_eq_some_head hne⟩
    by_cases hu : u ∈ U
    · have hfl : flipL U L = L.reverse := by simp [flipL, hl, hu]
      have hat : attL U L = [u] := by simp [attL, hl, hu]
      rw [hfl, hat, List.getLast?_reverse, hh]
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil]
      rw [hf u h hl hh hu, Sym2.eq_swap (a := h), Sym2.eq_swap (a := u)]
      exact add_comm _ _
    · have hfl : flipL U L = L := by simp [flipL, hl, hu]
      have hat : attL U L = [] := by simp [attL, hl, hu]
      rw [hfl, hat, hl]
      simp

theorem side_R (U : Multiset V) (x : V) (f : V → V) (R : List V)
    (hf : ∀ u t, R.head? = some u → R.getLast? = some t → u ∈ U → f u = t) :
    ((((flipR U R).head?.map fun b => s(x, b)).toList : List _) : Multiset (Sym2 V)) +
        (((attR U R).map fun u => s(x, u) : List _) : Multiset (Sym2 V)) =
      (((R.head?.map fun b => s(x, b)).toList : List _) : Multiset (Sym2 V)) +
        (((attR U R).map fun u => s(x, f u) : List _) : Multiset (Sym2 V)) := by
  cases hh : R.head? with
  | none =>
    have : R = [] := List.head?_eq_none_iff.1 hh
    subst this
    simp [flipR, attR]
  | some u =>
    have hne : R ≠ [] := by rintro rfl; simp at hh
    obtain ⟨t, ht⟩ : ∃ t, R.getLast? = some t := ⟨R.getLast hne, List.getLast?_eq_some_getLast hne⟩
    by_cases hu : u ∈ U
    · have hfr : flipR U R = R.reverse := by simp [flipR, hh, hu]
      have hat : attR U R = [u] := by simp [attR, hh, hu]
      rw [hfr, hat, List.head?_reverse, ht]
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil]
      rw [hf u t hh ht hu]
      exact add_comm _ _
    · have hfr : flipR U R = R := by simp [flipR, hh, hu]
      have hat : attR U R = [] := by simp [attR, hh, hu]
      rw [hfr, hat, hh]
      simp

/-- The edges of `newX`. -/
theorem ms_newX (U : Multiset V) (x : V) (f : V → V) {p : List V} (hx : x ∈ p)
    (hfL : ∀ u h, (lpart x p).getLast? = some u → (lpart x p).head? = some h → u ∈ U → f u = h)
    (hfR : ∀ u t, (rpart x p).head? = some u → (rpart x p).getLast? = some t → u ∈ U →
      f u = t) :
    (walkEdges (newX U x p) : Multiset (Sym2 V)) +
        (((attL U (lpart x p) ++ attR U (rpart x p)).map fun u => s(x, u) : List _) :
          Multiset (Sym2 V)) =
      (walkEdges p : Multiset (Sym2 V)) +
        (((attL U (lpart x p) ++ attR U (rpart x p)).map fun u => s(x, f u) : List _) :
          Multiset (Sym2 V)) := by
  have hsplit := split_eq hx
  have e1 := side_L U x f (lpart x p) hfL
  have e2 := side_R U x f (rpart x p) hfR
  have hw : (walkEdges p : Multiset (Sym2 V)) =
      walkEdges (lpart x p ++ x :: rpart x p) := by rw [← hsplit]
  rw [hw]
  unfold newX
  rw [ms_walkEdges_split, ms_walkEdges_split, ms_walkEdges_flipL, ms_walkEdges_flipR]
  simp only [List.map_append, ← Multiset.coe_add]
  calc _ = (walkEdges (lpart x p) : Multiset (Sym2 V)) + walkEdges (rpart x p) +
        ((((flipL U (lpart x p)).getLast?.map fun a => s(a, x)).toList : List _) +
          (((attL U (lpart x p)).map fun u => s(x, u) : List _) : Multiset (Sym2 V))) +
        ((((flipR U (rpart x p)).head?.map fun b => s(x, b)).toList : List _) +
          (((attR U (rpart x p)).map fun u => s(x, u) : List _) : Multiset (Sym2 V))) := by abel
    _ = _ := by rw [e1, e2]; abel

/-! ### Appending `x` to a path avoiding it -/

theorem ms_walkEdges_concat_of {p : List V} {x ll : V} (hl : p.getLast? = some ll) :
    (walkEdges (p ++ [x]) : Multiset (Sym2 V)) = walkEdges p + {s(x, ll)} := by
  rw [walkEdges_concat, hl, ← Multiset.coe_add, Sym2.eq_swap]
  rfl

theorem ms_walkEdges_cons_of {p : List V} {x hh : V} (hh' : p.head? = some hh) :
    (walkEdges (x :: p) : Multiset (Sym2 V)) = walkEdges p + {s(x, hh)} := by
  rw [walkEdges_cons, hh', ← Multiset.coe_add, add_comm]
  rfl

theorem ms_cycleEdges_concat {p : List V} {x hh ll : V} (hh' : p.head? = some hh)
    (hl : p.getLast? = some ll) :
    (cycleEdges (p ++ [x]) : Multiset (Sym2 V)) = walkEdges p + {s(x, ll)} + {s(x, hh)} := by
  match p, hh' with
  | a :: t, hh' =>
    have ha : a = hh := by simpa using hh'
    subst ha
    rw [List.cons_append, cycleEdges_eq, ← List.cons_append, walkEdges_concat,
      List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast?_singleton]
    simp only [Option.map_some, Option.toList_some]
    rw [← Multiset.coe_add, ms_walkEdges_concat_of hl, Sym2.eq_swap (a := x)]
    rfl

/-! ### The replacement of one path -/

/-- `p` is chosen by a root whose leaf is the first vertex of `p`. -/
@[expose] def HdC (B : Finset V) (q : V → List V) (lf : V → V) (p : List V) : Prop :=
  ∃ b ∈ B, q b = p ∧ p.head? = some (lf b)

/-- `p` is chosen by a root whose leaf is the last vertex of `p`. -/
@[expose] def LtC (B : Finset V) (q : V → List V) (lf : V → V) (p : List V) : Prop :=
  ∃ b ∈ B, q b = p ∧ p.getLast? = some (lf b)

instance (B : Finset V) (q : V → List V) (lf : V → V) (p : List V) :
    Decidable (HdC B q lf p) :=
  inferInstanceAs (Decidable (∃ b ∈ B, q b = p ∧ p.head? = some (lf b)))

instance (B : Finset V) (q : V → List V) (lf : V → V) (p : List V) :
    Decidable (LtC B q lf p) :=
  inferInstanceAs (Decidable (∃ b ∈ B, q b = p ∧ p.getLast? = some (lf b)))

/-- The replacement `(new paths, new cycles)` of a path `p`. -/
@[expose] noncomputable def psi (U : Multiset V) (x : V) (B : Finset V) (q : V → List V)
    (lf : V → V) (p : List V) : List (List V) × List (List V) := by
  classical
  exact if x ∈ p then ([newX U x p], [])
    else if HdC B q lf p ∧ LtC B q lf p then ([], [p ++ [x]])
    else if LtC B q lf p then ([p ++ [x]], [])
    else if HdC B q lf p then ([x :: p], [])
    else ([p], [])

/-- The edge multiset of a pair `(paths, cycles)`. -/
@[expose] def pairMS (pc : List (List V) × List (List V)) : Multiset (Sym2 V) :=
  (pc.1.map fun p => (walkEdges p : Multiset (Sym2 V))).sum +
    (pc.2.map fun c => (cycleEdges c : Multiset (Sym2 V))).sum

theorem psi_length (U : Multiset V) (x : V) (B : Finset V) (q : V → List V) (lf : V → V)
    (p : List V) : (psi U x B q lf p).1.length + (psi U x B q lf p).2.length = 1 := by
  unfold psi
  split_ifs <;> rfl

theorem psi_of_mem {U : Multiset V} {x : V} {B : Finset V} {q : V → List V} {lf : V → V}
    {p : List V} (hx : x ∈ p) : psi U x B q lf p = ([newX U x p], []) := by
  unfold psi
  rw [if_pos hx]

theorem newX_perm (U : Multiset V) {x : V} {p : List V} (hx : x ∈ p) : (newX U x p).Perm p := by
  unfold newX
  conv_rhs => rw [split_eq hx]
  exact (flipL_perm U _).append ((flipR_perm U _).cons x)

theorem psi_valid {U : Multiset V} {x : V} {B : Finset V} {q : V → List V} {lf : V → V}
    {p : List V} (hp : 2 ≤ p.length ∧ p.Nodup) :
    (∀ p' ∈ (psi U x B q lf p).1, 2 ≤ p'.length ∧ p'.Nodup) ∧
      (∀ c ∈ (psi U x B q lf p).2, (Obj.cycle c).WF) := by
  by_cases hx : x ∈ p
  · rw [psi_of_mem hx]
    refine ⟨fun p' hp' => ?_, fun c hc => by simp at hc⟩
    rw [List.mem_singleton] at hp'
    subst hp'
    have hperm := newX_perm U hx
    exact ⟨hperm.length_eq ▸ hp.1, hperm.nodup_iff.2 hp.2⟩
  · have hnd1 : (p ++ [x]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hp.2, List.nodup_singleton x, fun a ha b hb hab => by
        rw [List.mem_singleton] at hb; subst hb; subst hab; exact hx ha⟩
    have hnd2 : (x :: p).Nodup := List.nodup_cons.2 ⟨hx, hp.2⟩
    have hl1 : 2 ≤ (p ++ [x]).length := by simp; omega
    have hl2 : 2 ≤ (x :: p).length := by simp; omega
    unfold psi
    rw [if_neg hx]
    split_ifs
    · refine ⟨fun p' hp' => by simp at hp', fun c hc => ?_⟩
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨hnd1, by simp; omega⟩
    · refine ⟨fun p' hp' => ?_, fun c hc => by simp at hc⟩
      rw [List.mem_singleton] at hp'; subst hp'; exact ⟨hl1, hnd1⟩
    · refine ⟨fun p' hp' => ?_, fun c hc => by simp at hc⟩
      rw [List.mem_singleton] at hp'; subst hp'; exact ⟨hl2, hnd2⟩
    · refine ⟨fun p' hp' => ?_, fun c hc => by simp at hc⟩
      rw [List.mem_singleton] at hp'; subst hp'; exact hp

/-- The sum of `{s(x, lf b)}` over the roots choosing `p` at its first vertex. -/
theorem sum_filter_head {B : Finset V} {q : V → List V} {lf : V → V} {p : List V} {x hh : V}
    (hh' : p.head? = some hh) (hinj : ∀ b ∈ B, ∀ b' ∈ B, lf b = lf b' → b = b') :
    (∑ b ∈ (B.filter fun b => q b = p).filter (fun b => p.head? = some (lf b)),
        ({s(x, lf b)} : Multiset (Sym2 V))) =
      if HdC B q lf p then ({s(x, hh)} : Multiset (Sym2 V)) else 0 := by
  classical
  set S := (B.filter fun b => q b = p).filter (fun b => p.head? = some (lf b)) with hS
  have hlf : ∀ b ∈ S, lf b = hh := by
    intro b hb
    rw [hS, Finset.mem_filter] at hb
    exact Option.some.inj (hb.2.symm.trans hh')
  by_cases hH : HdC B q lf p
  · rw [if_pos hH]
    obtain ⟨b, hb, hqb, hhb⟩ := hH
    have hbS : b ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_filter]; exact ⟨⟨hb, hqb⟩, hhb⟩
    have hSb : S = {b} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hbS, fun b' hb' => ?_⟩
      have hb'B : b' ∈ B := (Finset.mem_filter.1 (Finset.mem_filter.1 hb').1).1
      exact hinj b' hb'B b hb ((hlf b' hb').trans (hlf b hbS).symm)
    rw [hSb, Finset.sum_singleton, hlf b hbS]
  · rw [if_neg hH]
    have hSe : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro b hb
      rw [hS, Finset.mem_filter, Finset.mem_filter] at hb
      exact hH ⟨b, hb.1.1, hb.1.2, hb.2⟩
    rw [hSe, Finset.sum_empty]

theorem sum_filter_last {B : Finset V} {q : V → List V} {lf : V → V} {p : List V} {x ll : V}
    (hl' : p.getLast? = some ll) (hinj : ∀ b ∈ B, ∀ b' ∈ B, lf b = lf b' → b = b') :
    (∑ b ∈ (B.filter fun b => q b = p).filter (fun b => p.getLast? = some (lf b)),
        ({s(x, lf b)} : Multiset (Sym2 V))) =
      if LtC B q lf p then ({s(x, ll)} : Multiset (Sym2 V)) else 0 := by
  classical
  set S := (B.filter fun b => q b = p).filter (fun b => p.getLast? = some (lf b)) with hS
  have hlf : ∀ b ∈ S, lf b = ll := by
    intro b hb
    rw [hS, Finset.mem_filter] at hb
    exact Option.some.inj (hb.2.symm.trans hl')
  by_cases hL : LtC B q lf p
  · rw [if_pos hL]
    obtain ⟨b, hb, hqb, hlb⟩ := hL
    have hbS : b ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_filter]; exact ⟨⟨hb, hqb⟩, hlb⟩
    have hSb : S = {b} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hbS, fun b' hb' => ?_⟩
      have hb'B : b' ∈ B := (Finset.mem_filter.1 (Finset.mem_filter.1 hb').1).1
      exact hinj b' hb'B b hb ((hlf b' hb').trans (hlf b hbS).symm)
    rw [hSb, Finset.sum_singleton, hlf b hbS]
  · rw [if_neg hL]
    have hSe : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro b hb
      rw [hS, Finset.mem_filter, Finset.mem_filter] at hb
      exact hL ⟨b, hb.1.1, hb.1.2, hb.2⟩
    rw [hSe, Finset.sum_empty]

/-- The edges of the replacement of a path avoiding `x`. -/
theorem pairMS_psi_nonx (U : Multiset V) {x : V} {B : Finset V} {q : V → List V} {lf : V → V}
    {p : List V} (hx : x ∉ p) (hp : 2 ≤ p.length ∧ p.Nodup)
    (hB : ∀ b ∈ B, q b = p → p.head? = some (lf b) ∨ p.getLast? = some (lf b))
    (hinj : ∀ b ∈ B, ∀ b' ∈ B, lf b = lf b' → b = b') :
    pairMS (psi U x B q lf p) =
      (walkEdges p : Multiset (Sym2 V)) +
        ∑ b ∈ B.filter (fun b => q b = p), ({s(x, lf b)} : Multiset (Sym2 V)) := by
  classical
  obtain ⟨hh, hh'⟩ : ∃ hh, p.head? = some hh := by
    match p, hp with
    | a :: _, _ => exact ⟨a, rfl⟩
  obtain ⟨ll, hl'⟩ : ∃ ll, p.getLast? = some ll := by
    match p, hp with
    | a :: t, _ => exact ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil a t)⟩
  have hne : hh ≠ ll := by
    rintro rfl
    exact head_ne_getLast hp.2 hp.1 hh' hl'
  -- split the sum
  have hsplit : (∑ b ∈ B.filter (fun b => q b = p), ({s(x, lf b)} : Multiset (Sym2 V))) =
      (if HdC B q lf p then ({s(x, hh)} : Multiset (Sym2 V)) else 0) +
        (if LtC B q lf p then ({s(x, ll)} : Multiset (Sym2 V)) else 0) := by
    have h1 := Finset.sum_filter_add_sum_filter_not (B.filter fun b => q b = p)
      (fun b => p.head? = some (lf b)) (fun b => ({s(x, lf b)} : Multiset (Sym2 V)))
    rw [← h1, sum_filter_head hh' hinj, ← sum_filter_last hl' hinj]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hb, hqb⟩, hnh⟩
      exact ⟨⟨hb, hqb⟩, (hB b hb hqb).resolve_left hnh⟩
    · rintro ⟨⟨hb, hqb⟩, hlb⟩
      refine ⟨⟨hb, hqb⟩, fun hhb => hne ?_⟩
      exact Option.some.inj (hh'.symm.trans (hhb.trans (hlb.symm.trans hl')))
  rw [hsplit]
  unfold psi pairMS
  rw [if_neg hx]
  by_cases hH : HdC B q lf p <;> by_cases hL : LtC B q lf p
  · rw [if_pos ⟨hH, hL⟩, if_pos hH, if_pos hL]
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    rw [ms_cycleEdges_concat hh' hl']
    abel
  · rw [if_neg (fun h => hL h.2), if_neg hL, if_pos hH, if_pos hH, if_neg hL]
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]
    exact ms_walkEdges_cons_of hh'
  · rw [if_neg (fun h => hH h.1), if_pos hL, if_neg hH, if_pos hL]
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    exact ms_walkEdges_concat_of hl'
  · rw [if_neg (fun h => hH h.1), if_neg hL, if_neg hH, if_neg hH, if_neg hL]
    simp

/-! ### Bookkeeping lemmas -/

theorem exists_rel_of_mem_tail {R : V → V → Prop} :
    ∀ {l : List V}, List.IsChain R l → ∀ {u : V}, u ∈ l.tail → ∃ a, R a u
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: t, hl, u, h => by
    rw [List.isChain_cons_cons] at hl
    rw [List.tail_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨a, hl.1⟩
    · exact exists_rel_of_mem_tail hl.2 (by rw [List.tail_cons]; exact h)

theorem nodup_bind_of {B : Finset V} {g : V → List V} (hnd : ∀ b ∈ B, (g b).Nodup)
    (hdisj : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∀ v ∈ g b, v ∉ g b') :
    (B.val.bind fun b => (g b : Multiset V)).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro v
  rw [Multiset.count_bind]
  change (∑ b ∈ B, Multiset.count v (g b : Multiset V)) ≤ 1
  by_cases hex : ∃ b ∈ B, v ∈ g b
  · obtain ⟨b₀, hb₀, hv⟩ := hex
    rw [Finset.sum_eq_single b₀]
    · rw [Multiset.coe_count]
      exact List.nodup_iff_count_le_one.1 (hnd b₀ hb₀) v
    · intro b hb hne
      rw [Multiset.coe_count, List.count_eq_zero]
      exact hdisj b₀ hb₀ b hb (Ne.symm hne) v hv
    · intro h; exact absurd hb₀ h
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · omega
    · intro b hb
      rw [Multiset.coe_count, List.count_eq_zero]
      exact hex b hb

omit [DecidableEq V] in
theorem sum_map_multiset_map {W X : Type*} (P : List (List V)) (g : List V → Multiset W)
    (h : W → X) : (P.map fun p => (g p).map h).sum = ((P.map g).sum).map h := by
  induction P with
  | nil => simp
  | cons p P ih => simp [ih, Multiset.map_add]

theorem pcMS_flatMap (C P : List (List V)) (g : List V → List (List V) × List (List V)) :
    pcMS (P.flatMap fun p => (g p).1) (C ++ P.flatMap fun p => (g p).2) =
      (P.map fun p => pairMS (g p)).sum + (C.map fun c => (cycleEdges c : Multiset (Sym2 V))).sum := by
  induction P with
  | nil => simp [pcMS_eq]
  | cons p P ih =>
    rw [pcMS_eq] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      pairMS] at ih ⊢
    calc _ = ((g p).1.map fun p => (walkEdges p : Multiset (Sym2 V))).sum +
          ((g p).2.map fun c => (cycleEdges c : Multiset (Sym2 V))).sum +
          (((P.flatMap fun p => (g p).1).map fun p => (walkEdges p : Multiset (Sym2 V))).sum +
            ((C.map fun c => (cycleEdges c : Multiset (Sym2 V))).sum +
              ((P.flatMap fun p => (g p).2).map fun c => (cycleEdges c : Multiset (Sym2 V))).sum)) := by
          abel
      _ = _ := by rw [ih]; abel

/-! ### The global rebuild -/

/-- All attachments of `p` at `x` (none if `x ∉ p`). -/
@[expose] def allAtt (x : V) (p : List V) : List V :=
  if x ∈ p then (lpart x p).getLast?.toList ++ (rpart x p).head?.toList else []

/-- The attachments of `p` at `x` lying in `U`. -/
@[expose] def attIn (U : Multiset V) (x : V) (p : List V) : List V :=
  if x ∈ p then attL U (lpart x p) ++ attR U (rpart x p) else []

theorem attIn_eq_filter (U : Multiset V) (x : V) (p : List V) :
    attIn U x p = (allAtt x p).filter (fun u => decide (u ∈ U)) := by
  unfold attIn allAtt attL attR
  split_ifs <;> simp [List.filter_append]

theorem ms_allAtt_le {F : Finset (Sym2 V)} {P C : List (List V)}
    (_h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) (x : V) (p : List V) :
    (((allAtt x p).map fun u => s(x, u) : List _) : Multiset (Sym2 V)) ≤ walkEdges p := by
  unfold allAtt
  split_ifs with hx
  · have hw : (walkEdges p : Multiset (Sym2 V)) =
        walkEdges (lpart x p ++ x :: rpart x p) := by rw [← split_eq hx]
    rw [hw, ms_walkEdges_split]
    have e : ((((lpart x p).getLast?.toList ++ (rpart x p).head?.toList).map
        fun u => s(x, u) : List _) : Multiset (Sym2 V)) =
        (((lpart x p).getLast?.map fun a => s(a, x)).toList : List _) +
          (((rpart x p).head?.map fun b => s(x, b)).toList : List _) := by
      rw [List.map_append, ← Multiset.coe_add]
      congr 2
      · cases (lpart x p).getLast? <;> simp [Sym2.eq_swap]
      · cases (rpart x p).head? <;> simp
    rw [e, add_assoc]
    exact le_add_left le_rfl
  · simp

theorem sum_attIn {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x : V} {U : Multiset V}
    (hUnd : U.Nodup) (hUarm : ∀ u ∈ U, ∃ a, ArmTo P x u a) :
    (P.map fun p => (attIn U x p : Multiset V)).sum = U := by
  -- the multiset of all attachments is duplicate free
  have hA : ((P.flatMap (allAtt x) : List V) : Multiset V).Nodup := by
    have hle : (((P.flatMap (allAtt x)).map fun u => s(x, u) : List _) : Multiset (Sym2 V)) ≤
        pcMS P C := by
      rw [List.map_flatMap, coe_flatMap, pcMS_eq]
      refine le_trans ?_ (le_add_right le_rfl)
      exact List.sum_le_sum (fun p _ => ms_allAtt_le h x p)
    have hnd : (pcMS P C).Nodup := nodup_pcMS.2 h.2.2.1
    have := Multiset.nodup_of_le hle hnd
    rw [← Multiset.map_coe] at this
    exact Multiset.Nodup.of_map _ this
  have hsum : (P.map fun p => (attIn U x p : Multiset V)).sum =
      (((P.flatMap (attIn U x)) : List V) : Multiset V) := by
    rw [coe_flatMap]
  rw [hsum]
  have hflt : P.flatMap (attIn U x) = (P.flatMap (allAtt x)).filter (fun u => decide (u ∈ U)) := by
    rw [List.filter_flatMap]
    congr 1
    funext p
    exact attIn_eq_filter U x p
  refine Multiset.Nodup.ext ?_ hUnd |>.2 ?_
  · rw [hflt]
    exact Multiset.Nodup.filter _ hA
  · intro u
    rw [Multiset.mem_coe, hflt, List.mem_filter, decide_eq_true_eq]
    refine ⟨fun h' => h'.2, fun hu => ⟨?_, hu⟩⟩
    obtain ⟨a, p, hp, L, R, hpLR, hs⟩ := hUarm u hu
    have hxp : x ∈ p := by rw [hpLR]; simp
    have hpn : (L ++ x :: R).Nodup := hpLR ▸ (h.1 p hp).2
    have hL : lpart x p = L := by rw [hpLR]; exact lpart_append (not_mem_of_nodup_split hpn) R
    have hR : rpart x p = R := by rw [hpLR]; exact rpart_append (not_mem_of_nodup_split hpn) R
    refine List.mem_flatMap.2 ⟨p, hp, ?_⟩
    unfold allAtt
    rw [if_pos hxp, hL, hR]
    rcases hs with ⟨hs, -⟩ | ⟨hs, -⟩
    · rw [hs]; simp
    · rw [hs]; simp

theorem sum_roots {P : List (List V)} (hPnd : P.Nodup) {B : Finset V} {q : V → List V}
    (hq : ∀ b ∈ B, q b ∈ P) {W : Type*} (g : V → W) :
    (P.map fun p => ∑ b ∈ B.filter (fun b => q b = p), ({g b} : Multiset W)).sum = B.val.map g := by
  rw [← List.sum_toFinset _ hPnd, Finset.sum_fiberwise_of_maps_to
    (fun b hb => List.mem_toFinset.2 (hq b hb))]
  rw [Finset.sum_eq_multiset_sum]
  have e : (fun i => ({g i} : Multiset W)) = (fun w => ({w} : Multiset W)) ∘ g := rfl
  rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]

theorem telescope {P : List (List V)} {x : V} {B : Finset V} {l : V → List V}
    (hl1 : ∀ b ∈ B, (l b).head? = some b)
    (hl2 : ∀ b ∈ B, List.IsChain (ChainRel P x) (l b)) :
    (B.val.bind fun b => (((l b).tail : List V) : Multiset V)).map (fun u => (succ P x u).getD u) +
        B.val.map (fun b => (l b).getLast?.getD b) =
      (B.val.bind fun b => (((l b).tail : List V) : Multiset V)) + B.val := by
  have hB : B.val = B.val.bind (fun b => ({b} : Multiset V)) := by
    rw [Multiset.bind_singleton, Multiset.map_id']
  rw [Multiset.map_bind, ← Multiset.bind_singleton B.val (fun b => (l b).getLast?.getD b),
    ← Multiset.bind_add]
  conv_rhs => arg 2; rw [hB]
  rw [← Multiset.bind_add]
  refine Multiset.bind_congr (fun b hb => ?_)
  have hb' : b ∈ B := hb
  obtain ⟨t, ht⟩ : ∃ t, l b = b :: t := by
    have := hl1 b hb'
    cases h : l b with
    | nil => rw [h] at this; simp at this
    | cons a t => rw [h] at this; exact ⟨t, by simpa using this⟩
  have hmap := chain_tail_map (P := P) (x := x) (fun u => (succ P x u).getD u)
    (fun u a hu => by simp [hu]) (hl2 b hb')
  rw [Multiset.map_coe, hmap]
  have hne : l b ≠ [] := by rw [ht]; exact List.cons_ne_nil _ _
  rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
  have e1 : (((l b).dropLast : List V) : Multiset V) + {(l b).getLast hne} = (l b : Multiset V) := by
    conv_rhs => rw [← List.dropLast_append_getLast hne]
    rw [← Multiset.coe_add]
    rfl
  rw [e1, ht, List.tail_cons]
  rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]

theorem flatMap_psi_length (U : Multiset V) (x : V) (B : Finset V) (q : V → List V) (lf : V → V)
    (P : List (List V)) :
    (P.flatMap fun p => (psi U x B q lf p).1).length +
      (P.flatMap fun p => (psi U x B q lf p).2).length = P.length := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := psi_length U x B q lf p
    omega

/-- The rebuild: reversing the arms along the chains and attaching `x` to the chosen paths. -/
theorem rebuild {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x : V} {B : Finset V}
    (hBF : ∀ b ∈ B, s(x, b) ∉ F) (l q : V → List V)
    (hl1 : ∀ b ∈ B, (l b).head? = some b)
    (hl2 : ∀ b ∈ B, List.IsChain (ChainRel P x) (l b))
    (hq : ∀ b ∈ B, q b ∈ P ∧ x ∉ q b ∧
      ((q b).head? = (l b).getLast? ∨ (q b).getLast? = (l b).getLast?))
    (hlnd : ∀ b ∈ B, (l b).Nodup)
    (hldisj : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∀ v ∈ l b, v ∉ l b') :
    ∃ P' C' : List (List V), IsPathCycleDecomp
      (((F ∪ B.image fun b => s(x, b)) : Finset (Sym2 V)) : Set (Sym2 V)) P' C' ∧
      P'.length + C'.length = P.length + C.length := by
  classical
  set U : Multiset V := B.val.bind fun b => (((l b).tail : List V) : Multiset V) with hU
  set lf : V → V := fun b => (l b).getLast?.getD b with hlf
  set f : V → V := fun u => (succ P x u).getD u with hf
  have hleaf : ∀ b ∈ B, (l b).getLast? = some (lf b) := by
    intro b hb
    have hne : l b ≠ [] := by
      intro h0; have := hl1 b hb; rw [h0] at this; simp at this
    rw [hlf]
    simp only
    rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
  have hinj : ∀ b ∈ B, ∀ b' ∈ B, lf b = lf b' → b = b' := by
    intro b hb b' hb' he
    by_contra hne
    have h1 : lf b ∈ l b := List.mem_of_getLast? (hleaf b hb)
    have h2 : lf b' ∈ l b' := List.mem_of_getLast? (hleaf b' hb')
    rw [← he] at h2
    exact hldisj b hb b' hb' hne _ h1 h2
  have hUnd : U.Nodup := nodup_bind_of (g := fun b => (l b).tail)
    (fun b hb => (hlnd b hb).sublist (List.tail_sublist _))
    (fun b hb b' hb' hne v hv hv' => hldisj b hb b' hb' hne v (List.mem_of_mem_tail hv)
      (List.mem_of_mem_tail hv'))
  have hUarm : ∀ u ∈ U, ∃ a, ArmTo P x u a := by
    intro u hu
    obtain ⟨b, hb, hub⟩ := Multiset.mem_bind.1 hu
    obtain ⟨a, ha⟩ := exists_rel_of_mem_tail (hl2 b hb) (Multiset.mem_coe.1 hub)
    exact ⟨a, (succ_eq_some h).1 ha⟩
  have hPnd : P.Nodup := nodup_P h
  set g := psi U x B q lf with hg
  set sx : V → Sym2 V := fun v => s(x, v) with hsx
  set E : List V → Multiset (Sym2 V) :=
    fun p => ∑ b ∈ B.filter (fun b => q b = p), ({sx (lf b)} : Multiset (Sym2 V)) with hE
  -- the identity for one path
  have hper : ∀ p ∈ P, pairMS (g p) + (((attIn U x p).map sx : List _) : Multiset (Sym2 V)) =
      (walkEdges p : Multiset (Sym2 V)) +
        (((attIn U x p).map (sx ∘ f) : List _) : Multiset (Sym2 V)) + E p := by
    intro p hp
    by_cases hx : x ∈ p
    · have hE0 : E p = 0 := by
        rw [hE]
        simp only
        rw [Finset.sum_eq_zero]
        intro b hb
        rw [Finset.mem_filter] at hb
        exact absurd (hb.2 ▸ hx) (hq b hb.1).2.1
      rw [hE0, add_zero, hg, psi_of_mem hx]
      unfold attIn
      rw [if_pos hx]
      simp only [pairMS, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hfL : ∀ u hh, (lpart x p).getLast? = some u → (lpart x p).head? = some hh →
          u ∈ U → f u = hh := by
        intro u hh hu hhh _
        have ha : ArmTo P x u hh :=
          ⟨p, hp, lpart x p, rpart x p, split_eq hx, Or.inr ⟨hu, hhh⟩⟩
        rw [hf]; simp only; rw [(succ_eq_some h).2 ha, Option.getD_some]
      have hfR : ∀ u t, (rpart x p).head? = some u → (rpart x p).getLast? = some t →
          u ∈ U → f u = t := by
        intro u t hu ht _
        have ha : ArmTo P x u t :=
          ⟨p, hp, lpart x p, rpart x p, split_eq hx, Or.inl ⟨hu, ht⟩⟩
        rw [hf]; simp only; rw [(succ_eq_some h).2 ha, Option.getD_some]
      exact ms_newX U x f hx hfL hfR
    · have hat : attIn U x p = [] := by unfold attIn; rw [if_neg hx]
      rw [hat, List.map_nil, List.map_nil, Multiset.coe_nil, add_zero, add_zero, hg]
      refine pairMS_psi_nonx U hx (h.1 p hp) ?_ hinj
      intro b hb hqb
      rw [← hqb, ← hleaf b hb]
      exact (hq b hb).2.2
  -- summing over `P`
  have hsum : (P.map fun p => pairMS (g p)).sum + U.map sx =
      (P.map fun p => (walkEdges p : Multiset (Sym2 V))).sum + U.map (sx ∘ f) +
        B.val.map (sx ∘ lf) := by
    have h1 : (P.map fun p => pairMS (g p) +
        (((attIn U x p).map sx : List _) : Multiset (Sym2 V))).sum =
        (P.map fun p => (walkEdges p : Multiset (Sym2 V)) +
          (((attIn U x p).map (sx ∘ f) : List _) : Multiset (Sym2 V)) + E p).sum :=
      congrArg List.sum (List.map_congr_left hper)
    rw [List.sum_map_add, List.sum_map_add, List.sum_map_add] at h1
    have hA1 : (P.map fun p => (((attIn U x p).map sx : List _) : Multiset (Sym2 V))).sum =
        U.map sx := by
      simp_rw [← Multiset.map_coe]
      rw [sum_map_multiset_map, sum_attIn h hUnd hUarm]
    have hA2 : (P.map fun p => (((attIn U x p).map (sx ∘ f) : List _) : Multiset (Sym2 V))).sum =
        U.map (sx ∘ f) := by
      simp_rw [← Multiset.map_coe]
      rw [sum_map_multiset_map, sum_attIn h hUnd hUarm]
    have hC : (P.map E).sum = B.val.map (sx ∘ lf) := by
      rw [hE]
      exact sum_roots hPnd (fun b hb => (hq b hb).1) (sx ∘ lf)
    rw [hA1, hA2, hC] at h1
    exact h1
  have htel := congrArg (Multiset.map sx) (telescope (P := P) (x := x) hl1 hl2)
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_map, Multiset.map_map] at htel
  have hcancel : (P.map fun p => pairMS (g p)).sum =
      (P.map fun p => (walkEdges p : Multiset (Sym2 V))).sum + B.val.map sx := by
    have := hsum
    rw [add_assoc, htel] at this
    have h2 : (P.map fun p => pairMS (g p)).sum + U.map sx =
        ((P.map fun p => (walkEdges p : Multiset (Sym2 V))).sum + B.val.map sx) + U.map sx := by
      rw [this]; abel
    exact add_right_cancel h2
  refine ⟨P.flatMap (fun p => (g p).1), C ++ P.flatMap (fun p => (g p).2), ?_, ?_⟩
  · refine isPCD_of_ms_add h ?_ ?_ ?_ ?_
    · intro p' hp'
      obtain ⟨p, hp, hp'⟩ := List.mem_flatMap.1 hp'
      exact (psi_valid (h.1 p hp)).1 p' hp'
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact h.2.1 c hc
      · obtain ⟨p, hp, hc⟩ := List.mem_flatMap.1 hc
        exact (psi_valid (h.1 p hp)).2 c hc
    · rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he'
      exact hBF b hb he
    · rw [pcMS_flatMap, hcancel, pcMS_eq,
        Finset.image_val_of_injOn (fun a _ b _ hab => Sym2.congr_right.1 hab)]
      abel
  · rw [List.length_append]
    have := flatMap_psi_length U x B q lf P
    rw [hg]
    omega

/-! ### The attachment lemma -/

/-- **Attachment lemma.** If every neighbour of `x` in `F ∪ {xb : b ∈ B}` is an end of a path of
a decomposition `(P, C)` of `F` (where `xb ∉ F` for `b ∈ B`), then `F ∪ {xb : b ∈ B}` has a
decomposition with as many elements. -/
theorem attach {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x : V} {B : Finset V}
    (hxB : x ∉ B) (hBF : ∀ b ∈ B, s(x, b) ∉ F)
    (hend : ∀ v, (s(x, v) ∈ F ∨ v ∈ B) → ∃ p ∈ P, p.head? = some v ∨ p.getLast? = some v) :
    ∃ P' C' : List (List V), IsPathCycleDecomp
      (((F ∪ B.image fun b => s(x, b)) : Finset (Sym2 V)) : Set (Sym2 V)) P' C' ∧
      P'.length + C'.length = P.length + C.length := by
  classical
  have hroot : ∀ b ∈ B, succ P x b = none := by
    intro b hb
    cases hs : succ P x b with
    | none => rfl
    | some t => exact absurd (armTo_mem h ((succ_eq_some h).1 hs)) (hBF b hb)
  have hreach : ∀ b ∈ B, ∀ t, Reach P x t b → t ≠ x ∧
      ∃ p ∈ P, p.head? = some t ∨ p.getLast? = some t := by
    intro b hb t ⟨k, hk⟩
    have hcase : s(x, t) ∈ F ∨ t ∈ B := by
      cases k with
      | zero => exact Or.inr ((Option.some.inj hk) ▸ hb)
      | succ k =>
        left
        rw [Nat.add_comm, iterS_add, iterS_one] at hk
        cases hs : succ P x t with
        | none => rw [hs] at hk; simp at hk
        | some a => exact armTo_mem h ((succ_eq_some h).1 hs)
    refine ⟨?_, hend t hcase⟩
    rcases hcase with hc | hc
    · rintro rfl; exact not_isDiag_of_isPCD h hc (Sym2.mk_isDiag_iff.2 rfl)
    · rintro rfl; exact hxB hc
  have hch : ∀ b, b ∈ B → ∃ l : List V, l.head? = some b ∧ List.IsChain (ChainRel P x) l ∧
      ∃ c, l.getLast? = some c ∧ Live P x c :=
    fun b hb => exists_chain h (hroot b hb) (hreach b hb)
  choose! l hl1 hl2 c hc hlive using hch
  have hq' : ∀ b, b ∈ B → ∃ q : List V, q ∈ P ∧ x ∉ q ∧
      (q.head? = (l b).getLast? ∨ q.getLast? = (l b).getLast?) := by
    intro b hb
    obtain ⟨q, hq, hxq, hqe⟩ := hlive b hb
    rw [hc b hb]
    exact ⟨q, hq, hxq, hqe⟩
  choose! q hq1 hq2 hq3 using hq'
  have hreachl : ∀ b ∈ B, ∀ v ∈ l b, Reach P x v b := fun b hb v hv =>
    chain_reach (hl2 b hb) (hl1 b hb) v hv
  exact rebuild h hBF l q hl1 hl2 (fun b hb => ⟨hq1 b hb, hq2 b hb, hq3 b hb⟩)
    (fun b hb => chain_nodup (hroot b hb) (hl2 b hb) (hreachl b hb))
    (fun b hb b' hb' hne v hv hv' => by
      obtain ⟨k, hk⟩ := hreachl b hb v hv
      obtain ⟨k', hk'⟩ := hreachl b' hb' v hv'
      exact hne (reach_root_unique (hroot b hb) (hroot b' hb') hk hk').2)

end Lov

end EG
```
