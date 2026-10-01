module

public import EG.Lib.Ext.LovaszLists

/-!
# The Lovász construction (manuscript s1:citThm21)

Lemma `EG.LovaszC.lovasz_construction`: let `(P, C)` be a path-and-cycle decomposition of an edge
set `F`, `x` a vertex and `Z` a set of vertices with `x ∉ Z` and `s(x, z) ∉ F` for `z ∈ Z`, such that
every vertex of `Z ∪ N_F(x)` is an end of some path of `P`. Then `F ∪ {s(x, z) : z ∈ Z}` has a
path-and-cycle decomposition with `|P| + |C|` members.

This is Lovász's construction (L. Lovász, *On covering of graphs*, 1968), as reproduced in
L. Yan, *On path decompositions of graphs*, PhD thesis, Arizona State University, 1998, §2.1
("Lovász construction"); see `formal/work/p3/lovasz.md`.

Construction. Each `v ∈ N := Z ∪ N_F(x)` gets a designated path `des v` of `P` ending at `v`
(`orient v`: that path traversed from `v`). `nxt v` is the vertex before `x` on `orient v` (none if
`x` is not on it). `Reach v`: `v` is reached from `Z` by iterating `nxt`. A path `U = P[i]` is
*labelled* at an end `a` if `Reach a` and `des a = i`. The output for `U` (`out i`):
* `x ∈ U`, `U = A ++ x :: B`: the path `A' ++ x :: B'` with `A' = A.reverse` if the head is
  labelled, `B' = B.reverse` if the last vertex is labelled (`reroute`);
* `x ∉ U`: `x :: U`, `U ++ [x]`, the cycle `U ++ [x]`, or `U`, according to the labels.
Its edges are those of `U`, minus the edges `s(x, nxt a)`, plus the edges `s(x, a)`, for the labels
`a` of `U` (`mem_oedges_out`). Globally the removed edges are `s(x, b)` for `b` reached and not in
`Z` (each is added back at `des b`), and the added ones are `s(x, a)` for all reached `a`.
-/

public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EG

namespace LovaszC

variable {V : Type*} [DecidableEq V]

section Construction

variable (P : List (List V)) (x : V) (des : V → ℕ) (Z : Finset V)

/-- The `i`-th path of `P` (`[]` if `i` is out of range). -/
def pth (i : ℕ) : List V := P.getD i []

/-- The designated path of `v` traversed from `v`. -/
def orient (v : V) : List V :=
  if (pth P (des v)).head? = some v then pth P (des v) else (pth P (des v)).reverse

/-- The vertex before `x` on the designated path of `v` traversed from `v`. -/
def nxt (v : V) : Option V :=
  if x ∈ orient P des v then (pre x (orient P des v)).getLast? else none

/-- Iterates of `nxt`. -/
def iter : ℕ → V → Option V
  | 0, v => some v
  | k + 1, v => (iter k v).bind (nxt P x des)

/-- `v` is reached from `Z` by iterating `nxt` (the entries of the Lovász sequences). -/
def Reach (v : V) : Prop := ∃ z ∈ Z, ∃ k, iter P x des k z = some v

/-- The head of `P[i]` is a label of `P[i]`. -/
def Lab₁ (i : ℕ) : Prop := ∃ a, (pth P i).head? = some a ∧ Reach P x des Z a ∧ des a = i

/-- The last vertex of `P[i]` is a label of `P[i]`. -/
def Lab₂ (i : ℕ) : Prop := ∃ a, (pth P i).getLast? = some a ∧ Reach P x des Z a ∧ des a = i

open Classical in
/-- The output of the construction for `P[i]`: a list and whether it is a cycle. -/
noncomputable def out (i : ℕ) : List V × Bool :=
  if x ∈ pth P i then
    (reroute x (pth P i) (decide (Lab₁ P x des Z i)) (decide (Lab₂ P x des Z i)), false)
  else if Lab₁ P x des Z i ∧ Lab₂ P x des Z i then (pth P i ++ [x], true)
  else if Lab₁ P x des Z i then (x :: pth P i, false)
  else if Lab₂ P x des Z i then (pth P i ++ [x], false)
  else (pth P i, false)

end Construction

theorem pth_eq {P : List (List V)} {i : ℕ} (hi : i < P.length) : pth P i = P[i] := by
  simp [pth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The edges of an output (a path or a cycle). -/
def oedges (o : List V × Bool) : List (Sym2 V) := if o.2 then cycleEdges o.1 else walkEdges o.1

/-- The hypotheses of the construction. `des v` is a path of `P` ending at `v`, for `v ∈ Z ∪ N_F(x)`. -/
structure Hyp (F : Finset (Sym2 V)) (P C : List (List V)) (x : V) (Z : Finset V) (des : V → ℕ) :
    Prop where
  dec : IsPathCycleDecomp (F : Set (Sym2 V)) P C
  xZ : x ∉ Z
  ZF : ∀ z ∈ Z, s(x, z) ∉ F
  des_lt : ∀ v, (v ∈ Z ∨ s(x, v) ∈ F) → des v < P.length
  des_end : ∀ v, (v ∈ Z ∨ s(x, v) ∈ F) →
    (pth P (des v)).head? = some v ∨ (pth P (des v)).getLast? = some v

namespace Hyp

variable {F : Finset (Sym2 V)} {P C : List (List V)} {x : V} {Z : Finset V} {des : V → ℕ}
  (h : Hyp F P C x Z des)
include h

theorem pth_mem {i : ℕ} (hi : i < P.length) : pth P i ∈ P := by
  rw [pth_eq hi]
  exact List.getElem_mem hi

theorem pth_valid {i : ℕ} (hi : i < P.length) : 2 ≤ (pth P i).length ∧ (pth P i).Nodup :=
  h.dec.1 _ (h.pth_mem hi)

theorem walk_F {i : ℕ} (hi : i < P.length) {e : Sym2 V} (he : e ∈ walkEdges (pth P i)) :
    e ∈ F := by
  have := (h.dec.2.2.2 e).1 (List.mem_append_left _ (List.mem_flatMap.2 ⟨_, h.pth_mem hi, he⟩))
  exact_mod_cast this

omit [DecidableEq V] in
theorem cyc_F {e : Sym2 V} (he : e ∈ C.flatMap cycleEdges) : e ∈ F := by
  have := (h.dec.2.2.2 e).1 (List.mem_append_right _ he)
  exact_mod_cast this

theorem F_cases {e : Sym2 V} (he : e ∈ F) :
    (∃ i, i < P.length ∧ e ∈ walkEdges (pth P i)) ∨ e ∈ C.flatMap cycleEdges := by
  have := (h.dec.2.2.2 e).2 (by exact_mod_cast he)
  rcases List.mem_append.1 this with h1 | h1
  · obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 h1
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    refine Or.inl ⟨i, hi, ?_⟩
    rwa [pth_eq hi]
  · exact Or.inr h1

theorem walk_not_cyc {i : ℕ} (hi : i < P.length) {e : Sym2 V} (he : e ∈ walkEdges (pth P i))
    (hc : e ∈ C.flatMap cycleEdges) : False := by
  have hnd := h.dec.2.2.1
  rw [List.nodup_append] at hnd
  exact hnd.2.2 e (List.mem_flatMap.2 ⟨_, h.pth_mem hi, he⟩) e hc rfl

/-- Distinct paths of `P` have no common edge. -/
theorem walk_disj {i j : ℕ} (hi : i < P.length) (hj : j < P.length) {e : Sym2 V}
    (h1 : e ∈ walkEdges (pth P i)) (h2 : e ∈ walkEdges (pth P j)) : i = j := by
  have hnd := (List.nodup_append.1 h.dec.2.2.1).1
  rw [List.nodup_flatMap] at hnd
  have hpw := List.pairwise_iff_getElem.1 hnd.2
  rw [pth_eq hi] at h1
  rw [pth_eq hj] at h2
  by_contra hij
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.disjoint_left.1 (hpw i j hi hj hlt) h1 h2
  · exact List.disjoint_left.1 (hpw j i hj hi hlt) h2 h1

theorem loopless {e : Sym2 V} (he : e ∈ F) : ¬ e.IsDiag := by
  rcases h.F_cases he with ⟨i, hi, hei⟩ | hc
  · exact not_isDiag_of_mem_walkEdges (h.pth_valid hi).2 hei
  · obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 hc
    obtain ⟨hnd, h3⟩ := h.dec.2.1 c hc
    exact not_isDiag_of_mem_cycleEdges hnd (by omega) hec

theorem N_ne {v : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) : v ≠ x := by
  rintro rfl
  rcases hv with hv | hv
  · exact h.xZ hv
  · exact h.loopless hv (Sym2.mk_isDiag_iff.2 rfl)

end Hyp

/-! ### Orientation and `nxt` -/

theorem head_ne_last {U : List V} (hU : U.Nodup) (h2 : 2 ≤ U.length) {a : V}
    (hh : U.head? = some a) (hl : U.getLast? = some a) : False :=
  Cor22.head_ne_getLast hU h2 hh hl

theorem orient_of_head {P : List (List V)} {des : V → ℕ} {v : V}
    (hh : (pth P (des v)).head? = some v) : orient P des v = pth P (des v) := by
  simp [orient, hh]

theorem orient_of_last {P : List (List V)} {des : V → ℕ} {v : V}
    (hv : (pth P (des v)).Nodup ∧ 2 ≤ (pth P (des v)).length)
    (hl : (pth P (des v)).getLast? = some v) : orient P des v = (pth P (des v)).reverse := by
  have hh : ¬ (pth P (des v)).head? = some v := fun hh => head_ne_last hv.1 hv.2 hh hl
  simp [orient, hh]

namespace Hyp

variable {F : Finset (Sym2 V)} {P C : List (List V)} {x : V} {Z : Finset V} {des : V → ℕ}
  (h : Hyp F P C x Z des)
include h

theorem orient_eq {v : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) :
    orient P des v = pth P (des v) ∨ orient P des v = (pth P (des v)).reverse := by
  unfold orient
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orient_head {v : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) : (orient P des v).head? = some v := by
  rcases h.des_end v hv with hh | hl
  · rw [orient_of_head hh, hh]
  · have hval := h.pth_valid (h.des_lt v hv)
    rw [orient_of_last ⟨hval.2, hval.1⟩ hl, List.head?_reverse, hl]

theorem mem_orient_iff {v : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) {u : V} :
    u ∈ orient P des v ↔ u ∈ pth P (des v) := by
  rcases h.orient_eq hv with h1 | h1 <;> rw [h1]
  exact List.mem_reverse

theorem mem_walkEdges_orient {v : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) {e : Sym2 V} :
    e ∈ walkEdges (orient P des v) ↔ e ∈ walkEdges (pth P (des v)) := by
  rcases h.orient_eq hv with h1 | h1 <;> rw [h1]
  exact mem_walkEdges_reverse

theorem orient_nodup {v : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) : (orient P des v).Nodup := by
  have hval := h.pth_valid (h.des_lt v hv)
  rcases h.orient_eq hv with h1 | h1 <;> rw [h1]
  · exact hval.2
  · exact List.nodup_reverse.2 hval.2

/-- The edge from `x` to `nxt v` lies on the designated path of `v`. -/
theorem nxt_edge {v b : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) (hb : nxt P x des v = some b) :
    s(x, b) ∈ walkEdges (pth P (des v)) := by
  unfold nxt at hb
  split_ifs at hb with hx
  rw [← h.mem_walkEdges_orient hv, mem_walkEdges_split hx]
  exact Or.inr (Or.inl ⟨b, hb, Sym2.eq_swap⟩)

theorem nxt_F {v b : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) (hb : nxt P x des v = some b) :
    s(x, b) ∈ F :=
  h.walk_F (h.des_lt v hv) (h.nxt_edge hv hb)

theorem nxt_N {v b : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) (hb : nxt P x des v = some b) :
    b ∈ Z ∨ s(x, b) ∈ F :=
  Or.inr (h.nxt_F hv hb)

theorem nxt_notZ {v b : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) (hb : nxt P x des v = some b) : b ∉ Z :=
  fun hz => h.ZF b hz (h.nxt_F hv hb)

/-- `nxt` on the head of a path it is designated for. -/
theorem nxt_of_head {i : ℕ} {a : V} (ha : a ∈ Z ∨ s(x, a) ∈ F) (hd : des a = i)
    (hh : (pth P i).head? = some a) :
    nxt P x des a = if x ∈ pth P i then (pre x (pth P i)).getLast? else none := by
  subst hd
  unfold nxt
  rw [orient_of_head hh]

/-- `nxt` on the last vertex of a path it is designated for. -/
theorem nxt_of_last {i : ℕ} {a : V} (ha : a ∈ Z ∨ s(x, a) ∈ F) (hd : des a = i)
    (hl : (pth P i).getLast? = some a) :
    nxt P x des a = if x ∈ pth P i then (post x (pth P i)).head? else none := by
  subst hd
  have hval := h.pth_valid (h.des_lt a ha)
  unfold nxt
  rw [orient_of_last ⟨hval.2, hval.1⟩ hl]
  by_cases hx : x ∈ pth P (des a)
  · rw [if_pos (List.mem_reverse.2 hx), if_pos hx, (pre_reverse hval.2 hx).1, List.getLast?_reverse]
  · rw [if_neg (fun h' => hx (List.mem_reverse.1 h')), if_neg hx]

/-- `nxt` is injective. -/
theorem nxt_inj {v w b : V} (hv : v ∈ Z ∨ s(x, v) ∈ F) (hw : w ∈ Z ∨ s(x, w) ∈ F)
    (h1 : nxt P x des v = some b) (h2 : nxt P x des w = some b) : v = w := by
  have e1 := h.nxt_edge hv h1
  have e2 := h.nxt_edge hw h2
  have hij := h.walk_disj (h.des_lt v hv) (h.des_lt w hw) e1 e2
  by_contra hvw
  set i := des v with hi
  have hval := h.pth_valid (h.des_lt v hv)
  -- `v` and `w` are the two ends of `P[i]`
  have key : ∀ {a c : V}, (a ∈ Z ∨ s(x, a) ∈ F) → (c ∈ Z ∨ s(x, c) ∈ F) → des a = i →
      des c = i → (pth P i).head? = some a → (pth P i).getLast? = some c →
      nxt P x des a = some b → nxt P x des c = some b → False := by
    intro a c ha hc hda hdc hh hl ha' hc'
    rw [h.nxt_of_head ha hda hh] at ha'
    rw [h.nxt_of_last hc hdc hl] at hc'
    split_ifs at ha' with hx
    rw [if_pos hx] at hc'
    exact pre_post_disjoint hval.2 hx (List.mem_of_getLast? ha') (List.mem_of_mem_head? hc')
  have hdw : des w = i := hij.symm
  rcases h.des_end v hv with hvh | hvl <;> rcases h.des_end w hw with hwh | hwl
  · rw [← hi] at hvh; rw [hdw] at hwh
    exact hvw (Option.some.inj (hvh.symm.trans hwh))
  · rw [← hi] at hvh; rw [hdw] at hwl
    exact key hv hw rfl hdw hvh hwl h1 h2
  · rw [← hi] at hvl; rw [hdw] at hwh
    exact key hw hv hdw rfl hwh hvl h2 h1
  · rw [← hi] at hvl; rw [hdw] at hwl
    exact hvw (Option.some.inj (hvl.symm.trans hwl))

/-! ### Reached vertices -/

theorem reach_of_mem {z : V} (hz : z ∈ Z) : Reach P x des Z z := ⟨z, hz, 0, rfl⟩

theorem reach_nxt {a b : V} (ha : Reach P x des Z a) (hb : nxt P x des a = some b) :
    Reach P x des Z b := by
  obtain ⟨z, hz, k, hk⟩ := ha
  exact ⟨z, hz, k + 1, by simp [iter, hk, hb]⟩

theorem iter_N {z : V} (hz : z ∈ Z) : ∀ k {v : V}, iter P x des k z = some v →
    v ∈ Z ∨ s(x, v) ∈ F
  | 0, v, hk => by
    simp only [iter, Option.some.injEq] at hk
    exact Or.inl (hk ▸ hz)
  | k + 1, v, hk => by
    simp only [iter] at hk
    obtain ⟨a, ha, hav⟩ := Option.bind_eq_some_iff.1 hk
    exact h.nxt_N (iter_N hz k ha) hav

theorem reach_N {v : V} (hv : Reach P x des Z v) : v ∈ Z ∨ s(x, v) ∈ F := by
  obtain ⟨z, hz, k, hk⟩ := hv
  exact h.iter_N hz k hk

theorem reach_pred {b : V} (hb : Reach P x des Z b) (hbZ : b ∉ Z) :
    ∃ a, Reach P x des Z a ∧ nxt P x des a = some b := by
  obtain ⟨z, hz, k, hk⟩ := hb
  cases k with
  | zero =>
    simp only [iter, Option.some.injEq] at hk
    exact absurd (hk ▸ hz) hbZ
  | succ k =>
    simp only [iter] at hk
    obtain ⟨a, ha, hab⟩ := Option.bind_eq_some_iff.1 hk
    exact ⟨a, ⟨z, hz, k, ha⟩, hab⟩

end Hyp

/-! ### One path -/

theorem head_append_cons {A B : List V} {x a : V} (h : (A ++ x :: B).head? = some a)
    (hax : a ≠ x) : A.head? = some a := by
  cases A with
  | nil => simp at h; exact absurd h.symm hax
  | cons c A => simpa using h

theorem last_append_cons {A B : List V} {x a : V} (h : (A ++ x :: B).getLast? = some a)
    (hax : a ≠ x) : B.getLast? = some a := by
  rw [List.getLast?_append] at h
  cases B with
  | nil => simp at h; exact absurd h.symm hax
  | cons c B =>
    have hne : (x :: c :: B).getLast? = (c :: B).getLast? := List.getLast?_cons_cons ..
    rw [hne, List.getLast?_eq_some_getLast (List.cons_ne_nil c B)] at h
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil c B)]
    simpa using h

namespace Hyp

variable {F : Finset (Sym2 V)} {P C : List (List V)} {x : V} {Z : Finset V} {des : V → ℕ}
  (h : Hyp F P C x Z des)
include h

theorem label_end {i : ℕ} {a : V} (ha : Reach P x des Z a) (hd : des a = i) :
    (pth P i).head? = some a ∨ (pth P i).getLast? = some a := by
  have := h.des_end a (h.reach_N ha)
  rwa [hd] at this

/-- A label at the head of a path through `x`: it heads `pre x U`, and `nxt` of it is the vertex
before `x`. -/
theorem lab₁_spec {i : ℕ} (hx : x ∈ pth P i) {a : V} (hh : (pth P i).head? = some a)
    (ha : Reach P x des Z a) (hd : des a = i) :
    (pre x (pth P i)).head? = some a ∧ nxt P x des a = (pre x (pth P i)).getLast? := by
  refine ⟨?_, ?_⟩
  · have hh' := hh
    rw [pre_append_post hx] at hh'
    exact head_append_cons hh' (h.N_ne (h.reach_N ha))
  · rw [h.nxt_of_head (h.reach_N ha) hd hh, if_pos hx]

theorem lab₂_spec {i : ℕ} (hx : x ∈ pth P i) {a : V} (hl : (pth P i).getLast? = some a)
    (ha : Reach P x des Z a) (hd : des a = i) :
    (post x (pth P i)).getLast? = some a ∧ nxt P x des a = (post x (pth P i)).head? := by
  refine ⟨?_, ?_⟩
  · have hl' := hl
    rw [pre_append_post hx] at hl'
    exact last_append_cons hl' (h.N_ne (h.reach_N ha))
  · rw [h.nxt_of_last (h.reach_N ha) hd hl, if_pos hx]

theorem nxt_none {i : ℕ} (hx : x ∉ pth P i) {a : V} (ha : Reach P x des Z a) (hd : des a = i) :
    nxt P x des a = none := by
  rcases h.label_end ha hd with hh | hl
  · rw [h.nxt_of_head (h.reach_N ha) hd hh, if_neg hx]
  · rw [h.nxt_of_last (h.reach_N ha) hd hl, if_neg hx]

theorem sym2_x_eq {a b : V} (ha : a ≠ x) (hab : s(x, b) = s(a, x)) : b = a := by
  rcases Sym2.eq_iff.1 hab with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1.symm ha
  · exact h2

/-- The edges of the output for `P[i]`: those of `P[i]` except the edges `s(x, nxt a)`, plus the
edges `s(x, a)`, for the labels `a` of `P[i]`. -/
theorem mem_oedges_out {i : ℕ} (hi : i < P.length) (e : Sym2 V) :
    e ∈ oedges (out P x des Z i) ↔
      (e ∈ walkEdges (pth P i) ∧
        ¬ ∃ a b, Reach P x des Z a ∧ des a = i ∧ nxt P x des a = some b ∧ e = s(x, b)) ∨
      ∃ a, Reach P x des Z a ∧ des a = i ∧ e = s(x, a) := by
  classical
  have hval := h.pth_valid hi
  by_cases hx : x ∈ pth P i
  · -- the path goes through `x`
    have hout : out P x des Z i =
        (reroute x (pth P i) (decide (Lab₁ P x des Z i)) (decide (Lab₂ P x des Z i)), false) := by
      unfold out; rw [if_pos hx]
    rw [hout]
    simp only [oedges, Bool.false_eq_true, if_false]
    rw [mem_walkEdges_reroute]
    have hxA := not_mem_pre x (pth P i)
    have hxB := not_mem_post hval.2 hx
    have noxA : ∀ {b}, s(x, b) ∉ walkEdges (pre x (pth P i)) :=
      fun hb => hxA (mem_of_mem_walkEdges hb (Sym2.mem_mk_left _ _))
    have noxB : ∀ {b}, s(x, b) ∉ walkEdges (post x (pth P i)) :=
      fun hb => hxB (mem_of_mem_walkEdges hb (Sym2.mem_mk_left _ _))
    constructor
    · rintro (hA | ⟨a', ha', rfl⟩ | ⟨b, hb, rfl⟩ | hB)
      · refine Or.inl ⟨(mem_walkEdges_split hx e).2 (Or.inl hA), ?_⟩
        rintro ⟨a, b, -, -, -, rfl⟩
        exact noxA hA
      · by_cases h1 : Lab₁ P x des Z i
        · rw [decide_eq_true h1, if_pos rfl] at ha'
          obtain ⟨a, hh, ha, hd⟩ := h1
          have := (h.lab₁_spec hx hh ha hd).1
          rw [this, Option.some.injEq] at ha'
          subst ha'
          exact Or.inr ⟨a, ha, hd, Sym2.eq_swap⟩
        · rw [decide_eq_false h1] at ha'
          simp only [Bool.false_eq_true, if_false] at ha'
          refine Or.inl ⟨(mem_walkEdges_split hx _).2 (Or.inr (Or.inl ⟨a', ha', rfl⟩)), ?_⟩
          rintro ⟨a, b, ha, hd, hab, heq⟩
          rcases h.label_end ha hd with hh | hl
          · exact h1 ⟨a, hh, ha, hd⟩
          · rw [(h.lab₂_spec hx hl ha hd).2] at hab
            have ha'mem := List.mem_of_getLast? ha'
            have hba : b = a' :=
              h.sym2_x_eq (fun hax => by rw [hax] at ha'mem; exact hxA ha'mem) heq.symm
            rw [hba] at hab
            exact pre_post_disjoint hval.2 hx ha'mem (List.mem_of_mem_head? hab)
      · by_cases h2 : Lab₂ P x des Z i
        · rw [decide_eq_true h2, if_pos rfl] at hb
          obtain ⟨a, hl, ha, hd⟩ := h2
          have := (h.lab₂_spec hx hl ha hd).1
          rw [this, Option.some.injEq] at hb
          subst hb
          exact Or.inr ⟨a, ha, hd, rfl⟩
        · rw [decide_eq_false h2] at hb
          simp only [Bool.false_eq_true, if_false] at hb
          refine Or.inl ⟨(mem_walkEdges_split hx _).2 (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))), ?_⟩
          rintro ⟨a, b', ha, hd, hab, heq⟩
          rcases h.label_end ha hd with hh | hl
          · rw [(h.lab₁_spec hx hh ha hd).2] at hab
            have hbmem := List.mem_of_mem_head? hb
            have hbb : b = b' := by
              rcases Sym2.eq_iff.1 heq with ⟨-, h2⟩ | ⟨-, h2⟩
              · exact h2
              · rw [h2] at hbmem; exact absurd hbmem hxB
            rw [← hbb] at hab
            exact pre_post_disjoint hval.2 hx (List.mem_of_getLast? hab) hbmem
          · exact h2 ⟨a, hl, ha, hd⟩
      · refine Or.inl ⟨(mem_walkEdges_split hx e).2 (Or.inr (Or.inr (Or.inr hB))), ?_⟩
        rintro ⟨a, b, -, -, -, rfl⟩
        exact noxB hB
    · rintro (⟨he, hR⟩ | ⟨a, ha, hd, rfl⟩)
      · rcases (mem_walkEdges_split hx e).1 he with hA | ⟨a', ha', rfl⟩ | ⟨b, hb, rfl⟩ | hB
        · exact Or.inl hA
        · by_cases h1 : Lab₁ P x des Z i
          · obtain ⟨a, hh, ha, hd⟩ := h1
            exact absurd ⟨a, a', ha, hd, (h.lab₁_spec hx hh ha hd).2.trans ha', Sym2.eq_swap⟩ hR
          · rw [decide_eq_false h1]
            exact Or.inr (Or.inl ⟨a', by simpa using ha', rfl⟩)
        · by_cases h2 : Lab₂ P x des Z i
          · obtain ⟨a, hl, ha, hd⟩ := h2
            exact absurd ⟨a, b, ha, hd, (h.lab₂_spec hx hl ha hd).2.trans hb, rfl⟩ hR
          · rw [decide_eq_false h2]
            exact Or.inr (Or.inr (Or.inl ⟨b, by simpa using hb, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr hB))
      · rcases h.label_end ha hd with hh | hl
        · have h1 : Lab₁ P x des Z i := ⟨a, hh, ha, hd⟩
          rw [decide_eq_true h1]
          exact Or.inr (Or.inl ⟨a, by simpa using (h.lab₁_spec hx hh ha hd).1, Sym2.eq_swap⟩)
        · have h2 : Lab₂ P x des Z i := ⟨a, hl, ha, hd⟩
          rw [decide_eq_true h2]
          exact Or.inr (Or.inr (Or.inl ⟨a, by simpa using (h.lab₂_spec hx hl ha hd).1, rfl⟩))
  · -- the path avoids `x`: no edge is removed
    have hR : ¬ ∃ a b, Reach P x des Z a ∧ des a = i ∧ nxt P x des a = some b ∧ e = s(x, b) := by
      rintro ⟨a, b, ha, hd, hab, -⟩
      rw [h.nxt_none hx ha hd] at hab
      exact absurd hab (by simp)
    have hA : (∃ a, Reach P x des Z a ∧ des a = i ∧ e = s(x, a)) ↔
        ((∃ a, (pth P i).head? = some a ∧ e = s(x, a)) ∧ Lab₁ P x des Z i ∨
          (∃ a, (pth P i).getLast? = some a ∧ e = s(x, a)) ∧ Lab₂ P x des Z i) := by
      constructor
      · rintro ⟨a, ha, hd, rfl⟩
        rcases h.label_end ha hd with hh | hl
        · exact Or.inl ⟨⟨a, hh, rfl⟩, a, hh, ha, hd⟩
        · exact Or.inr ⟨⟨a, hl, rfl⟩, a, hl, ha, hd⟩
      · rintro (⟨⟨a, hh, rfl⟩, a', hh', ha, hd⟩ | ⟨⟨a, hl, rfl⟩, a', hl', ha, hd⟩)
        · rw [hh, Option.some.injEq] at hh'; subst hh'; exact ⟨a, ha, hd, rfl⟩
        · rw [hl, Option.some.injEq] at hl'; subst hl'; exact ⟨a, ha, hd, rfl⟩
    have hne : pth P i ≠ [] := fun h' => by rw [h'] at hval; simp at hval
    rw [hA]
    simp only [hR, not_false_eq_true, and_true]
    unfold out
    rw [if_neg hx]
    by_cases h1 : Lab₁ P x des Z i <;> by_cases h2 : Lab₂ P x des Z i
    · rw [if_pos ⟨h1, h2⟩]
      simp only [oedges, if_true]
      rw [mem_cycleEdges_concat hne]
      simp only [h1, h2, and_true]
      constructor
      · rintro (h' | ⟨a, ha, rfl⟩ | h')
        · exact Or.inl h'
        · exact Or.inr (Or.inr ⟨a, ha, Sym2.eq_swap⟩)
        · exact Or.inr (Or.inl h')
      · rintro (h' | h' | ⟨a, ha, rfl⟩)
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
        · exact Or.inr (Or.inl ⟨a, ha, Sym2.eq_swap⟩)
    · rw [if_neg (fun h' => h2 h'.2), if_pos h1]
      simp only [oedges, Bool.false_eq_true, if_false]
      rw [mem_walkEdges_cons]
      simp only [h1, h2, and_true, and_false, or_false]
      exact or_comm
    · rw [if_neg (fun h' => h1 h'.1), if_neg h1, if_pos h2]
      simp only [oedges, Bool.false_eq_true, if_false]
      rw [mem_walkEdges_concat]
      simp only [h1, h2, and_true, and_false, false_or]
      constructor
      · rintro (h' | ⟨a, ha, rfl⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨a, ha, Sym2.eq_swap⟩
      · rintro (h' | ⟨a, ha, rfl⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨a, ha, Sym2.eq_swap⟩
    · rw [if_neg (fun h' => h1 h'.1), if_neg h1, if_neg h2]
      simp [oedges, h1, h2]

/-- The output for `P[i]` is a path or a cycle. -/
theorem out_valid {i : ℕ} (hi : i < P.length) :
    ((out P x des Z i).2 = false → 2 ≤ (out P x des Z i).1.length ∧ (out P x des Z i).1.Nodup) ∧
    ((out P x des Z i).2 = true → (Obj.cycle (out P x des Z i).1).WF) := by
  classical
  have hval := h.pth_valid hi
  unfold out
  by_cases hx : x ∈ pth P i
  · rw [if_pos hx]
    refine ⟨fun _ => ⟨?_, reroute_nodup hval.2 hx _ _⟩, fun h' => absurd h' (by simp)⟩
    rw [reroute_length hx]; exact hval.1
  · rw [if_neg hx]
    have hnd1 : (pth P i ++ [x]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hval.2, List.nodup_singleton x, fun a ha b hb hab => by
        rw [List.mem_singleton] at hb; subst hb; subst hab; exact hx ha⟩
    have hnd2 : (x :: pth P i).Nodup := List.nodup_cons.2 ⟨hx, hval.2⟩
    split_ifs
    · refine ⟨fun h' => absurd h' (by simp), fun _ => ⟨hnd1, ?_⟩⟩
      simp; omega
    · exact ⟨fun _ => ⟨by simp; omega, hnd2⟩, fun h' => absurd h' (by simp)⟩
    · exact ⟨fun _ => ⟨by simp; omega, hnd1⟩, fun h' => absurd h' (by simp)⟩
    · exact ⟨fun _ => hval, fun h' => absurd h' (by simp)⟩

theorem oedges_nodup {i : ℕ} (hi : i < P.length) : (oedges (out P x des Z i)).Nodup := by
  have hv := h.out_valid hi
  unfold oedges
  cases hb : (out P x des Z i).2
  · simp only [Bool.false_eq_true, if_false]
    exact nodup_walkEdges (hv.1 hb).2
  · simp only [if_true]
    exact nodup_cycleEdges (hv.2 hb).1 (hv.2 hb).2

end Hyp

/-! ### All paths together -/

namespace Hyp

variable {F : Finset (Sym2 V)} {P C : List (List V)} {x : V} {Z : Finset V} {des : V → ℕ}
  (h : Hyp F P C x Z des)
include h

/-- An added edge `s(x, a)` with `a ∉ Z` is an edge of the designated path of the predecessor of
`a`. -/
theorem added_edge {a : V} (ha : Reach P x des Z a) (haZ : a ∉ Z) :
    ∃ a₀, Reach P x des Z a₀ ∧ nxt P x des a₀ = some a ∧
      s(x, a) ∈ walkEdges (pth P (des a₀)) := by
  obtain ⟨a₀, h0, h1⟩ := h.reach_pred ha haZ
  exact ⟨a₀, h0, h1, h.nxt_edge (h.reach_N h0) h1⟩

theorem sym2_x_inj {a a' : V} (ha : a ≠ x) (h' : s(x, a) = s(x, a')) : a = a' := by
  rcases Sym2.eq_iff.1 h' with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact h2
  · exact absurd h2 ha

/-- The outputs of distinct paths are edge-disjoint. -/
theorem out_disj {i j : ℕ} (hi : i < P.length) (hj : j < P.length) (hij : i ≠ j) {e : Sym2 V}
    (h1 : e ∈ oedges (out P x des Z i)) (h2 : e ∈ oedges (out P x des Z j)) : False := by
  -- an edge of `P[k]` that is not removed from it is not an added edge of another path
  have key : ∀ {k l : ℕ}, k < P.length → k ≠ l → e ∈ walkEdges (pth P k) →
      (¬ ∃ a b, Reach P x des Z a ∧ des a = k ∧ nxt P x des a = some b ∧ e = s(x, b)) →
      ∀ {a}, Reach P x des Z a → des a = l → e = s(x, a) → False := by
    intro k l hk hkl he hR a ha hd hea
    subst hea
    by_cases haZ : a ∈ Z
    · exact h.ZF a haZ (h.walk_F hk he)
    · obtain ⟨a₀, h0, h1, h2⟩ := h.added_edge ha haZ
      have := h.walk_disj hk (h.des_lt a₀ (h.reach_N h0)) he h2
      exact hR ⟨a₀, a, h0, this.symm, h1, rfl⟩
  rw [h.mem_oedges_out hi] at h1
  rw [h.mem_oedges_out hj] at h2
  rcases h1 with ⟨he1, hR1⟩ | ⟨a, ha, hd, rfl⟩ <;> rcases h2 with ⟨he2, hR2⟩ | ⟨a', ha', hd', he'⟩
  · exact hij (h.walk_disj hi hj he1 he2)
  · exact key hi hij he1 hR1 ha' hd' he'
  · exact key hj (Ne.symm hij) he2 hR2 ha hd rfl
  · have := h.sym2_x_inj (h.N_ne (h.reach_N ha)) he'
    subst this
    exact hij (hd.symm.trans hd')

/-- The outputs are edge-disjoint from the cycles of `C`. -/
theorem out_disj_cyc {i : ℕ} (hi : i < P.length) {e : Sym2 V}
    (h1 : e ∈ oedges (out P x des Z i)) (h2 : e ∈ C.flatMap cycleEdges) : False := by
  rw [h.mem_oedges_out hi] at h1
  rcases h1 with ⟨he1, -⟩ | ⟨a, ha, hd, rfl⟩
  · exact h.walk_not_cyc hi he1 h2
  · by_cases haZ : a ∈ Z
    · exact h.ZF a haZ (h.cyc_F h2)
    · obtain ⟨a₀, h0, -, h3⟩ := h.added_edge ha haZ
      exact h.walk_not_cyc (h.des_lt a₀ (h.reach_N h0)) h3 h2

/-- The outputs together with `C` cover exactly `F ∪ {s(x, z) : z ∈ Z}`. -/
theorem out_cover (e : Sym2 V) :
    ((∃ i, i < P.length ∧ e ∈ oedges (out P x des Z i)) ∨ e ∈ C.flatMap cycleEdges) ↔
      (e ∈ F ∨ ∃ z ∈ Z, e = s(x, z)) := by
  constructor
  · rintro (⟨i, hi, he⟩ | he)
    · rw [h.mem_oedges_out hi] at he
      rcases he with ⟨he, -⟩ | ⟨a, ha, hd, rfl⟩
      · exact Or.inl (h.walk_F hi he)
      · by_cases haZ : a ∈ Z
        · exact Or.inr ⟨a, haZ, rfl⟩
        · obtain ⟨a₀, h0, -, h3⟩ := h.added_edge ha haZ
          exact Or.inl (h.walk_F (h.des_lt a₀ (h.reach_N h0)) h3)
    · exact Or.inl (h.cyc_F he)
  · rintro (he | ⟨z, hz, rfl⟩)
    · rcases h.F_cases he with ⟨i, hi, hei⟩ | hc
      · by_cases hR : ∃ a b, Reach P x des Z a ∧ des a = i ∧ nxt P x des a = some b ∧ e = s(x, b)
        · obtain ⟨a, b, ha, -, hab, rfl⟩ := hR
          have hb := h.reach_nxt ha hab
          refine Or.inl ⟨des b, h.des_lt b (h.reach_N hb), ?_⟩
          rw [h.mem_oedges_out (h.des_lt b (h.reach_N hb))]
          exact Or.inr ⟨b, hb, rfl, rfl⟩
        · refine Or.inl ⟨i, hi, ?_⟩
          rw [h.mem_oedges_out hi]
          exact Or.inl ⟨hei, hR⟩
      · exact Or.inr hc
    · have hz' : Reach P x des Z z := h.reach_of_mem hz
      refine Or.inl ⟨des z, h.des_lt z (Or.inl hz), ?_⟩
      rw [h.mem_oedges_out (h.des_lt z (Or.inl hz))]
      exact Or.inr ⟨z, hz', rfl, rfl⟩

end Hyp

/-- Splitting outputs into paths and cycles permutes their edges. -/
theorem split_perm :
    ∀ outs : List (List V × Bool),
      (((outs.filter (fun o => !o.2)).map Prod.fst).flatMap walkEdges ++
        ((outs.filter (fun o => o.2)).map Prod.fst).flatMap cycleEdges).Perm (outs.flatMap oedges)
  | [] => by simp
  | (l, b) :: outs => by
    have ih := split_perm outs
    cases b
    · simp only [List.filter_cons, Bool.not_false, if_true, Bool.false_eq_true, if_false,
        List.map_cons, List.flatMap_cons, oedges, List.append_assoc]
      exact List.Perm.append_left _ ih
    · simp only [List.filter_cons, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        List.map_cons, List.flatMap_cons, oedges]
      exact (List.perm_append_comm_assoc _ _ _).trans (List.Perm.append_left _ ih)

/-- **Lovász's construction** ([s1:citThm21], Lovász 1968, as in Yan 1998, §2.1). Let `(P, C)` be a
path-and-cycle decomposition of `F`, `x` a vertex and `Z` a set of vertices with `x ∉ Z` and
`s(x, z) ∉ F` for `z ∈ Z`, such that every vertex of `Z` and every neighbour of `x` in `F` is an end of
a path of `P`. Then `F ∪ {s(x, z) : z ∈ Z}` has a path-and-cycle decomposition with as many members
as `(P, C)`. -/
theorem lovasz_construction {F : Finset (Sym2 V)} {P C : List (List V)} {x : V} {Z : Finset V}
    (hD : IsPathCycleDecomp (F : Set (Sym2 V)) P C) (hxZ : x ∉ Z) (hZF : ∀ z ∈ Z, s(x, z) ∉ F)
    (hends : ∀ v, (v ∈ Z ∨ s(x, v) ∈ F) → ∃ p ∈ P, p.head? = some v ∨ p.getLast? = some v) :
    ∃ P' C' : List (List V),
      IsPathCycleDecomp ((F ∪ Z.image (fun z => s(x, z)) : Finset (Sym2 V)) : Set (Sym2 V)) P' C' ∧
      P'.length + C'.length = P.length + C.length := by
  classical
  have hends' : ∀ v, (v ∈ Z ∨ s(x, v) ∈ F) → ∃ i, i < P.length ∧
      ((pth P i).head? = some v ∨ (pth P i).getLast? = some v) := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ := hends v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact ⟨i, hi, by rwa [pth_eq hi]⟩
  choose! des hdes using hends'
  have h : Hyp F P C x Z des :=
    ⟨hD, hxZ, hZF, fun v hv => (hdes v hv).1, fun v hv => (hdes v hv).2⟩
  set outs := (List.range P.length).map (out P x des Z) with houts
  have hmem : ∀ o ∈ outs, ∃ i, i < P.length ∧ o = out P x des Z i := by
    intro o ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
    exact ⟨i, List.mem_range.1 hi, rfl⟩
  refine ⟨(outs.filter (fun o => !o.2)).map Prod.fst,
    C ++ (outs.filter (fun o => o.2)).map Prod.fst, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    obtain ⟨ho, hb⟩ := List.mem_filter.1 ho
    obtain ⟨i, hi, rfl⟩ := hmem o ho
    exact (h.out_valid hi).1 (by simpa using hb)
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hD.2.1 c hc
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
      obtain ⟨ho, hb⟩ := List.mem_filter.1 ho
      obtain ⟨i, hi, rfl⟩ := hmem o ho
      exact (h.out_valid hi).2 (by simpa using hb)
  · -- no repeated edge
    have hperm : ((((outs.filter (fun o => !o.2)).map Prod.fst).flatMap walkEdges ++
        (C ++ (outs.filter (fun o => o.2)).map Prod.fst).flatMap cycleEdges)).Perm
        (outs.flatMap oedges ++ C.flatMap cycleEdges) := by
      rw [List.flatMap_append]
      refine (List.Perm.append_left _ List.perm_append_comm).trans ?_
      rw [← List.append_assoc]
      exact List.Perm.append_right _ (split_perm outs)
    rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨?_, (List.nodup_append.1 hD.2.2.1).2.1, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun o ho => ?_, ?_⟩
      · obtain ⟨i, hi, rfl⟩ := hmem o ho
        exact h.oedges_nodup hi
      · rw [houts, List.pairwise_map]
        refine List.pairwise_lt_range.imp_of_mem ?_
        intro i j hi hj hij
        rw [Function.onFun, List.disjoint_left]
        exact fun e he1 he2 => h.out_disj (List.mem_range.1 hi) (List.mem_range.1 hj)
          (Nat.ne_of_lt hij) he1 he2
    · intro e he e' he' hee
      subst hee
      obtain ⟨o, ho, heo⟩ := List.mem_flatMap.1 he
      obtain ⟨i, hi, rfl⟩ := hmem o ho
      exact h.out_disj_cyc hi heo he'
  · -- the edges
    intro e
    have hperm : ((((outs.filter (fun o => !o.2)).map Prod.fst).flatMap walkEdges ++
        (C ++ (outs.filter (fun o => o.2)).map Prod.fst).flatMap cycleEdges)).Perm
        (outs.flatMap oedges ++ C.flatMap cycleEdges) := by
      rw [List.flatMap_append]
      refine (List.Perm.append_left _ List.perm_append_comm).trans ?_
      rw [← List.append_assoc]
      exact List.Perm.append_right _ (split_perm outs)
    rw [hperm.mem_iff, List.mem_append, Finset.coe_union, Set.mem_union, Finset.mem_coe,
      Finset.coe_image, Set.mem_image]
    have hc := h.out_cover e
    have h1 : e ∈ outs.flatMap oedges ↔ ∃ i, i < P.length ∧ e ∈ oedges (out P x des Z i) := by
      constructor
      · intro he
        obtain ⟨o, ho, heo⟩ := List.mem_flatMap.1 he
        obtain ⟨i, hi, rfl⟩ := hmem o ho
        exact ⟨i, hi, heo⟩
      · rintro ⟨i, hi, he⟩
        exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, he⟩
    rw [h1, hc]
    constructor
    · rintro (he | ⟨z, hz, rfl⟩)
      · exact Or.inl he
      · exact Or.inr ⟨z, hz, rfl⟩
    · rintro (he | ⟨z, hz, rfl⟩)
      · exact Or.inl he
      · exact Or.inr ⟨z, hz, rfl⟩
  · -- the count
    have hlen := List.length_eq_length_filter_add (l := outs) (fun o => !o.2)
    simp only [List.length_map, List.length_append, houts, List.length_range] at hlen ⊢
    have e1 : (List.filter (fun o => !!o.2) (List.map (out P x des Z) (List.range P.length))) =
        List.filter (fun o => o.2) (List.map (out P x des Z) (List.range P.length)) := by
      congr 1; funext o; simp
    rw [e1] at hlen
    omega

end LovaszC

end EG
