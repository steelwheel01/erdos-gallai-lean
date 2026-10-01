module

public import EG.Spec.Ext.Haxell
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.List.Lex
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Haxell's condition for matchability (manuscript s1:citHaxell)

* `EG.haxell_stated : EG.Spec.HaxellStatedForm` — the stated form (factor `2q-1`).
* `EG.haxell : EG.Spec.HaxellStatement` — the locked `q²`-form, derived from the stated form by
  `EG.haxellStatement_of_statedForm`.

The proof follows "Proof of the stated form" after [s1:citHaxell] in s1.tex (Haxell's
alternating-tree argument): induction on `|𝓧|`; a *good* set `M` (a matching of edges avoiding
`a₀` covering `𝓧 \ {a₀}`); *configurations* `(x₁, 𝓢₁, …, x_k, 𝓢_k)`; the counting bound
`|Z^{(k)}| ≤ (2q-1)(|𝓧^{(k)}|-1)` giving `(*)`; the swap step; one move; termination by the
order `σ∞ <lex τ∞` on signatures.

Encoding choices (internal to this file).
* A configuration is the list `[x_k, …, x₁]` of its edges (newest first); the sets
  `𝓢_i = {m ∈ M : m ∩ x_i ∩ 𝓨 ≠ ∅}` are determined by `M` and `x_i` (property (C2)), and are
  computed by `S Y M x`. `Xc`, `Zc` are `𝓧^{(k)}`, `Z^{(k)}`; `Valid` is (C1) and `𝓢_i ≠ ∅`.
* "`a(x_i) ∈ 𝓧^{(i-1)}`" is written `x_i ∩ 𝓧 ⊆ 𝓧^{(i-1)}` (equivalent, as `|x_i ∩ 𝓧| = 1`).
* Termination: instead of iterating moves, we take a good `M` and a configuration whose *key*
  is maximal (the key of a signature `(s₁, …, s_k)` is the list `(B - s₁, …, B - s_k)` in
  `Fin (B+1)`, `B = |𝓗|`, ordered lexicographically; the finitely many keys have length at most
  `|𝓧|`). Larger key corresponds to `≺`-smaller signature: an extension `σ ++ [s]` has a larger
  key, and `(s₁, …, s_{i-1}, s_i - 1)` has a key larger than that of every extension of
  `(s₁, …, s_i)` (manuscript "Termination"). One move from a maximal configuration then gives a
  contradiction unless the swap step finds `M` and `x` as required.
-/

public section


namespace EG

namespace Haxell

variable {α : Type*} [DecidableEq α]

/-! ### Configurations -/

/-- `𝓢(x) = {m ∈ M : m ∩ x ∩ 𝓨 ≠ ∅}` (property (C2)). -/
def S (Y : Finset α) (M : Finset (Finset α)) (x : Finset α) : Finset (Finset α) :=
  M.filter (fun m => (m ∩ x ∩ Y).Nonempty)

/-- `𝓧^{(k)}` of a configuration given newest first. -/
def Xc (X Y : Finset α) (a0 : α) (M : Finset (Finset α)) : List (Finset α) → Finset α
  | [] => {a0}
  | x :: c => Xc X Y a0 M c ∪ (S Y M x).biUnion (· ∩ X)

/-- `Z^{(k)}` of a configuration given newest first. -/
def Zc (Y : Finset α) (M : Finset (Finset α)) : List (Finset α) → Finset α
  | [] => ∅
  | x :: c => Zc Y M c ∪ (x ∩ Y) ∪ (S Y M x).biUnion (· ∩ Y)

/-- A configuration for `M`: properties (C1) and `𝓢_i ≠ ∅`, with every `x_i` an edge. -/
def Valid (X Y : Finset α) (H : Finset (Finset α)) (a0 : α) (M : Finset (Finset α)) :
    List (Finset α) → Prop
  | [] => True
  | x :: c => Valid X Y H a0 M c ∧ x ∈ H ∧ x ∩ X ⊆ Xc X Y a0 M c ∧ Disjoint x (Zc Y M c) ∧
      (S Y M x).Nonempty

/-- A good set: pairwise disjoint edges of `H`, none containing `a₀`, covering `𝓧 \ {a₀}`. -/
def Good (X : Finset α) (H : Finset (Finset α)) (a0 : α) (M : Finset (Finset α)) : Prop :=
  M ⊆ H ∧ (∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint m m') ∧ (∀ m ∈ M, a0 ∉ m) ∧
    ∀ a ∈ X, a ≠ a0 → ∃ m ∈ M, a ∈ m

/-- One entry of the key: `B - |𝓢(x)|`. -/
def kent (Y : Finset α) (B : ℕ) (M : Finset (Finset α)) (x : Finset α) : Fin (B + 1) :=
  ⟨B - (S Y M x).card, by omega⟩

/-- The key of a configuration: the signature, oldest first, with each entry `s` replaced by
`B - s`. -/
def key (Y : Finset α) (B : ℕ) (M : Finset (Finset α)) (c : List (Finset α)) :
    List (Fin (B + 1)) :=
  (c.map (kent Y B M)).reverse

/-- The goal of the augmentation: a good `M` and an edge `x ∋ a₀` sharing no vertex of `𝓨` with
an edge of `M`. -/
def Success (X Y : Finset α) (H : Finset (Finset α)) (a0 : α) : Prop :=
  ∃ M x, Good X H a0 M ∧ x ∈ H ∧ a0 ∈ x ∧ ∀ m ∈ M, ¬ (m ∩ x ∩ Y).Nonempty

/-! ### Basic lemmas -/

section Basic

variable {X Y : Finset α} {H : Finset (Finset α)} {a0 : α} {M : Finset (Finset α)}

theorem mem_S {x m : Finset α} : m ∈ S Y M x ↔ m ∈ M ∧ (m ∩ x ∩ Y).Nonempty := by
  simp [S]

theorem S_subset (x : Finset α) : S Y M x ⊆ M := Finset.filter_subset _ _

theorem key_nil (B : ℕ) : key Y B M [] = [] := by simp [key]

theorem key_cons (B : ℕ) (x : Finset α) (c : List (Finset α)) :
    key Y B M (x :: c) = key Y B M c ++ [kent Y B M x] := by
  simp [key]

theorem key_append (B : ℕ) (c d : List (Finset α)) :
    key Y B M (c ++ d) = key Y B M d ++ key Y B M c := by
  simp [key]

theorem length_key (B : ℕ) (c : List (Finset α)) : (key Y B M c).length = c.length := by
  simp [key]

theorem a0_mem_Xc (c : List (Finset α)) : a0 ∈ Xc X Y a0 M c := by
  induction c with
  | nil => simp [Xc]
  | cons x c ih => simp only [Xc]; exact Finset.mem_union_left _ ih

theorem Xc_subset (ha0 : a0 ∈ X) (c : List (Finset α)) : Xc X Y a0 M c ⊆ X := by
  induction c with
  | nil => simpa [Xc] using ha0
  | cons x c ih =>
    simp only [Xc]
    refine Finset.union_subset ih ?_
    intro b hb
    simp only [Finset.mem_biUnion, Finset.mem_inter] at hb
    obtain ⟨_, _, _, hbX⟩ := hb
    exact hbX

theorem Zc_subset (c : List (Finset α)) : Zc Y M c ⊆ Y := by
  induction c with
  | nil => simp [Zc]
  | cons x c ih =>
    simp only [Zc]
    refine Finset.union_subset (Finset.union_subset ih Finset.inter_subset_right) ?_
    intro b hb
    simp only [Finset.mem_biUnion, Finset.mem_inter] at hb
    obtain ⟨_, _, _, hbY⟩ := hb
    exact hbY

theorem Xc_mono_append (pre rest : List (Finset α)) :
    Xc X Y a0 M rest ⊆ Xc X Y a0 M (pre ++ rest) := by
  induction pre with
  | nil => exact le_rfl
  | cons x pre ih => simp only [List.cons_append, Xc]; exact ih.trans Finset.subset_union_left

theorem Zc_mono_append (pre rest : List (Finset α)) :
    Zc Y M rest ⊆ Zc Y M (pre ++ rest) := by
  induction pre with
  | nil => exact le_rfl
  | cons x pre ih =>
    simp only [List.cons_append, Zc]
    exact ih.trans (Finset.subset_union_left.trans Finset.subset_union_left)

theorem Valid.of_append {pre rest : List (Finset α)} (h : Valid X Y H a0 M (pre ++ rest)) :
    Valid X Y H a0 M rest := by
  induction pre with
  | nil => exact h
  | cons x pre ih => exact ih h.1

/-- `x_i ∩ 𝓨 ⊆ Z^{(k)}` for every edge `x_i` of the configuration. -/
theorem inter_Y_subset_Zc {c : List (Finset α)} {x : Finset α} (hx : x ∈ c) :
    x ∩ Y ⊆ Zc Y M c := by
  induction c with
  | nil => simp at hx
  | cons x' c ih =>
    simp only [Zc]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Finset.subset_union_right.trans Finset.subset_union_left
    · exact (ih hx).trans (Finset.subset_union_left.trans Finset.subset_union_left)

/-- `m ∩ 𝓨 ⊆ Z^{(k)}` for every `m ∈ 𝓢_i`. -/
theorem S_inter_Y_subset_Zc {c : List (Finset α)} {x m : Finset α} (hx : x ∈ c)
    (hm : m ∈ S Y M x) : m ∩ Y ⊆ Zc Y M c := by
  induction c with
  | nil => simp at hx
  | cons x' c ih =>
    simp only [Zc]
    rcases List.mem_cons.1 hx with rfl | hx
    · intro b hb
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, hm, hb⟩)
    · exact (ih hx).trans (Finset.subset_union_left.trans Finset.subset_union_left)

/-- The configuration decomposes at the (unique) `𝓢_i` containing the edge of a vertex
`b ≠ a₀` of `𝓧^{(k)}`. -/
theorem exists_decomp {c : List (Finset α)} {b : α} (hb : b ∈ Xc X Y a0 M c) (hb0 : b ≠ a0) :
    ∃ pre x rest m, c = pre ++ x :: rest ∧ m ∈ S Y M x ∧ b ∈ m := by
  induction c with
  | nil => simp [Xc] at hb; exact absurd hb hb0
  | cons x c ih =>
    simp only [Xc, Finset.mem_union, Finset.mem_biUnion, Finset.mem_inter] at hb
    rcases hb with hb | ⟨m, hm, hbm, -⟩
    · obtain ⟨pre, x', rest, m, rfl, hm, hbm⟩ := ih hb
      exact ⟨x :: pre, x', rest, m, rfl, hm, hbm⟩
    · exact ⟨[], x, c, m, rfl, hm, hbm⟩

/-- Configurations whose sets `𝓢_i` agree for `M` and `M'` have the same `𝓧`, `Z`, validity
and key. -/
theorem agree {M' : Finset (Finset α)} (B : ℕ) {c : List (Finset α)}
    (h : ∀ x ∈ c, S Y M' x = S Y M x) :
    Xc X Y a0 M' c = Xc X Y a0 M c ∧ Zc Y M' c = Zc Y M c ∧
      (Valid X Y H a0 M' c ↔ Valid X Y H a0 M c) ∧ key Y B M' c = key Y B M c := by
  induction c with
  | nil => simp [Xc, Zc, Valid, key]
  | cons x c ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    have hx := h x (List.mem_cons_self)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Xc, h1, hx]
    · simp only [Zc, h2, hx]
    · simp only [Valid, h1, h2, h3, hx]
    · rw [key_cons, key_cons, h4]
      simp [kent, hx]

end Basic

/-! ### Swapping one edge of a good set -/

section Swap

variable {X Y : Finset α} {H : Finset (Finset α)} {a0 : α} {M : Finset (Finset α)}

theorem inter_X_eq (hX1 : ∀ e ∈ H, (e ∩ X).card = 1) {e : Finset α} (he : e ∈ H) {b : α}
    (hbe : b ∈ e) (hbX : b ∈ X) : e ∩ X = {b} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (hX1 e he)
  have hb : b ∈ e ∩ X := Finset.mem_inter.2 ⟨hbe, hbX⟩
  rw [hc, Finset.mem_singleton] at hb
  rw [hc, hb]

theorem S_swap {y m x : Finset α} (h : ¬ (y ∩ x ∩ Y).Nonempty) :
    S Y (insert y (M.erase m)) x = (S Y M x).erase m := by
  ext m'
  simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨rfl | ⟨hne, hm'⟩, hn⟩
    · exact absurd hn h
    · exact ⟨hne, hm', hn⟩
  · rintro ⟨hne, hm', hn⟩
    exact ⟨Or.inr ⟨hne, hm'⟩, hn⟩

/-- Swap step: `M' := (M \ {m}) ∪ {y}` is good. -/
theorem good_swap (hsub : ∀ e ∈ H, e ⊆ X ∪ Y) (hM : Good X H a0 M) {y m : Finset α}
    (hyH : y ∈ H) (hmM : m ∈ M) (hyX : y ∩ X = m ∩ X) (ha0y : a0 ∉ y)
    (hyM : ∀ m' ∈ M, ¬ (m' ∩ y ∩ Y).Nonempty) :
    Good X H a0 (insert y (M.erase m)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  have hdisj : ∀ m' ∈ M, m' ≠ m → Disjoint y m' := by
    intro m' hm' hne
    rw [Finset.disjoint_left]
    intro z hzy hzm'
    rcases Finset.mem_union.1 (hsub y hyH hzy) with hzX | hzY
    · have hz : z ∈ m ∩ X := hyX ▸ Finset.mem_inter.2 ⟨hzy, hzX⟩
      exact Finset.disjoint_left.1 (h2 m hmM m' hm' (Ne.symm hne)) (Finset.mem_inter.1 hz).1 hzm'
    · exact hyM m' hm' ⟨z, by simp [hzy, hzm', hzY]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hyH
    · exact h1 (Finset.mem_of_mem_erase he)
  · intro e he e' he' hne
    simp only [Finset.mem_insert, Finset.mem_erase] at he he'
    rcases he with rfl | ⟨hem, heM⟩ <;> rcases he' with rfl | ⟨hem', heM'⟩
    · exact absurd rfl hne
    · exact hdisj e' heM' hem'
    · exact (hdisj e heM hem).symm
    · exact h2 e heM e' heM' hne
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_erase] at he
    rcases he with rfl | ⟨_, heM⟩
    · exact ha0y
    · exact h3 e heM
  · intro a haX ha0'
    obtain ⟨e, heM, hae⟩ := h4 a haX ha0'
    by_cases hem : e = m
    · subst hem
      refine ⟨y, Finset.mem_insert_self _ _, ?_⟩
      have ha : a ∈ e ∩ X := Finset.mem_inter.2 ⟨hae, haX⟩
      rw [← hyX] at ha
      exact (Finset.mem_inter.1 ha).1
    · exact ⟨e, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hem, heM⟩), hae⟩

end Swap

/-! ### Counting: `|Z^{(k)}| ≤ (2q-1)(|𝓧^{(k)}|-1)` -/

section Count

variable {X Y : Finset α} {H : Finset (Finset α)} {a0 : α} {M : Finset (Finset α)} {q : ℕ}

/-- If the vertex `a(m)` of `m ∈ M` lies in `𝓧^{(k)}`, then `m ∩ 𝓨 ⊆ Z^{(k)}` (`m` lies in some
`𝓢_i`, as `m ↦ a(m)` is injective on `M` and `a(m) ≠ a₀`). -/
theorem inv_J (hM : Good X H a0 M) {c : List (Finset α)} (hc : Valid X Y H a0 M c) :
    ∀ m ∈ M, ∀ b ∈ m, b ∈ Xc X Y a0 M c → m ∩ Y ⊆ Zc Y M c := by
  induction c with
  | nil =>
    intro m hm b hbm hb
    simp only [Xc, Finset.mem_singleton] at hb
    subst hb
    exact absurd hbm (hM.2.2.1 m hm)
  | cons x c ih =>
    intro m hm b hbm hb
    simp only [Xc, Finset.mem_union, Finset.mem_biUnion, Finset.mem_inter] at hb
    simp only [Zc]
    rcases hb with hb | ⟨m', hm', hbm', -⟩
    · exact (ih hc.1 m hm b hbm hb).trans
        (Finset.subset_union_left.trans Finset.subset_union_left)
    · have hmm : m' = m := by
        by_contra hne
        exact Finset.disjoint_left.1 (hM.2.1 m' (S_subset x hm') m hm hne) hbm' hbm
      subst hmm
      intro z hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m', hm', hz⟩)

theorem card_Xc_cons (hX1 : ∀ e ∈ H, (e ∩ X).card = 1) (hM : Good X H a0 M)
    {x : Finset α} {c : List (Finset α)} (hc : Valid X Y H a0 M (x :: c)) :
    (Xc X Y a0 M (x :: c)).card = (Xc X Y a0 M c).card + (S Y M x).card := by
  simp only [Xc]
  rw [Finset.card_union_of_disjoint ?_, Finset.card_biUnion ?_]
  · congr 1
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun m hm => hX1 m (hM.1 (S_subset x hm))
  · intro m hm m' hm' hne
    have hd := hM.2.1 m (S_subset x hm) m' (S_subset x hm') hne
    show Disjoint (m ∩ X) (m' ∩ X)
    rw [Finset.disjoint_left] at hd ⊢
    intro z hz hz'
    exact hd (Finset.mem_inter.1 hz).1 (Finset.mem_inter.1 hz').1
  · rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨m, hm, hbm, -⟩ : ∃ m ∈ S Y M x, b ∈ m ∧ b ∈ X := by simpa using hb'
    have hJ := inv_J hM hc.1 m (S_subset x hm) b hbm hb
    obtain ⟨z, hz⟩ := (mem_S.1 hm).2
    simp only [Finset.mem_inter] at hz
    exact Finset.disjoint_left.1 hc.2.2.2.1 hz.1.2 (hJ (Finset.mem_inter.2 ⟨hz.1.1, hz.2⟩))

theorem card_Zc_cons (hYq : ∀ e ∈ H, (e ∩ Y).card ≤ q) (hM : Good X H a0 M)
    {x : Finset α} (hx : x ∈ H) (c : List (Finset α)) :
    (Zc Y M (x :: c)).card ≤ (Zc Y M c).card + q + (q - 1) * (S Y M x).card := by
  have hsub : Zc Y M (x :: c) ⊆
      Zc Y M c ∪ (x ∩ Y) ∪ (S Y M x).biUnion (fun m => (m ∩ Y) \ x) := by
    intro z hz
    simp only [Zc, Finset.mem_union, Finset.mem_biUnion, Finset.mem_inter,
      Finset.mem_sdiff] at hz ⊢
    rcases hz with (hz | hz) | ⟨m, hm, hzm, hzY⟩
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · by_cases hzx : z ∈ x
      · exact Or.inl (Or.inr ⟨hzx, hzY⟩)
      · exact Or.inr ⟨m, hm, ⟨hzm, hzY⟩, hzx⟩
  have h1 := Finset.card_union_le (Zc Y M c ∪ (x ∩ Y)) ((S Y M x).biUnion (fun m => (m ∩ Y) \ x))
  have h2 := Finset.card_union_le (Zc Y M c) (x ∩ Y)
  have h3 := hYq x hx
  have h4 : ((S Y M x).biUnion (fun m => (m ∩ Y) \ x)).card ≤ (S Y M x).card * (q - 1) := by
    refine Finset.card_biUnion_le_card_mul _ _ _ fun m hm => ?_
    obtain ⟨hmM, z, hz⟩ := mem_S.1 hm
    have hlt : ((m ∩ Y) \ x).card < (m ∩ Y).card := by
      refine Finset.card_lt_card ⟨Finset.sdiff_subset, fun h => ?_⟩
      simp only [Finset.mem_inter] at hz
      have hz' : z ∈ m ∩ Y := Finset.mem_inter.2 ⟨hz.1.1, hz.2⟩
      exact (Finset.mem_sdiff.1 (h hz')).2 hz.1.2
    have := hYq m (hM.1 hmM)
    omega
  have h5 := Finset.card_le_card hsub
  rw [mul_comm] at h4
  omega

theorem count (hq : 1 ≤ q) (hX1 : ∀ e ∈ H, (e ∩ X).card = 1)
    (hYq : ∀ e ∈ H, (e ∩ Y).card ≤ q) (hM : Good X H a0 M) :
    ∀ {c : List (Finset α)}, Valid X Y H a0 M c →
      (Zc Y M c).card + (2 * q - 1) ≤ (2 * q - 1) * (Xc X Y a0 M c).card ∧
        c.length + 1 ≤ (Xc X Y a0 M c).card
  | [], _ => by simp [Zc, Xc]
  | x :: c, hc => by
    obtain ⟨ih1, ih2⟩ := count hq hX1 hYq hM hc.1
    have hX := card_Xc_cons hX1 hM hc
    have hZ := card_Zc_cons hYq hM hc.2.1 c
    have hs : 1 ≤ (S Y M x).card := Finset.card_pos.2 hc.2.2.2.2
    rw [hX]
    simp only [List.length_cons]
    refine ⟨?_, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have e1 : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    have e2 : r + 1 - 1 = r := by omega
    rw [e1] at ih1 ⊢
    rw [e2] at hZ
    nlinarith

/-- `(*)`: the hypothesis applied to `𝓧^{(k)}` and `Z^{(k)}`. -/
theorem star (hq : 1 ≤ q) (hX1 : ∀ e ∈ H, (e ∩ X).card = 1)
    (hYq : ∀ e ∈ H, (e ∩ Y).card ≤ q) (ha0 : a0 ∈ X)
    (hHall : ∀ X' ⊆ X, X'.Nonempty → ∀ Z ⊆ Y, Z.card ≤ (2 * q - 1) * (X'.card - 1) →
      ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z)
    (hM : Good X H a0 M) {c : List (Finset α)} (hc : Valid X Y H a0 M c) :
    ∃ x ∈ H, x ∩ X ⊆ Xc X Y a0 M c ∧ Disjoint x (Zc Y M c) := by
  refine hHall _ (Xc_subset ha0 c) ⟨a0, a0_mem_Xc c⟩ _ (Zc_subset c) ?_
  have h := (count hq hX1 hYq hM hc).1
  rw [Nat.mul_sub_one]
  omega

end Count

/-! ### The swap step and the augmentation -/

section Augment

variable {X Y : Finset α} {H : Finset (Finset α)} {a0 : α} {q : ℕ}

theorem lt_append_single {B : ℕ} (l : List (Fin (B + 1))) (a : Fin (B + 1)) : l < l ++ [a] := by
  show List.Lex (· < ·) l (l ++ [a])
  simpa using List.Lex.append_left (· < ·) (List.Lex.nil (a := a) (l := [])) l

theorem append_cons_lt {B : ℕ} (p t : List (Fin (B + 1))) {a b : Fin (B + 1)} (h : a < b) :
    p ++ a :: t < p ++ [b] := by
  show List.Lex (· < ·) _ _
  exact List.Lex.append_left (· < ·) (List.Lex.rel h) p

/-- The swap step (repeated): it either finds a good `M` and an edge `x ∋ a₀` as required, or
a good `M'` with a configuration whose key exceeds that of every extension of the key of the
given configuration (the signature `(s₁, …, s_{i-1}, s_i - 1)`). -/
theorem swap (hsub : ∀ e ∈ H, e ⊆ X ∪ Y) (hX1 : ∀ e ∈ H, (e ∩ X).card = 1) (ha0 : a0 ∈ X) :
    ∀ (n : ℕ) (c : List (Finset α)), c.length = n → ∀ M, Good X H a0 M →
      Valid X Y H a0 M c → ∀ y ∈ H, y ∩ X ⊆ Xc X Y a0 M c → Disjoint y (Zc Y M c) →
      (∀ m ∈ M, ¬ (m ∩ y ∩ Y).Nonempty) →
      Success X Y H a0 ∨ ∃ M' c', Good X H a0 M' ∧ Valid X Y H a0 M' c' ∧
        ∀ u, key Y H.card M c ++ u < key Y H.card M' c' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcn M hM hc y hyH hyX hyZ hyM
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 (hX1 y hyH)
  have hbyX : b ∈ y ∩ X := by rw [hb]; exact Finset.mem_singleton_self b
  have hby : b ∈ y := (Finset.mem_inter.1 hbyX).1
  have hbX : b ∈ X := (Finset.mem_inter.1 hbyX).2
  by_cases hb0 : b = a0
  · subst hb0
    exact Or.inl ⟨M, y, hM, hyH, hby, hyM⟩
  have hbXc : b ∈ Xc X Y a0 M c := hyX hbyX
  obtain ⟨pre, x, rest, m, rfl, hmS, hbm⟩ := exists_decomp hbXc hb0
  obtain ⟨hmM, hmxY⟩ := mem_S.1 hmS
  have hmH : m ∈ H := hM.1 hmM
  have hmX : m ∩ X = {b} := inter_X_eq hX1 hmH hbm hbX
  have hyX' : y ∩ X = m ∩ X := by rw [hb, hmX]
  have ha0y : a0 ∉ y := by
    intro h
    have h' : a0 ∈ y ∩ X := Finset.mem_inter.2 ⟨h, ha0⟩
    rw [hb, Finset.mem_singleton] at h'
    exact hb0 h'.symm
  have hM' : Good X H a0 (insert y (M.erase m)) := good_swap hsub hM hyH hmM hyX' ha0y hyM
  have hvx : Valid X Y H a0 M (x :: rest) := Valid.of_append hc
  have hyx' : ∀ x' ∈ x :: rest, ¬ (y ∩ x' ∩ Y).Nonempty := by
    rintro x' hx' ⟨z, hz⟩
    simp only [Finset.mem_inter] at hz
    have hzZ : z ∈ Zc Y M (pre ++ x :: rest) :=
      inter_Y_subset_Zc (List.mem_append_right _ hx') (Finset.mem_inter.2 ⟨hz.1.2, hz.2⟩)
    exact Finset.disjoint_left.1 hyZ hz.1.1 hzZ
  have hSx' : ∀ x' ∈ x :: rest, S Y (insert y (M.erase m)) x' = (S Y M x').erase m :=
    fun x' hx' => S_swap (hyx' x' hx')
  have hmrest : ∀ x' ∈ rest, m ∉ S Y M x' := by
    intro x' hx' hm'
    have h1 : m ∩ Y ⊆ Zc Y M rest := S_inter_Y_subset_Zc hx' hm'
    obtain ⟨z, hz⟩ := hmxY
    simp only [Finset.mem_inter] at hz
    exact Finset.disjoint_left.1 hvx.2.2.2.1 hz.1.2 (h1 (Finset.mem_inter.2 ⟨hz.1.1, hz.2⟩))
  obtain ⟨hA1, hA2, hA3, hA4⟩ := agree (X := X) (H := H) (a0 := a0) (Y := Y)
    (M := M) (M' := insert y (M.erase m)) H.card (c := rest) (fun x' hx' => by
      rw [hSx' x' (List.mem_cons_of_mem _ hx'), Finset.erase_eq_of_notMem (hmrest x' hx')])
  have hvrest' : Valid X Y H a0 (insert y (M.erase m)) rest := hA3.2 hvx.1
  have hkey : key Y H.card M (pre ++ x :: rest) =
      key Y H.card M rest ++ kent Y H.card M x :: key Y H.card M pre := by
    rw [key_append, key_cons]
    simp
  have hs1 : 1 ≤ (S Y M x).card := Finset.card_pos.2 ⟨m, hmS⟩
  have hsB : (S Y M x).card ≤ H.card := Finset.card_le_card ((S_subset x).trans hM.1)
  have hSx := hSx' x List.mem_cons_self
  by_cases hne : ((S Y M x).erase m).Nonempty
  · right
    refine ⟨insert y (M.erase m), x :: rest, hM',
      ⟨hvrest', hvx.2.1, hA1 ▸ hvx.2.2.1, hA2 ▸ hvx.2.2.2.1, hSx ▸ hne⟩, fun u => ?_⟩
    rw [key_cons, hA4, hkey]
    have hlt : kent Y H.card M x < kent Y H.card (insert y (M.erase m)) x := by
      simp only [kent, Fin.mk_lt_mk, hSx, Finset.card_erase_of_mem hmS]
      omega
    simpa using append_cons_lt (key Y H.card M rest) (key Y H.card M pre ++ u) hlt
  · have hSm : ∀ m' ∈ insert y (M.erase m), ¬ (m' ∩ x ∩ Y).Nonempty := by
      intro m' hm' hn
      rcases Finset.mem_insert.1 hm' with rfl | hm'
      · exact hyx' x List.mem_cons_self hn
      · obtain ⟨hne', hm'M⟩ := Finset.mem_erase.1 hm'
        exact hne ⟨m', Finset.mem_erase.2 ⟨hne', mem_S.2 ⟨hm'M, hn⟩⟩⟩
    have hlen : rest.length < n := by
      rw [← hcn]
      simp
      omega
    rcases ih rest.length hlen rest rfl _ hM' hvrest' x hvx.2.1 (hA1 ▸ hvx.2.2.1)
      (hA2 ▸ hvx.2.2.2.1) hSm with h | ⟨M'', c'', h1, h2, h3⟩
    · exact Or.inl h
    · right
      refine ⟨M'', c'', h1, h2, fun u => ?_⟩
      have h4 := h3 (kent Y H.card M x :: (key Y H.card M pre ++ u))
      rw [hA4] at h4
      rw [hkey]
      simpa using h4

/-- Given a good set, the swap steps and moves find a good `M` and an edge `x ∋ a₀` sharing no
vertex of `𝓨` with an edge of `M` (manuscript: "One move" and "Termination"). -/
theorem augment (hq : 1 ≤ q) (hsub : ∀ e ∈ H, e ⊆ X ∪ Y) (hX1 : ∀ e ∈ H, (e ∩ X).card = 1)
    (hYq : ∀ e ∈ H, (e ∩ Y).card ≤ q) (ha0 : a0 ∈ X)
    (hHall : ∀ X' ⊆ X, X'.Nonempty → ∀ Z ⊆ Y, Z.card ≤ (2 * q - 1) * (X'.card - 1) →
      ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z)
    {M0 : Finset (Finset α)} (hM0 : Good X H a0 M0) : Success X Y H a0 := by
  by_contra hns
  let K : Set (List (Fin (H.card + 1))) :=
    {k | ∃ M c, Good X H a0 M ∧ Valid X Y H a0 M c ∧ key Y H.card M c = k}
  have hfin : K.Finite := by
    refine (List.finite_length_le (Fin (H.card + 1)) X.card).subset ?_
    rintro k ⟨M, c, hM, hc, rfl⟩
    simp only [Set.mem_ofPred_eq, length_key]
    have h1 := (count hq hX1 hYq hM hc).2
    have h2 := Finset.card_le_card (Xc_subset (Y := Y) (M := M) ha0 c)
    omega
  have hne : K.Nonempty := ⟨[], M0, [], hM0, trivial, key_nil _⟩
  obtain ⟨k, ⟨M, c, hM, hc, rfl⟩, hmax⟩ := Set.exists_max_image K id hfin hne
  obtain ⟨x, hxH, hxX, hxZ⟩ := star hq hX1 hYq ha0 hHall hM hc
  by_cases hS : (S Y M x).Nonempty
  · have hv : Valid X Y H a0 M (x :: c) := ⟨hc, hxH, hxX, hxZ, hS⟩
    have hle : key Y H.card M (x :: c) ≤ key Y H.card M c := hmax _ ⟨M, x :: c, hM, hv, rfl⟩
    rw [key_cons] at hle
    exact absurd hle (not_le.2 (lt_append_single _ _))
  · have hxM : ∀ m ∈ M, ¬ (m ∩ x ∩ Y).Nonempty := fun m hm h => hS ⟨m, mem_S.2 ⟨hm, h⟩⟩
    rcases swap hsub hX1 ha0 c.length c rfl M hM hc x hxH hxX hxZ hxM with
      h | ⟨M', c', hM', hc', hlt⟩
    · exact hns h
    · have hle : key Y H.card M' c' ≤ key Y H.card M c := hmax _ ⟨M', c', hM', hc', rfl⟩
      exact absurd hle (not_le.2 (by simpa using hlt []))

end Augment

/-- [s1:citHaxell] The stated form with `ℕ` arithmetic and nonempty `𝓧'`, and matchings given by
pairwise disjointness of distinct edges; proved by induction on `|𝓧|`. -/
theorem haxell_nat {q : ℕ} (hq : 1 ≤ q) (Y : Finset α) :
    ∀ (n : ℕ) (X : Finset α) (H : Finset (Finset α)), X.card = n → Disjoint X Y →
      (∀ e ∈ H, e ⊆ X ∪ Y) → (∀ e ∈ H, (e ∩ X).card = 1) → (∀ e ∈ H, (e ∩ Y).card ≤ q) →
      (∀ X' ⊆ X, X'.Nonempty → ∀ Z ⊆ Y, Z.card ≤ (2 * q - 1) * (X'.card - 1) →
        ∃ e ∈ H, e ∩ X ⊆ X' ∧ Disjoint e Z) →
      ∃ M ⊆ H, (∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint m m') ∧ ∀ a ∈ X, ∃ e ∈ M, a ∈ e := by
  intro n
  induction n with
  | zero =>
    intro X H hX _ _ _ _ _
    refine ⟨∅, Finset.empty_subset _, by simp, fun a ha => ?_⟩
    simp [Finset.card_eq_zero.1 hX] at ha
  | succ n ih =>
    intro X H hX hXY hsub hX1 hYq hHall
    obtain ⟨a0, ha0⟩ : X.Nonempty := Finset.card_pos.1 (by omega)
    have hH0 : ∀ e ∈ H.filter (fun e => a0 ∉ e), e ∈ H ∧ a0 ∉ e :=
      fun e he => Finset.mem_filter.1 he
    have hXe : ∀ e ∈ H.filter (fun e => a0 ∉ e), e ∩ X.erase a0 = e ∩ X := by
      intro e he
      ext z
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => (hH0 e he).2 (h ▸ h1), h2⟩
    obtain ⟨M0, hM0H, hM0d, hM0c⟩ := ih (X.erase a0) (H.filter (fun e => a0 ∉ e))
      (by rw [Finset.card_erase_of_mem ha0]; omega)
      (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hXY)
      (by
        intro e he z hz
        have hz' := hsub e (hH0 e he).1 hz
        simp only [Finset.mem_union, Finset.mem_erase] at hz' ⊢
        rcases hz' with h | h
        · exact Or.inl ⟨fun h' => (hH0 e he).2 (h' ▸ hz), h⟩
        · exact Or.inr h)
      (fun e he => by rw [hXe e he]; exact hX1 e (hH0 e he).1)
      (fun e he => hYq e (hH0 e he).1)
      (by
        intro X' hX' hX'ne Z hZ hZc
        obtain ⟨e, heH, heX, heZ⟩ :=
          hHall X' (hX'.trans (Finset.erase_subset _ _)) hX'ne Z hZ hZc
        have ha0e : a0 ∉ e := fun h =>
          Finset.notMem_erase a0 X (hX' (heX (Finset.mem_inter.2 ⟨h, ha0⟩)))
        have he0 : e ∈ H.filter (fun e => a0 ∉ e) := Finset.mem_filter.2 ⟨heH, ha0e⟩
        exact ⟨e, he0, by rw [hXe e he0]; exact heX, heZ⟩)
    have hGood : Haxell.Good X H a0 M0 :=
      ⟨hM0H.trans (Finset.filter_subset _ _), hM0d, fun m hm => (hH0 m (hM0H hm)).2,
        fun a ha hne => hM0c a (Finset.mem_erase.2 ⟨hne, ha⟩)⟩
    obtain ⟨M, x, hM, hxH, ha0x, hxM⟩ :=
      Haxell.augment hq hsub hX1 hYq ha0 hHall hGood
    have hxd : ∀ m ∈ M, Disjoint x m := by
      intro m hm
      rw [Finset.disjoint_left]
      intro z hzx hzm
      rcases Finset.mem_union.1 (hsub x hxH hzx) with hzX | hzY
      · have hz : z ∈ x ∩ X := Finset.mem_inter.2 ⟨hzx, hzX⟩
        rw [Haxell.inter_X_eq hX1 hxH ha0x ha0, Finset.mem_singleton] at hz
        exact hM.2.2.1 m hm (hz ▸ hzm)
      · exact hxM m hm ⟨z, by simp [hzx, hzm, hzY]⟩
    refine ⟨insert x M, ?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact hxH
      · exact hM.1 he
    · intro e he e' he' hne
      rcases Finset.mem_insert.1 he with rfl | heM <;>
        rcases Finset.mem_insert.1 he' with rfl | heM'
      · exact absurd rfl hne
      · exact hxd e' heM'
      · exact (hxd e heM).symm
      · exact hM.2.1 e heM e' heM' hne
    · intro a ha
      by_cases ha' : a = a0
      · subst ha'
        exact ⟨x, Finset.mem_insert_self _ _, ha0x⟩
      · obtain ⟨e, heM, hae⟩ := hM.2.2.2 a ha ha'
        exact ⟨e, Finset.mem_insert_of_mem heM, hae⟩

end Haxell

universe u

/-- [s1:citHaxell] Haxell's condition for matchability, the stated form (factor `2q-1`, bound
compared in `ℤ`). Proof: Haxell's alternating-tree argument (`EG.Haxell.haxell_nat`). -/
theorem haxell_stated : EG.Spec.HaxellStatedForm.{u} := by
  intro α _ X Y q H hq hXY hsub hX1 hYq hHall
  obtain ⟨M, hMH, hMd, hMc⟩ := Haxell.haxell_nat hq Y X.card X H rfl hXY hsub hX1 hYq
    (by
      intro X' hX' hX'ne Z hZ hZc
      refine hHall X' hX' Z hZ ?_
      have h1 : 1 ≤ X'.card := Finset.card_pos.2 hX'ne
      have h2 : ((2 * q - 1 : ℕ) : ℤ) = 2 * (q : ℤ) - 1 := by omega
      have h3 : ((X'.card - 1 : ℕ) : ℤ) = (X'.card : ℤ) - 1 := by omega
      rw [← h2, ← h3]
      exact_mod_cast hZc)
  exact ⟨M, hMH, fun m hm m' hm' hne => hMd m hm m' hm' hne, hMc⟩

/-- The stated form of [s1:citHaxell] implies its `q²`-form (`EG.Spec.HaxellStatement`): for
`X' = ∅` the stated hypothesis is vacuous, and for nonempty `X'`,
`(2q-1)(|X'|-1) < q²|X'|` since `q² - (2q-1) = (q-1)² ≥ 0`. -/
theorem haxellStatement_of_statedForm (h : EG.Spec.HaxellStatedForm.{u}) :
    EG.Spec.HaxellStatement.{u} := by
  intro α _ X Y q H hq hXY hsub hX1 hYq hHall
  refine h α X Y q H hq hXY hsub hX1 hYq ?_
  intro X' hX' Z hZ hZc
  have hne : X'.Nonempty := by
    rcases X'.eq_empty_or_nonempty with rfl | hne
    · have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
      simp only [Finset.card_empty, Nat.cast_zero, zero_sub] at hZc
      have : (0 : ℤ) ≤ Z.card := Nat.cast_nonneg _
      nlinarith
    · exact hne
  refine hHall X' hX' hne Z hZ ?_
  have h1 : (1 : ℤ) ≤ X'.card := by exact_mod_cast Finset.card_pos.2 hne
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hlt : (Z.card : ℤ) < (q : ℤ) ^ 2 * X'.card := by
    nlinarith [sq_nonneg ((q : ℤ) - 1)]
  exact_mod_cast hlt

/-- [s1:citHaxell] Haxell's condition for matchability in the locked `q²`-form used by
[s3:lemL9rho]. -/
theorem haxell : EG.Spec.HaxellStatement.{u} :=
  haxellStatement_of_statedForm haxell_stated

end EG
