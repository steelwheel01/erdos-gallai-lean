module

public import EG.Lib.Found.Graph
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Bucić–Montgomery Proposition 8 (manuscript s1:citProp8)

Proof of `EG.Spec.BMProp8Statement` (used by `EG.Todo.BMProp8`), reconstructed from [BM]'s
proof (arXiv:2211.07689v2, l. 393–424; blueprint `formal/work/p2/blueprint_s1.md`, node
`s1:citProp8`, hazard P8-PROOF-EXTERNAL).

* Walks through `W`: `EG.BM8.ThroughW W w` (every vertex of the walk other than its two ends lies
  in `W`); conversions to and from list paths through `W` (`exists_walk_of_path`,
  `exists_path_of_walk`, via Mathlib's `bypass`); ball composition
  `B^b(B^a(U,W),W) ⊆ B^{a+b}(U,W)` (`ball_ball_subset`); two balls around `x` and `y` that meet
  give an `xy`-path through `W` (`exists_path_of_mem_ball_inter`).
* The maximal-`r` argument, in the form "every `r` is feasible" (`feasible_succ`): with the
  natural-number reading `|X| 3^r ≤ t 2^r` of `|X| ≤ t (2/3)^r`, a feasible `r` has
  `2^r ≤ t²`, hence `(r+1)ℓ ≤ R := ⌊2ℓ log n⌋`; feasibility of `r = 2t` then contradicts
  `2^{2t} > t²` (`core`).
-/

public section

namespace EG

namespace BM8

variable {V : Type*}

/-! ### Interior vertices of lists -/

theorem mem_interior_of_ne {p : List V} {x y z : V} (hx : p.head? = some x)
    (hy : p.getLast? = some y) (hz : z ∈ p) (hzx : z ≠ x) (hzy : z ≠ y) : z ∈ interior p := by
  cases p with
  | nil => simp at hz
  | cons a t =>
    have hax : a = x := by simpa using hx
    subst hax
    have hzt : z ∈ t := by
      rcases List.mem_cons.1 hz with h | h
      · exact absurd h hzx
      · exact h
    cases t with
    | nil => simp at hzt
    | cons b t' =>
      rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil b t'),
        Option.some.injEq] at hy
      simp only [interior, List.tail_cons]
      exact List.mem_dropLast_of_mem_of_ne_getLast hzt (by rw [hy]; exact hzy)

theorem ne_of_mem_interior {p : List V} {x y z : V} (hnd : p.Nodup) (hx : p.head? = some x)
    (hy : p.getLast? = some y) (hz : z ∈ interior p) : z ≠ x ∧ z ≠ y := by
  cases p with
  | nil => simp [interior] at hz
  | cons a t =>
    have hax : a = x := by simpa using hx
    subst hax
    simp only [interior, List.tail_cons] at hz
    rw [List.nodup_cons] at hnd
    have hzt : z ∈ t := List.mem_of_mem_dropLast hz
    refine ⟨fun h => hnd.1 (h ▸ hzt), ?_⟩
    have hy' : t.getLast? = some y := by
      cases t with
      | nil => simp at hzt
      | cons b t' => rwa [List.getLast?_cons_cons] at hy
    rintro rfl
    have happ := List.dropLast_append_getLast? z hy'
    have hnd2 := hnd.2
    rw [← happ, List.nodup_append] at hnd2
    exact hnd2.2.2 z hz z (List.mem_singleton_self z) rfl

/-! ### Walks through `W` -/

/-- A walk "through `W`": every vertex of `w` other than its two ends lies in `W`. -/
def ThroughW (W : Finset V) {G : SimpleGraph V} {u v : V} (w : G.Walk u v) : Prop :=
  ∀ z ∈ w.support, z ≠ u → z ≠ v → z ∈ W

theorem ThroughW.append {W : Finset V} {G : SimpleGraph V} {u m v : V} {w₁ : G.Walk u m}
    {w₂ : G.Walk m v} (h₁ : ThroughW W w₁) (h₂ : ThroughW W w₂) (hm : m ∈ W) :
    ThroughW W (w₁.append w₂) := by
  intro z hz hzu hzv
  rw [SimpleGraph.Walk.support_append] at hz
  by_cases hzm : z = m
  · exact hzm ▸ hm
  rcases List.mem_append.1 hz with h | h
  · exact h₁ z h hzu hzm
  · exact h₂ z (List.mem_of_mem_tail h) hzm hzv

theorem ThroughW.reverse {W : Finset V} {G : SimpleGraph V} {u v : V} {w : G.Walk u v}
    (h : ThroughW W w) : ThroughW W w.reverse := by
  intro z hz hzv hzu
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
  exact h z hz hzu hzv

variable [DecidableEq V]

omit [DecidableEq V] in
theorem exists_walk_of_path {H : FGraph V} {W : Finset V} {u v : V} {p : List V}
    (hp : IsPathBetween H.edges u v p) (hW : IsThrough W p) :
    ∃ w : H.toSimpleGraph.Walk u v, ThroughW W w ∧ w.length = pathLength p := by
  obtain ⟨w, _, hs, hl⟩ := hp.exists_walk
  refine ⟨w, fun z hz hzu hzv => hW z ?_, hl⟩
  rw [hs] at hz
  exact mem_interior_of_ne hp.2.1 hp.2.2 hz hzu hzv

theorem exists_path_of_walk {H : FGraph V} {W : Finset V} {u v : V}
    (w : H.toSimpleGraph.Walk u v) (hw : ThroughW W w) :
    ∃ p, IsPathBetween H.edges u v p ∧ IsThrough W p ∧ pathLength p ≤ w.length := by
  have hq := w.bypass_isPath
  have hpb := isPathBetween_support hq
  refine ⟨w.bypass.support, hpb, fun z hz => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := ne_of_mem_interior hpb.1.2.1 hpb.2.1 hpb.2.2 hz
    exact hw z (w.support_bypass_subset_support (interior_subset _ hz)) h1 h2
  · rw [pathLength_support]
    exact w.length_bypass_le_length

/-! ### Balls -/

theorem mem_ball_iff_walk {H : FGraph V} {i : ℕ} {U W : Finset V} {w : V} :
    w ∈ ball H i U W ↔ w ∈ W ∧ ∃ u ∈ U, ∃ q : H.toSimpleGraph.Walk u w,
      ThroughW W q ∧ q.length ≤ i := by
  rw [mem_ball]
  constructor
  · rintro ⟨hw, u, hu, p, hp, hpW, hl⟩
    obtain ⟨q, hq, hql⟩ := exists_walk_of_path hp hpW
    exact ⟨hw, u, hu, q, hq, hql ▸ hl⟩
  · rintro ⟨hw, u, hu, q, hq, hl⟩
    obtain ⟨p, hp, hpW, hpl⟩ := exists_path_of_walk q hq
    exact ⟨hw, u, hu, p, hp, hpW, hpl.trans hl⟩

/-- Ball composition: `B^b(B^a(U,W),W) ⊆ B^{a+b}(U,W)`. -/
theorem ball_ball_subset {H : FGraph V} {a b : ℕ} {U W : Finset V} :
    ball H b (ball H a U W) W ⊆ ball H (a + b) U W := by
  intro y hy
  obtain ⟨hyW, z, hz, q₂, hq₂, hl₂⟩ := mem_ball_iff_walk.1 hy
  obtain ⟨hzW, u, hu, q₁, hq₁, hl₁⟩ := mem_ball_iff_walk.1 hz
  refine mem_ball_iff_walk.2 ⟨hyW, u, hu, q₁.append q₂, hq₁.append hq₂ hzW, ?_⟩
  rw [SimpleGraph.Walk.length_append]
  omega

theorem ball_union_subset {H : FGraph V} {i : ℕ} {A B W : Finset V} :
    ball H i (A ∪ B) W ⊆ ball H i A W ∪ ball H i B W := by
  intro w hw
  obtain ⟨hwW, u, hu, p, hp⟩ := mem_ball.1 hw
  rcases Finset.mem_union.1 hu with h | h
  · exact Finset.mem_union_left _ (mem_ball.2 ⟨hwW, u, h, p, hp⟩)
  · exact Finset.mem_union_right _ (mem_ball.2 ⟨hwW, u, h, p, hp⟩)

omit [DecidableEq V] in
theorem ball_empty {H : FGraph V} {i : ℕ} {W : Finset V} : ball H i ∅ W = ∅ := by
  ext w
  simp [mem_ball]

/-- Two balls of radius `R` around `x` and `y` that meet give an `xy`-path through `W` of length
at most `2R`. -/
theorem exists_path_of_mem_ball_inter {H : FGraph V} {R : ℕ} {W : Finset V} {x y z : V}
    (hx : z ∈ ball H R {x} W) (hy : z ∈ ball H R {y} W) :
    ∃ p, IsPathBetween H.edges x y p ∧ IsThrough W p ∧ pathLength p ≤ 2 * R := by
  obtain ⟨hzW, u, hu, q₁, hq₁, hl₁⟩ := mem_ball_iff_walk.1 hx
  obtain ⟨-, u', hu', q₂, hq₂, hl₂⟩ := mem_ball_iff_walk.1 hy
  rw [Finset.mem_singleton] at hu hu'
  subst hu hu'
  obtain ⟨p, hp, hpW, hpl⟩ := exists_path_of_walk _ (hq₁.append hq₂.reverse hzW)
  refine ⟨p, hp, hpW, hpl.trans ?_⟩
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-! ### The maximal-`r` argument -/

/-- `2^r ≤ t²` from `3^r ≤ t 2^r`. -/
theorem two_pow_le_sq {r t : ℕ} (h : 3 ^ r ≤ t * 2 ^ r) : 2 ^ r ≤ t ^ 2 := by
  have h1 : (3 ^ r) ^ 2 ≤ (t * 2 ^ r) ^ 2 := Nat.pow_le_pow_left h 2
  have h2 : 2 ^ r * 4 ^ r ≤ (3 ^ r) ^ 2 := by
    rw [← mul_pow, ← pow_mul, mul_comm r 2, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) r
  have h3 : (t * 2 ^ r) ^ 2 = t ^ 2 * 4 ^ r := by
    rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul]
    norm_num
  have h4 : 2 ^ r * 4 ^ r ≤ t ^ 2 * 4 ^ r := by omega
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

section Core

variable {G : FGraph V} {W S : Finset V} {ℓ t R : ℕ}

/-- `r` is feasible: some `X ⊆ S` has `|X| ≤ t (2/3)^r` and `|B^{(r+1)ℓ}(X, W)| > |W|/2`
(natural-number form). -/
def Feasible (G : FGraph V) (W S : Finset V) (ℓ t : ℕ) (r : ℕ) : Prop :=
  ∃ X ⊆ S, X.card * 3 ^ r ≤ t * 2 ^ r ∧ W.card < 2 * (ball G ((r + 1) * ℓ) X W).card

omit [DecidableEq V] in
theorem Feasible.two_pow_le {r : ℕ} (h : Feasible G W S ℓ t r) : 2 ^ r ≤ t ^ 2 := by
  obtain ⟨X, _, hX, hB⟩ := h
  have hne : X.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [ball_empty, Finset.card_empty] at hB
    omega
  have h1 : 1 ≤ X.card := Finset.card_pos.2 hne
  apply two_pow_le_sq
  calc 3 ^ r = 1 * 3 ^ r := (one_mul _).symm
    _ ≤ X.card * 3 ^ r := Nat.mul_le_mul_right _ h1
    _ ≤ t * 2 ^ r := hX

omit [DecidableEq V] in
theorem feasible_zero (hS : S ⊆ G.verts) (hSt : t ≤ S.card)
    (hball : ∀ U ⊆ G.verts, U.card = t → W.card < 2 * (ball G ℓ U W).card) :
    Feasible G W S ℓ t 0 := by
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq hSt
  refine ⟨T, hTS, by simp [hTc], ?_⟩
  rw [zero_add, one_mul]
  exact hball T (hTS.trans hS) hTc

theorem feasible_succ (hW : W ⊆ G.verts) (hWt : 4 * t ≤ W.card + 2)
    (hball : ∀ U ⊆ G.verts, U.card = t → W.card < 2 * (ball G ℓ U W).card)
    (hR : ∀ r : ℕ, 2 ^ r ≤ t ^ 2 → (r + 1) * ℓ ≤ R)
    (hsmall : ∀ s ∈ S, 2 * (ball G R {s} W).card ≤ W.card) {r : ℕ}
    (h : Feasible G W S ℓ t r) : Feasible G W S ℓ t (r + 1) := by
  have hrR := hR r h.two_pow_le
  obtain ⟨X, hXS, hX, hB⟩ := h
  -- `|X| ≥ 2`
  have hX2 : 2 ≤ X.card := by
    by_contra hlt
    rw [not_le] at hlt
    rcases Nat.lt_succ_iff.1 hlt |>.lt_or_eq with h0 | h1
    · have : X = ∅ := Finset.card_eq_zero.1 (by omega)
      subst this
      rw [ball_empty, Finset.card_empty] at hB
      omega
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
      have hxs := hsmall x (hXS (Finset.mem_singleton_self x))
      have := Finset.card_le_card (ball_mono_radius (H := G) (U := {x}) (W := W) hrR)
      omega
  -- split `X = X₀ ∪ X₁` with `3|Xᵢ| ≤ 2|X|`
  obtain ⟨X₀, hX₀X, hX₀c⟩ := Finset.exists_subset_card_eq (Nat.div_le_self X.card 2)
  set X₁ := X \ X₀ with hX₁
  have hX₁c : X₁.card = X.card - X.card / 2 := by
    rw [hX₁, Finset.card_sdiff_of_subset hX₀X, hX₀c]
  have hunion : X = X₀ ∪ X₁ := by
    rw [hX₁, Finset.union_sdiff_of_subset hX₀X]
  have hsmallX : ∀ Y : Finset V, Y ⊆ X → 3 * Y.card ≤ 2 * X.card →
      Y.card * 3 ^ (r + 1) ≤ t * 2 ^ (r + 1) := by
    intro Y _ hY
    calc Y.card * 3 ^ (r + 1) = (3 * Y.card) * 3 ^ r := by ring
      _ ≤ (2 * X.card) * 3 ^ r := Nat.mul_le_mul_right _ hY
      _ = 2 * (X.card * 3 ^ r) := by ring
      _ ≤ 2 * (t * 2 ^ r) := Nat.mul_le_mul_left _ hX
      _ = t * 2 ^ (r + 1) := by ring
  -- one of the two balls has at least `t` vertices
  have hBsplit : (ball G ((r + 1) * ℓ) X W).card ≤
      (ball G ((r + 1) * ℓ) X₀ W).card + (ball G ((r + 1) * ℓ) X₁ W).card := by
    rw [hunion]
    exact (Finset.card_le_card ball_union_subset).trans (Finset.card_union_le _ _)
  have hfinish : ∀ Y : Finset V, Y ⊆ X → 3 * Y.card ≤ 2 * X.card →
      t ≤ (ball G ((r + 1) * ℓ) Y W).card → Feasible G W S ℓ t (r + 1) := by
    intro Y hYX hY hBY
    obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq hBY
    have hT := hball T (hTB.trans (ball_subset.trans hW)) hTc
    have hsub : ball G ℓ T W ⊆ ball G ((r + 1 + 1) * ℓ) Y W := by
      have e : (r + 1 + 1) * ℓ = (r + 1) * ℓ + ℓ := by ring
      rw [e]
      exact (ball_mono_left hTB).trans ball_ball_subset
    refine ⟨Y, hYX.trans hXS, hsmallX Y hYX hY, ?_⟩
    have := Finset.card_le_card hsub
    omega
  by_cases h₀ : t ≤ (ball G ((r + 1) * ℓ) X₀ W).card
  · exact hfinish X₀ hX₀X (by omega) h₀
  · refine hfinish X₁ Finset.sdiff_subset (by omega) ?_
    omega

/-- The contradiction of [BM]'s proof: `t` vertices of `S` whose `R`-balls are all small
cannot exist. -/
theorem core (hW : W ⊆ G.verts) (hWt : 4 * t ≤ W.card + 2)
    (hball : ∀ U ⊆ G.verts, U.card = t → W.card < 2 * (ball G ℓ U W).card)
    (hR : ∀ r : ℕ, 2 ^ r ≤ t ^ 2 → (r + 1) * ℓ ≤ R)
    (hS : S ⊆ G.verts) (hSt : t ≤ S.card)
    (hsmall : ∀ s ∈ S, 2 * (ball G R {s} W).card ≤ W.card) : False := by
  have hall : ∀ r, Feasible G W S ℓ t r := by
    intro r
    induction r with
    | zero => exact feasible_zero hS hSt hball
    | succ r ih => exact feasible_succ hW hWt hball hR hsmall ih
  have h := (hall (2 * t)).two_pow_le
  have hlt : t < 2 ^ t := Nat.lt_two_pow_self
  have : t ^ 2 < 2 ^ (2 * t) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left hlt (by norm_num)
  omega

end Core

/-- [s1:citProp8] ([BM, Proposition 8]) "Let `1 ≤ ℓ, t ≤ n`. Let `G` be an `n`-vertex graph and
let `V ⊆ V(G)` be of size `|V| ≥ 4t − 2` such that, for every `U ⊆ V(G)` with `|U| = t`, we have
`|B^ℓ_G(U, V)| > |V|/2`. Let `x_1, …, x_{2t−1}, y_1, …, y_{2t−1}` be distinct vertices of `G`.
Then, for some `j ∈ [2t − 1]`, there is an `x_j y_j`-path in `G` through `V` with length at most
`4ℓ log n`." (`ℓ ≥ 1`, `ℓ ≤ n` and `t ≤ n` are not used.) -/
theorem bmProp8 {G : FGraph V} {W : Finset V} {ℓ t : ℕ} (ht : 1 ≤ t)
    (hW : W ⊆ G.verts) (hWt : 4 * t ≤ W.card + 2)
    (hball : ∀ U : Finset V, U ⊆ G.verts → U.card = t →
      (W.card : ℝ) / 2 < ((ball G ℓ U W).card : ℝ))
    (x y : Fin (2 * t - 1) → V) (hxy : ∀ i, x i ∈ G.verts ∧ y i ∈ G.verts)
    (hinj : Function.Injective (Sum.elim x y)) :
    ∃ (j : Fin (2 * t - 1)) (p : List V), IsPathBetween G.edges (x j) (y j) p ∧
      IsThrough W p ∧ (pathLength p : ℝ) ≤ 4 * (ℓ : ℝ) * Real.logb 2 (G.card : ℝ) := by
  classical
  set n := G.card with hn
  have hWn : W.card ≤ n := Finset.card_le_card hW
  have hball' : ∀ U ⊆ G.verts, U.card = t → W.card < 2 * (ball G ℓ U W).card := by
    intro U hU hc
    have h1 := hball U hU hc
    have h2 : (W.card : ℝ) < 2 * ((ball G ℓ U W).card : ℝ) := by linarith
    exact_mod_cast h2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hn1
  set R := ⌊2 * (ℓ : ℝ) * Real.logb 2 (n : ℝ)⌋₊ with hRdef
  have hR2 : 2 * (R : ℝ) ≤ 4 * (ℓ : ℝ) * Real.logb 2 n := by
    have := Nat.floor_le (show 0 ≤ 2 * (ℓ : ℝ) * Real.logb 2 n by positivity)
    linarith
  have hR : ∀ r : ℕ, 2 ^ r ≤ t ^ 2 → (r + 1) * ℓ ≤ R := by
    intro r hr
    have h2t : 2 * t ≤ n := by omega
    have h1 : 2 ^ (r + 1) ≤ n ^ 2 := by
      have e1 : 2 ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
      have e2 : (2 * t) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h2t 2
      have e3 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      omega
    have h2 : ((r + 1 : ℕ) : ℝ) ≤ 2 * Real.logb 2 n := by
      have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h3 : ((r + 1 : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) ^ 2) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
        exact_mod_cast h1
      rwa [Real.logb_pow, Nat.cast_ofNat] at h3
    apply Nat.le_floor
    push_cast at h2 ⊢
    have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    nlinarith
  by_contra hcon
  push Not at hcon
  -- for every `j`, one of the two `R`-balls is small
  have hsplit : ∀ j, 2 * (ball G R {x j} W).card ≤ W.card ∨
      2 * (ball G R {y j} W).card ≤ W.card := by
    intro j
    by_contra hj
    push Not at hj
    have hU : ball G R {x j} W ∪ ball G R {y j} W ⊆ W :=
      Finset.union_subset ball_subset ball_subset
    have hc := Finset.card_union_add_card_inter (ball G R {x j} W) (ball G R {y j} W)
    have hcU := Finset.card_le_card hU
    have hne : (ball G R {x j} W ∩ ball G R {y j} W).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨z, hz⟩ := hne
    rw [Finset.mem_inter] at hz
    obtain ⟨p, hp, hpW, hpl⟩ := exists_path_of_mem_ball_inter hz.1 hz.2
    have := hcon j p hp hpW
    have hpl' : (pathLength p : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hpl
    linarith
  -- the index sets `I_x`, `I_y`
  have hcase : ∀ z : Fin (2 * t - 1) → V, Function.Injective z → (∀ i, z i ∈ G.verts) →
      ¬ t ≤ (Finset.univ.filter fun j => 2 * (ball G R {z j} W).card ≤ W.card).card := by
    intro z hz hzV hc
    refine core (S := (Finset.univ.filter fun j => 2 * (ball G R {z j} W).card ≤ W.card).image z)
      hW hWt hball' hR ?_ ?_ ?_
    · intro v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
      exact hzV j
    · rwa [Finset.card_image_of_injective _ hz]
    · intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
      exact (Finset.mem_filter.1 hj).2
  have hxinj : Function.Injective x := fun a b h => Sum.inl_injective (hinj (by simpa using h))
  have hyinj : Function.Injective y := fun a b h => Sum.inr_injective (hinj (by simpa using h))
  have hunion : (Finset.univ.filter fun j => 2 * (ball G R {x j} W).card ≤ W.card) ∪
      (Finset.univ.filter fun j => 2 * (ball G R {y j} W).card ≤ W.card) = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hsplit j
  have hcard := Finset.card_union_le
    (Finset.univ.filter fun j => 2 * (ball G R {x j} W).card ≤ W.card)
    (Finset.univ.filter fun j => 2 * (ball G R {y j} W).card ≤ W.card)
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := hcase x hxinj (fun i => (hxy i).1)
  have h2 := hcase y hyinj (fun i => (hxy i).2)
  omega

end BM8

end EG
