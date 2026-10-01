module

public import EG.Defs.Link.HBFamily
public import EG.Lib.Found.Graph
public import Mathlib.Combinatorics.Hall.Basic

/-!
# Lemma HB (manuscript s3:lemHB): the Hall argument — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemHB]. The auxiliary bipartite graph has left
side the ordered pairs `(w,u)` along edges, right side the slots `(u,j,1)` (`j ∈ [b]`, load slots
of `u`) and `(w,i,2)` (`i ∈ [d_X(w)-m]`, spare slots of `w`); `(w,u)` is joined to the load slots
of `u` and the spare slots of `w`. Slots are encoded as `V × ℕ × Bool` (`true` = load,
`false` = spare, indices `0`-based).

* `EG.HBLemma.exists_subset_half`: the choice of `𝒰 ⊆ 𝒮'` with `1 ≤ |𝒰| ≤ 2N/3`, `|𝒰| ≥ |𝒮'|/2`;
* `EG.HBLemma.expansion_step`: `|ℛ| ≥ ε'|𝒮'|/(2L^2)` from the expansion of `X`;
* `EG.HBLemma.hall_cond`: Hall's condition (s3:eqHBhall);
* `EG.HBLemma.exists_family`: the lemma (Hall's theorem is Mathlib's
  `Finset.all_card_le_biUnion_card_iff_exists_injective`).
-/

public section

namespace EG.HBLemma

open Finset

variable {V : Type*} [DecidableEq V]

/-- The slots joined to the pair `a = (w,u)`: the `b` load slots of `u` and the `d_X(w)-m`
spare slots of `w`. -/
@[expose] def T (X : FGraph V) (m b : ℕ) (a : V × V) : Finset (V × ℕ × Bool) :=
  (range b).image (fun j => (a.2, j, true)) ∪ (range (X.deg a.1 - m)).image (fun i => (a.1, i, false))

theorem mem_T {X : FGraph V} {m b : ℕ} {a : V × V} {x : V × ℕ × Bool} :
    x ∈ T X m b a ↔ (x.2.2 = true ∧ x.1 = a.2 ∧ x.2.1 < b) ∨
      (x.2.2 = false ∧ x.1 = a.1 ∧ x.2.1 < X.deg a.1 - m) := by
  obtain ⟨x1, x2, x3⟩ := x
  simp only [T, mem_union, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨j, hj, rfl, rfl, rfl⟩ | ⟨i, hi, rfl, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl, hj⟩
    · exact Or.inr ⟨rfl, rfl, hi⟩
  · rintro (⟨rfl, rfl, hj⟩ | ⟨rfl, rfl, hi⟩)
    · exact Or.inl ⟨x2, hj, rfl, rfl, rfl⟩
    · exact Or.inr ⟨x2, hi, rfl, rfl, rfl⟩

/-- The choice of `𝒰`: "If `|𝒮'| ≤ 2N/3`, put `𝒰 := 𝒮'`. Otherwise let `𝒰 ⊆ 𝒮'` be any set
with `|𝒰| = ⌈|𝒮'|/2⌉`; then `1 ≤ |𝒰| ≤ ⌈N/2⌉ ≤ 2N/3`, because `N ≥ 2`." -/
theorem exists_subset_half (S' : Finset V) (N : ℕ) (hN : 2 ≤ N) (hS'N : S'.card ≤ N)
    (hne : S'.Nonempty) :
    ∃ U ⊆ S', 1 ≤ U.card ∧ (U.card : ℝ) ≤ 2 * (N : ℝ) / 3 ∧ (S'.card : ℝ) ≤ 2 * (U.card : ℝ) := by
  have hk : 1 ≤ S'.card := Finset.card_pos.2 hne
  by_cases hsmall : (S'.card : ℝ) ≤ 2 * (N : ℝ) / 3
  · refine ⟨S', subset_rfl, hk, hsmall, ?_⟩
    have : (0 : ℝ) ≤ S'.card := Nat.cast_nonneg _
    linarith
  · obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq (s := S') (n := (S'.card + 1) / 2)
      (by omega)
    refine ⟨U, hU, by omega, ?_, ?_⟩
    · rw [hUc]
      have h3 : 3 * ((S'.card + 1) / 2) ≤ 2 * N := by omega
      have h3' : (3 : ℝ) * (((S'.card + 1) / 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h3
      linarith
    · rw [hUc]
      have h2 : S'.card ≤ 2 * ((S'.card + 1) / 2) := by omega
      exact_mod_cast h2

/-- The expansion step of the proof of Lemma HB: if every `w ∈ 𝒮'` has at most `m-1`
neighbours outside `ℛ`, then `|ℛ| ≥ |Nbr_{X-F}(𝒰)| ≥ ε'|𝒰|/L^2 ≥ ε'|𝒮'|/(2L^2)`. -/
theorem expansion_step (X : FGraph V) {ε' s : ℝ} {m : ℕ} (hX : X.IsExpander ε' s)
    (hN : 2 ≤ X.card) (hε : 0 ≤ ε') (hs : 2 * (m : ℝ) ≤ s) (S' R : Finset V)
    (hS' : S' ⊆ X.verts) (hne : S'.Nonempty)
    (hout : ∀ w ∈ S', (X.nbrs w \ R).card ≤ m - 1) :
    ε' * (S'.card : ℝ) / (2 * Real.logb 2 (X.card : ℝ) ^ 2) ≤ (R.card : ℝ) := by
  obtain ⟨U, hUS, hU1, hU2, hU3⟩ := exists_subset_half S' X.card hN
    (by rw [FGraph.card_def]; exact Finset.card_le_card hS') hne
  set F : Finset (Sym2 V) := U.biUnion (fun w => (X.nbrs w \ R).image (fun u => s(w, u)))
    with hFdef
  have hF : F ⊆ X.edges := by
    intro e he
    obtain ⟨w, -, he⟩ := Finset.mem_biUnion.1 he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
    exact FGraph.mem_nbrs.1 (Finset.mem_sdiff.1 hu).1
  have hFc : (F.card : ℝ) ≤ s * (U.card : ℝ) := by
    have h1 : F.card ≤ ∑ w ∈ U, ((X.nbrs w \ R).image (fun u => s(w, u))).card :=
      Finset.card_biUnion_le
    have h2 : ∑ w ∈ U, ((X.nbrs w \ R).image (fun u => s(w, u))).card ≤ ∑ _w ∈ U, (m - 1) :=
      Finset.sum_le_sum fun w hw => (Finset.card_image_le).trans (hout w (hUS hw))
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 : (F.card : ℝ) ≤ (U.card : ℝ) * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
    have h4 : ((m - 1 : ℕ) : ℝ) ≤ s := by
      have : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
    nlinarith
  have key := hX U F (hUS.trans hS') hF hU1 hU2 hFc
  have hsub : (X.deleteEdges F).nbrSet U ⊆ R := by
    intro v hv
    rw [FGraph.mem_nbrSet] at hv
    obtain ⟨-, hvU, u, huU, hadj⟩ := hv
    by_contra hvR
    have hadj' : s(u, v) ∈ X.edges \ F := by
      rw [FGraph.adj_iff, FGraph.deleteEdges_edges] at hadj; exact hadj
    rw [Finset.mem_sdiff] at hadj'
    apply hadj'.2
    rw [hFdef, Finset.mem_biUnion]
    refine ⟨u, huU, Finset.mem_image.2 ⟨v, Finset.mem_sdiff.2 ⟨?_, hvR⟩, rfl⟩⟩
    exact FGraph.mem_nbrs.2 hadj'.1
  have hR : (((X.deleteEdges F).nbrSet U).card : ℝ) ≤ R.card := by
    exact_mod_cast Finset.card_le_card hsub

  refine le_trans ?_ (key.trans hR)
  have hL : 0 ≤ Real.logb 2 (X.card : ℝ) ^ 2 := sq_nonneg _
  rw [show ε' * (S'.card : ℝ) / (2 * Real.logb 2 (X.card : ℝ) ^ 2) =
      (ε' * (S'.card : ℝ) / 2) / Real.logb 2 (X.card : ℝ) ^ 2 by rw [div_div]]
  apply div_le_div_of_nonneg_right _ hL
  nlinarith

/-- Hall's condition (s3:eqHBhall): for every set `ℰ` of pairs along edges,
`|ℰ| ≤ |⋃_{a ∈ ℰ} 𝒯(a)|`. -/
theorem hall_cond (X : FGraph V) {ε' s : ℝ} {m b : ℕ} (hX : X.IsExpander ε' s)
    (hN : 2 ≤ X.card) (hε : 0 < ε') (hs : 2 * (m : ℝ) ≤ s)
    (hb : 2 * (m : ℝ) * Real.logb 2 (X.card : ℝ) ^ 2 / ε' ≤ b)
    (E : Finset (V × V)) (hE : ∀ a ∈ E, a.1 ∈ X.verts ∧ X.Adj a.1 a.2) :
    E.card ≤ (E.biUnion (T X m b)).card := by
  classical
  set S := E.image Prod.fst with hSdef
  set R := E.image Prod.snd with hRdef
  set Ew : V → Finset (V × V) := fun w => E.filter (fun a => a.1 = w) with hEwdef
  have hsum : E.card = ∑ w ∈ S, (Ew w).card :=
    Finset.card_eq_sum_card_fiberwise (fun a ha => Finset.mem_image_of_mem _ ha)
  -- `|ℰ_w| ≤ d_X(w)`: the second coordinates are distinct neighbours of `w`
  have hEw_img : ∀ w, ((Ew w).image Prod.snd).card = (Ew w).card := fun w =>
    Finset.card_image_of_injOn (fun a ha b hb h => by
      have ha' := (Finset.mem_filter.1 ha).2
      have hb' := (Finset.mem_filter.1 hb).2
      exact Prod.ext (ha'.trans hb'.symm) h)
  have hEw_sub : ∀ w, (Ew w).image Prod.snd ⊆ X.nbrs w := fun w u hu => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
    have haE : a ∈ E := (Finset.mem_filter.1 ha).1
    have haw : a.1 = w := (Finset.mem_filter.1 ha).2
    rw [← haw]
    exact FGraph.mem_nbrs.2 (hE a haE).2
  have hEw_le : ∀ w, (Ew w).card ≤ X.deg w := fun w => by
    rw [← hEw_img w, FGraph.deg_def]; exact Finset.card_le_card (hEw_sub w)
  have hdeg : ∀ w ∈ S, m ≤ X.deg w := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
    have h1 := hX.lt_deg hε hN (hE a ha).1
    have : (m : ℝ) ≤ X.deg a.1 := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  set S' := S.filter (fun w => X.deg w < (Ew w).card + m) with hS'def
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  -- `|ℰ| ≤ Σ_{w∈𝒮} (d_X(w) - m) + m|𝒮'|`
  have hle1 : E.card ≤ ∑ w ∈ S, (X.deg w - m) + m * S'.card := by
    have hpt : ∀ w ∈ S, (Ew w).card ≤ (X.deg w - m) + (if w ∈ S' then m else 0) := by
      intro w hw
      have h1 := hEw_le w
      have h2 := hdeg w hw
      by_cases h : w ∈ S'
      · rw [if_pos h]; omega
      · rw [if_neg h]
        have : ¬ X.deg w < (Ew w).card + m := fun h' => h (Finset.mem_filter.2 ⟨hw, h'⟩)
        omega
    rw [hsum]
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hS'S,
      Finset.sum_const, smul_eq_mul, mul_comm]
  -- the union contains all load slots of `ℛ` and all spare slots of `𝒮`
  set LR : Finset (V × ℕ × Bool) := (R ×ˢ range b).image (fun p => (p.1, p.2, true)) with hLR
  set SP : Finset (V × ℕ × Bool) :=
    S.biUnion (fun w => (range (X.deg w - m)).image (fun i => (w, i, false))) with hSP
  have hLRc : LR.card = R.card * b := by
    rw [hLR, Finset.card_image_of_injective _ (fun p q h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1), Finset.card_product,
      Finset.card_range]
  have hSPc : SP.card = ∑ w ∈ S, (X.deg w - m) := by
    rw [hSP, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.card_image_of_injective _ (fun i j h => by
        simp only [Prod.mk.injEq] at h; exact h.2.1), Finset.card_range]
    · intro w _ w' _ hww'
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx'
      simp only [Prod.mk.injEq] at hj
      exact hww' hj.1.symm
  have hdisj : Disjoint LR SP := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 hx'
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hw
    simp only [Prod.mk.injEq] at hi
    exact Bool.false_ne_true hi.2.2
  have hsub : LR ∪ SP ⊆ E.biUnion (T X m b) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_biUnion]
    rcases hx with hx | hx
    · obtain ⟨⟨u, j⟩, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hu, hj⟩ := Finset.mem_product.1 hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨a, ha, mem_T.2 (Or.inl ⟨rfl, rfl, Finset.mem_range.1 hj⟩)⟩
    · obtain ⟨w, hw, hx⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨a, ha, mem_T.2 (Or.inr ⟨rfl, rfl, Finset.mem_range.1 hi⟩)⟩
  have hU : R.card * b + ∑ w ∈ S, (X.deg w - m) ≤ (E.biUnion (T X m b)).card := by
    rw [← hLRc, ← hSPc, ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  -- the expansion step: `m|𝒮'| ≤ b|ℛ|`
  have hexp : m * S'.card ≤ R.card * b := by
    rcases S'.eq_empty_or_nonempty with h0 | hne
    · rw [h0, Finset.card_empty, mul_zero]; exact Nat.zero_le _
    have hS'v : S' ⊆ X.verts := fun w hw => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hS'S hw)
      exact (hE a ha).1
    have hout : ∀ w ∈ S', (X.nbrs w \ R).card ≤ m - 1 := by
      intro w hw
      have hlt := (Finset.mem_filter.1 hw).2
      have hsub1 : X.nbrs w \ R ⊆ X.nbrs w \ (Ew w).image Prod.snd := by
        apply Finset.sdiff_subset_sdiff subset_rfl
        intro u hu
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.1 ha).1
      have hc := Finset.card_le_card hsub1
      rw [Finset.card_sdiff_of_subset (hEw_sub w), hEw_img w, ← FGraph.deg_def] at hc
      omega
    have h := expansion_step X hX hN hε.le hs S' R hS'v hne hout
    have hL : 0 < Real.logb 2 (X.card : ℝ) := by
      apply Real.logb_pos (by norm_num); exact_mod_cast hN
    have hL2 : 0 < Real.logb 2 (X.card : ℝ) ^ 2 := by positivity
    have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
    have hreal : (m : ℝ) * (S'.card : ℝ) ≤ (R.card : ℝ) * (b : ℝ) := by
      have h1 : 2 * (m : ℝ) * Real.logb 2 (X.card : ℝ) ^ 2 / ε' * (ε' * (S'.card : ℝ) /
          (2 * Real.logb 2 (X.card : ℝ) ^ 2)) = (m : ℝ) * (S'.card : ℝ) := by
        field_simp
      have h2 : 0 ≤ 2 * (m : ℝ) * Real.logb 2 (X.card : ℝ) ^ 2 / ε' := by positivity
      have h3 : 0 ≤ ε' * (S'.card : ℝ) / (2 * Real.logb 2 (X.card : ℝ) ^ 2) := by positivity
      rw [← h1, mul_comm (R.card : ℝ)]
      exact mul_le_mul hb h (by positivity) (Nat.cast_nonneg _)
    exact_mod_cast hreal
  calc E.card ≤ ∑ w ∈ S, (X.deg w - m) + m * S'.card := hle1
    _ ≤ ∑ w ∈ S, (X.deg w - m) + R.card * b := Nat.add_le_add_left hexp _
    _ = R.card * b + ∑ w ∈ S, (X.deg w - m) := Nat.add_comm _ _
    _ ≤ _ := hU

/-- [s3:lemHB] Lemma HB, with any integer `b ≥ 2mL^2/ε'`: every vertex `w` has a set
`A(w) ⊆ N_X(w)` with `|A(w)| = m`, and every vertex lies in at most `b` of the sets `A(w)`. -/
theorem exists_family (X : FGraph V) {ε' s : ℝ} {m b : ℕ} (hX : X.IsExpander ε' s)
    (hN : 2 ≤ X.card) (hε : 0 < ε') (hs : 2 * (m : ℝ) ≤ s)
    (hb : 2 * (m : ℝ) * Real.logb 2 (X.card : ℝ) ^ 2 / ε' ≤ b) :
    ∃ A : V → Finset V, IsHBFamily X m b A := by
  classical
  set J : Finset (V × V) := (X.verts ×ˢ X.verts).filter (fun p => X.Adj p.1 p.2) with hJ
  have hJmem : ∀ {a : V × V}, a ∈ J ↔ a.1 ∈ X.verts ∧ X.Adj a.1 a.2 := by
    intro a
    rw [hJ, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.mem_verts_right⟩, h3⟩
  -- Hall's theorem on the index set `J`
  obtain ⟨χ, hχinj, hχT⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun a : J => T X m b a.1)).1 (fun sJ => by
      have e : sJ.biUnion (fun a : J => T X m b a.1) =
          (sJ.map (Function.Embedding.subtype _)).biUnion (T X m b) := by
        ext x; simp
      rw [e, ← Finset.card_map (Function.Embedding.subtype _)]
      refine hall_cond X hX hN hε hs hb _ fun a ha => ?_
      obtain ⟨a', -, rfl⟩ := Finset.mem_map.1 ha
      exact hJmem.1 a'.2)
  set χ' : V × V → V × ℕ × Bool := fun a => if h : a ∈ J then χ ⟨a, h⟩ else (a.1, 0, false)
    with hχ'
  have hχ'T : ∀ a ∈ J, χ' a ∈ T X m b a := fun a ha => by
    simp only [hχ', dif_pos ha]; exact hχT ⟨a, ha⟩
  have hχ'inj : ∀ a ∈ J, ∀ a' ∈ J, χ' a = χ' a' → a = a' := fun a ha a' ha' h => by
    simp only [hχ', dif_pos ha, dif_pos ha'] at h
    exact congrArg Subtype.val (hχinj h)
  have hnbJ : ∀ {w u : V}, w ∈ X.verts → u ∈ X.nbrs w → (w, u) ∈ J := fun hw hu =>
    hJmem.2 ⟨hw, FGraph.mem_nbrs.1 hu⟩
  set good : V → Finset V := fun w => (X.nbrs w).filter (fun u => (χ' (w, u)).2.2 = true)
    with hgood
  -- at least `m` pairs at `w` go to load slots
  have hgood_card : ∀ w ∈ X.verts, m ≤ (good w).card := by
    intro w hw
    have hbad : ((X.nbrs w).filter (fun u => ¬ (χ' (w, u)).2.2 = true)).card ≤ X.deg w - m := by
      have := Finset.card_le_card_of_injOn (fun u => χ' (w, u))
        (s := (X.nbrs w).filter (fun u => ¬ (χ' (w, u)).2.2 = true))
        (t := (range (X.deg w - m)).image (fun i => (w, i, false)))
        (fun u hu => by
          have hu' := Finset.mem_filter.1 hu
          have hT := mem_T.1 (hχ'T _ (hnbJ hw hu'.1))
          rcases hT with ⟨h1, -, -⟩ | ⟨h1, h2, h3⟩
          · exact absurd h1 hu'.2
          · exact Finset.mem_image.2 ⟨(χ' (w, u)).2.1, Finset.mem_range.2 h3,
              Prod.ext h2.symm (Prod.ext rfl h1.symm)⟩)
        (fun u hu u' hu' h => by
          have := hχ'inj _ (hnbJ hw (Finset.mem_filter.1 hu).1) _
            (hnbJ hw (Finset.mem_filter.1 hu').1) h
          exact (Prod.ext_iff.1 this).2)
      rwa [Finset.card_image_of_injective _ (fun i j h => by
        simp only [Prod.mk.injEq] at h; exact h.2.1), Finset.card_range] at this
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := X.nbrs w) (fun u => (χ' (w, u)).2.2 = true)
    have hm : m ≤ X.deg w := by
      have h1 := hX.lt_deg hε hN hw
      have : (m : ℝ) ≤ X.deg w := by
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith
      exact_mod_cast this
    rw [← FGraph.deg_def] at hsplit
    simp only [hgood]
    omega
  have hex : ∀ w, ∃ A : Finset V, A ⊆ good w ∧ (w ∈ X.verts → A.card = m) := by
    intro w
    by_cases hw : w ∈ X.verts
    · obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq (hgood_card w hw)
      exact ⟨A, hA, fun _ => hAc⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hw⟩
  choose A hAgood hAcard using hex
  refine ⟨A, fun w hw => ⟨(hAgood w).trans (Finset.filter_subset _ _), hAcard w hw⟩, ?_⟩
  -- every vertex lies in at most `b` sets `A(w)`
  intro u
  have := Finset.card_le_card_of_injOn (fun w => χ' (w, u))
    (s := X.verts.filter (fun w => u ∈ A w))
    (t := (range b).image (fun j => (u, j, true)))
    (fun w hw => by
      have hw' := Finset.mem_filter.1 hw
      have hu := Finset.mem_filter.1 (hAgood w hw'.2)
      have hT := mem_T.1 (hχ'T _ (hnbJ hw'.1 hu.1))
      rcases hT with ⟨h1, h2, h3⟩ | ⟨h1, -, -⟩
      · exact Finset.mem_image.2 ⟨(χ' (w, u)).2.1, Finset.mem_range.2 h3,
          Prod.ext h2.symm (Prod.ext rfl h1.symm)⟩
      · rw [hu.2] at h1; exact absurd h1 (by decide))
    (fun w hw w' hw' h => by
      have hw1 := Finset.mem_filter.1 hw
      have hw2 := Finset.mem_filter.1 hw'
      have hu1 := (Finset.mem_filter.1 (hAgood w hw1.2)).1
      have hu2 := (Finset.mem_filter.1 (hAgood w' hw2.2)).1
      have := hχ'inj _ (hnbJ hw1.1 hu1) _ (hnbJ hw2.1 hu2) h
      exact (Prod.ext_iff.1 this).1)
  rwa [Finset.card_image_of_injective _ (fun i j h => by
    simp only [Prod.mk.injEq] at h; exact h.2.1), Finset.card_range] at this

end EG.HBLemma
