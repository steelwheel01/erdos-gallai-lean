module

public import EG.Defs.Stage1.COL
public import EG.Lib.Found.ColourClass
public import EG.Lib.HB.Run
public import EG.Lib.Prob.Indep

/-!
# API for the stage-1 lending data (s3:defCOL)

Lemmas about `EG.Stage1` (`EG/Defs/Stage1/COL.lean`):
* index families: membership (`mem_IU`, `mem_IJS`, `mem_IJV`), pairwise disjointness,
  `klend_eq_card_lentIdx` (the manuscript's `|I^U| + |I^JS| + |I^JV|` is the size of the tagged
  union), `lentIdx_eq_empty_iff` ("If `r ≥ R-1`, all three families are empty"),
  `klend_pos_iff`, `card_IU`, `card_IJV`;
* parameters: `KJS_mul_rhoJS` (`K^JS_l ρ_l = M_l^{-2}`), `rhoJS_le_one`, `one_le_kown`;
* `ownIdx`: values of the bijection (`ownIdx_none`, `ownIdx_some`);
* classes: `*_eq_colourClass` (by `rfl`), vertex sets (`V(Y)`), edge membership, partition facts
  (`disjoint_Own_Lend`, `Own_union_Lend`, `disjoint_ownClass`, `biUnion_ownClass`,
  `disjoint_lentClass`, `biUnion_lentClass_of_mem_supp`) and `COLg_of_mem_supp`
  ([s3:lemCOL] (g) holds on the support of `colouringLaw`), `COLg_of_mem_supp_colLaw`,
  `COLg_of_map_eq` (the support forms used by the lemCOL Specs);
* `Tj`: `Tj_subset`, `disjoint_Tj` ("the sets `T_j(Y,l)`, `0 ≤ j < K^JS_l`, are pairwise
  disjoint");
* laws: point masses of `jsLabelLaw` and `idxLaw`, `prob_mem_LJV` ("`p_Y` … is the probability
  that a fixed edge of `H_Y` lies in `LJV_{Y,l}`"), `prob_mem_ownClass`, `prob_mem_ownM`
  (`P(e ∈ M_Y) = 1/(2k_own)`, [s5:lemE1] (a)), `isRSubset_Tj` ("for fixed `(l,j)`, the set
  `T_j(Y,l)` is a `ρ_l`-random subset of `V(Y)`");
* labels given the bits (COL-RANDOM-EDGESET): `edgeBits`, `edgeLabels`,
  `indepFun_edgeBits_edgeLabels`, `map_edgeLabels_cond_edgeBits`, `map_idx_cond_edgeBits`,
  `map_own_cond_edgeBits`, `idxLaw_eq_of_nonempty`.
-/

public section

namespace EG.Stage1

open EG.HB EG.FinDist Finset

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

/-! ### Index families -/

omit [DecidableEq V] in
theorem mem_lateRounds {r l : ℕ} : l ∈ lateRounds run r ↔ r + 2 ≤ l ∧ l ≤ run.R := by
  simp [lateRounds]

omit [DecidableEq V] in
theorem lateRounds_eq_empty_iff {r : ℕ} : lateRounds run r = ∅ ↔ run.R < r + 2 := by
  rw [lateRounds, Finset.Icc_eq_empty_iff]
  omega

omit [DecidableEq V] in
theorem lateRounds_nonempty_iff {r : ℕ} : (lateRounds run r).Nonempty ↔ r + 2 ≤ run.R := by
  rw [Finset.nonempty_iff_ne_empty, Ne, lateRounds_eq_empty_iff]
  omega

omit [DecidableEq V] in
theorem card_lateRounds (r : ℕ) : (lateRounds run r).card = run.R + 1 - (r + 2) := by
  simp [lateRounds]

variable {G run}

theorem mem_IU {Y : PartId} {i : LentTag} :
    i ∈ IU G run Y ↔ run.isLight G Y.1 Y.2 ∧
      ∃ l c σ, i = LentTag.U l c σ ∧ l ∈ lateRounds run Y.1 ∧ σ < Tslot G run Y := by
  classical
  unfold IU
  split_ifs with h
  · simp only [mem_image, mem_product, mem_univ, mem_range, true_and, h]
    constructor
    · rintro ⟨⟨l, c, σ⟩, ⟨hl, hσ⟩, rfl⟩
      exact ⟨l, c, σ, rfl, hl, hσ⟩
    · rintro ⟨l, c, σ, rfl, hl, hσ⟩
      exact ⟨⟨l, c, σ⟩, ⟨hl, hσ⟩, rfl⟩
  · simp [h]

theorem mem_IJS {Y : PartId} {i : LentTag} :
    i ∈ IJS G run Y ↔ ∃ l j, i = LentTag.JS l j ∧ l ∈ lateRounds run Y.1 ∧ j < KJS G run l := by
  simp only [IJS, mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨l, hl, j, hj, rfl⟩
    exact ⟨l, j, rfl, hl, hj⟩
  · rintro ⟨l, j, rfl, hl, hj⟩
    exact ⟨l, hl, j, hj, rfl⟩

omit [DecidableEq V] in
theorem mem_IJV {Y : PartId} {i : LentTag} :
    i ∈ IJV run Y ↔ ∃ l, i = LentTag.JV l ∧ l ∈ lateRounds run Y.1 := by
  simp only [IJV, mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, rfl, hl⟩
  · rintro ⟨l, rfl, hl⟩
    exact ⟨l, hl, rfl⟩

@[simp] theorem U_mem_IU {Y : PartId} {l : ℕ} {c : Fin 4} {σ : ℕ} :
    LentTag.U l c σ ∈ IU G run Y ↔
      run.isLight G Y.1 Y.2 ∧ l ∈ lateRounds run Y.1 ∧ σ < Tslot G run Y := by
  rw [mem_IU]
  constructor
  · rintro ⟨h, l', c', σ', he, hl, hσ⟩
    cases he
    exact ⟨h, hl, hσ⟩
  · rintro ⟨h, hl, hσ⟩
    exact ⟨h, l, c, σ, rfl, hl, hσ⟩

@[simp] theorem JS_mem_IJS {Y : PartId} {l j : ℕ} :
    LentTag.JS l j ∈ IJS G run Y ↔ l ∈ lateRounds run Y.1 ∧ j < KJS G run l := by
  rw [mem_IJS]
  constructor
  · rintro ⟨l', j', he, hl, hj⟩
    cases he
    exact ⟨hl, hj⟩
  · rintro ⟨hl, hj⟩
    exact ⟨l, j, rfl, hl, hj⟩

omit [DecidableEq V] in
@[simp] theorem JV_mem_IJV {Y : PartId} {l : ℕ} :
    LentTag.JV l ∈ IJV run Y ↔ l ∈ lateRounds run Y.1 := by
  rw [mem_IJV]
  constructor
  · rintro ⟨l', he, hl⟩
    cases he
    exact hl
  · intro hl
    exact ⟨l, rfl, hl⟩

theorem disjoint_IU_IJS (Y : PartId) : Disjoint (IU G run Y) (IJS G run Y) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  obtain ⟨-, l, c, σ, rfl, -⟩ := mem_IU.1 h1
  obtain ⟨l', j, he, -⟩ := mem_IJS.1 h2
  cases he

theorem disjoint_IU_IJV (Y : PartId) : Disjoint (IU G run Y) (IJV run Y) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  obtain ⟨-, l, c, σ, rfl, -⟩ := mem_IU.1 h1
  obtain ⟨l', he, -⟩ := mem_IJV.1 h2
  cases he

theorem disjoint_IJS_IJV (Y : PartId) : Disjoint (IJS G run Y) (IJV run Y) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  obtain ⟨l, j, rfl, -⟩ := mem_IJS.1 h1
  obtain ⟨l', he, -⟩ := mem_IJV.1 h2
  cases he

theorem mem_lentIdx {Y : PartId} {i : LentTag} :
    i ∈ lentIdx G run Y ↔ i ∈ IU G run Y ∨ i ∈ IJS G run Y ∨ i ∈ IJV run Y := by
  simp [lentIdx]

/-- [s3:defCOL] (ii) `k_lend(Y) = |I^U(Y)| + |I^JS(Y)| + |I^JV(Y)|` is the size of the tagged
union from which the lent index is drawn. -/
theorem klend_eq_card_lentIdx (Y : PartId) : klend G run Y = (lentIdx G run Y).card := by
  rw [lentIdx, card_union_of_disjoint, card_union_of_disjoint (disjoint_IU_IJS Y), klend]
  exact Finset.disjoint_union_left.2 ⟨disjoint_IU_IJV Y, disjoint_IJS_IJV Y⟩

theorem lentIdx_eq_empty_iff {Y : PartId} : lentIdx G run Y = ∅ ↔ run.R < Y.1 + 2 := by
  constructor
  · intro h
    by_contra hR
    have hl : Y.1 + 2 ∈ lateRounds run Y.1 := (mem_lateRounds run).2 ⟨le_rfl, by omega⟩
    have : LentTag.JV (Y.1 + 2) ∈ lentIdx G run Y := mem_lentIdx.2 (Or.inr (Or.inr
      (JV_mem_IJV.2 hl)))
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro hR
    have he : lateRounds run Y.1 = ∅ := (lateRounds_eq_empty_iff run).2 hR
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rcases mem_lentIdx.1 hi with h | h | h
    · obtain ⟨-, l, c, σ, -, hl, -⟩ := mem_IU.1 h
      rw [he] at hl; exact Finset.notMem_empty _ hl
    · obtain ⟨l, j, -, hl, -⟩ := mem_IJS.1 h
      rw [he] at hl; exact Finset.notMem_empty _ hl
    · obtain ⟨l, -, hl⟩ := mem_IJV.1 h
      rw [he] at hl; exact Finset.notMem_empty _ hl

theorem lentIdx_nonempty_iff {Y : PartId} : (lentIdx G run Y).Nonempty ↔ Y.1 + 2 ≤ run.R := by
  rw [Finset.nonempty_iff_ne_empty, Ne, lentIdx_eq_empty_iff]
  omega

/-- `k_lend(Y) ≥ 1` iff `r ≤ R - 2`. -/
theorem klend_pos_iff {Y : PartId} : 0 < klend G run Y ↔ Y.1 + 2 ≤ run.R := by
  rw [klend_eq_card_lentIdx, Finset.card_pos, lentIdx_nonempty_iff]

omit [DecidableEq V] in
theorem card_IJV (Y : PartId) : (IJV run Y).card = run.R + 1 - (Y.1 + 2) := by
  rw [IJV, card_image_of_injective _ (fun a b h => by cases h; rfl), card_lateRounds]

/-- For a light `Y`, `|I^U(Y)| = (R - r - 1) · 4 · T^sl_Y` (the number of sublabels of
[s5:lemZones] (ii); `R + 1 - (r + 2) = R - r - 1` in `ℕ`). -/
theorem card_IU_of_isLight {Y : PartId} (hY : run.isLight G Y.1 Y.2) :
    (IU G run Y).card = (run.R + 1 - (Y.1 + 2)) * 4 * Tslot G run Y := by
  classical
  simp only [IU, hY, if_true]
  rw [card_image_of_injective _ (fun a b h => by
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only [LentTag.U.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl)]
  simp [card_product, card_lateRounds, mul_assoc]

theorem IU_eq_empty_of_not_isLight {Y : PartId} (hY : ¬ run.isLight G Y.1 Y.2) :
    IU G run Y = ∅ := by
  classical
  simp [IU, hY]

/-! ### Parameters -/

variable (G run)

/-- [s3:defCOL] "`K^JS_l ρ_l = M_l^{-2}`". -/
theorem KJS_mul_rhoJS (l : ℕ) : (KJS G run l : ℝ) * rhoJS G run l = (run.M G l : ℝ) ^ (-2 : ℤ) := by
  unfold KJS rhoJS
  rcases Nat.eq_zero_or_pos (run.M G l) with h | h
  · rw [h]; simp
  · have hM : (run.M G l : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast
    rw [show ((run.M G l : ℝ) ^ 2) = (run.M G l : ℝ) ^ (2 : ℤ) by norm_cast, ← zpow_add₀ hM]
    norm_num

theorem rhoJS_nonneg (l : ℕ) : 0 ≤ rhoJS G run l := by
  unfold rhoJS
  rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  positivity

theorem rhoJS_le_one (l : ℕ) : rhoJS G run l ≤ 1 := by
  unfold rhoJS
  rcases Nat.eq_zero_or_pos (run.M G l) with h | h
  · rw [h]; simp
  · exact zpow_le_one_of_nonpos₀ (by exact_mod_cast h) (by norm_num)

theorem one_le_kown (Y : PartId) : 1 ≤ kown G run Y := by
  simp [kown]

/-! ### Own labels -/

@[simp] theorem ownIdxOf_none (J : ℕ) : ((ownIdxOf J) none : ℕ) = 4 * J := rfl

@[simp] theorem ownIdxOf_some (J : ℕ) (j : Fin J) (c : Fin 4) :
    ((ownIdxOf J) (some (j, c)) : ℕ) = 4 * j + c := rfl

@[simp] theorem ownIdx_none (N : ℕ) : ((ownIdx N) none : ℕ) = 4 * Vortex.pvJ N := rfl

@[simp] theorem ownIdx_some (N : ℕ) (j : Fin (Vortex.pvJ N)) (c : Fin 4) :
    ((ownIdx N) (some (j, c)) : ℕ) = 4 * j + c := rfl

/-! ### Classes -/

variable (Y : PartId) (c : Colouring G run Y)

theorem Own_eq_colourClass :
    Own G run Y c = (run.ancGraph G Y).colourClass (fun e => (c e).1) false := rfl

theorem Lend_eq_colourClass :
    Lend G run Y c = (run.ancGraph G Y).colourClass (fun e => (c e).1) true := rfl

theorem lentClass_eq_colourClass (i : LentTag) :
    lentClass G run Y c i =
      (run.ancGraph G Y).colourClass (fun e => ((c e).1, (c e).2.1)) (true, some i) := rfl

theorem ownClass_eq_colourClass (o : Fin (kown G run Y)) :
    ownClass G run Y c o =
      (run.ancGraph G Y).colourClass (fun e => ((c e).1, (c e).2.2)) (false, o) := rfl

@[simp] theorem Own_verts : (Own G run Y c).verts = run.ancVerts G Y := by
  simp [Own_eq_colourClass]

@[simp] theorem Lend_verts : (Lend G run Y c).verts = run.ancVerts G Y := by
  simp [Lend_eq_colourClass]

@[simp] theorem lentClass_verts (i : LentTag) : (lentClass G run Y c i).verts = run.ancVerts G Y := by
  simp [lentClass_eq_colourClass]

@[simp] theorem ownClass_verts (o : Fin (kown G run Y)) :
    (ownClass G run Y c o).verts = run.ancVerts G Y := by
  simp [ownClass_eq_colourClass]

theorem mem_Own_edges {e : Sym2 V} :
    e ∈ (Own G run Y c).edges ↔ ∃ h : e ∈ (run.ancGraph G Y).edges, (c ⟨e, h⟩).1 = false := by
  rw [Own_eq_colourClass, FGraph.mem_colourClass_edges]

theorem mem_Lend_edges {e : Sym2 V} :
    e ∈ (Lend G run Y c).edges ↔ ∃ h : e ∈ (run.ancGraph G Y).edges, (c ⟨e, h⟩).1 = true := by
  rw [Lend_eq_colourClass, FGraph.mem_colourClass_edges]

theorem mem_lentClass_edges {i : LentTag} {e : Sym2 V} :
    e ∈ (lentClass G run Y c i).edges ↔
      ∃ h : e ∈ (run.ancGraph G Y).edges, (c ⟨e, h⟩).1 = true ∧ (c ⟨e, h⟩).2.1 = some i := by
  rw [lentClass_eq_colourClass, FGraph.mem_colourClass_edges]
  simp only [Prod.mk.injEq]

theorem mem_ownClass_edges {o : Fin (kown G run Y)} {e : Sym2 V} :
    e ∈ (ownClass G run Y c o).edges ↔
      ∃ h : e ∈ (run.ancGraph G Y).edges, (c ⟨e, h⟩).1 = false ∧ (c ⟨e, h⟩).2.2 = o := by
  rw [ownClass_eq_colourClass, FGraph.mem_colourClass_edges]
  simp only [Prod.mk.injEq]

theorem Own_edges_subset : (Own G run Y c).edges ⊆ (run.ancGraph G Y).edges :=
  FGraph.colourClass_edges_subset _ _ _

theorem Lend_edges_subset : (Lend G run Y c).edges ⊆ (run.ancGraph G Y).edges :=
  FGraph.colourClass_edges_subset _ _ _

theorem lentClass_edges_subset_Lend (i : LentTag) :
    (lentClass G run Y c i).edges ⊆ (Lend G run Y c).edges := by
  intro e he
  obtain ⟨h, hb, -⟩ := (mem_lentClass_edges G run Y c).1 he
  exact (mem_Lend_edges G run Y c).2 ⟨h, hb⟩

theorem ownClass_edges_subset_Own (o : Fin (kown G run Y)) :
    (ownClass G run Y c o).edges ⊆ (Own G run Y c).edges := by
  intro e he
  obtain ⟨h, hb, -⟩ := (mem_ownClass_edges G run Y c).1 he
  exact (mem_Own_edges G run Y c).2 ⟨h, hb⟩

theorem disjoint_Own_Lend : Disjoint (Own G run Y c).edges (Lend G run Y c).edges :=
  FGraph.disjoint_colourClass_edges _ _ (by decide)

theorem Own_union_Lend :
    (Own G run Y c).edges ∪ (Lend G run Y c).edges = (run.ancGraph G Y).edges := by
  ext e
  simp only [Finset.mem_union, mem_Own_edges, mem_Lend_edges]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases hb : (c ⟨e, h⟩).1
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨h, hb⟩

theorem disjoint_ownClass {o o' : Fin (kown G run Y)} (h : o ≠ o') :
    Disjoint (ownClass G run Y c o).edges (ownClass G run Y c o').edges :=
  FGraph.disjoint_colourClass_edges _ _ (by simpa using h)

theorem biUnion_ownClass :
    (Finset.univ.biUnion fun o => (ownClass G run Y c o).edges) = (Own G run Y c).edges := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_ownClass_edges, mem_Own_edges]
  constructor
  · rintro ⟨o, h, hb, -⟩
    exact ⟨h, hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨(c ⟨e, h⟩).2.2, h, hb, rfl⟩

theorem disjoint_lentClass {i i' : LentTag} (h : i ≠ i') :
    Disjoint (lentClass G run Y c i).edges (lentClass G run Y c i').edges :=
  FGraph.disjoint_colourClass_edges _ _ (by simpa using h)

/-- On the support of `colouringLaw`, every edge's lent index is `none` or in `lentIdx`. -/
theorem idx_mem_of_mem_supp_idxLaw {o : Option LentTag} (ho : o ∈ (idxLaw G run Y).supp) :
    ∀ i, o = some i → i ∈ lentIdx G run Y := by
  intro i hi
  subst hi
  unfold idxLaw at ho
  split_ifs at ho with h
  · have : Nonempty ↥(lentIdx G run Y) := h.to_subtype
    have hw := (mem_supp.1 ho)
    rw [map_w] at hw
    obtain ⟨j, hj, -⟩ := exists_of_prob_pos _ (lt_of_le_of_ne (prob_nonneg _ _) (Ne.symm hw))
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some.injEq] at hj
    exact hj ▸ j.2
  · exact absurd ((mem_supp.1 ho)) (by simp [dirac_w_of_ne])

theorem idx_eq_none_of_mem_supp_idxLaw (hR : run.R < Y.1 + 2) {o : Option LentTag}
    (ho : o ∈ (idxLaw G run Y).supp) : o = none := by
  cases o with
  | none => rfl
  | some i =>
    have := idx_mem_of_mem_supp_idxLaw G run Y ho i rfl
    rw [lentIdx_eq_empty_iff.2 hR] at this
    exact absurd this (Finset.notMem_empty _)

theorem idx_mem_of_mem_supp {c : Colouring G run Y} (hc : c ∈ (colouringLaw G run Y).supp)
    (e : ↥(run.ancGraph G Y).edges) : ∀ i, (c e).2.1 = some i → i ∈ lentIdx G run Y := by
  have he : c e ∈ (edgeLaw G run Y).supp := (mem_supp_pi _).1 hc e
  have : (c e).2.1 ∈ (idxLaw G run Y).supp := by
    rw [mem_supp] at he ⊢
    intro h0
    apply he
    simp [edgeLaw, prod_w', h0]
  exact idx_mem_of_mem_supp_idxLaw G run Y this

/-- On the support, if `r ≤ R - 2`, the lent classes partition `Lend_Y`. -/
theorem biUnion_lentClass_of_mem_supp {c : Colouring G run Y}
    (hc : c ∈ (colouringLaw G run Y).supp) (hR : Y.1 + 2 ≤ run.R) :
    ((lentIdx G run Y).biUnion fun i => (lentClass G run Y c i).edges) =
      (Lend G run Y c).edges := by
  ext e
  simp only [Finset.mem_biUnion, mem_lentClass_edges, mem_Lend_edges]
  constructor
  · rintro ⟨i, -, h, hb, -⟩
    exact ⟨h, hb⟩
  · rintro ⟨h, hb⟩
    have hsupp := idx_mem_of_mem_supp G run Y hc ⟨e, h⟩
    rcases hidx : (c ⟨e, h⟩).2.1 with _ | i
    · -- `idx = none` has weight `0` when `lentIdx` is nonempty
      exfalso
      have he : c ⟨e, h⟩ ∈ (edgeLaw G run Y).supp := (mem_supp_pi _).1 hc ⟨e, h⟩
      have hne : (lentIdx G run Y).Nonempty := lentIdx_nonempty_iff.2 hR
      rw [mem_supp] at he
      apply he
      have : (idxLaw G run Y).w none = 0 := by
        unfold idxLaw
        rw [dif_pos hne, map_w]
        have : Nonempty ↥(lentIdx G run Y) := hne.to_subtype
        rw [prob_eq_zero_iff]
        intro j hj
        simp at hj
      simp [edgeLaw, prod_w', hidx, this]
    · exact ⟨i, hsupp i hidx, h, hb, hidx⟩

/-- [s3:lemCOL] (g) (the partition facts) holds on the support of the colouring law. -/
theorem COLg_of_mem_supp {ω : COLOut G run Y} (hω : ω.1 ∈ (colouringLaw G run Y).supp) :
    COLg G run Y ω := by
  refine ⟨disjoint_Own_Lend G run Y ω.1, Own_union_Lend G run Y ω.1,
    fun o o' h => disjoint_ownClass G run Y ω.1 h, biUnion_ownClass G run Y ω.1,
    fun hR => ⟨fun i _ i' _ h => disjoint_lentClass G run Y ω.1 h,
      biUnion_lentClass_of_mem_supp G run Y hω hR⟩, fun hR => lentIdx_eq_empty_iff.2 hR⟩

/-- [s3:lemCOL] (g) on the support of `colLaw` ("Item (g) always holds" is read on the support;
design note D-S1-10, CONVENTIONS "Stage 1"). -/
theorem COLg_of_mem_supp_colLaw {ω : COLOut G run Y} (hω : ω ∈ (colLaw G run Y).supp) :
    COLg G run Y ω := by
  apply COLg_of_mem_supp
  rw [mem_supp] at hω ⊢
  intro h
  apply hω
  simp [colLaw, prod_w', h]

/-- [s3:lemCOL] (g) in the hypothesis form of the lemCOL Specs: if `μ.map D = colLaw G run Y`,
then COL(g) holds at `D ω` for every outcome `ω` of positive weight. -/
theorem COLg_of_map_eq {Ω : Type*} {μ : FinDist Ω} {D : Ω → COLOut G run Y}
    (hD : μ.map D = colLaw G run Y) {ω : Ω} (hω : 0 < μ.w ω) : COLg G run Y (D ω) := by
  apply COLg_of_mem_supp_colLaw
  rw [← hD, mem_supp, map_w]
  exact ne_of_gt ((prob_pos_iff _ _).2 ⟨ω, rfl, hω⟩)

/-! ### `T_j(Y,l)` -/

theorem Tj_subset (lab : JSLabels G run Y) (l j : ℕ) : Tj G run Y lab l j ⊆ run.ancVerts G Y :=
  Finset.filter_subset _ _

/-- [s3:defCOL] "the sets `T_j(Y,l)`, `0 ≤ j < K^JS_l`, are pairwise disjoint" (for every
outcome). -/
theorem disjoint_Tj (lab : JSLabels G run Y) (l : ℕ) {j j' : ℕ} (h : j ≠ j') :
    Disjoint (Tj G run Y lab l j) (Tj G run Y lab l j') := by
  rw [Finset.disjoint_left]
  intro y h1 h2
  obtain ⟨-, hs, hj⟩ := Finset.mem_filter.1 h1
  obtain ⟨-, hs', hj'⟩ := Finset.mem_filter.1 h2
  rw [hj] at hj'
  exact h (Option.some.inj hj')

/-! ### COL(a) for light and standalone ancestors -/

/-- [s5:defStages] "COL(a) fails for `Y`, i.e. one of `Own_Y`, `Lend_Y` is not a
`(2^{-6}, s_r/8)`-expander, or some lent class is not a `(2^{-6}, s_r/(16k_lend(Y)))`-expander, or
some own class is not a `(2^{-6}, s_r/(16k_own))`-expander": for a light `Y`, `COLa` is exactly
this list (`ε_Y = 2^{-6}`, `s_Y = s_r/2`). -/
theorem COLa_iff_of_isLight {Y : PartId} (hY : run.isLight G Y.1 Y.2) (ω : COLOut G run Y) :
    COLa G run Y ω ↔
      (Own G run Y ω.1).IsExpander (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 8) ∧
      (Lend G run Y ω.1).IsExpander (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 8) ∧
      (∀ i ∈ lentIdx G run Y, (lentClass G run Y ω.1 i).IsExpander (2 ^ (-6 : ℤ))
        ((run.s G Y.1 : ℝ) / (16 * klend G run Y))) ∧
      (∀ o : Fin (kown G run Y), (ownClass G run Y ω.1 o).IsExpander (2 ^ (-6 : ℤ))
        ((run.s G Y.1 : ℝ) / (16 * kown G run Y))) := by
  classical
  have he : run.ancEps G Y = 2 ^ (-6 : ℤ) := by simp [Run.ancEps, hY]
  have hs : run.ancS G Y = (run.s G Y.1 : ℝ) / 2 := by simp [Run.ancS, hY]
  have h4 : (run.s G Y.1 : ℝ) / 2 / 4 = (run.s G Y.1 : ℝ) / 8 := by ring
  have h8 : (run.s G Y.1 : ℝ) / 2 / (8 * klend G run Y) =
      (run.s G Y.1 : ℝ) / (16 * klend G run Y) := by ring
  simp only [COLa, he, hs, h4, h8]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d hY⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, fun _ => d⟩⟩

/-- For a standalone `Y` (`ε_Y = 2^{-5}`, `s_Y = s_r`), `COLa` reads: `Own_Y`, `Lend_Y` are
`(2^{-5}, s_r/4)`-expanders and every lent class is a `(2^{-5}, s_r/(8k_lend(Y)))`-expander. -/
theorem COLa_iff_of_not_isLight {Y : PartId} (hY : ¬ run.isLight G Y.1 Y.2)
    (ω : COLOut G run Y) :
    COLa G run Y ω ↔
      (Own G run Y ω.1).IsExpander (2 ^ (-5 : ℤ)) ((run.s G Y.1 : ℝ) / 4) ∧
      (Lend G run Y ω.1).IsExpander (2 ^ (-5 : ℤ)) ((run.s G Y.1 : ℝ) / 4) ∧
      (∀ i ∈ lentIdx G run Y, (lentClass G run Y ω.1 i).IsExpander (2 ^ (-5 : ℤ))
        ((run.s G Y.1 : ℝ) / (8 * klend G run Y))) := by
  classical
  have he : run.ancEps G Y = 2 ^ (-5 : ℤ) := by simp [Run.ancEps, hY]
  have hs : run.ancS G Y = (run.s G Y.1 : ℝ) := by simp [Run.ancS, hY]
  simp only [COLa, he, hs]
  exact ⟨fun ⟨a, b, c, _⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c, fun h => absurd h hY⟩⟩

/-! ### Laws -/

theorem jsLabelLaw_w (l : ℕ) (o : Option ℕ) :
    (jsLabelLaw G run l).w o = jsWeight (run.M G l) o := rfl

/-- [s3:defCOL] (iv) "`P(lab_{Y,l}(y) = j) = ρ_l`" for `0 ≤ j < K^JS_l`. -/
theorem prob_jsLabelLaw_some (l : ℕ) {j : ℕ} (hj : j < KJS G run l) :
    (jsLabelLaw G run l).prob {some j} = rhoJS G run l := by
  rw [prob_singleton, jsLabelLaw_w]
  simp only [jsWeight]
  rw [if_pos (show j < run.M G l ^ 2 from hj)]
  rfl

/-- [s3:defCOL] (iv) "`P(lab_{Y,l}(y) = ∗) = 1 - M_l^{-2}`". -/
theorem prob_jsLabelLaw_none (l : ℕ) :
    (jsLabelLaw G run l).prob {none} = 1 - (run.M G l : ℝ) ^ (-2 : ℤ) := by
  rw [prob_singleton, jsLabelLaw_w]
  rfl

/-- [s3:defCOL] (ii) the lent index is uniform on the tagged union: `P(idx = i) = 1/k_lend(Y)`
for `i ∈ lentIdx`. -/
theorem prob_idxLaw_some {i : LentTag} (hi : i ∈ lentIdx G run Y) :
    (idxLaw G run Y).prob {some i} = 1 / (klend G run Y : ℝ) := by
  have hne : (lentIdx G run Y).Nonempty := ⟨i, hi⟩
  have : Nonempty ↥(lentIdx G run Y) := hne.to_subtype
  unfold idxLaw
  rw [dif_pos hne, prob_map]
  have e : (fun j : ↥(lentIdx G run Y) => some j.1) ⁻¹' {some i} = {⟨i, hi⟩} := by
    ext j
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some.injEq]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  rw [e, prob_singleton, uniform_w_eq, Fintype.card_coe, klend_eq_card_lentIdx]

/-- [s3:defCOL] (Derived quantities) "`p_Y := 1/(2k_lend(Y))`. For each fixed `l` with
`r+2 ≤ l ≤ R`, this is the probability that a fixed edge of `H_Y` lies in `LJV_{Y,l}`." -/
theorem prob_mem_LJV {l : ℕ} (hl : l ∈ lateRounds run Y.1) (e : ↥(run.ancGraph G Y).edges) :
    (colouringLaw G run Y).prob {c | (e : Sym2 V) ∈ (LJV G run Y c l).edges} = pY G run Y := by
  have hi : LentTag.JV l ∈ lentIdx G run Y :=
    mem_lentIdx.2 (Or.inr (Or.inr (JV_mem_IJV.2 hl)))
  have e1 : {c : Colouring G run Y | (e : Sym2 V) ∈ (LJV G run Y c l).edges} =
      {c | c e ∈ ({true} : Set Bool) ×ˢ (({some (LentTag.JV l)} : Set (Option LentTag)) ×ˢ
        (Set.univ : Set (Fin (kown G run Y))))} := by
    ext c
    simp only [LJV, lentClass_eq_colourClass, FGraph.coe_mem_colourClass_edges, Prod.mk.injEq,
      Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
  rw [e1, colouringLaw, prob_pi_eval, edgeLaw, prob_prod_set_prod, prob_prod_set_prod,
    prob_idxLaw_some G run Y hi, prob_univ, bitLaw, prob_bernoulli_true, pY]
  field_simp

/-- The own label `o` on a fixed edge has probability `1/(2k_own(Y))`: the edge has bit `false`
(probability `1/2`) and own label `o` (uniform on `[k_own(Y)]`), independently ([s3:defCOL]
(i), (iii)). -/
theorem prob_mem_ownClass (e : ↥(run.ancGraph G Y).edges) (o : Fin (kown G run Y)) :
    (colouringLaw G run Y).prob {c | (e : Sym2 V) ∈ (ownClass G run Y c o).edges} =
      1 / (2 * (kown G run Y : ℝ)) := by
  have e1 : {c : Colouring G run Y | (e : Sym2 V) ∈ (ownClass G run Y c o).edges} =
      {c | c e ∈ ({false} : Set Bool) ×ˢ ((Set.univ : Set (Option LentTag)) ×ˢ
        ({o} : Set (Fin (kown G run Y))))} := by
    ext c
    simp only [ownClass_eq_colourClass, FGraph.coe_mem_colourClass_edges, Prod.mk.injEq,
      Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, true_and]
  rw [e1, colouringLaw, prob_pi_eval, edgeLaw, prob_prod_set_prod, prob_prod_set_prod, prob_univ,
    prob_singleton, prob_singleton]
  simp only [ownLaw, uniform, bitLaw, bernoulli, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num
  ring

/-- [s5:lemE1] (a) "`P(wu ∈ M_Y) = 1/2 · 1/k_own`": the instance `o = ownIdx N none` of
`prob_mem_ownClass`. -/
theorem prob_mem_ownM (e : ↥(run.ancGraph G Y).edges) :
    (colouringLaw G run Y).prob {c | (e : Sym2 V) ∈ (ownM G run Y c).edges} =
      1 / (2 * (kown G run Y : ℝ)) :=
  prob_mem_ownClass G run Y e _

/-- [s3:defCOL] "for fixed `(l,j)`, the set `T_j(Y,l)` is a `ρ_l`-random subset of `V(Y)`"
(under the law of the JS labels of `Y`; independence of the colouring is the product structure
of `colLaw`). -/
theorem isRSubset_Tj {l j : ℕ} (hl : l ∈ lateRounds run Y.1) (hj : j < KJS G run l) :
    (jsLaw G run Y).IsRSubset (fun lab => Tj G run Y lab l j) (run.ancVerts G Y)
      (rhoJS G run l) := by
  classical
  have hsite : ∀ y : ↥(run.ancVerts G Y), (l, (y : V)) ∈ jsSites G run Y := fun y =>
    Finset.mem_product.2 ⟨hl, y.2⟩
  let b : ↥(run.ancVerts G Y) → JSLabels G run Y → Bool := fun y lab =>
    decide (lab ⟨(l, (y : V)), hsite y⟩ = some j)
  have e : (fun lab => Tj G run Y lab l j) =
      fun lab => FinDist.selectSet (run.ancVerts G Y) fun y => b y lab := by
    funext lab
    ext y
    rw [Tj, Finset.mem_filter, mem_selectSet]
    constructor
    · rintro ⟨hy, hs, h⟩
      exact ⟨hy, by simpa [b] using h⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, hsite ⟨y, hy⟩, by simpa [b] using h⟩
  rw [e]
  refine isRSubset_selectSet (rhoJS_nonneg G run l) (rhoJS_le_one G run l) ?_ ?_
  · refine iIndepFun_pi_of_dependsOn _ (fun y => {⟨(l, (y : V)), hsite y⟩}) ?_ b ?_
    · intro y y' hyy'
      simp only [Set.disjoint_singleton, ne_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
      exact fun h => hyy' (Subtype.ext h)
    · intro y f f' h
      simp only [b]
      rw [h _ rfl]
  · intro y
    have : {lab : JSLabels G run Y | b y lab = true} =
        {lab | lab ⟨(l, (y : V)), hsite y⟩ ∈ ({some j} : Set (Option ℕ))} := by
      ext lab
      simp [b]
    rw [this, jsLaw, prob_pi_eval]
    exact prob_jsLabelLaw_some G run l hj

/-! ### The labels given the bits (COL-RANDOM-EDGESET)

[s3:defCOL] "Given `Lend_Y`, the indices of its edges are a uniform `k_lend`-colouring of `Lend_Y`;
given `Own_Y`, … the own labels are a uniform `k_own`-colouring of `Own_Y`." Conditioning on the
bit vector `β` (equivalently on `Lend_Y` and `Own_Y`), the lent indices of the edges with bit
`true` are independent with law `idxLaw` (uniform on `lentIdx`, `idxLaw_eq_of_nonempty`), and the
own labels of the edges with bit `false` are a uniform `k_own`-colouring (`randColouring`). -/

/-- The bit vector of a colouring (`true` = the edge is in `Lend_Y`). -/
@[expose] def edgeBits (c : Colouring G run Y) : ↥(run.ancGraph G Y).edges → Bool :=
  fun e => (c e).1

/-- The (lent index, own label) pairs of a colouring. -/
@[expose] def edgeLabels (c : Colouring G run Y) :
    ↥(run.ancGraph G Y).edges → Option LentTag × Fin (kown G run Y) :=
  fun e => (c e).2

/-- Restriction of a finite product to the coordinates satisfying `p`. -/
theorem map_pi_restrict {ι : Type*} [Fintype ι] {κ : ι → Type*} (μ : ∀ i, FinDist (κ i))
    (p : ι → Prop) [DecidablePred p] :
    (FinDist.pi μ).map (fun f (i : {i // p i}) => f i) = FinDist.pi fun i : {i // p i} => μ i := by
  rw [pi_eq_map_prod μ p, FinDist.map_map]
  have : ((fun f (i : {i // p i}) => f i) ∘ (Equiv.piEquivPiSubtypeProd p κ).symm) = Prod.fst := by
    funext q i
    simp [Equiv.piEquivPiSubtypeProd, i.2]
  rw [this, map_fst_prod]

/-- The bits and the (index, own label) pairs are independent product families. -/
theorem map_edgeBits_edgeLabels :
    (colouringLaw G run Y).map (fun c => (edgeBits G run Y c, edgeLabels G run Y c)) =
      (FinDist.pi fun _ : ↥(run.ancGraph G Y).edges => bitLaw).prod
        (FinDist.pi fun _ : ↥(run.ancGraph G Y).edges =>
          (idxLaw G run Y).prod (ownLaw G run Y)) := by
  have : (fun c : Colouring G run Y => (edgeBits G run Y c, edgeLabels G run Y c)) =
      Equiv.arrowProdEquivProdArrow _ (fun _ => Bool)
        (fun _ => Option LentTag × Fin (kown G run Y)) := rfl
  rw [this]
  ext p
  rw [map_equiv_w, prod_w', pi_w, pi_w, colouringLaw, pi_w, ← Finset.prod_mul_distrib]
  rfl

theorem map_edgeBits :
    (colouringLaw G run Y).map (edgeBits G run Y) =
      FinDist.pi fun _ : ↥(run.ancGraph G Y).edges => bitLaw := by
  have := congrArg (fun ν => ν.map Prod.fst) (map_edgeBits_edgeLabels G run Y)
  simpa [FinDist.map_map, Function.comp_def] using this

theorem map_edgeLabels :
    (colouringLaw G run Y).map (edgeLabels G run Y) =
      FinDist.pi fun _ : ↥(run.ancGraph G Y).edges => (idxLaw G run Y).prod (ownLaw G run Y) := by
  have := congrArg (fun ν => ν.map Prod.snd) (map_edgeBits_edgeLabels G run Y)
  simpa [FinDist.map_map, Function.comp_def] using this

/-- [s3:defCOL] "every edge `e` of `H_Y` carries three independent uniform random variables":
the bits are independent of the (index, own label) pairs. -/
theorem indepFun_edgeBits_edgeLabels :
    (colouringLaw G run Y).IndepFun (edgeBits G run Y) (edgeLabels G run Y) := by
  rw [indepFun_iff_map_eq_prod, map_edgeBits_edgeLabels, map_edgeBits, map_edgeLabels]

/-- Given the bit vector `β`, the (index, own label) pairs keep their product law. -/
theorem map_edgeLabels_cond_edgeBits (β : ↥(run.ancGraph G Y).edges → Bool)
    (hβ : 0 < (colouringLaw G run Y).prob (edgeBits G run Y ⁻¹' {β})) :
    ((colouringLaw G run Y).cond (edgeBits G run Y ⁻¹' {β}) hβ).map (edgeLabels G run Y) =
      FinDist.pi fun _ : ↥(run.ancGraph G Y).edges => (idxLaw G run Y).prod (ownLaw G run Y) := by
  rw [(indepFun_edgeBits_edgeLabels G run Y).map_cond β hβ, map_edgeLabels]

/-- [s3:defCOL] "Given `Lend_Y`, the indices of its edges are a uniform `k_lend`-colouring of
`Lend_Y`": given the bits `β`, the indices of the edges with bit `true` are independent, each
with law `idxLaw` (uniform on `lentIdx`, see `idxLaw_eq_of_nonempty`). -/
theorem map_idx_cond_edgeBits (β : ↥(run.ancGraph G Y).edges → Bool)
    (hβ : 0 < (colouringLaw G run Y).prob (edgeBits G run Y ⁻¹' {β})) :
    ((colouringLaw G run Y).cond (edgeBits G run Y ⁻¹' {β}) hβ).map
        (fun c (e : {e // β e = true}) => (c e).2.1) =
      FinDist.pi fun _ : {e // β e = true} => idxLaw G run Y := by
  have h := map_edgeLabels_cond_edgeBits G run Y β hβ
  have := congrArg (fun ν => (ν.map (fun f (e : {e // β e = true}) => f e)).map
    (fun f e => (f e).1)) h
  simp only [FinDist.map_map] at this
  refine this.trans ?_
  rw [← FinDist.map_map, map_pi_restrict, map_pi]
  simp

/-- [s3:defCOL] "given `Own_Y`, … the own labels are a uniform `k_own`-colouring of `Own_Y`":
given the bits `β`, the own labels of the edges with bit `false` are a uniformly random
`k_own`-colouring. -/
theorem map_own_cond_edgeBits (β : ↥(run.ancGraph G Y).edges → Bool)
    (hβ : 0 < (colouringLaw G run Y).prob (edgeBits G run Y ⁻¹' {β})) :
    ((colouringLaw G run Y).cond (edgeBits G run Y ⁻¹' {β}) hβ).map
        (fun c (e : {e // β e = false}) => (c e).2.2) =
      FinDist.randColouring {e // β e = false} (kown G run Y) := by
  have h := map_edgeLabels_cond_edgeBits G run Y β hβ
  have := congrArg (fun ν => (ν.map (fun f (e : {e // β e = false}) => f e)).map
    (fun f e => (f e).2)) h
  simp only [FinDist.map_map] at this
  refine this.trans ?_
  rw [← FinDist.map_map, map_pi_restrict, map_pi]
  simp [ownLaw, randColouring]

/-- The index law is the uniform law on `lentIdx` (as `some`) when `lentIdx` is nonempty. -/
theorem idxLaw_eq_of_nonempty (h : (lentIdx G run Y).Nonempty) :
    haveI : Nonempty ↥(lentIdx G run Y) := h.to_subtype
    idxLaw G run Y = (FinDist.uniform ↥(lentIdx G run Y)).map (fun i => some i.1) := by
  unfold idxLaw
  rw [dif_pos h]

end EG.Stage1
