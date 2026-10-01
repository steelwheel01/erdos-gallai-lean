module

public import EG.Lib.Light.KREDAux

/-!
# The round-by-round construction of Lemma K-RED (s5:lemKRED)

Library of the P3-s5 unit (`formal/work/p3/s5.md`). Manuscript v6.1, `s5.tex`, Lemma
[s5:lemKRED]: "Process the rounds `l = R, R−1, …, 1` (children before parents). At round `l`:
(1) for every non-demoted light part `Z` of round `l`, let `LentU(Z) := E(H_Z) ∩ ⋃_{l' ≥ l+2, c}
LentU_{l',c}` …, put `H_0(Z) := E_l(Z) \ (LentU(Z) ∪ Lent_ext(Z))`, and decompose `H_0(Z)` by
Lemma s5:lemChild into `H^obj(Z)` (as objects) and arcs; (2) for every demoted light part `Z` of
round `l`, decompose `E_l(Z)` by Lemma s5:lemDemoted; (3) if `l ≥ 3`, apply Lemma s5:lemParent to
the bundles `B_{l,c}`, `c ∈ [4]`, formed from the arcs of step (1)."

The construction is a downward induction on the round `m` (`KHyp.step`). The invariant `KInv m`:
there are a set `U` of U-lent edges (used at the rounds `≥ m`, all available at rounds `≥ m`) and
a decomposition of `Srest m U`, the edges of the light parts of rounds `≥ m` minus their
`Lent_ext` and minus `U`, together with `U` ("Every edge of `𝒟` lies in exactly one object"),
with at most `Σ_{l ≥ m} kcost l` objects (the cost items "child vortices", "demoted parts",
"U-chaining" of the proof). `KHyp.exists_decomp`: the result for `m = 1`.
-/

public section

namespace EG.Light

open EG.HB EG.Stage1

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

variable (G run) in
open Classical in
/-- The edges handled by the rounds `≥ m`: `⋃_{r(Z) ≥ m} (E_{r(Z)}(Z) \ Lent_ext(Z)) \ U`, together
with the U-lent edges `U` used at these rounds. -/
@[expose] noncomputable def Srest (Lext : PartId → Finset (Sym2 V)) (m : ℕ)
    (U : Finset (Sym2 V)) : Finset (Sym2 V) :=
  (((run.lightParts G).filter fun Z => m ≤ Z.1).biUnion fun Z =>
    (run.E G Z.1 Z.2 \ Lext Z) \ U) ∪ U

open Classical in
/-- The U-lent edges available at the rounds `≥ m`. -/
@[expose] noncomputable def availFrom (ω : Outcome G run) (m : ℕ) : Finset (Sym2 V) :=
  (Finset.Icc m run.R).biUnion fun l => Finset.univ.biUnion fun c : Fin 4 => lentUAvail ω l c

open Classical in
/-- The cost of round `l`: child vortices `369 Σ_Z |Pl(Z)|`, demoted parts `80 Σ_Z |Z|`, and the
U-chaining bound of Lemma s5:lemParent (ii) (for `l ≥ 3`). -/
@[expose] noncomputable def kcost (ω : Outcome G run) (l : ℕ) : ℝ :=
  369 * ((∑ Z ∈ childParts ω l, (Pl ω Z).card : ℕ) : ℝ) +
    80 * ((∑ Z ∈ (run.lightParts G).filter (fun Z => Z.1 = l ∧ demoted ω Z),
      (run.ancVerts G Z).card : ℕ) : ℝ) +
    (if 3 ≤ l then pbound G run l else 0)

/-- The invariant of the construction after the rounds `≥ m`. -/
def KInv (ω : Outcome G run) (Lext : PartId → Finset (Sym2 V)) (m : ℕ) : Prop :=
  ∃ (U : Finset (Sym2 V)) (D : List (Obj V)), U ⊆ availFrom ω m ∧
    IsDecomp ((Srest G run Lext m U : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
    (D.length : ℝ) ≤ ∑ l ∈ Finset.Icc m run.R, kcost ω l

theorem mem_Srest {Lext : PartId → Finset (Sym2 V)} {m : ℕ} {U : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ Srest G run Lext m U ↔
      (∃ Z ∈ run.lightParts G, m ≤ Z.1 ∧ e ∈ run.E G Z.1 Z.2 ∧ e ∉ Lext Z ∧ e ∉ U) ∨ e ∈ U := by
  simp only [Srest, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro (⟨Z, ⟨hZ, hm⟩, ⟨he, hL⟩, hU⟩ | hU)
    · exact Or.inl ⟨Z, hZ, hm, he, hL, hU⟩
    · exact Or.inr hU
  · rintro (⟨Z, hZ, hm, he, hL, hU⟩ | hU)
    · exact Or.inl ⟨Z, ⟨hZ, hm⟩, ⟨he, hL⟩, hU⟩
    · exact Or.inr hU

theorem mem_availFrom {ω : Outcome G run} {m : ℕ} {e : Sym2 V} :
    e ∈ availFrom ω m ↔ ∃ l, m ≤ l ∧ l ≤ run.R ∧ ∃ c, e ∈ lentUAvail ω l c := by
  simp only [availFrom, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, c, he⟩; exact ⟨l, h1, h2, c, he⟩
  · rintro ⟨l, h1, h2, c, he⟩; exact ⟨l, ⟨h1, h2⟩, c, he⟩

theorem isDecomp_union_finset' {A B : Finset (Sym2 V)} {D₁ D₂ : List (Obj V)}
    (hA : IsDecomp (A : Set (Sym2 V)) D₁) (hB : IsDecomp (B : Set (Sym2 V)) D₂)
    (hAB : Disjoint A B) : IsDecomp ((A ∪ B : Finset (Sym2 V)) : Set (Sym2 V)) (D₁ ++ D₂) :=
  (hA.append hB (Finset.disjoint_coe.2 hAB)).congr (Finset.coe_union A B).symm

theorem mem_childParts' {ω : Outcome G run} {l : ℕ} {Z : PartId} :
    Z ∈ childParts ω l ↔ Z ∈ run.lightParts G ∧ Z.1 = l ∧ ¬ demoted ω Z := by
  classical
  unfold childParts
  rw [Finset.mem_filter]

theorem mem_bundleEdges' {ω : Outcome G run} {l : ℕ} {arcs : PartId → List (Arc V)} {c : Fin 4}
    {e : Sym2 V} : e ∈ bundleEdges ω l arcs c ↔
      ∃ Z ∈ childParts ω l, e ∈ arcEdges ((arcs Z).filter fun a => a.2 = c) := by
  unfold bundleEdges
  rw [Finset.mem_biUnion]

theorem arcEdges_filter_subset (as : List (Arc V)) (p : Arc V → Bool) :
    arcEdges (as.filter p) ⊆ arcEdges as := by
  intro e he
  rw [mem_arcEdges] at he ⊢
  obtain ⟨a, ha, he⟩ := he
  exact ⟨a, List.mem_of_mem_filter ha, he⟩

theorem mem_arcEdges_filter_self {as : List (Arc V)} {e : Sym2 V} (he : e ∈ arcEdges as) :
    ∃ c : Fin 4, e ∈ arcEdges (as.filter fun a => a.2 = c) := by
  rw [mem_arcEdges] at he
  obtain ⟨a, ha, he⟩ := he
  refine ⟨a.2, ?_⟩
  rw [mem_arcEdges]
  exact ⟨a, List.mem_filter.2 ⟨ha, by simp⟩, he⟩

namespace KHyp

variable {ω : Outcome G run} {Lext : PartId → Finset (Sym2 V)}

/-- One round of the construction: from the invariant after the rounds `≥ m + 1` to the invariant
after the rounds `≥ m` ([s5:lemKRED] steps (1)–(3) at round `m`, and the proof's "Every edge of
`𝒟` lies in exactly one object, and no other edge is used" and "Cost"). -/
theorem step (h : KHyp ω Lext) {m : ℕ} (hmR : m ≤ run.R) (hI : KInv ω Lext (m + 1)) :
    KInv ω Lext m := by
  classical
  obtain ⟨U, D, hU, hD, hlen⟩ := hI
  set LP := run.lightParts G with hLP
  set CP := childParts ω m with hCPdef
  set DP := LP.filter fun Z => Z.1 = m ∧ demoted ω Z with hDPdef
  set H0 : PartId → Finset (Sym2 V) := fun Z => (run.E G Z.1 Z.2 \ Lext Z) \ U with hH0
  -- facts on `U`
  have f1 : ∀ e ∈ U, ∃ l, m + 1 ≤ l ∧ l ≤ run.R ∧ ∃ c, e ∈ lentUAvail ω l c :=
    fun e he => mem_availFrom.1 (hU he)
  have hCP : ∀ Z ∈ CP, Z ∈ LP ∧ Z.1 = m ∧ ¬ demoted ω Z := fun Z hZ => mem_childParts'.1 hZ
  have hDP : ∀ Z ∈ DP, Z ∈ LP ∧ Z.1 = m ∧ demoted ω Z := fun Z hZ => by
    have := Finset.mem_filter.1 hZ
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hUdem : ∀ Z ∈ LP, demoted ω Z → Disjoint U (run.E G Z.1 Z.2) := by
    intro Z hZ hd
    rw [Finset.disjoint_left]
    intro e he heZ
    obtain ⟨l, -, -, c, hl⟩ := f1 e he
    exact Finset.disjoint_left.1 (h.disjoint_lentUAvail_E_of_demoted hZ hd) hl heZ
  -- the admissible `H_0`
  have hadm : ∀ Z ∈ CP, H0Adm ω Z (H0 Z) := by
    intro Z hZ
    obtain ⟨hZl, -, -⟩ := hCP Z hZ
    refine ⟨fun e he => ?_, fun e he => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).1⟩
    refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨h.ancE Z hZl (Own_edges_subset G run Z _ he),
      fun hL => Finset.disjoint_left.1 (disjoint_Own_lentJSJV ω Z) he ((h.lext Z hZl).1 hL)⟩,
      fun hU' => ?_⟩
    obtain ⟨l, -, -, c, hl⟩ := f1 e hU'
    exact Finset.disjoint_left.1 (h.disjoint_lentUAvail_Own hZl) hl he
  -- step (1): Lemma child side for every non-demoted part of round `m`
  have hchild : ∀ Z ∈ CP, ∃ (Hobj : Finset (Sym2 V)) (Dobj : List (Obj V)) (as : List (Arc V)),
      Disjoint Hobj (arcEdges as) ∧ Hobj ∪ arcEdges as = H0 Z ∧
      IsDecomp (Hobj : Set (Sym2 V)) Dobj ∧ Dobj.length ≤ 369 * (Pl ω Z).card ∧
      ArcSys ω Z (H0 Z) as := fun Z hZ =>
    h.child Z (hCP Z hZ).1 (hCP Z hZ).2.2 (H0 Z) (hadm Z hZ)
  choose! Hobj Dobj arcs hHd hHu hHdec hHlen hHarc using hchild
  have harcH0 : ∀ Z ∈ CP, arcEdges (arcs Z) ⊆ H0 Z := fun Z hZ =>
    (hHu Z hZ) ▸ Finset.subset_union_right
  have hobjH0 : ∀ Z ∈ CP, Hobj Z ⊆ H0 Z := fun Z hZ =>
    (hHu Z hZ) ▸ Finset.subset_union_left
  -- step (2): demoted parts of round `m`
  have hdem : ∀ Z ∈ DP, ∃ D' : List (Obj V), IsDecomp ((run.E G Z.1 Z.2 : Finset (Sym2 V)) :
      Set (Sym2 V)) D' ∧ D'.length ≤ 80 * (run.ancVerts G Z).card := fun Z hZ =>
    h.demot Z (hDP Z hZ).1 (hDP Z hZ).2.2 _ (h.ancX Z (hDP Z hZ).1) subset_rfl
  choose! Ddem hDdec hDlen using hdem
  -- step (3): Lemma parent side (no arcs if `m ≤ 2`)
  have hpar : ∃ (LentU : Fin 4 → Finset (Sym2 V)) (Dp : Fin 4 → List (Obj V)),
      (∀ c, Disjoint (LentU c) (bundleEdges ω m arcs c)) ∧
      (∀ c, IsDecomp ((bundleEdges ω m arcs c ∪ LentU c : Finset (Sym2 V)) : Set (Sym2 V))
        (Dp c)) ∧
      (∀ c, LentU c ⊆ lentUAvail ω m c) ∧
      ((∑ c, (Dp c).length : ℕ) : ℝ) ≤ (if 3 ≤ m then pbound G run m else 0) ∧
      (∀ c c', c ≠ c' → Disjoint (LentU c) (LentU c')) := by
    by_cases h3 : 3 ≤ m
    · obtain ⟨LentU, Dp, p1, p2, p3, p4, p5⟩ :=
        h.parent m h3 hmR H0 arcs (fun Z hZ => ⟨hadm Z hZ, hHarc Z hZ⟩)
      exact ⟨LentU, Dp, p1, p2, p3, by rw [if_pos h3]; exact p4, p5⟩
    · have harcs : ∀ Z ∈ CP, arcs Z = [] := by
        intro Z hZ
        apply (hHarc Z hZ).2.2.2.2
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨-, Y, hg, hY2, -⟩ := (mem_Rt ω).1 hv
        have := (h.round Y hg.1).1
        have hZm := (hCP Z hZ).2.1
        omega
      have hb : ∀ c, bundleEdges ω m arcs c = ∅ := by
        intro c
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨Z, hZ, he⟩ := mem_bundleEdges'.1 he
        rw [harcs Z hZ] at he
        simp [arcEdges] at he
      refine ⟨fun _ => ∅, fun _ => [], fun c => Finset.disjoint_empty_left _, fun c => ?_,
        fun c => Finset.empty_subset _, ?_, fun _ _ _ => Finset.disjoint_empty_left _⟩
      · rw [hb c, Finset.empty_union, Finset.coe_empty]
        exact isDecomp_nil
      · rw [if_neg h3]; simp
  obtain ⟨LentU, Dp, p1, p2, p3, p4, p5⟩ := hpar
  -- facts on `LentU`
  have f3 : ∀ c, ∀ Z ∈ LP, m ≤ Z.1 → Disjoint (LentU c) (run.E G Z.1 Z.2) := fun c Z hZ hm =>
    ((h.disjoint_lentUAvail_E_of_lt hZ (by omega)).mono_left (p3 c))
  have f4 : ∀ c, ∀ Z ∈ LP, demoted ω Z → Disjoint (LentU c) (run.E G Z.1 Z.2) := fun c Z hZ hd =>
    ((h.disjoint_lentUAvail_E_of_demoted hZ hd).mono_left (p3 c))
  have fUL : ∀ c, Disjoint U (LentU c) := by
    intro c
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨l, hl, -, c', hl'⟩ := f1 e he
    have hne : (l, c') ≠ (m, c) := fun hh => by
      have := congrArg Prod.fst hh; simp at this; omega
    exact Finset.disjoint_left.1 (h.avail l m c' c hne) hl' (p3 c he')
  -- the bundles lie in the sets `H_0(Z)`
  have fB : ∀ c, ∀ e ∈ bundleEdges ω m arcs c, ∃ Z ∈ CP, e ∈ arcEdges (arcs Z) := by
    intro c e he
    obtain ⟨Z, hZ, he⟩ := mem_bundleEdges'.1 he
    exact ⟨Z, hZ, arcEdges_filter_subset _ _ he⟩
  -- the new set `U'` and the pieces
  set U' := U ∪ Finset.univ.biUnion LentU with hU'
  set A1 := CP.biUnion Hobj with hA1
  set A2 := DP.biUnion fun Z => run.E G Z.1 Z.2 with hA2
  set A3 := Finset.univ.biUnion fun c => bundleEdges ω m arcs c ∪ LentU c with hA3
  have hnotU' : ∀ e, e ∉ U → (∀ c, e ∉ LentU c) → e ∉ U' := by
    intro e h1 h2 he
    rcases Finset.mem_union.1 he with he | he
    · exact h1 he
    · obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 he
      exact h2 c hc
  -- membership in `H_0(Z)`
  have hH0mem : ∀ Z, ∀ e, e ∈ H0 Z ↔ e ∈ run.E G Z.1 Z.2 ∧ e ∉ Lext Z ∧ e ∉ U := by
    intro Z e
    simp only [hH0, Finset.mem_sdiff, and_assoc]
  -- the round-`m` pieces: an edge of `A1 ∪ A2 ∪ A3` lies in `E_m(Z) \ U` or in some `LentU c`
  have hround : ∀ e ∈ A1 ∪ (A2 ∪ A3), (∃ Z ∈ LP, Z.1 = m ∧ e ∈ run.E G Z.1 Z.2 ∧ e ∉ U) ∨
      ∃ c, e ∈ LentU c := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨Z, hZ, he⟩ := Finset.mem_biUnion.1 he
      have := (hH0mem Z e).1 (hobjH0 Z hZ he)
      exact Or.inl ⟨Z, (hCP Z hZ).1, (hCP Z hZ).2.1, this.1, this.2.2⟩
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨Z, hZ, he⟩ := Finset.mem_biUnion.1 he
      exact Or.inl ⟨Z, (hDP Z hZ).1, (hDP Z hZ).2.1, he,
        fun hU'' => Finset.disjoint_left.1 (hUdem Z (hDP Z hZ).1 (hDP Z hZ).2.2) hU'' he⟩
    · obtain ⟨c, -, he⟩ := Finset.mem_biUnion.1 he
      rcases Finset.mem_union.1 he with he | he
      · obtain ⟨Z, hZ, he⟩ := fB c e he
        have := (hH0mem Z e).1 (harcH0 Z hZ he)
        exact Or.inl ⟨Z, (hCP Z hZ).1, (hCP Z hZ).2.1, this.1, this.2.2⟩
      · exact Or.inr ⟨c, he⟩
  -- the set identity
  have hset : Srest G run Lext m U' = Srest G run Lext (m + 1) U ∪ (A1 ∪ (A2 ∪ A3)) := by
    ext e
    constructor
    · intro he
      rcases mem_Srest.1 he with ⟨Z, hZ, hmZ, heZ, heL, heU'⟩ | he
      · have heU : e ∉ U := fun h' => heU' (Finset.mem_union_left _ h')
        have heLU : ∀ c, e ∉ LentU c := fun c h' =>
          heU' (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, h'⟩))
        rcases Nat.lt_or_ge m Z.1 with hlt | hge
        · exact Finset.mem_union_left _ (mem_Srest.2 (Or.inl ⟨Z, hZ, hlt, heZ, heL, heU⟩))
        · have hZm : Z.1 = m := le_antisymm hge hmZ
          refine Finset.mem_union_right _ ?_
          by_cases hd : demoted ω Z
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_biUnion.2 ⟨Z, Finset.mem_filter.2 ⟨hZ, hZm, hd⟩, heZ⟩))
          · have hZc : Z ∈ CP := mem_childParts'.2 ⟨hZ, hZm, hd⟩
            have heH0 : e ∈ H0 Z := (hH0mem Z e).2 ⟨heZ, heL, heU⟩
            rw [← hHu Z hZc] at heH0
            rcases Finset.mem_union.1 heH0 with h1 | h1
            · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨Z, hZc, h1⟩)
            · obtain ⟨c, hc⟩ := mem_arcEdges_filter_self h1
              refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_union_left _
                (mem_bundleEdges'.2 ⟨Z, hZc, hc⟩)⟩
      · rcases Finset.mem_union.1 he with he | he
        · exact Finset.mem_union_left _ (mem_Srest.2 (Or.inr he))
        · obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 he
          refine Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ ?_))
          exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_union_right _ hc⟩
    · intro he
      rcases Finset.mem_union.1 he with he | he
      · rcases mem_Srest.1 he with ⟨Z, hZ, hmZ, heZ, heL, heU⟩ | he
        · refine mem_Srest.2 (Or.inl ⟨Z, hZ, by omega, heZ, heL, hnotU' e heU fun c hc => ?_⟩)
          exact Finset.disjoint_left.1 (f3 c Z hZ (by omega)) hc heZ
        · exact mem_Srest.2 (Or.inr (Finset.mem_union_left _ he))
      · rcases hround e he with ⟨Z, hZ, hZm, heZ, heU⟩ | ⟨c, hc⟩
        · have heL : e ∉ Lext Z := by
            by_cases hd : demoted ω Z
            · rw [(h.lext Z hZ).2 hd]; exact Finset.notMem_empty e
            · -- `e` lies in `H_0(Z')` for a part `Z'` of round `m`; `Z' = Z`
              intro hL
              rcases Finset.mem_union.1 he with he | he
              · obtain ⟨Z', hZ', he'⟩ := Finset.mem_biUnion.1 he
                have h2 := (hH0mem Z' e).1 (hobjH0 Z' hZ' he')
                by_cases hZZ : Z' = Z
                · exact h2.2.1 (hZZ ▸ hL)
                · exact Finset.disjoint_left.1 (h.disjE Z' (hCP Z' hZ').1 Z hZ hZZ) h2.1
                    (h.Lext_subset hZ hL)
              rcases Finset.mem_union.1 he with he | he
              · obtain ⟨Z', hZ', he'⟩ := Finset.mem_biUnion.1 he
                by_cases hZZ : Z' = Z
                · exact hd (hZZ ▸ (hDP Z' hZ').2.2)
                · exact Finset.disjoint_left.1 (h.disjE Z' (hDP Z' hZ').1 Z hZ hZZ) he'
                    (h.Lext_subset hZ hL)
              · obtain ⟨c, -, he⟩ := Finset.mem_biUnion.1 he
                rcases Finset.mem_union.1 he with he | he
                · obtain ⟨Z', hZ', he'⟩ := fB c e he
                  have h2 := (hH0mem Z' e).1 (harcH0 Z' hZ' he')
                  by_cases hZZ : Z' = Z
                  · exact h2.2.1 (hZZ ▸ hL)
                  · exact Finset.disjoint_left.1 (h.disjE Z' (hCP Z' hZ').1 Z hZ hZZ) h2.1
                      (h.Lext_subset hZ hL)
                · exact Finset.disjoint_left.1 (h.disjoint_lentUAvail_Lext hZ) (p3 c he) hL
          refine mem_Srest.2 (Or.inl ⟨Z, hZ, hZm.ge, heZ, heL, hnotU' e heU fun c hc => ?_⟩)
          exact Finset.disjoint_left.1 (f3 c Z hZ hZm.ge) hc heZ
        · exact mem_Srest.2 (Or.inr (Finset.mem_union_right _
            (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, hc⟩)))
  -- edges of the bundles lie in the parts of round `m`
  have hbE : ∀ c, ∀ e ∈ bundleEdges ω m arcs c, ∃ Z ∈ CP, e ∈ run.E G Z.1 Z.2 := by
    intro c e he
    obtain ⟨Z, hZ, he⟩ := fB c e he
    exact ⟨Z, hZ, ((hH0mem Z e).1 (harcH0 Z hZ he)).1⟩
  have hobjE : ∀ Z ∈ CP, Hobj Z ⊆ run.E G Z.1 Z.2 := fun Z hZ e he =>
    ((hH0mem Z e).1 (hobjH0 Z hZ he)).1
  -- decompositions of the pieces
  have hdA1 : IsDecomp ((A1 : Finset (Sym2 V)) : Set (Sym2 V)) (CP.toList.flatMap Dobj) := by
    refine isDecomp_finset_biUnion CP ?_ hHdec
    intro Z hZ Z' hZ' hne
    have hZ1 := Finset.mem_coe.1 hZ
    have hZ1' := Finset.mem_coe.1 hZ'
    exact (h.disjE Z (hCP Z hZ1).1 Z' (hCP Z' hZ1').1 hne).mono (hobjE Z hZ1) (hobjE Z' hZ1')
  have hdA2 : IsDecomp ((A2 : Finset (Sym2 V)) : Set (Sym2 V)) (DP.toList.flatMap Ddem) := by
    refine isDecomp_finset_biUnion DP ?_ hDdec
    intro Z hZ Z' hZ' hne
    exact h.disjE Z (hDP Z (Finset.mem_coe.1 hZ)).1 Z' (hDP Z' (Finset.mem_coe.1 hZ')).1 hne
  have hdA3 : IsDecomp ((A3 : Finset (Sym2 V)) : Set (Sym2 V))
      ((Finset.univ : Finset (Fin 4)).toList.flatMap Dp) := by
    refine isDecomp_finset_biUnion Finset.univ ?_ fun c _ => p2 c
    intro c _ c' _ hcc'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he he'
    rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
    · obtain ⟨Z, hZ, hez⟩ := mem_bundleEdges'.1 he
      obtain ⟨Z', hZ', hez'⟩ := mem_bundleEdges'.1 he'
      by_cases hZZ : Z = Z'
      · subst hZZ
        exact Finset.disjoint_left.1 (disjoint_arcEdges_filter (hHarc Z hZ).1 hcc') hez hez'
      · have h1 := ((hH0mem Z e).1 (harcH0 Z hZ (arcEdges_filter_subset _ _ hez))).1
        have h2 := ((hH0mem Z' e).1 (harcH0 Z' hZ' (arcEdges_filter_subset _ _ hez'))).1
        exact Finset.disjoint_left.1 (h.disjE Z (hCP Z hZ).1 Z' (hCP Z' hZ').1 hZZ) h1 h2
    · obtain ⟨Z, hZ, hez⟩ := hbE c e he
      exact Finset.disjoint_left.1 (f3 c' Z (hCP Z hZ).1 (hCP Z hZ).2.1.ge) he' hez
    · obtain ⟨Z, hZ, hez⟩ := hbE c' e he'
      exact Finset.disjoint_left.1 (f3 c Z (hCP Z hZ).1 (hCP Z hZ).2.1.ge) he hez
    · exact Finset.disjoint_left.1 (p5 c c' hcc') he he'
  -- disjointness of the pieces
  have hd2 : Disjoint A2 A3 := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨Z, hZ, heZ⟩ := Finset.mem_biUnion.1 he
    obtain ⟨c, -, he'⟩ := Finset.mem_biUnion.1 he'
    rcases Finset.mem_union.1 he' with he' | he'
    · obtain ⟨Z', hZ', heZ'⟩ := hbE c e he'
      have hne : Z ≠ Z' := fun hh => (hCP Z' hZ').2.2 (hh ▸ (hDP Z hZ).2.2)
      exact Finset.disjoint_left.1 (h.disjE Z (hDP Z hZ).1 Z' (hCP Z' hZ').1 hne) heZ heZ'
    · exact Finset.disjoint_left.1 (f4 c Z (hDP Z hZ).1 (hDP Z hZ).2.2) he' heZ
  have hd1 : Disjoint A1 (A2 ∪ A3) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨Z, hZ, heo⟩ := Finset.mem_biUnion.1 he
    have heZ := hobjE Z hZ heo
    rcases Finset.mem_union.1 he' with he' | he'
    · obtain ⟨Z', hZ', heZ'⟩ := Finset.mem_biUnion.1 he'
      have hne : Z ≠ Z' := fun hh => (hCP Z hZ).2.2 (hh ▸ (hDP Z' hZ').2.2)
      exact Finset.disjoint_left.1 (h.disjE Z (hCP Z hZ).1 Z' (hDP Z' hZ').1 hne) heZ heZ'
    · obtain ⟨c, -, he'⟩ := Finset.mem_biUnion.1 he'
      rcases Finset.mem_union.1 he' with he' | he'
      · obtain ⟨Z', hZ', hea⟩ := fB c e he'
        by_cases hZZ : Z = Z'
        · subst hZZ
          exact Finset.disjoint_left.1 (hHd Z hZ) heo hea
        · have heZ' := ((hH0mem Z' e).1 (harcH0 Z' hZ' hea)).1
          exact Finset.disjoint_left.1 (h.disjE Z (hCP Z hZ).1 Z' (hCP Z' hZ').1 hZZ) heZ heZ'
      · exact Finset.disjoint_left.1 (f3 c Z (hCP Z hZ).1 (hCP Z hZ).2.1.ge) he' heZ
  have hd0 : Disjoint (Srest G run Lext (m + 1) U) (A1 ∪ (A2 ∪ A3)) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rcases mem_Srest.1 he with ⟨Z', hZ', hmZ', heZ', -, heU⟩ | heU <;>
      rcases hround e he' with ⟨Z, hZ, hZm, heZ, heU2⟩ | ⟨c, hc⟩
    · have hne : Z' ≠ Z := fun hh => by rw [hh] at hmZ'; omega
      exact Finset.disjoint_left.1 (h.disjE Z' hZ' Z hZ hne) heZ' heZ
    · exact Finset.disjoint_left.1 (f3 c Z' hZ' (by omega)) hc heZ'
    · exact heU2 heU
    · exact Finset.disjoint_left.1 (fUL c) heU hc
  refine ⟨U', D ++ (CP.toList.flatMap Dobj ++ (DP.toList.flatMap Ddem ++
      (Finset.univ : Finset (Fin 4)).toList.flatMap Dp)), ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨l, hl, hlR, c, hc⟩ := f1 e he
      exact mem_availFrom.2 ⟨l, by omega, hlR, c, hc⟩
    · obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 he
      exact mem_availFrom.2 ⟨m, le_rfl, hmR, c, p3 c hc⟩
  · rw [hset]
    exact isDecomp_union_finset' hD (isDecomp_union_finset' hdA1
      (isDecomp_union_finset' hdA2 hdA3 hd2) hd1) hd0
  · -- the count
    have hIcc : Finset.Icc m run.R = insert m (Finset.Icc (m + 1) run.R) := by
      ext l; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m ∉ Finset.Icc (m + 1) run.R := by simp
    rw [hIcc, Finset.sum_insert hnot]
    simp only [List.length_append, length_flatMap_toList, Nat.cast_add]
    have e1 : ((∑ Z ∈ CP, (Dobj Z).length : ℕ) : ℝ) ≤
        369 * ((∑ Z ∈ CP, (Pl ω Z).card : ℕ) : ℝ) := by
      have : ∑ Z ∈ CP, (Dobj Z).length ≤ 369 * ∑ Z ∈ CP, (Pl ω Z).card := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun Z hZ => hHlen Z hZ
      exact_mod_cast this
    have e2 : ((∑ Z ∈ DP, (Ddem Z).length : ℕ) : ℝ) ≤
        80 * ((∑ Z ∈ DP, (run.ancVerts G Z).card : ℕ) : ℝ) := by
      have : ∑ Z ∈ DP, (Ddem Z).length ≤ 80 * ∑ Z ∈ DP, (run.ancVerts G Z).card := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun Z hZ => hDlen Z hZ
      exact_mod_cast this
    have hk : kcost ω m = 369 * ((∑ Z ∈ CP, (Pl ω Z).card : ℕ) : ℝ) +
        80 * ((∑ Z ∈ DP, (run.ancVerts G Z).card : ℕ) : ℝ) +
        (if 3 ≤ m then pbound G run m else 0) := rfl
    rw [hk]
    linarith

/-- [s5:lemKRED], the light-part edges: the construction over all rounds `R, R−1, …, 1` gives a
decomposition of `⋃_{Y light} (E_{r(Y)}(Y) \ Lent_ext(Y))` into at most `Σ_{l ≤ R} kcost l`
objects. -/
theorem exists_decomp (h : KHyp ω Lext) :
    ∃ D : List (Obj V),
      IsDecomp ((((run.lightParts G).biUnion fun Z => run.E G Z.1 Z.2 \ Lext Z :
        Finset (Sym2 V))) : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ ∑ l ∈ Finset.Icc 1 run.R, kcost ω l := by
  classical
  have hall : ∀ k, k ≤ run.R → KInv ω Lext (run.R + 1 - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, [], Finset.empty_subset _, ?_, ?_⟩
      · have : Srest G run Lext (run.R + 1 - 0) ∅ = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro e he
          rcases mem_Srest.1 he with ⟨Z, hZ, hmZ, -⟩ | he
          · have := (h.round Z hZ).2; omega
          · exact Finset.notMem_empty e he
        rw [this, Finset.coe_empty]
        exact isDecomp_nil
      · have : Finset.Icc (run.R + 1 - 0) run.R = ∅ := by
          ext l; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
        rw [this, Finset.sum_empty]; simp
    | succ k ih =>
      intro hk
      have hI := ih (by omega)
      have he : run.R + 1 - k = (run.R - k) + 1 := by omega
      rw [he] at hI
      have := h.step (m := run.R - k) (by omega) hI
      rwa [show run.R + 1 - (k + 1) = run.R - k by omega]
  have hI := hall run.R le_rfl
  rw [show run.R + 1 - run.R = 1 by omega] at hI
  obtain ⟨U, D, hU, hD, hlen⟩ := hI
  refine ⟨D, hD.congr ?_, hlen⟩
  congr 1
  ext e
  rw [mem_Srest, Finset.mem_biUnion]
  constructor
  · rintro (⟨Z, hZ, -, heZ, heL, -⟩ | heU)
    · exact ⟨Z, hZ, Finset.mem_sdiff.2 ⟨heZ, heL⟩⟩
    · obtain ⟨l, -, -, c, hc⟩ := mem_availFrom.1 (hU heU)
      exact h.mem_E_sdiff_of_mem_lentUAvail hc
  · rintro ⟨Z, hZ, he⟩
    obtain ⟨heZ, heL⟩ := Finset.mem_sdiff.1 he
    by_cases heU : e ∈ U
    · exact Or.inr heU
    · exact Or.inl ⟨Z, hZ, (h.round Z hZ).1, heZ, heL, heU⟩

end KHyp

end EG.Light
