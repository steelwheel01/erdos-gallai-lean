module

public import EG.Spec.Link.L15
public import EG.Spec.Stage1.COLa
public import EG.Spec.HB.Structure
public import EG.Spec.Lend.COLJV
public import EG.Lib.Stage1.COL
public import EG.Lib.Prob.TotalExp
public import EG.Lib.Prob.Uniform
public import EG.Lib.Lend.Standing
public import EG.Lib.Gamma.Full

/-!
# Lemma COL (a), failure bound (manuscript s3:lemCOL, proof of (a)) — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemCOL] (a):
"Stage (i) is a uniform `2`-colouring of `E(H_Y)`. By Lemma s3:lemL15p with `k = 2`, which needs
`s_Y ≥ 80L` (row 3 of Table s3:tabCOLJV), `Own_Y` and `Lend_Y` are `(ε_Y,s_Y/4)`-expanders on
`V(Y)`, except with probability at most `4N^{-5}`.
Condition on stage (i) with `Lend_Y` such an expander. Stage (ii) is then a uniform
`k`-colouring of `Lend_Y`. By Lemma s3:lemL15p, which needs `s_Y/4 ≥ 40kL` (row 3), every lent
class is an `(ε_Y,s_Y/(8k))`-expander on `V(Y)`, except with probability at most `2kN^{-5}`.
If `Y` is light, condition on `Own_Y` being a `(2^{-6},s_r/8)`-expander. Stage (iii) is a uniform
`k_own`-colouring. Lemma s3:lemL15p, which needs `s_r/8 ≥ 40k_own L` (row 3), makes every own
class an expander with parameters `2^{-6}` and `s_r/(16k_own)`, except with probability at most
`2k_own N^{-5}`. Using row 9 (`k ≤ λ^{3.3}`), `k_own ≤ L ≤ 2λ` and `N^3 ≥ λ^{309}/8`, the total
failure probability of (a) is at most `2(2+k+k_own)N^{-5} ≤ N^{-2}/4`."

Formal route. Lemma 15⁺ enters as the hypothesis `hL15 : Spec.L15pStatement` (transported to any
law with the uniform colouring as image, `l15p_fail`). "Condition on stage (i)" is conditioning on
the bit vector `edgeBits` (`prob_le_of_cond`, the law of total probability); given the bits, the
lent indices of the lent edges and the own labels of the own edges are uniform colourings
(`Stage1.map_idx_cond_edgeBits`, `Stage1.map_own_cond_edgeBits`). `H_Y` is an
`(ε_Y,s_Y)`-expander by Proposition s2:propStructure (i) (`hStr : Spec.StructureExpStatement`);
rows 3 and 9 of the COL-JV table are the hypotheses `h3`, `h9`. The bound `k_own ≤ L ≤ 2λ` is
replaced by the cruder `k_own ≤ L_Y/2 + 1 ≤ N` (`Standing.kown_le`), which suffices.
-/

public section

namespace EG.COLaProof

open EG.HB EG.FinDist

universe u v

/-! ### General tools -/

section General

variable {Ω β : Type*}

/-- The law of total probability, as a bound: if `P(A | π = b) ≤ q` for every value `b` of `π`
of positive probability, then `P(A) ≤ q`. -/
theorem prob_le_of_cond [DecidableEq β] (μ : FinDist Ω) (π : Ω → β) {A : Set Ω} {q : ℝ}
    (h : ∀ b (hb : 0 < μ.prob (π ⁻¹' {b})), (μ.cond (π ⁻¹' {b}) hb).prob A ≤ q) :
    μ.prob A ≤ q := by
  have := μ.expect_le_of_cond_le π (X := A.indicator 1) (Y := fun _ => q) fun b hb => by
    rw [← prob_eq_expect, expect_const]; exact h b hb
  rwa [← prob_eq_expect, expect_const] at this

variable {V : Type u} [DecidableEq V]

/-- [s3:lemL15p] for a colouring with the law of the uniform colouring (a transport of the
statement): all `k` classes are `(ε′,s/(2k))`-expanders except with probability `2kN^{-5}`. -/
theorem l15p_fail (hL15 : Spec.L15pStatement.{u}) {X : FGraph V} {ε' s : ℝ} {k : ℕ} [NeZero k]
    (hε0 : 0 < ε') (hε1 : ε' ≤ 1) (hs : 40 * (k : ℝ) * Real.logb 2 (X.card : ℝ) ≤ s)
    (hX : X.IsExpander ε' s) (μ : FinDist Ω) (c : Ω → X.edges → Fin k)
    (hc : μ.map c = randColouring X.edges k) :
    μ.prob {ω | ¬ ∀ i : Fin k, (X.colourClass (c ω) i).IsExpander ε' (s / (2 * (k : ℝ)))} ≤
      2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) := by
  obtain ⟨-, h2⟩ := hL15 V X ε' s k hε0 hε1 hs hX
  rw [← hc, prob_map] at h2
  have e : {ω | ¬ ∀ i : Fin k, (X.colourClass (c ω) i).IsExpander ε' (s / (2 * (k : ℝ)))} =
      (c ⁻¹' {c' | ∀ i : Fin k, (X.restrictEdges (FinDist.selectSet X.edges
        fun e => decide (c' e = i))).IsExpander ε' (s / (2 * (k : ℝ)))})ᶜ := rfl
  rw [e, prob_compl]
  linarith

end General

/-! ### The three stages -/

section Stages

variable {V : Type u} [DecidableEq V] {G : FGraph V} {run : Run V} (Y : PartId)

theorem card_ancGraph : (run.ancGraph G Y).card = (run.ancVerts G Y).card := by
  rw [FGraph.card_def, Run.ancGraph_verts]

theorem logb_card_ancGraph :
    Real.logb 2 ((run.ancGraph G Y).card : ℝ) = run.LY G Y := by
  rw [card_ancGraph]; rfl

/-! #### Stage (i): the bits -/

/-- The bits as a `2`-colouring (`false ↦ 0`, `true ↦ 1`). -/
noncomputable def col2 (c : Stage1.Colouring G run Y) : ↥(run.ancGraph G Y).edges → Fin 2 :=
  fun e => finTwoEquiv.symm (c e).1

theorem map_col2 :
    (Stage1.colouringLaw G run Y).map (col2 Y) = randColouring (run.ancGraph G Y).edges 2 := by
  have e1 : col2 (G := G) (run := run) Y =
      (fun (b : ↥(run.ancGraph G Y).edges → Bool) e => finTwoEquiv.symm (b e)) ∘
        Stage1.edgeBits G run Y := rfl
  rw [e1, ← FinDist.map_map, Stage1.map_edgeBits,
    map_pi (μ := fun _ => Stage1.bitLaw) (fun _ => (finTwoEquiv.symm : Bool → Fin 2))]
  have hb : Stage1.bitLaw.map (finTwoEquiv.symm : Bool → Fin 2) = uniform (Fin 2) := by
    ext j
    rw [map_equiv_w, Equiv.symm_symm, uniform_w]
    fin_cases j
    · simp [Stage1.bitLaw, finTwoEquiv]; norm_num
    · simp [Stage1.bitLaw, finTwoEquiv]
  rw [hb]
  rfl

theorem Own_eq (c : Stage1.Colouring G run Y) :
    Stage1.Own G run Y c = (run.ancGraph G Y).colourClass (col2 Y c) 0 := by
  refine FGraph.ext (by simp) ?_
  ext e
  rw [Stage1.mem_Own_edges, FGraph.mem_colourClass_edges]
  refine exists_congr fun h => ?_
  cases hb : (c ⟨e, h⟩).1 <;> simp [col2, hb, finTwoEquiv]

theorem Lend_eq (c : Stage1.Colouring G run Y) :
    Stage1.Lend G run Y c = (run.ancGraph G Y).colourClass (col2 Y c) 1 := by
  refine FGraph.ext (by simp) ?_
  ext e
  rw [Stage1.mem_Lend_edges, FGraph.mem_colourClass_edges]
  refine exists_congr fun h => ?_
  cases hb : (c ⟨e, h⟩).1 <;> simp [col2, hb, finTwoEquiv]

/-- Stage (i): "`Own_Y` and `Lend_Y` are `(ε_Y,s_Y/4)`-expanders on `V(Y)`, except with
probability at most `4N^{-5}`" (Lemma 15⁺ with `k = 2`, row 3: `s_Y ≥ 80L`). -/
theorem prob_stage1_le (hL15 : Spec.L15pStatement.{u}) {ε s : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 80 * run.LY G Y ≤ s) (hH : (run.ancGraph G Y).IsExpander ε s) :
    (Stage1.colouringLaw G run Y).prob {c | ¬ ((Stage1.Own G run Y c).IsExpander ε (s / 4) ∧
      (Stage1.Lend G run Y c).IsExpander ε (s / 4))} ≤
      4 * ((run.ancVerts G Y).card : ℝ) ^ (-5 : ℤ) := by
  have hs' : 40 * ((2 : ℕ) : ℝ) * Real.logb 2 ((run.ancGraph G Y).card : ℝ) ≤ s := by
    rw [logb_card_ancGraph]; push_cast; linarith
  have h := l15p_fail hL15 hε0 hε1 hs' hH _ (col2 Y) (map_col2 Y)
  have e4 : s / (2 * ((2 : ℕ) : ℝ)) = s / 4 := by norm_num
  rw [e4, card_ancGraph] at h
  have hsub : {c : Stage1.Colouring G run Y | ¬ ((Stage1.Own G run Y c).IsExpander ε (s / 4) ∧
      (Stage1.Lend G run Y c).IsExpander ε (s / 4))} ⊆ {ω | ¬ ∀ i : Fin 2,
        ((run.ancGraph G Y).colourClass (col2 Y ω) i).IsExpander ε (s / 4)} := by
    intro c hc hall
    exact hc ⟨by rw [Own_eq]; exact hall 0, by rw [Lend_eq]; exact hall 1⟩
  refine (prob_mono _ hsub).trans (h.trans (le_of_eq ?_))
  push_cast; ring

/-! #### Stage (ii): the lent indices given the bits -/

/-- The lent classes' index set, enumerated. -/
noncomputable def lentEquiv : ↥(Stage1.lentIdx G run Y) ≃ Fin (Stage1.klend G run Y) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, Stage1.klend_eq_card_lentIdx])

/-- The lent index as a colour in `Fin k_lend` (junk `0` off `lentIdx`). -/
noncomputable def gIdx [NeZero (Stage1.klend G run Y)] :
    Option Stage1.LentTag → Fin (Stage1.klend G run Y)
  | some i => if hi : i ∈ Stage1.lentIdx G run Y then lentEquiv Y ⟨i, hi⟩ else 0
  | none => 0

theorem gIdx_some [NeZero (Stage1.klend G run Y)] {i : Stage1.LentTag}
    (hi : i ∈ Stage1.lentIdx G run Y) : gIdx Y (some i) = lentEquiv Y ⟨i, hi⟩ := by
  simp [gIdx, hi]

theorem map_idxLaw_gIdx [NeZero (Stage1.klend G run Y)] (hR : Y.1 + 2 ≤ run.R) :
    (Stage1.idxLaw G run Y).map (gIdx Y) = uniform (Fin (Stage1.klend G run Y)) := by
  have hne : (Stage1.lentIdx G run Y).Nonempty := Stage1.lentIdx_nonempty_iff.2 hR
  have : Nonempty ↥(Stage1.lentIdx G run Y) := hne.to_subtype
  rw [Stage1.idxLaw_eq_of_nonempty G run Y hne, FinDist.map_map]
  have : (gIdx Y ∘ fun i : ↥(Stage1.lentIdx G run Y) => some i.1) = ⇑(lentEquiv Y) := by
    funext i
    simp only [Function.comp_apply]
    exact gIdx_some Y i.2
  rw [this]
  exact map_equiv_uniform _

/-- On the support, if `r ≤ R-2`, every lent index is `some i` with `i ∈ lentIdx`. -/
theorem idx_some_of_mem_supp {c : Stage1.Colouring G run Y}
    (hc : c ∈ (Stage1.colouringLaw G run Y).supp) (hR : Y.1 + 2 ≤ run.R)
    (e : ↥(run.ancGraph G Y).edges) : ∃ i ∈ Stage1.lentIdx G run Y, (c e).2.1 = some i := by
  rcases hidx : (c e).2.1 with _ | i
  · exfalso
    have he : c e ∈ (Stage1.edgeLaw G run Y).supp := (mem_supp_pi _).1 hc e
    have hne : (Stage1.lentIdx G run Y).Nonempty := Stage1.lentIdx_nonempty_iff.2 hR
    rw [mem_supp] at he
    apply he
    have : (Stage1.idxLaw G run Y).w none = 0 := by
      unfold Stage1.idxLaw
      rw [dif_pos hne, map_w]
      have : Nonempty ↥(Stage1.lentIdx G run Y) := hne.to_subtype
      rw [prob_eq_zero_iff]
      intro j hj
      simp at hj
    simp [Stage1.edgeLaw, prod_w', hidx, this]
  · exact ⟨i, Stage1.idx_mem_of_mem_supp G run Y hc e i hidx, rfl⟩

variable (β : ↥(run.ancGraph G Y).edges → Bool)

/-- The edges of the colour class `b` of the bit vector `β`, as edges of `H_Y` with bit `b`. -/
noncomputable def τ (b : Bool) :
    ↥((run.ancGraph G Y).colourClass β b).edges ≃ {e : ↥(run.ancGraph G Y).edges // β e = b} where
  toFun e := ⟨⟨e.1, (FGraph.mem_colourClass_edges.1 e.2).fst⟩,
    (FGraph.mem_colourClass_edges.1 e.2).snd⟩
  invFun e := ⟨e.1.1, FGraph.mem_colourClass_edges.2 ⟨e.1.2, e.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The lent indices of the lent edges given the bits `β`, as a `k_lend`-colouring of the lent
class graph `H_Y[β = true]`. -/
noncomputable def cL [NeZero (Stage1.klend G run Y)] (c : Stage1.Colouring G run Y) :
    ↥((run.ancGraph G Y).colourClass β true).edges → Fin (Stage1.klend G run Y) :=
  fun e => gIdx Y (c (τ Y β true e).1).2.1

theorem map_cL [NeZero (Stage1.klend G run Y)] (hR : Y.1 + 2 ≤ run.R)
    (hβ : 0 < (Stage1.colouringLaw G run Y).prob (Stage1.edgeBits G run Y ⁻¹' {β})) :
    ((Stage1.colouringLaw G run Y).cond (Stage1.edgeBits G run Y ⁻¹' {β}) hβ).map (cL Y β) =
      randColouring ((run.ancGraph G Y).colourClass β true).edges (Stage1.klend G run Y) := by
  have e1 : cL (G := G) (run := run) Y β =
      (fun (F : {e : ↥(run.ancGraph G Y).edges // β e = true} → Fin (Stage1.klend G run Y))
        (e : ↥((run.ancGraph G Y).colourClass β true).edges) => F (τ Y β true e)) ∘
      (fun (F : {e : ↥(run.ancGraph G Y).edges // β e = true} → Option Stage1.LentTag) e' =>
        gIdx Y (F e')) ∘
      (fun (c : Stage1.Colouring G run Y) (e : {e : ↥(run.ancGraph G Y).edges // β e = true}) =>
        (c e).2.1) := rfl
  rw [e1, ← FinDist.map_map, ← FinDist.map_map, Stage1.map_idx_cond_edgeBits,
    map_pi (μ := fun _ => Stage1.idxLaw G run Y) (fun _ => gIdx Y), map_idxLaw_gIdx Y hR,
    pi_uniform, randColouring_eq_uniform]
  exact map_equiv_uniform (Equiv.arrowCongr (τ Y β true).symm (Equiv.refl _))

theorem lentClass_eq [NeZero (Stage1.klend G run Y)] (hR : Y.1 + 2 ≤ run.R)
    {c : Stage1.Colouring G run Y} (hc : c ∈ (Stage1.colouringLaw G run Y).supp)
    {i : Stage1.LentTag} (hi : i ∈ Stage1.lentIdx G run Y) :
    Stage1.lentClass G run Y c i =
      ((run.ancGraph G Y).colourClass (Stage1.edgeBits G run Y c) true).colourClass
        (cL Y (Stage1.edgeBits G run Y c) c) (lentEquiv Y ⟨i, hi⟩) := by
  refine FGraph.ext (by simp) ?_
  ext e
  rw [Stage1.mem_lentClass_edges, FGraph.mem_colourClass_edges]
  constructor
  · rintro ⟨h, hb, hidx⟩
    refine ⟨FGraph.mem_colourClass_edges.2 ⟨h, hb⟩, ?_⟩
    show gIdx Y (c ⟨e, _⟩).2.1 = _
    rw [hidx, gIdx_some Y hi]
  · rintro ⟨h', hg⟩
    obtain ⟨h, hb⟩ := FGraph.mem_colourClass_edges.1 h'
    refine ⟨h, hb, ?_⟩
    obtain ⟨i', hi', hidx⟩ := idx_some_of_mem_supp Y hc hR ⟨e, h⟩
    have hg' : gIdx Y (c ⟨e, h⟩).2.1 = lentEquiv Y ⟨i, hi⟩ := hg
    rw [hidx, gIdx_some Y hi'] at hg'
    have hii : i' = i := congrArg Subtype.val ((lentEquiv Y).injective hg')
    rw [hidx, hii]

/-- Stage (ii): "Condition on stage (i) with `Lend_Y` such an expander. … every lent class is an
`(ε_Y,s_Y/(8k))`-expander on `V(Y)`, except with probability at most `2kN^{-5}`" (row 3:
`s_Y/4 ≥ 40kL`). -/
theorem prob_stage2_le (hL15 : Spec.L15pStatement.{u}) {ε s : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 40 * (Stage1.klend G run Y : ℝ) * run.LY G Y ≤ s / 4) :
    (Stage1.colouringLaw G run Y).prob {c | (Stage1.Lend G run Y c).IsExpander ε (s / 4) ∧
      ¬ ∀ i ∈ Stage1.lentIdx G run Y, (Stage1.lentClass G run Y c i).IsExpander ε
        (s / (8 * (Stage1.klend G run Y : ℝ)))} ≤
      2 * (Stage1.klend G run Y : ℝ) * ((run.ancVerts G Y).card : ℝ) ^ (-5 : ℤ) := by
  classical
  have hk0 : (0 : ℝ) ≤ Stage1.klend G run Y := Nat.cast_nonneg _
  have hN5 : (0 : ℝ) ≤ ((run.ancVerts G Y).card : ℝ) ^ (-5 : ℤ) := zpow_nonneg (Nat.cast_nonneg _) _
  by_cases hR : Y.1 + 2 ≤ run.R
  swap
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [prob_eq_zero_iff]
    intro c hc
    exfalso
    apply hc.2
    intro i hi
    rw [(Stage1.lentIdx_eq_empty_iff (G := G) (run := run)).2 (by omega)] at hi
    simp at hi
  have : NeZero (Stage1.klend G run Y) := ⟨(Stage1.klend_pos_iff.2 hR).ne'⟩
  refine prob_le_of_cond _ (Stage1.edgeBits G run Y) fun β hβ => ?_
  set Xβ := (run.ancGraph G Y).colourClass β true with hXβ
  by_cases hX : Xβ.IsExpander ε (s / 4)
  · have hs' : 40 * (Stage1.klend G run Y : ℝ) * Real.logb 2 (Xβ.card : ℝ) ≤ s / 4 := by
      rw [hXβ, FGraph.colourClass_card, logb_card_ancGraph]; exact hs
    have h := l15p_fail hL15 hε0 hε1 hs' hX _ (cL Y β) (map_cL Y β hR hβ)
    have hcard : Xβ.card = (run.ancVerts G Y).card := by
      rw [hXβ, FGraph.colourClass_card, card_ancGraph]
    rw [hcard] at h
    refine le_trans (prob_mono_ae _ fun c hc hcA => ?_) h
    obtain ⟨hcβ, hcpos⟩ := (cond_w_pos_iff _ hβ).1 hc
    have hsupp : c ∈ (Stage1.colouringLaw G run Y).supp := (mem_supp_iff_pos _).2 hcpos
    have hcβ' : Stage1.edgeBits G run Y c = β := hcβ
    subst hcβ'
    intro hall
    apply hcA.2
    intro i hi
    rw [lentClass_eq Y hR hsupp hi]
    have e8 : s / 4 / (2 * (Stage1.klend G run Y : ℝ)) = s / (8 * (Stage1.klend G run Y : ℝ)) := by
      rw [div_div]; ring_nf
    rw [← e8]
    exact hall _
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [prob_eq_zero_iff]
    intro c hc
    by_contra hw
    have hpos := lt_of_le_of_ne (w_nonneg _ c) (Ne.symm hw)
    obtain ⟨hcβ, -⟩ := (cond_w_pos_iff _ hβ).1 hpos
    have hcβ' : Stage1.edgeBits G run Y c = β := hcβ
    apply hX
    rw [hXβ, ← hcβ']
    exact hc.1

/-! #### Stage (iii): the own labels given the bits -/

/-- The own labels of the own edges given the bits `β`, as a `k_own`-colouring of the own class
graph `H_Y[β = false]`. -/
noncomputable def cO (c : Stage1.Colouring G run Y) :
    ↥((run.ancGraph G Y).colourClass β false).edges → Fin (Stage1.kown G run Y) :=
  fun e => (c (τ Y β false e).1).2.2

theorem map_cO
    (hβ : 0 < (Stage1.colouringLaw G run Y).prob (Stage1.edgeBits G run Y ⁻¹' {β})) :
    ((Stage1.colouringLaw G run Y).cond (Stage1.edgeBits G run Y ⁻¹' {β}) hβ).map (cO Y β) =
      randColouring ((run.ancGraph G Y).colourClass β false).edges (Stage1.kown G run Y) := by
  have e1 : cO (G := G) (run := run) Y β =
      (fun (F : {e : ↥(run.ancGraph G Y).edges // β e = false} → Fin (Stage1.kown G run Y))
        (e : ↥((run.ancGraph G Y).colourClass β false).edges) => F (τ Y β false e)) ∘
      (fun (c : Stage1.Colouring G run Y) (e : {e : ↥(run.ancGraph G Y).edges // β e = false}) =>
        (c e).2.2) := rfl
  rw [e1, ← FinDist.map_map, Stage1.map_own_cond_edgeBits, randColouring_eq_uniform,
    randColouring_eq_uniform]
  exact map_equiv_uniform (Equiv.arrowCongr (τ Y β false).symm (Equiv.refl _))

theorem ownClass_eq (c : Stage1.Colouring G run Y) (o : Fin (Stage1.kown G run Y)) :
    Stage1.ownClass G run Y c o =
      ((run.ancGraph G Y).colourClass (Stage1.edgeBits G run Y c) false).colourClass
        (cO Y (Stage1.edgeBits G run Y c) c) o := by
  refine FGraph.ext (by simp) ?_
  ext e
  rw [Stage1.mem_ownClass_edges, FGraph.mem_colourClass_edges]
  constructor
  · rintro ⟨h, hb, ho⟩
    exact ⟨FGraph.mem_colourClass_edges.2 ⟨h, hb⟩, ho⟩
  · rintro ⟨h', ho⟩
    obtain ⟨h, hb⟩ := FGraph.mem_colourClass_edges.1 h'
    exact ⟨h, hb, ho⟩

/-- Stage (iii): "condition on `Own_Y` being a `(2^{-6},s_r/8)`-expander. Stage (iii) is a
uniform `k_own`-colouring. Lemma s3:lemL15p, which needs `s_r/8 ≥ 40k_own L` (row 3), makes every
own class an expander with parameters `2^{-6}` and `s_r/(16k_own)`, except with probability at
most `2k_own N^{-5}`" (here with general `(ε, s/4)`). -/
theorem prob_stage3_le (hL15 : Spec.L15pStatement.{u}) {ε s : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 40 * (Stage1.kown G run Y : ℝ) * run.LY G Y ≤ s / 4) :
    (Stage1.colouringLaw G run Y).prob {c | (Stage1.Own G run Y c).IsExpander ε (s / 4) ∧
      ¬ ∀ o : Fin (Stage1.kown G run Y), (Stage1.ownClass G run Y c o).IsExpander ε
        (s / 4 / (2 * (Stage1.kown G run Y : ℝ)))} ≤
      2 * (Stage1.kown G run Y : ℝ) * ((run.ancVerts G Y).card : ℝ) ^ (-5 : ℤ) := by
  classical
  have hk0 : (0 : ℝ) ≤ Stage1.kown G run Y := Nat.cast_nonneg _
  have hN5 : (0 : ℝ) ≤ ((run.ancVerts G Y).card : ℝ) ^ (-5 : ℤ) := zpow_nonneg (Nat.cast_nonneg _) _
  refine prob_le_of_cond _ (Stage1.edgeBits G run Y) fun β hβ => ?_
  set Xβ := (run.ancGraph G Y).colourClass β false with hXβ
  by_cases hX : Xβ.IsExpander ε (s / 4)
  · have hs' : 40 * (Stage1.kown G run Y : ℝ) * Real.logb 2 (Xβ.card : ℝ) ≤ s / 4 := by
      rw [hXβ, FGraph.colourClass_card, logb_card_ancGraph]; exact hs
    have h := l15p_fail hL15 hε0 hε1 hs' hX _ (cO Y β) (map_cO Y β hβ)
    have hcard : Xβ.card = (run.ancVerts G Y).card := by
      rw [hXβ, FGraph.colourClass_card, card_ancGraph]
    rw [hcard] at h
    refine le_trans (prob_mono_ae _ fun c hc hcA => ?_) h
    obtain ⟨hcβ, -⟩ := (cond_w_pos_iff _ hβ).1 hc
    have hcβ' : Stage1.edgeBits G run Y c = β := hcβ
    subst hcβ'
    intro hall
    apply hcA.2
    intro o
    rw [ownClass_eq Y c o]
    exact hall o
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [prob_eq_zero_iff]
    intro c hc
    by_contra hw
    have hpos := lt_of_le_of_ne (w_nonneg _ c) (Ne.symm hw)
    obtain ⟨hcβ, -⟩ := (cond_w_pos_iff _ hβ).1 hpos
    have hcβ' : Stage1.edgeBits G run Y c = β := hcβ
    apply hX
    rw [hXβ, ← hcβ']
    exact hc.1

end Stages

/-! ### Assembly -/

section Assembly

variable {V : Type u} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- [s2:propStructure] (i): "`H_Y` is an `(ε_Y,s_Y)`-expander on `V(Y)`". -/
theorem ancGraph_isExpander (hStr : Spec.StructureExpStatement.{u}) {Dstar : ℝ}
    (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {Y : PartId} (hY : Y ∈ run.ancestors G) :
    (run.ancGraph G Y).IsExpander (run.ancEps G Y) (run.ancS G Y) := by
  classical
  obtain ⟨hX0, hX, -, -⟩ := hStr V G Dstar run hΓ.gamma2a hV
  have hR := Standing.isRound_of_mem_ancestors hY
  have hRi : Y.1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  have ha : Y.2 ∈ run.prePartAddrs G Y.1 := (Run.mem_ancestors run G).1 hY
  by_cases hl : run.isLight G Y.1 Y.2
  · have e : run.ancGraph G Y = run.X G Y.1 Y.2 := by
      show Round.partGraph (run.graph G Y.1) (run.choice Y.1) Y.2 = _
      unfold Round.partGraph
      exact if_pos hl
    rw [e, Run.ancEps, Run.ancS, if_pos hl, if_pos hl]
    exact (hX Y.1 hRi Y.2 ha hl).2
  · have e : run.ancGraph G Y = run.X0 G Y.1 Y.2 := by
      show Round.partGraph (run.graph G Y.1) (run.choice Y.1) Y.2 = _
      unfold Round.partGraph
      exact if_neg hl
    rw [e, Run.ancEps, Run.ancS, if_neg hl, if_neg hl]
    exact (hX0 Y.1 hRi Y.2 ha).2

/-- `L_Y = log |V(Y)| ≤ |V(Y)|`. -/
theorem logb_le_self (n : ℕ) (hn : 0 < n) : Real.logb 2 (n : ℝ) ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.logb_le_iff_le_rpow (by norm_num) hn0, Real.rpow_natCast]
  exact_mod_cast (Nat.lt_two_pow_self).le

/-- The final numerics: "`2(2+k+k_own)N^{-5} ≤ … ≤ N^{-2}/4`". -/
theorem final_bound {N k ko x : ℝ} (hx : (2 : ℝ) ^ 256 ≤ x) (hN : x ^ 103 / 2 ≤ N)
    (hk : k ≤ x ^ (33 / 10 : ℝ)) (hko : ko ≤ N) (hko0 : 0 ≤ ko) :
    4 * N ^ (-5 : ℤ) + 2 * k * N ^ (-5 : ℤ) + 2 * ko * N ^ (-5 : ℤ) ≤ N ^ (-2 : ℤ) / 4 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hk4 : k ≤ x ^ 4 := by
    refine hk.trans ?_
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hx99 : (64 : ℝ) ≤ x ^ 99 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 99)
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have h103 : x ^ 103 = x ^ 4 * x ^ 99 := by ring
  have hN32 : 32 * x ^ 4 ≤ N := by
    have : 64 * x ^ 4 ≤ x ^ 4 * x ^ 99 :=
      (mul_le_mul_of_nonneg_right hx99 hx4).trans_eq (mul_comm _ _)
    linarith
  have hx4' : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx1
  have hN1 : (32 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hS : 4 * (4 + 2 * k + 2 * ko) ≤ N ^ 3 := by
    have h1 : 4 * (4 + 2 * k + 2 * ko) ≤ 12 * N := by linarith
    have h2 : 12 * N ≤ N * N * N := by
      have : (12 : ℝ) ≤ N * N := by nlinarith
      nlinarith
    calc 4 * (4 + 2 * k + 2 * ko) ≤ N * N * N := h1.trans h2
      _ = N ^ 3 := by ring
  have hN5 : (0 : ℝ) < (N ^ 5)⁻¹ := by positivity
  have e : N ^ 3 * (N ^ 5)⁻¹ = (N ^ 2)⁻¹ := by
    field_simp
  calc 4 * N ^ (-5 : ℤ) + 2 * k * N ^ (-5 : ℤ) + 2 * ko * N ^ (-5 : ℤ)
      = (4 + 2 * k + 2 * ko) * (N ^ 5)⁻¹ := by rw [zpow_neg, zpow_ofNat]; ring
    _ ≤ (N ^ 3 / 4) * (N ^ 5)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hN5.le
    _ = (N ^ 3 * (N ^ 5)⁻¹) / 4 := by ring
    _ = N ^ (-2 : ℤ) / 4 := by rw [e, zpow_neg, zpow_ofNat]

/-- [s3:lemCOL] (a), failure bound: "the total failure probability of (a) is at most
`2(2+k+k_own)N^{-5} ≤ … ≤ N^{-2}/4`". Inputs: Lemma 15⁺ (`hL15`), Proposition s2:propStructure
(i) (`hStr`) and rows 3 and 9 of the COL-JV table (`h3`, `h9`). -/
theorem colaProb (hL15 : Spec.L15pStatement.{u}) (hStr : Spec.StructureExpStatement.{u})
    (h3 : Spec.COLJVRow3Statement.{u}) (h9 : Spec.COLJVRow9Statement.{u}) :
    Spec.COLaProbStatement.{u, v} := by
  intro V _ G Dstar run hΓ hV _ Y hY Ω μ D hD
  classical
  have hR := Standing.isRound_of_mem_ancestors hY
  set N : ℝ := ((run.ancVerts G Y).card : ℝ) with hNdef
  obtain ⟨r3a, r3b, r3c⟩ := h3 V G Dstar run hΓ hV Y hY
  have r9 := h9 V G Dstar run hΓ hV Y hY
  have hH := ancGraph_isExpander hStr hΓ hV hY
  have hε : 0 < run.ancEps G Y ∧ run.ancEps G Y ≤ 1 := by
    by_cases hl : run.isLight G Y.1 Y.2
    · rw [Run.ancEps_of_isLight run G hl, epsC]; norm_num
    · rw [Run.ancEps_of_not_isLight run G hl, epsC]; norm_num
  have hs0 : (0 : ℝ) ≤ (run.s G Y.1 : ℝ) := Nat.cast_nonneg _
  have hsY : (run.s G Y.1 : ℝ) / 2 ≤ run.ancS G Y := by
    unfold Run.ancS; split_ifs <;> linarith
  have r3c' : 40 * (Stage1.kown G run Y : ℝ) * run.LY G Y ≤ run.ancS G Y / 4 := by linarith
  have hA1 := prob_stage1_le Y hL15 hε.1 hε.2 r3b hH
  have hA2 := prob_stage2_le Y hL15 hε.1 hε.2 r3a
  have hA3 := prob_stage3_le Y hL15 hε.1 hε.2 r3c'
  -- the event depends only on the colouring
  have e : {ω | ¬ Stage1.COLa G run Y (D ω)} =
      D ⁻¹' (Prod.fst ⁻¹' {c | ¬ Stage1.COLa G run Y (c, fun _ => none)}) := rfl
  rw [e, ← prob_map, hD, Stage1.colLaw, prob_prod_fst]
  have hsub : {c : Stage1.Colouring G run Y | ¬ Stage1.COLa G run Y (c, fun _ => none)} ⊆
      ({c | ¬ ((Stage1.Own G run Y c).IsExpander (run.ancEps G Y) (run.ancS G Y / 4) ∧
          (Stage1.Lend G run Y c).IsExpander (run.ancEps G Y) (run.ancS G Y / 4))} ∪
        {c | (Stage1.Lend G run Y c).IsExpander (run.ancEps G Y) (run.ancS G Y / 4) ∧
          ¬ ∀ i ∈ Stage1.lentIdx G run Y, (Stage1.lentClass G run Y c i).IsExpander
            (run.ancEps G Y) (run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ)))}) ∪
        {c | (Stage1.Own G run Y c).IsExpander (run.ancEps G Y) (run.ancS G Y / 4) ∧
          ¬ ∀ o : Fin (Stage1.kown G run Y), (Stage1.ownClass G run Y c o).IsExpander
            (run.ancEps G Y) (run.ancS G Y / 4 / (2 * (Stage1.kown G run Y : ℝ)))} := by
    intro c hc
    by_cases h1 : (Stage1.Own G run Y c).IsExpander (run.ancEps G Y) (run.ancS G Y / 4) ∧
        (Stage1.Lend G run Y c).IsExpander (run.ancEps G Y) (run.ancS G Y / 4)
    · by_cases h2 : ∀ i ∈ Stage1.lentIdx G run Y, (Stage1.lentClass G run Y c i).IsExpander
          (run.ancEps G Y) (run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ)))
      · right
        refine ⟨h1.1, fun h3' => hc ⟨h1.1, h1.2, h2, fun hl o => ?_⟩⟩
        have e1 : run.ancEps G Y = (2 : ℝ) ^ (-6 : ℤ) := by
          unfold Run.ancEps; rw [if_pos hl]
        have e2 : run.ancS G Y / 4 / (2 * (Stage1.kown G run Y : ℝ)) =
            (run.s G Y.1 : ℝ) / (16 * (Stage1.kown G run Y : ℝ)) := by
          unfold Run.ancS; rw [if_pos hl]; ring
        have := h3' o
        rwa [e1, e2] at this
      · left; right; exact ⟨h1.2, h2⟩
    · left; left; exact h1
  refine (prob_mono _ hsub).trans ?_
  refine ((prob_union_le _ _ _).trans (add_le_add ((prob_union_le _ _ _).trans
    (add_le_add hA1 hA2)) hA3)).trans ?_
  -- numerics
  obtain ⟨-, hx0, -⟩ := Standing.lam_facts hΓ hV hR
  have hx := Standing.lam_ge hΓ hV hR
  have hN := Standing.card_ancVerts_ge hY
  have hcard : 0 < (run.ancVerts G Y).card := by
    have : (0 : ℝ) < ((run.ancVerts G Y).card : ℝ) := by
      have : (0 : ℝ) < run.lam G Y.1 ^ 103 / 2 := by positivity
      linarith
    exact_mod_cast this
  have hko : (Stage1.kown G run Y : ℝ) ≤ N := by
    have h1 := Standing.kown_le (G := G) (run := run) Y
    have h2 : run.LY G Y ≤ N := logb_le_self _ hcard
    have h3' : (2 : ℝ) ≤ N := by
      have hl1 : (1 : ℝ) ≤ run.lam G Y.1 := le_trans (by norm_num) hx
      have : run.lam G Y.1 ≤ run.lam G Y.1 ^ 103 := le_self_pow₀ hl1 (by norm_num)
      have h4 : (4 : ℝ) ≤ run.lam G Y.1 := le_trans (by norm_num) hx
      linarith
    linarith
  exact final_bound hx hN r9 hko (Nat.cast_nonneg _)

end Assembly

end EG.COLaProof
