import EG.Spec.Vortex.TPV
import EG.Spec.Vortex.VX
import EG.Lib.Vortex.Size
import EG.Lib.Found.Fnum

/-! Cheap non-vacuity checks for the s4 Specs written by the P2 s4 Spec unit
(`EG/Spec/Vortex/TPV.lean`, `EG/Spec/Vortex/VX.lean`, Defs `EG/Defs/Probe/S4/TPV.lean`;
`formal/work/p2s/s4.md`).

* the size predicates `TPVSize`, `VXSize` hold for some `N` (by `EG.Vortex.eventually_size`);
* the admissibility predicate `TPVAdm Z O E` holds for `E = E(O)` whenever `V(O) = Z`;
* the conclusion `TPVConcl` is satisfiable (for `P = ∅`, every admissible `E`: `E^V = ∅`,
  `E^Q = E`; and for `E = ∅`), so it is not contradictory by encoding;
* the conclusion of `VXStatement` is satisfiable for an edgeless `G`.

* the expander hypotheses are satisfiable (fix round, review item "non-vacuity coverage"): the
  complete graph `completeOn Z` is an `(ε,s)`-expander whenever `0 ≤ ε` and
  `ε(2N/3)/log₂²N + s ≤ N/3` (`completeOn_isExpander`: a vertex outside `U` is missing from
  `Nbr_{K-F}(U)` only if all its `|U|` edges to `U` lie in `F`, so at most `|F|/|U| ≤ s` vertices
  are missing); for large `N` this gives `TPVHyp univ K P 2^{-5} (2^{150}L^{42})` for every `P`
  (`tpvHyp_satisfiable`) and both hypothesis regimes of Theorem VX⁺ (`vxHyp_satisfiable_5`,
  `vxHyp_satisfiable_6`), on `Fin N` with `TPVSize N`, `VXSize N`.
-/

open EG EG.Vortex Filter Topology

example : ∃ N : ℕ, TPVSize N := (eventually_size.exists).imp fun _ h => h.1

example : ∃ N : ℕ, VXSize N := (eventually_size.exists).imp fun _ h => h.2.2

section

variable {V : Type} [DecidableEq V]

/-- `E = E(O)` is admissible for Lemma TPV. -/
example (O : FGraph V) : TPVAdm O.verts O O.edges :=
  ⟨O.loopless, O.edge_verts, subset_rfl⟩

/-- For `P = ∅` the TPV conclusion holds for every edge set (`E^V = ∅`, `E^Q = E`). -/
example (Z : Finset V) (O : FGraph V) (E : Finset (Sym2 V)) : TPVConcl Z O ∅ E := by
  refine ⟨∅, E, by simp, by simp, ?_, by simp, ⟨[], by simpa using isDecomp_nil, by simp⟩,
    fun _ => rfl⟩
  intro e _ he
  induction e using Sym2.ind with
  | h a b => exact absurd (he a (Sym2.mem_mk_left a b)) (by simp)

/-- For `E = ∅` the TPV conclusion holds for every `P`. -/
example (Z P : Finset V) (O : FGraph V) : TPVConcl Z O P ∅ :=
  ⟨∅, ∅, by simp, by simp, by simp, by simp, ⟨[], by simpa using isDecomp_nil, by simp⟩,
    fun _ => rfl⟩

/-- The body of the VX⁺ conclusion is satisfiable for an edgeless graph. -/
example (Z : Finset V) :
    let G : FGraph V := ⟨Z, ∅, by simp, by simp⟩
    (∃ D : List (Obj V), IsDecomp (G.edges : Set (Sym2 V)) D ∧
        (D.length : ℝ) ≤ 38.4 * (Z.card : ℝ) + 13 * (Z.card : ℝ) ∧
        (D.countP Obj.isEdge : ℝ) ≤ (Z.card : ℝ) + 13 * (Z.card : ℝ) / L Z.card) ∧
      fnum G.edges ≤ 80 * Z.card := by
  intro G
  refine ⟨⟨[], by simpa [G] using isDecomp_nil, by simp; positivity, ?_⟩, by simp [G]⟩
  simp only [List.countP_nil, Nat.cast_zero]
  have := L_nonneg Z.card
  positivity

end

/-- The Specs elaborate at the intended types. -/
example : EG.Spec.TPVStatement.{0} ↔ EG.Spec.TPVStatement.{0} := Iff.rfl
example : EG.Spec.VXStatement.{0} ↔ EG.Spec.VXStatement.{0} := Iff.rfl

/-! ## Satisfiability of the expander hypotheses (fix round) -/

namespace EGTest.S4

variable {V : Type} [DecidableEq V]

/-- The complete graph on a finite vertex set `Z`. -/
def completeOn (Z : Finset V) : FGraph V where
  verts := Z
  edges := Z.sym2.filter (fun e => ¬ e.IsDiag)
  edge_verts e he v hv := by
    rw [Finset.mem_filter, Finset.mem_sym2_iff] at he
    exact he.1 v hv
  loopless e he := (Finset.mem_filter.1 he).2

theorem lost_mul_card_le (Z U : Finset V) (F : Finset (Sym2 V)) (hU : U ⊆ Z) :
    ((Z \ U) \ ((completeOn Z).deleteEdges F).nbrSet U).card * U.card ≤ F.card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun p => s(p.2, p.1)) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at h1
    obtain ⟨⟨hvZ, hvU⟩, hvN⟩ := h1
    by_contra hF
    apply hvN
    simp only [FGraph.nbrSet, FGraph.deleteEdges, FGraph.Adj, completeOn, Finset.mem_filter,
      Finset.mem_sdiff]
    refine ⟨⟨hvZ, hvU⟩, p.2, h2, ⟨?_, hF⟩⟩
    rw [Finset.mem_sym2_iff]
    refine ⟨?_, ?_⟩
    · intro w hw
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact hU h2
      · exact hvZ
    · rw [Sym2.mk_isDiag_iff]
      rintro h
      exact hvU (h ▸ h2)
  · rintro ⟨v, u⟩ hp ⟨v', u'⟩ hp' he
    rw [Finset.mem_coe, Finset.mem_product] at hp hp'
    have hv : v ∉ U := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hp.1).1).2
    have hv' : v' ∉ U := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hp'.1).1).2
    simp only at he
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · exact absurd (h1 ▸ hp.2) hv'

theorem completeOn_isExpander (Z : Finset V) (ε s : ℝ) (hε : 0 ≤ ε)
    (h : ε * (2 * (Z.card : ℝ) / 3) / Real.logb 2 Z.card ^ 2 + s ≤ (Z.card : ℝ) / 3) :
    (completeOn Z).IsExpander ε s := by
  intro U F hUZ _ hU1 hU2 hFs
  have hcard : (completeOn Z).card = Z.card := rfl
  rw [hcard] at hU2 ⊢
  have hUZ' : U ⊆ Z := hUZ
  set nbr := ((completeOn Z).deleteEdges F).nbrSet U with hnbr
  have hsub : nbr ⊆ Z \ U := Finset.filter_subset _ _
  have hlost := lost_mul_card_le Z U F hUZ'
  have e1 : ((Z \ U) \ nbr).card + nbr.card = (Z \ U).card := Finset.card_sdiff_add_card_eq_card hsub
  have e2 : (Z \ U).card + U.card = Z.card := Finset.card_sdiff_add_card_eq_card hUZ'
  have hu : (0 : ℝ) < U.card := by exact_mod_cast hU1
  have hl : (((Z \ U) \ nbr).card : ℝ) * U.card ≤ F.card := by exact_mod_cast hlost
  have hls : (((Z \ U) \ nbr).card : ℝ) ≤ s := by
    have : (((Z \ U) \ nbr).card : ℝ) * U.card ≤ s * U.card := hl.trans hFs
    exact le_of_mul_le_mul_right this hu
  have e1' : (((Z \ U) \ nbr).card : ℝ) + nbr.card = (Z \ U).card := by exact_mod_cast e1
  have e2' : ((Z \ U).card : ℝ) + U.card = Z.card := by exact_mod_cast e2
  have hmono : ε * U.card / Real.logb 2 Z.card ^ 2 ≤
      ε * (2 * (Z.card : ℝ) / 3) / Real.logb 2 Z.card ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hU2 hε) (sq_nonneg _)
  linarith

/-- Eventually `L ≥ 2^{10}`, `2^{151} L^{42} ≤ N/8` and `log₂ L ≤ L`. -/
theorem eventually_expander_room : ∀ᶠ N : ℕ in atTop,
    (2 : ℝ) ^ 10 ≤ L N ∧ (2 : ℝ) ^ 151 * L N ^ 42 ≤ (N : ℝ) / 8 ∧ Real.logb 2 (L N) ≤ L N := by
  have hc : (0 : ℝ) < 2 ^ (-154 : ℤ) := by positivity
  filter_upwards [eventually_L_ge (2 ^ 10),
    (tendsto_L_pow_div 42).eventually (eventually_le_nhds hc),
    tendsto_L.eventually eventually_logb_le, eventually_ge_atTop 1] with N hL h42 hlog hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨hL, ?_, ?_⟩
  · rw [div_le_iff₀ hN0] at h42
    have : (2 : ℝ) ^ (-154 : ℤ) = 1 / 2 ^ 154 := by norm_num
    rw [this] at h42
    nlinarith
  · have := L_nonneg N
    linarith

/-- The room condition gives the hypothesis of `completeOn_isExpander` for `ε ≤ 1`, `s ≤ N/8`. -/
theorem room_of (N : ℕ) (hL : (2 : ℝ) ^ 10 ≤ L N) (ε s : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : s ≤ (N : ℝ) / 8) :
    ε * (2 * (N : ℝ) / 3) / Real.logb 2 N ^ 2 + s ≤ (N : ℝ) / 3 := by
  have hL1 : (2 : ℝ) ^ 20 ≤ Real.logb 2 N ^ 2 := by
    have h : (2 : ℝ) ^ 20 = ((2 : ℝ) ^ 10) ^ 2 := by norm_num
    rw [h]
    exact pow_le_pow_left₀ (by norm_num) hL 2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : ε * (2 * (N : ℝ) / 3) / Real.logb 2 N ^ 2 ≤ ε * (2 * (N : ℝ) / 3) / 2 ^ 20 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hL1
  have h2 : ε * (2 * (N : ℝ) / 3) ≤ 1 * (2 * (N : ℝ) / 3) :=
    mul_le_mul_of_nonneg_right hε1 (by positivity)
  have h3 : ε * (2 * (N : ℝ) / 3) / 2 ^ 20 ≤ 1 * (2 * (N : ℝ) / 3) / 2 ^ 20 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  linarith

/-- `2^{151} L^{38} log₂ L ≤ N/8` under the room condition. -/
theorem vx_s_le (N : ℕ) (hL : (2 : ℝ) ^ 10 ≤ L N) (hb : (2 : ℝ) ^ 151 * L N ^ 42 ≤ (N : ℝ) / 8)
    (hlog : Real.logb 2 (L N) ≤ L N) :
    (2 : ℝ) ^ 151 * L N ^ 38 * Real.logb 2 (L N) ≤ (N : ℝ) / 8 := by
  have hL1 : (1 : ℝ) ≤ L N := le_trans (by norm_num) hL
  have h38 : (0 : ℝ) ≤ L N ^ 38 := pow_nonneg (L_nonneg N) 38
  have h1 : L N ^ 38 * Real.logb 2 (L N) ≤ L N ^ 38 * L N := mul_le_mul_of_nonneg_left hlog h38
  have h2 : L N ^ 38 * L N ≤ L N ^ 42 := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hL1 (by norm_num)
  have h3 : (2 : ℝ) ^ 151 * (L N ^ 38 * Real.logb 2 (L N)) ≤ 2 ^ 151 * L N ^ 42 :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  linarith [mul_assoc ((2 : ℝ) ^ 151) (L N ^ 38) (Real.logb 2 (L N))]

/-- Satisfiability of the hypotheses of Lemma TPV (`EG.Vortex.TPVHyp`), for every `P`: the
complete graph on `N` vertices, `ε_O = 2^{-5}`, `s = 2^{150} L^{42}`. -/
theorem tpvHyp_satisfiable : ∃ (N : ℕ) (O : FGraph (Fin N)) (εO s : ℝ),
    ∀ P : Finset (Fin N), TPVHyp Finset.univ O P εO s := by
  obtain ⟨N, ⟨hT, -, -⟩, hL, hb, -⟩ := (eventually_size.and eventually_expander_room).exists
  refine ⟨N, completeOn Finset.univ, 2 ^ (-5 : ℤ), 2 ^ 150 * L N ^ 42, fun P => ?_⟩
  have hc : (Finset.univ : Finset (Fin N)).card = N := Finset.card_fin N
  have hε : (0 : ℝ) ≤ 2 ^ (-5 : ℤ) := by positivity
  have hε1 : (2 : ℝ) ^ (-5 : ℤ) ≤ 1 := by norm_num
  have h42 : (0 : ℝ) ≤ L N ^ 42 := pow_nonneg (L_nonneg N) 42
  refine ⟨by rw [hc]; exact hT, rfl, ?_, by norm_num, le_rfl, by rw [hc], Finset.subset_univ P⟩
  apply completeOn_isExpander _ _ _ hε
  rw [hc]
  exact room_of N hL _ _ hε hε1 (by nlinarith)

/-- Satisfiability of the hypotheses of Theorem VX⁺ (`EG.Spec.VXStatement`), first regime
`ε_O = 2^{-5}`, `s = 2^{146} L^{38} log₂ L`. -/
theorem vxHyp_satisfiable_5 : ∃ (N : ℕ) (O : FGraph (Fin N)) (εO s : ℝ),
    VXSize (Finset.univ : Finset (Fin N)).card ∧ O.verts = Finset.univ ∧ O.IsExpander εO s ∧
    εO = (2 : ℝ) ^ (-5 : ℤ) ∧
    (2 : ℝ) ^ 146 * L (Finset.univ : Finset (Fin N)).card ^ 38 *
      Real.logb 2 (L (Finset.univ : Finset (Fin N)).card) ≤ s := by
  obtain ⟨N, ⟨-, -, hV⟩, hL, hb, hlog⟩ := (eventually_size.and eventually_expander_room).exists
  have hc : (Finset.univ : Finset (Fin N)).card = N := Finset.card_fin N
  refine ⟨N, completeOn Finset.univ, 2 ^ (-5 : ℤ), 2 ^ 146 * L N ^ 38 * Real.logb 2 (L N),
    by rw [hc]; exact hV, rfl, ?_, rfl, by rw [hc]⟩
  have hε : (0 : ℝ) ≤ 2 ^ (-5 : ℤ) := by positivity
  have hε1 : (2 : ℝ) ^ (-5 : ℤ) ≤ 1 := by norm_num
  have hs := vx_s_le N hL hb hlog
  have hlog0 : 0 ≤ Real.logb 2 (L N) :=
    Real.logb_nonneg (by norm_num) (le_trans (by norm_num) hL)
  have h38 : (0 : ℝ) ≤ L N ^ 38 * Real.logb 2 (L N) := mul_nonneg (pow_nonneg (L_nonneg N) 38) hlog0
  apply completeOn_isExpander _ _ _ hε
  rw [hc]
  refine room_of N hL _ _ hε hε1 ?_
  rw [mul_assoc] at hs ⊢
  nlinarith

/-- Satisfiability of the hypotheses of Theorem VX⁺ (`EG.Spec.VXStatement`), second regime
`ε_O = 2^{-6}`, `s = 2^{151} L^{38} log₂ L`. -/
theorem vxHyp_satisfiable_6 : ∃ (N : ℕ) (O : FGraph (Fin N)) (εO s : ℝ),
    VXSize (Finset.univ : Finset (Fin N)).card ∧ O.verts = Finset.univ ∧ O.IsExpander εO s ∧
    εO = (2 : ℝ) ^ (-6 : ℤ) ∧
    (2 : ℝ) ^ 151 * L (Finset.univ : Finset (Fin N)).card ^ 38 *
      Real.logb 2 (L (Finset.univ : Finset (Fin N)).card) ≤ s := by
  obtain ⟨N, ⟨-, -, hV⟩, hL, hb, hlog⟩ := (eventually_size.and eventually_expander_room).exists
  have hc : (Finset.univ : Finset (Fin N)).card = N := Finset.card_fin N
  refine ⟨N, completeOn Finset.univ, 2 ^ (-6 : ℤ), 2 ^ 151 * L N ^ 38 * Real.logb 2 (L N),
    by rw [hc]; exact hV, rfl, ?_, rfl, by rw [hc]⟩
  have hε : (0 : ℝ) ≤ 2 ^ (-6 : ℤ) := by positivity
  have hε1 : (2 : ℝ) ^ (-6 : ℤ) ≤ 1 := by norm_num
  apply completeOn_isExpander _ _ _ hε
  rw [hc]
  exact room_of N hL _ _ hε hε1 (vx_s_le N hL hb hlog)

end EGTest.S4
