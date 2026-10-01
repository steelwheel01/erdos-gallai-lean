module

public import EG.Spec.Quot.MULT
public import EG.Lib.Quot.Quotient
public import EG.Lib.HB.Run

/-!
# Proof of Lemma MULT and of the PAR-MULT identity (manuscript s7:lemMULT) — probe P-1, stage 3

Unit P1, design note `formal/work/p2b/P1.md`. Manuscript proof: "Let `(h,u_1),…,(h,u_m)` be the
coloured hub items of colour `κ` at `h` with junction `w` […]. By step (e) […], the junction of
`(h,u_i)` lies in `Cand_l(u_i) ⊆ Pool_{l,r(u_i)}` […] so `r(u_i) = r` for all `i`. Moreover
`w ∈ Cand_l(u_i) ⊆ N_{H_{Y(u_i)}}(u_i) ⊆ V(Y(u_i))` […]. By (J1) of Lemma s6:lemJplus, for each class
`Y` there is at most one `J^hub` edge of class `Y` at `h` in round `l`, aggregated over all
MIX-parts. So the classes `Y(u_1),…,Y(u_m)` are pairwise distinct. Hence `m ≤ mult_r(w)` […], and
`mult_r(w) ≤ μ_r(w)` by Proposition s2:propOV. For the second statement: `[w]` is not isolated in
`B^{H,(ι)}_κ` if and only if some edge of rank `ι` is incident to `[w]`. By the definition of ranks,
this holds if and only if some pair `{h,[w]}` carries at least `ι` edges, that is,
`max_h m_κ(h,w) ≥ ι`."

The second inequality is the proved Lib lemma `EG.HB.Run.mult_le_mu` (an s2 fact, unconditional).
-/

public section

namespace EG

open EG.Quot Finset

namespace Quot.Rules

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

/-- [s7:lemMULT] first inequality, for every vertex `w` (its pool round `r(w)`). -/
theorem mHub_le_multAt (hI : I.Valid) (ξ : Xi I.G I.M) (κ : ℕ) (h w : V) :
    R.mHub ξ κ h w ≤ I.multAt (I.poolRound w) w := by
  unfold Rules.mHub RoundInput.multAt
  refine Finset.card_le_card_of_injOn (fun it => I.cls it.2) ?_ ?_
  · intro it hit
    rw [Finset.mem_coe, Finset.mem_filter] at hit
    obtain ⟨hc, -, -, hw⟩ := hit
    have hu := RoundInput.hubItems_port ((Rules.mem_colouredHub).1 hc).1
    have hcand := Rules.mem_cand (Rules.junction_mem_cand hw)
    have hanc := hI.cls_anc _ hu
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hanc, hcand.2.1.symm, (hI.ljv_in _ hanc _ hcand.2.2).2 w (Sym2.mem_mk_right _ _)⟩
  · intro it hit it' hit' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hit hit'
    have hH := ((Rules.mem_colouredHub).1 hit.1).1
    have hH' := ((Rules.mem_colouredHub).1 hit'.1).1
    have hu := RoundInput.hubItems_port hH
    have hu' := RoundInput.hubItems_port hH'
    have hJ := hI.J1 h (I.cls it.2)
    have hmem : ∀ x ∈ R.colouredHub ξ.1, x.1 = h → I.cls x.2 = I.cls it.2 →
        s(x.1, x.2) ∈ I.Jhub.filter (fun e => ∃ u ∈ I.ports, e = s(h, u) ∧ I.cls u = I.cls it.2)
        := by
      intro x hx hxh hxc
      have hxH := ((Rules.mem_colouredHub).1 hx).1
      rw [Finset.mem_filter]
      exact ⟨RoundInput.hubItems_Jhub hxH, x.2, RoundInput.hubItems_port hxH, by rw [hxh], hxc⟩
    have e := Finset.card_le_one.1 hJ _ (hmem it hit.1 hit.2.1 rfl) _
      (hmem it' hit'.1 hit'.2.1 heq.symm)
    exact RoundInput.hubItems_edge_inj hH hH' hI e

/-! ### Sub-layer counts -/

/-- Membership in `subLayerRanks`: the copy `(t ι, x)` is a vertex of `Q` (for tag families whose
rank component is `ι`). -/
theorem mem_subLayerRanks {Q : FGraph (QVert V)} {t : ℕ → QTag} (ht : ∀ ι, (t ι).2.2.1 = ι)
    {x : V} {ι : ℕ} : ι ∈ EG.Spec.subLayerRanks Q t x ↔ (t ι, x) ∈ Q.verts := by
  unfold EG.Spec.subLayerRanks
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Finset.mem_filter] at hq
    obtain ⟨hq, h1, h2⟩ := hq
    have : q = (t q.1.2.2.1, x) := Prod.ext h1 h2
    rw [← this]; exact hq
  · intro h
    exact ⟨(t ι, x), Finset.mem_filter.2 ⟨h, by rw [ht], rfl⟩, ht ι⟩

/-- A vertex of `Q_l` is an end of the `Q`-edge of a layer edge, in the sub-layer of its rank. -/
theorem mem_Q_verts {ξ : Xi I.G I.M} {x : QVert V} :
    x ∈ (R.Q ξ).verts ↔ ∃ e ∈ R.layerEdges ξ, ∃ q, R.qEdge ξ (R.rank ξ e) e = some q ∧ x ∈ q := by
  rw [R.Q_verts, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨e, he, hqe⟩ := (R.mem_qEdges).1 hq
    exact ⟨e, he, q, hqe, Sym2.mem_toFinset.1 hx⟩
  · rintro ⟨e, he, q, hqe, hx⟩
    exact ⟨q, (R.mem_qEdges).2 ⟨e, he, hqe⟩, Sym2.mem_toFinset.2 hx⟩

/-- The ranks of a class (same rank-`0` `Q`-edge `c`) are exactly `1, …, n`, `n` its size. -/
theorem mem_Icc_class (hR : R.Valid) (ξ : Xi I.G I.M) (c : Option (Sym2 (QVert V))) (ι : ℕ) :
    ι ∈ Icc 1 (open Classical in ((R.layerEdges ξ).filter (fun e => R.qEdge ξ 0 e = c)).card) ↔
      ∃ e ∈ R.layerEdges ξ, R.qEdge ξ 0 e = c ∧ R.rank ξ e = ι := by
  have himg := @image_rankIn_eq_Icc _ _ _ decEqOptQEdge _ (hR.rankOrder ξ).1 (R.qEdge ξ 0) c
  have hlen : (@List.filter _ (fun x => @decide (R.qEdge ξ 0 x = c) (decEqOptQEdge _ _))
      (R.rankOrder ξ)).length =
      (open Classical in ((R.layerEdges ξ).filter (fun e => R.qEdge ξ 0 e = c))).card := by
    rw [← List.toFinset_card_of_nodup ((hR.rankOrder ξ).1.filter _), List.toFinset_filter,
      (hR.rankOrder ξ).2]
    congr 1
    classical
    exact Finset.filter_congr (fun x _ => by simp)
  rw [← hlen, ← himg, Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [List.mem_toFinset, List.mem_filter] at he
    refine ⟨e, ?_, by simpa using he.2, (rank_eq_rankIn ξ e).symm⟩
    rw [← (hR.rankOrder ξ).2]; exact List.mem_toFinset.2 he.1
  · rintro ⟨e, he, hc, rfl⟩
    refine ⟨e, ?_, (rank_eq_rankIn ξ e).symm⟩
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨?_, by simpa using hc⟩
    rw [← List.mem_toFinset, (hR.rankOrder ξ).2]; exact he

omit [DecidableEq V] in
theorem mem_Icc_sup {s : Finset V} {f : V → ℕ} {ι : ℕ} :
    ι ∈ Icc 1 (s.sup f) ↔ ∃ h ∈ s, ι ∈ Icc 1 (f h) := by
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have : (⊥ : ℕ) < ι := by simp; omega
    obtain ⟨h, hs, hh⟩ := (Finset.le_sup_iff this).1 h2
    exact ⟨h, hs, h1, hh⟩
  · rintro ⟨h, hs, h1, h2⟩
    exact ⟨h1, h2.trans (Finset.le_sup hs)⟩

/-- The HUB class of `(h, w)` in colour `κ` has `m_κ(h,w)` members. -/
theorem card_hub_class (ξ : Xi I.G I.M) (κ : ℕ) (h w : V) :
    (open Classical in ((R.layerEdges ξ).filter (fun e => R.qEdge ξ 0 e =
      some s((hubTag κ 0 true, h), (hubTag κ 0 false, w))))).card = R.mHub ξ κ h w := by
  classical
  unfold Rules.mHub
  rw [← Finset.card_image_of_injective ((R.colouredHub ξ.1).filter _)
    (Sum.inr_injective (α := ParObj V))]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_image, Rules.mem_layerEdges]
  constructor
  · rintro ⟨⟨o, -, rfl⟩ | ⟨it, hit, rfl⟩, hq⟩
    · obtain ⟨κ', w₁, w₂, -, -, -, -, hq'⟩ := Rules.qEdge_par_iff.1 hq
      exfalso
      have := Sym2.mem_mk_left (hubTag κ 0 true, h) (hubTag κ 0 false, w)
      rw [hq'] at this
      rcases Sym2.mem_iff.1 this with h1 | h1 <;> simp [hubTag, parTag] at h1
    · obtain ⟨κ', w', h1, h2, hq'⟩ := Rules.qEdge_hub_iff.1 hq
      rcases Sym2.eq_iff.1 hq' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp only [hubTag, Prod.mk.injEq] at e1 e2
        obtain ⟨⟨-, rfl, -, -⟩, rfl⟩ := e1
        obtain ⟨-, rfl⟩ := e2
        exact ⟨it, ⟨hit, rfl, h1, h2⟩, rfl⟩
      · simp [hubTag] at e1
  · rintro ⟨it, ⟨hit, rfl, h1, h2⟩, rfl⟩
    refine ⟨Or.inr ⟨it, hit, rfl⟩, ?_⟩
    exact Rules.qEdge_hub_iff.2 ⟨κ, w, h1, h2, rfl⟩

/-- The PAR class of `{w, w'}` in colour `κ` has `m_κ(w,w')` members (`w ≠ w'`). -/
theorem card_par_class (ξ : Xi I.G I.M) (κ : ℕ) {w w' : V} (hne : w ≠ w') :
    (open Classical in ((R.layerEdges ξ).filter (fun e => R.qEdge ξ 0 e =
      some s((parTag κ 0, w), (parTag κ 0, w'))))).card = R.mPar ξ κ w w' := by
  classical
  unfold Rules.mPar
  rw [← Finset.card_image_of_injective ((R.unpaidPar ξ).filter _)
    (Sum.inl_injective (β := V × V))]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_image, Rules.mem_layerEdges]
  constructor
  · rintro ⟨⟨o, ho, rfl⟩ | ⟨it, -, rfl⟩, hq⟩
    · obtain ⟨κ', w₁, w₂, h1, h2, h3, -, hq'⟩ := Rules.qEdge_par_iff.1 hq
      have hκ : κ' = κ := by
        have := Sym2.mem_mk_left (parTag κ 0, w) (parTag κ 0, w')
        rw [hq'] at this
        rcases Sym2.mem_iff.1 this with h1 | h1 <;> simp [parTag] at h1 <;> exact h1.1.symm
      subst hκ
      refine ⟨o, ⟨ho, h1, w₁, w₂, h2, h3, ?_⟩, rfl⟩
      rcases Sym2.eq_iff.1 hq' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp only [Prod.mk.injEq] at e1 e2
        rw [e1.2, e2.2]
      · simp only [Prod.mk.injEq] at e1 e2
        rw [e1.2, e2.2, Sym2.eq_swap]
    · obtain ⟨κ', w'', -, -, hq'⟩ := Rules.qEdge_hub_iff.1 hq
      exfalso
      have := Sym2.mem_mk_left (parTag κ 0, w) (parTag κ 0, w')
      rw [hq'] at this
      rcases Sym2.mem_iff.1 this with h1 | h1 <;> simp [hubTag, parTag] at h1
  · rintro ⟨o, ⟨ho, h1, w₁, w₂, h2, h3, h4⟩, rfl⟩
    refine ⟨Or.inl ⟨o, ho, rfl⟩, ?_⟩
    have hne' : w₁ ≠ w₂ := by
      intro e; subst e
      rcases Sym2.eq_iff.1 h4 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hne (e1.symm.trans e2)
      · exact hne (e2.symm.trans e1)
    refine Rules.qEdge_par_iff.2 ⟨κ, w₁, w₂, h1, h2, h3, hne', ?_⟩
    rcases Sym2.eq_iff.1 h4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

end Quot.Rules

open Quot.Rules

/-- [s7:lemMULT] (first inequality, round level) "Let `3 ≤ l ≤ R`, `κ ∈ [4M_l]`, let `h` be a hub
and let `w ∈ Pool_{l,r}`. Then `m_κ(h,w) ≤ mult_r(w)`." -/
theorem mult : EG.Spec.MultStatement := by
  intro V _ I hI R _ ξ κ h w r _ _ _ hr
  rw [← hr]
  exact mHub_le_multAt hI ξ κ h w

/-- [s7:lemMULT] (second statement) "the number of sub-layers `B^{H,(ι)}_κ` (`ι ≥ 1`) in which
`[w]` is not isolated equals `max_h m_κ(h,w)`, and the number of those in which `h` is not isolated
equals `max_w m_κ(h,w)`." -/
theorem multSublayer : EG.Spec.MultSublayerStatement := by
  intro V _ I hI R hR ξ κ _
  classical
  refine ⟨fun w _ => ?_, fun h _ => ?_⟩
  · -- junction copies `[w]`
    suffices hs : EG.Spec.subLayerRanks (R.Q ξ) (fun ι => hubTag κ ι false) w =
        Icc 1 (I.hubs.sup (fun h => R.mHub ξ κ h w)) by
      rw [hs, Nat.card_Icc, Nat.add_sub_cancel]
    ext ι
    rw [mem_subLayerRanks (fun _ => rfl), mem_Icc_sup, mem_Q_verts]
    constructor
    · rintro ⟨e, he, q, hq, hx⟩
      rcases e with o | it
      · obtain ⟨κ', w₁, w₂, -, -, -, -, rfl⟩ := Rules.qEdge_par_iff.1 hq
        rcases Sym2.mem_iff.1 hx with h1 | h1 <;> simp [hubTag, parTag] at h1
      · obtain ⟨κ', w', h1, h2, rfl⟩ := Rules.qEdge_hub_iff.1 hq
        rcases Sym2.mem_iff.1 hx with e1 | e1
        · simp [hubTag] at e1
        · simp only [hubTag, Prod.mk.injEq, true_and, and_true] at e1
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e1
          have hit := (Rules.hubColour_eq_some h1).1
          refine ⟨it.1, RoundInput.hubItems_hub ((Rules.mem_colouredHub).1 hit).1, ?_⟩
          rw [← card_hub_class, mem_Icc_class hR]
          exact ⟨_, he, (Rules.qEdge_hub_iff.2 ⟨κ, w, h1, h2, rfl⟩), rfl⟩
    · rintro ⟨h, -, hι⟩
      rw [← card_hub_class, mem_Icc_class hR] at hι
      obtain ⟨e, he, hc, rfl⟩ := hι
      refine ⟨e, he, _, ?_, Sym2.mem_mk_right (hubTag κ (R.rank ξ e) true, h) _⟩
      rw [qEdge_map ξ 0 (R.rank ξ e) e, hc]
      simp only [Option.map_some, Sym2.map_mk]; rfl
  · -- hub copies `h`
    suffices hs : EG.Spec.subLayerRanks (R.Q ξ) (fun ι => hubTag κ ι true) h =
        Icc 1 (I.pool.sup (fun w => R.mHub ξ κ h w)) by
      rw [hs, Nat.card_Icc, Nat.add_sub_cancel]
    ext ι
    rw [mem_subLayerRanks (fun _ => rfl), mem_Icc_sup, mem_Q_verts]
    constructor
    · rintro ⟨e, he, q, hq, hx⟩
      rcases e with o | it
      · obtain ⟨κ', w₁, w₂, -, -, -, -, rfl⟩ := Rules.qEdge_par_iff.1 hq
        rcases Sym2.mem_iff.1 hx with h1 | h1 <;> simp [hubTag, parTag] at h1
      · obtain ⟨κ', w', h1, h2, rfl⟩ := Rules.qEdge_hub_iff.1 hq
        rcases Sym2.mem_iff.1 hx with e1 | e1
        · simp only [hubTag, Prod.mk.injEq, true_and, and_true] at e1
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e1
          refine ⟨w', Rules.junction_pool h2, ?_⟩
          rw [← card_hub_class, mem_Icc_class hR]
          exact ⟨_, he, (Rules.qEdge_hub_iff.2 ⟨κ, w', h1, h2, rfl⟩), rfl⟩
        · simp [hubTag] at e1
    · rintro ⟨w, -, hι⟩
      rw [← card_hub_class, mem_Icc_class hR] at hι
      obtain ⟨e, he, hc, rfl⟩ := hι
      refine ⟨e, he, _, ?_, Sym2.mem_mk_left _ (hubTag κ (R.rank ξ e) false, w)⟩
      rw [qEdge_map ξ 0 (R.rank ξ e) e, hc]
      simp only [Option.map_some, Sym2.map_mk]; rfl

/-- [s7] (PAR-MULT identity, preamble of "Quotient size and payments") "For a PAR colour `κ` and
`w ≠ w'` in `Pool_l`, let `m_κ(w,w')` be the number of edges `[w][w']` of `B^P_κ`. As in Lemma
s7:lemMULT, `[w]` is not isolated in exactly `max_{w'} m_κ(w,w')` of the sub-layers
`B^{P,(ι)}_κ`." -/
theorem parMultSublayer : EG.Spec.ParMultSublayerStatement := by
  intro V _ I hI R hR ξ κ _ w _
  classical
  suffices hs : EG.Spec.subLayerRanks (R.Q ξ) (fun ι => parTag κ ι) w =
      Icc 1 ((I.pool.erase w).sup (fun w' => R.mPar ξ κ w w')) by
    rw [hs, Nat.card_Icc, Nat.add_sub_cancel]
  ext ι
  rw [mem_subLayerRanks (fun _ => rfl), mem_Icc_sup, mem_Q_verts]
  constructor
  · rintro ⟨e, he, q, hq, hx⟩
    rcases e with o | it
    · obtain ⟨κ', w₁, w₂, h1, h2, h3, hne, rfl⟩ := Rules.qEdge_par_iff.1 hq
      have hq0 : R.qEdge ξ 0 (.inl o) = some s((parTag κ' 0, w₁), (parTag κ' 0, w₂)) :=
        Rules.qEdge_par_iff.2 ⟨κ', w₁, w₂, h1, h2, h3, hne, rfl⟩
      rcases Sym2.mem_iff.1 hx with e1 | e1
      · simp only [parTag, Prod.mk.injEq, true_and, and_true] at e1
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e1
        refine ⟨w₂, Finset.mem_erase.2 ⟨Ne.symm hne, Rules.junction_pool h3⟩, ?_⟩
        rw [← card_par_class ξ κ hne, mem_Icc_class hR]
        exact ⟨_, he, hq0, rfl⟩
      · simp only [parTag, Prod.mk.injEq, true_and, and_true] at e1
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e1
        refine ⟨w₁, Finset.mem_erase.2 ⟨hne, Rules.junction_pool h2⟩, ?_⟩
        rw [← card_par_class ξ κ (Ne.symm hne), mem_Icc_class hR]
        exact ⟨_, he, by rw [hq0, Sym2.eq_swap], rfl⟩
    · obtain ⟨κ', w', -, -, rfl⟩ := Rules.qEdge_hub_iff.1 hq
      rcases Sym2.mem_iff.1 hx with h1 | h1 <;> simp [hubTag, parTag] at h1
  · rintro ⟨w', hw', hι⟩
    have hne : w ≠ w' := Ne.symm (Finset.mem_erase.1 hw').1
    rw [← card_par_class ξ κ hne, mem_Icc_class hR] at hι
    obtain ⟨e, he, hc, rfl⟩ := hι
    refine ⟨e, he, _, ?_, Sym2.mem_mk_left _ (parTag κ (R.rank ξ e), w')⟩
    rw [qEdge_map ξ 0 (R.rank ξ e) e, hc]
    simp only [Option.map_some, Sym2.map_mk]; rfl

/-- [s7:lemMULT] (both inequalities, run level) "Let `3 ≤ l ≤ R`, `κ ∈ [4M_l]`, let `h` be a hub
and let `w ∈ Pool_{l,r}`. Then `m_κ(h,w) ≤ mult_r(w) ≤ μ_r(w)`." (Conditional on
`(RoundInput.ofPast …).Valid`, OBL-P1-1.) -/
theorem multRun : EG.Spec.MultRunStatement := by
  intro V _ run G δ S π l J _ _ hI R _ ξ κ h w r _ _ hw
  refine ⟨?_, HB.Run.mult_le_mu run G r w⟩
  by_cases hp : w ∈ (RoundInput.ofPast run G δ S π l J).pool
  · have hr : (RoundInput.ofPast run G δ S π l J).poolRound w = r := Stage1.poolRound_eq hw
    have := mHub_le_multAt (R := R) hI ξ κ h w
    rw [hr, ofPast_multAt] at this
    exact this
  · have : R.mHub ξ κ h w = 0 := by
      unfold Rules.mHub
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro it - ⟨-, -, hj⟩
      exact hp (Rules.junction_pool hj)
    rw [this]; exact Nat.zero_le _

end EG
