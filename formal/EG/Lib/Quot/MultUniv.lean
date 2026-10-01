module

public import EG.Spec.Quot.MULT
public import EG.Proof.Quot.MULT

/-!
# Lemma MULT, sub-layer counts, on vertex types of every universe (manuscript s7:lemMULT)

`EG.Spec.MultSublayerStatement` and `EG.Spec.ParMultSublayerStatement` are stated on `Type`; the
s7b consumers (s7:lemUHsplit (ii), through s7:lemCC (iii) and s7:lemUltra (iii)) quantify over
`V : Type u`. These are the same statements for `V : Type u`, with the proofs of
`EG.multSublayer` and `EG.parMultSublayer` (`EG/Proof/Quot/MULT.lean`, unit P1) verbatim; the
helper lemmas used there are universe-polymorphic.
-/

public section

namespace EG

open EG.Quot EG.Quot.Rules EG.Spec Finset

universe u

/-- [s7:lemMULT] (second statement), for `V : Type u` (`EG.Spec.MultSublayerStatement`). -/
theorem multSublayer_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (κ : ℕ), κ < 4 * I.M →
      (∀ w ∈ I.pool, (subLayerRanks (R.Q ξ) (fun ι => hubTag κ ι false) w).card =
          I.hubs.sup (fun h => R.mHub ξ κ h w)) ∧
      (∀ h ∈ I.hubs, (subLayerRanks (R.Q ξ) (fun ι => hubTag κ ι true) h).card =
          I.pool.sup (fun w => R.mHub ξ κ h w)) := by
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

/-- [s7] (PAR-MULT identity, preamble of "Quotient size and payments"; for `V : Type u`) "For a PAR colour `κ` and
`w ≠ w'` in `Pool_l`, let `m_κ(w,w')` be the number of edges `[w][w']` of `B^P_κ`. As in Lemma
s7:lemMULT, `[w]` is not isolated in exactly `max_{w'} m_κ(w,w')` of the sub-layers
`B^{P,(ι)}_κ`." -/
theorem parMultSublayer_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (ξ : Xi I.G I.M) (κ : ℕ), κ < 3 * I.M → ∀ w ∈ I.pool,
      (subLayerRanks (R.Q ξ) (fun ι => parTag κ ι) w).card =
        (I.pool.erase w).sup (fun w' => R.mPar ξ κ w w') := by
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

end EG
