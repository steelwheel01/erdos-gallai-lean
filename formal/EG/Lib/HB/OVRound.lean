module

public import EG.Lib.HB.OVPotential
public import EG.Lib.HB.Run

/-!
# Helpers for Proposition s2:propOV (manuscript s2:propOV)

Helper lemmas for `EG.Todo.OVRound` (unit P3-s2):
* `STree.dupGe_pos_of_two_leaves`: the LCA step of (K3): "let `u ∈ Dup*_r` lie in a pre-part `Y`.
  Then `u` lies in another leaf `Leaf ≠ Y` … Let `ν` be the lowest common ancestor of the leaves
  `Y` and `Leaf`; they lie below different children of `ν`, and `u` lies in both (vertex sets
  shrink downwards), so `u ∈ N''_ν` …; and `|ν| ≥ |Y^0|`";
* `sum_card_inter_eq`: the double count `Σ_a |Z_a ∩ D| = Σ_{w ∈ D} #{a : w ∈ Z_a}`.
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

namespace STree

theorem dupGe_pos_of_two_leaves (M : ℝ) (v : V) :
    ∀ (t : STree V) (K : FGraph V) (L0 L1 : Addr), L0 ∈ t.leafAddrs → L1 ∈ t.leafAddrs →
      L0 ≠ L1 → v ∈ (t.graphAtD K L0).verts → v ∈ (t.graphAtD K L1).verts →
      M ≤ ((t.graphAtD K L0).card : ℝ) → 1 ≤ t.dupGe K M v := by
  intro t
  induction t with
  | nil =>
    intro K L0 L1 h0 h1 hne _ _ _
    simp only [leafAddrs_nil, Finset.mem_singleton] at h0 h1
    exact absurd (h0.trans h1.symm) hne
  | node p l r ihl ihr =>
    intro K L0 L1 h0 h1 hne hv0 hv1 hM
    have hdup : (STree.node p l r).dupGe K M v =
        (if M ≤ (K.card : ℝ) ∧ v ∈ p.2 then 1 else 0) +
          (l.dupGe (splitFst K p.1 p.2) M v + r.dupGe (splitSnd K p.1 p.2) M v) :=
      card_filter_internalAddrs_node p l r _
    rw [hdup]
    rcases L0 with _ | ⟨b0, a0⟩
    · exact absurd h0 (mem_leafAddrs_node_nil p l r)
    rcases L1 with _ | ⟨b1, a1⟩
    · exact absurd h1 (mem_leafAddrs_node_nil p l r)
    rw [mem_leafAddrs_node_cons] at h0 h1
    cases b0 <;> cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
      have := ihl (splitFst K p.1 p.2) a0 a1 h0 h1 (fun h => hne (by rw [h])) hv0 hv1 hM
      omega
    · -- `false` and `true`: the root is the lowest common ancestor
      simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
      have hf : v ∈ (splitFst K p.1 p.2).verts := graphAtD_verts_subset l _ a0 hv0
      have hs : v ∈ (splitSnd K p.1 p.2).verts := graphAtD_verts_subset r _ a1 hv1
      have hN : v ∈ p.2 := mem_right_of_mem_both hf hs
      have hc1 : ((l.graphAtD (splitFst K p.1 p.2) a0).card : ℝ) ≤ (K.card : ℝ) := by
        have h1 : (l.graphAtD (splitFst K p.1 p.2) a0).card ≤ (splitFst K p.1 p.2).card :=
          Finset.card_le_card (graphAtD_verts_subset l _ a0)
        have h2 := splitFst_card_le K p.1 p.2
        exact_mod_cast h1.trans h2
      have hK : M ≤ (K.card : ℝ) := le_trans hM hc1
      rw [if_pos ⟨hK, hN⟩]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
      have hf : v ∈ (splitFst K p.1 p.2).verts := graphAtD_verts_subset l _ a1 hv1
      have hs : v ∈ (splitSnd K p.1 p.2).verts := graphAtD_verts_subset r _ a0 hv0
      have hN : v ∈ p.2 := mem_right_of_mem_both hf hs
      have hc1 : ((r.graphAtD (splitSnd K p.1 p.2) a0).card : ℝ) ≤ (K.card : ℝ) := by
        have h1 : (r.graphAtD (splitSnd K p.1 p.2) a0).card ≤ (splitSnd K p.1 p.2).card :=
          Finset.card_le_card (graphAtD_verts_subset r _ a0)
        have h2 := splitSnd_card_le K p.1 p.2
        exact_mod_cast h1.trans h2
      have hK : M ≤ (K.card : ℝ) := le_trans hM hc1
      rw [if_pos ⟨hK, hN⟩]; omega
    · simp only [↓reduceIte] at h0 h1
      have := ihr (splitSnd K p.1 p.2) a0 a1 h0 h1 (fun h => hne (by rw [h])) hv0 hv1 hM
      omega

end STree

/-- Double count: `Σ_{a ∈ A} |Z_a ∩ D| = Σ_{w ∈ D} #{a ∈ A : w ∈ Z_a}`. -/
theorem sum_card_inter_eq {α : Type*} (A : Finset α) (Z : α → Finset V) (D : Finset V) :
    ∑ a ∈ A, (Z a ∩ D).card = ∑ w ∈ D, (A.filter (fun a => w ∈ Z a)).card := by
  have h1 : ∀ a ∈ A, (Z a ∩ D).card = ∑ w ∈ D, if w ∈ Z a then 1 else 0 := by
    intro a _
    rw [Finset.sum_boole, Finset.inter_comm, ← Finset.filter_mem_eq_inter]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_boole]; simp

/-! ### Round-level counts (K1), (K2), (K3), (F11) -/

namespace Round

variable (H : FGraph V) (c : RoundChoice V)

theorem X0_card_eq (a : Addr) : (X0 H c a).card = (Z0 H c a).card := rfl

theorem sum_Z0_le_leafMass :
    ∑ a ∈ prePartAddrs H c, (Z0 H c a).card ≤ (twoLevel H c).leafMass (graph' H c) := by
  unfold STree.leafMass
  exact Finset.sum_le_sum_of_subset (prePartAddrs_subset_leafAddrs H c)

theorem card_mul_P_le :
    (prePartAddrs H c).card * POf (d H) ≤ ∑ a ∈ prePartAddrs H c, (Z0 H c a).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  exact Finset.sum_le_sum (fun a ha => (Finset.mem_filter.1 ha).2)

/-- "`μ_r(w) ≤ 1 + dup_{≥P_r}(w)`" (Lemma OV (b) with `M = P_r`; the pre-parts are the leaves
of size at least `P_r`). -/
theorem mu_le_one_add_dupGe (w : V) :
    mu H c w ≤ 1 + (twoLevel H c).dupGe (graph' H c) (POf (d H) : ℝ) w := by
  refine le_trans (le_of_eq ?_) (STree.ov_b (POf (d H) : ℝ) (twoLevel H c) (graph' H c) w)
  unfold mu prePartAddrs
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro a _
  change POf (d H) ≤ (X0 H c a).card ∧ w ∈ (X0 H c a).verts ↔ _
  rw [← Nat.cast_le (α := ℝ)]
  rfl

theorem sum_mu_sub_one_le (hv : Valid H c) :
    ∑ w ∈ H.verts, (mu H c w - 1) ≤ (twoLevel H c).DeltaGe (graph' H c) (POf (d H) : ℝ) := by
  rw [← STree.sum_dupGe _ _ (wf_twoLevel H c hv)]
  apply Finset.sum_le_sum
  intro w _
  have := mu_le_one_add_dupGe H c w
  omega

theorem D_subset_verts : D H c ⊆ H.verts := by
  intro v hv
  unfold D at hv
  rw [Finset.mem_filter, Finset.mem_biUnion] at hv
  obtain ⟨a, _, hva⟩ := hv.1
  exact Z0_subset_verts H c a hva

theorem card_D_le : (D H c).card ≤ ∑ w ∈ H.verts, (mu H c w - 1) := by
  calc (D H c).card = ∑ _w ∈ D H c, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ w ∈ D H c, (mu H c w - 1) := by
        apply Finset.sum_le_sum
        intro w hw
        have := (mem_D H c).1 hw
        omega
    _ ≤ ∑ w ∈ H.verts, (mu H c w - 1) :=
        Finset.sum_le_sum_of_subset (D_subset_verts H c)

theorem sum_inter_D_le :
    ∑ a ∈ prePartAddrs H c, (Z0 H c a ∩ D H c).card ≤ 2 * ∑ w ∈ H.verts, (mu H c w - 1) := by
  rw [sum_card_inter_eq]
  calc ∑ w ∈ D H c, ((prePartAddrs H c).filter (fun a => w ∈ Z0 H c a)).card
      = ∑ w ∈ D H c, mu H c w := rfl
    _ ≤ ∑ w ∈ D H c, 2 * (mu H c w - 1) := by
        apply Finset.sum_le_sum
        intro w hw
        have := (mem_D H c).1 hw
        omega
    _ = 2 * ∑ w ∈ D H c, (mu H c w - 1) := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ w ∈ H.verts, (mu H c w - 1) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (D_subset_verts H c))

open Classical in
theorem sum_failL1_le :
    ∑ a ∈ (prePartAddrs H c).filter (fun a => ¬ isL1 H c a), (Z0 H c a).card ≤
      2 * ∑ a ∈ prePartAddrs H c, (Z0 H c a ∩ D H c).card := by
  calc ∑ a ∈ (prePartAddrs H c).filter (fun a => ¬ isL1 H c a), (Z0 H c a).card
      ≤ ∑ a ∈ (prePartAddrs H c).filter (fun a => ¬ isL1 H c a), 2 * (Z0 H c a ∩ D H c).card := by
        apply Finset.sum_le_sum
        intro a ha
        have hL := (Finset.mem_filter.1 ha).2
        unfold isL1 at hL
        have hS : (guests H c a).card ≤ (Z0 H c a ∩ D H c).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        omega
    _ = 2 * ∑ a ∈ (prePartAddrs H c).filter (fun a => ¬ isL1 H c a), (Z0 H c a ∩ D H c).card := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ a ∈ prePartAddrs H c, (Z0 H c a ∩ D H c).card :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

theorem sum_inter_DupStar_le (hv : Valid H c) :
    ∑ a ∈ prePartAddrs H c, (Z0 H c a ∩ DupStar H c).card ≤
      2 * (twoLevel H c).DeltaGe (graph' H c) (POf (d H) : ℝ) := by
  rw [sum_card_inter_eq, ← STree.sum_dupGe _ _ (wf_twoLevel H c hv), Finset.mul_sum]
  calc ∑ w ∈ DupStar H c, ((prePartAddrs H c).filter (fun a => w ∈ Z0 H c a)).card
      ≤ ∑ w ∈ DupStar H c, 2 * (twoLevel H c).dupGe (graph' H c) (POf (d H) : ℝ) w := by
        apply Finset.sum_le_sum
        intro u hu
        change mu H c u ≤ _
        have h1 := mu_le_one_add_dupGe H c u
        rcases Nat.eq_zero_or_pos (mu H c u) with h0 | h0
        · omega
        -- `u` lies in a pre-part `Y` and in a second leaf
        obtain ⟨Y, hY⟩ := Finset.card_pos.1 h0
        rw [Finset.mem_filter] at hY
        have hYleaf := prePartAddrs_subset_leafAddrs H c hY.1
        obtain ⟨L1, hL1, L2, hL2, hne, hu1, hu2⟩ := STree.mem_dup_iff_exists.1 hu
        have hYP : ((POf (d H) : ℕ) : ℝ) ≤ ((X0 H c Y).card : ℝ) := by
          exact_mod_cast (Finset.mem_filter.1 hY.1).2
        have hpos : 1 ≤ (twoLevel H c).dupGe (graph' H c) (POf (d H) : ℝ) u := by
          by_cases h1Y : L1 = Y
          · subst h1Y
            exact STree.dupGe_pos_of_two_leaves _ u _ _ L1 L2 hL1 hL2 hne hu1 hu2 hYP
          · exact STree.dupGe_pos_of_two_leaves _ u _ _ Y L1 hYleaf hL1 (Ne.symm h1Y) hY.2 hu1
              hYP
        omega
    _ ≤ ∑ w ∈ H.verts, 2 * (twoLevel H c).dupGe (graph' H c) (POf (d H) : ℝ) w := by
        apply Finset.sum_le_sum_of_subset
        exact (STree.dup_subset _ _).trans (by rfl)

theorem sum_mult_eq :
    ∑ w ∈ H.verts, ((prePartAddrs H c).filter (fun a => w ∈ partVerts H c a)).card =
      ∑ a ∈ prePartAddrs H c, (partVerts H c a).card := by
  have h := sum_card_inter_eq (prePartAddrs H c) (partVerts H c) H.verts
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.inter_eq_left.2 ((partVerts_subset H c a).trans (Z0_subset_verts H c a))]

theorem sum_partVerts_le :
    ∑ a ∈ prePartAddrs H c, (partVerts H c a).card ≤ ∑ a ∈ prePartAddrs H c, (Z0 H c a).card :=
  Finset.sum_le_sum (fun a _ => Finset.card_le_card (partVerts_subset H c a))

theorem mult_le_mu (w : V) :
    ((prePartAddrs H c).filter (fun a => w ∈ partVerts H c a)).card ≤ mu H c w := by
  unfold mu
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, partVerts_subset H c a ha.2⟩

end Round

/-! ### Run level -/

namespace Run

variable (run : Run V) (G : FGraph V)

/-- "each ancestor corresponds to a distinct pre-part": the ancestors of round `r` are
`{(r, a) : a a round-`r` pre-part}`. -/
theorem ancestors_filter_eq (r : ℕ) :
    (run.ancestors G).filter (fun Y => Y.1 = r) = (run.prePartAddrs G r).image (fun a => (r, a)) := by
  ext ⟨r', a⟩
  simp only [Finset.mem_filter, mem_ancestors, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨a, h, rfl, rfl⟩
  · rintro ⟨b, hb, rfl, rfl⟩; exact ⟨hb, rfl⟩

theorem card_ancestors_filter (r : ℕ) :
    ((run.ancestors G).filter (fun Y => Y.1 = r)).card = (run.prePartAddrs G r).card := by
  rw [ancestors_filter_eq, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]

theorem sum_ancVerts_eq (r : ℕ) :
    ∑ Y ∈ (run.ancestors G).filter (fun Y => Y.1 = r), (run.ancVerts G Y).card =
      ∑ a ∈ run.prePartAddrs G r, (run.partVerts G r a).card := by
  rw [ancestors_filter_eq, Finset.sum_image (fun a _ b _ h => by simpa using h)]
  rfl

theorem mu_of_isRound {r : ℕ} (hr : run.IsRound r) (w : V) :
    run.mu G r w = Round.mu (run.graph G r) (run.choice r) w := if_pos hr

theorem D_of_isRound {r : ℕ} (hr : run.IsRound r) :
    run.D G r = Round.D (run.graph G r) (run.choice r) := if_pos hr

theorem dup_eq {r : ℕ} (hr : run.IsRound r) :
    run.dup G r = ∑ w ∈ (run.graph G r).verts, (Round.mu (run.graph G r) (run.choice r) w - 1) := by
  unfold dup
  rw [graph_verts]
  exact Finset.sum_congr rfl (fun w _ => by rw [mu_of_isRound run G hr])

/-- `ν_l ≤ Σ_{r ≤ l-2} (number of ancestors of round r)`. -/
theorem nuAnc_le_sum (l : ℕ) :
    run.nuAnc G l ≤ ∑ r ∈ (Finset.Icc 1 run.R).filter (fun r => r + 2 ≤ l),
      ((run.ancestors G).filter (fun Y => Y.1 = r)).card := by
  unfold nuAnc
  rw [Finset.card_eq_sum_card_fiberwise (f := fun Y : PartId => Y.1)
    (t := (Finset.Icc 1 run.R).filter (fun r => r + 2 ≤ l))]
  · apply Finset.sum_le_sum
    intro r _
    apply Finset.card_le_card
    intro Y hY
    simp only [Finset.mem_filter] at hY ⊢
    exact ⟨hY.1.1, hY.2⟩
  · intro Y hY
    rw [Finset.mem_coe, Finset.mem_filter] at hY
    rw [Finset.mem_coe, Finset.mem_filter]
    have := isRound_of_mem_parts run G hY.1
    exact ⟨Finset.mem_Icc.2 this, hY.2⟩

end Run

end EG.HB
