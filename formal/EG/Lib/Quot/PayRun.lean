module

public import EG.Lib.Quot.Pay
public import EG.Lib.Quot.OfPastValid
public import EG.Lib.Chain.JSet

/-!
# Payments of the round step (manuscript s7:lemPay), (a2) and (a3) on the past of a run

For the past `I = RoundInput.ofPast run G δ S π l J` of a round with `JPlusProps` (Lemma J⁺):

* (a2) `card_paidPool_le`: "The number of items with a vertex in `Pool_l` is at most
  `Σ_{v∈Pool_l} ω_l(v)`" ("If `v ∈ D_l`, then `v` is a hub and not a port or a fresh centre, by
  (J3). The items with vertex `v` are therefore `J^hub` items `(v,u)` … By (J1) there is at most
  one such item per class `Y`. Each such class has `d_{Y,l}(v) ≥ 1` … So there are at most
  `c^agg_{v,l}` items with vertex `v`. If `v ∉ D_l`, then `v` carries at most `M_l − 1 ≤ M_l`
  J-edges by (J2).");
* (a3) `card_paidJVBad_le`: "A port carries at most `M_l − 1` items by (J2)";
* (b) `card_freshCentres_le`: `|⋃_Z F_Z| ≤ Σ_Z |F_Z|`.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain Finset

universe u

variable {V : Type u} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {J : Finset (Sym2 V)}

open Classical in
/-- The items with a vertex `v ∈ D_l` are `J^hub` edges at the hub `v`. -/
theorem items_at_hub_subset (hJ : JPlusProps run G δ S l J) {v : V} (hv : v ∈ run.D G l) :
    (RoundInput.ofPast run G δ S π l J).items.filter (fun e => v ∈ e) ⊆
      (cAggClasses run G δ v l).biUnion (fun Y => J.filter (IsJhubEdge run G δ S l v Y)) := by
  classical
  intro e he
  obtain ⟨he, hve⟩ := mem_filter.1 he
  obtain ⟨heJ', hnl⟩ := (RoundInput.mem_items _).1 he
  have heJ : e ∈ J := by rwa [ofPast_J run G δ S π l hJ] at heJ'
  have hvq : ∀ a ∈ run.Std G l, v ∉ qs run G δ S l a := fun a ha hq =>
    Finset.disjoint_left.1 (disjoint_D_qsRound run G δ S l) hv
      ((mem_qsRound run G δ S).2 ⟨a, ha, hq⟩)
  rcases hJ.types e heJ with hp | ⟨h, Y, hh⟩ | ⟨x, Y, hx⟩ | ⟨w, Y, hw⟩
  · obtain ⟨a, ha, -, u, u', rfl, hu, hu', -⟩ := hp
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · exact absurd hu (hvq a ha)
    · exact absurd hu' (hvq a ha)
  · have hY := hh.mem_cAggClasses
    obtain ⟨a, ha, hea, u, rfl, hha, hu, hYu⟩ := hh
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · exact mem_biUnion.2 ⟨Y, hY, mem_filter.2 ⟨heJ, a, ha, hea, u, rfl, hha, hu, hYu⟩⟩
    · exact absurd hu (hvq a ha)
  · obtain ⟨a, ha, -, u, rfl, hxa, hu, -⟩ := hx
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · exact absurd ((mem_freshCentres run G).2 ⟨a, ha, hxa⟩)
        (Finset.disjoint_left.1 (disjoint_D_freshCentres run G l) hv)
    · exact absurd hu (hvq a ha)
  · exfalso
    apply hnl
    change e ∈ Chain.Jlost run G δ S l J
    exact mem_filter.2 ⟨heJ, w, Y, hw⟩

/-- [s7:lemPay] (a2) "The number of items with a vertex in `Pool_l` is at most
`Σ_{v∈Pool_l} ω_l(v)`". -/
theorem card_paidPool_le (hJ : JPlusProps run G δ S l J)
    (hI : (RoundInput.ofPast run G δ S π l J).Valid) :
    (RoundInput.ofPast run G δ S π l J).paidPool.card ≤
      ∑ v ∈ Stage1.poolL G π l, poolWeight run G δ l v := by
  classical
  set I := RoundInput.ofPast run G δ S π l J with hIdef
  have hsub : I.paidPool ⊆ I.pool.biUnion (fun v => I.items.filter (fun e => v ∈ e)) := by
    intro e he
    simp only [RoundInput.paidPool, mem_filter] at he
    obtain ⟨he, v, hve, hvp⟩ := he
    exact mem_biUnion.2 ⟨v, hvp, mem_filter.2 ⟨he, hve⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine sum_le_sum fun v _ => ?_
  by_cases hv : v ∈ run.D G l
  · have hw : poolWeight run G δ l v = cAgg run G δ v l := by
      unfold poolWeight; rw [if_pos hv]
    rw [hw]
    refine (card_le_card (items_at_hub_subset (π := π) hJ hv)).trans
      (card_biUnion_le.trans ?_)
    refine (sum_le_sum fun Y _ => hJ.J1hub_all v Y).trans ?_
    rw [sum_const, smul_eq_mul, mul_one]
    rfl
  · have hw : poolWeight run G δ l v = run.M G l := by
      unfold poolWeight; rw [if_neg hv]
    rw [hw]
    have hsub' : I.items.filter (fun e => v ∈ e) ⊆ edgesAt I.J v := by
      intro e he
      obtain ⟨he, hve⟩ := mem_filter.1 he
      exact mem_filter.2 ⟨((RoundInput.mem_items _).1 he).1, hve⟩
    refine (card_le_card hsub').trans ?_
    exact (hI.J2 v hv).trans (Nat.sub_le _ _)

/-- A classed port of round `l` is not a hub. -/
theorem not_mem_D_of_mem_classedPorts {u : V} (hu : u ∈ classedPorts run G l) :
    u ∉ run.D G l := by
  obtain ⟨a, -, hua⟩ := (mem_classedPorts run G).1 hu
  exact ((mem_ports_iff run G).1 (classed_subset_ports run G l a hua)).2

/-- [s7:lemPay] (a3) "The number of items with a JV-bad port end is at most `M_l − 1` times the
number of JV-bad classed ports of round `l`." -/
theorem card_paidJVBad_le (hI : (RoundInput.ofPast run G δ S π l J).Valid) :
    (RoundInput.ofPast run G δ S π l J).paidJVBad.card ≤
      (jvBadPorts run G δ S π l).card * (run.M G l - 1) := by
  classical
  set I := RoundInput.ofPast run G δ S π l J with hIdef
  have hsub : I.paidJVBad ⊆ (jvBadPorts run G δ S π l).biUnion (fun u => edgesAt I.J u) := by
    intro e he
    simp only [RoundInput.paidJVBad, mem_filter] at he
    obtain ⟨he, u, hue, -, hbad⟩ := he
    have hbad' : JVBad run G δ S π l u := hbad
    refine mem_biUnion.2 ⟨u, ?_, ?_⟩
    · unfold jvBadPorts
      exact mem_filter.2 ⟨hbad'.1, hbad'⟩
    · exact mem_filter.2 ⟨((RoundInput.mem_items _).1 he).1, hue⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun u hu => ?_
  have hcp : u ∈ classedPorts run G l := by
    unfold jvBadPorts at hu
    exact (mem_filter.1 hu).1
  exact hI.J2 u (not_mem_D_of_mem_classedPorts hcp)

/-- `|⋃_{Z ∈ Std_l} F_Z| ≤ Σ_{Z ∈ Std_l} |F_Z|`. -/
theorem card_freshCentres_le :
    (freshCentres run G l).card ≤ ∑ a ∈ run.Std G l, (run.fresh G l a).card := by
  unfold freshCentres
  exact card_biUnion_le

end EG.Quot
