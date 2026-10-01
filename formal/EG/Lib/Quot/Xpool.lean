module

public import EG.Lib.Quot.Xprime
public import EG.Lib.Chain.Design
public import EG.Lib.HB.Run

/-!
# The pooled weights of `X_pool` (manuscript s7:lemEXprime, "Pooled weights")

"`Σ_h c^agg_{h,l} ≤ Σ_{Z∈Std_l} Σ_{u∈Q_Z} deg_{E_l(Z)}(u)`. Every vertex has `E_l(Z)`-degree at
most `M_l − 1` (Lemma s2:lemCap(ii))". The manuscript then bounds `Σ_Z |Z^0| ≤ 1.37n`; here the
classed-port sets `Q_Z` of one round are disjoint (`EG.Chain.classed_disjoint`), so
`Σ_Z |Q_Z| ≤ n` and `Σ_h c^agg_{h,l} ≤ (M_l − 1)n` (the manuscript's `1.37nM_l` is weaker).

* `card_filter_mem_le_degE`: `#{h ∈ S : hu ∈ F} ≤ deg_F(u)`;
* `sum_cAgg_le`: `Σ_{h∈S} c^agg_{h,l} ≤ (M_l − 1) Σ_{Z∈Std_l} |Q_Z|`;
* `sum_card_classed_le`, `classedPorts_subset_verts`: `Σ_Z |Q_Z| ≤ n`;
* `sum_poolWeight_le`: `Σ_{v∈V(G)} ω_l(v) ≤ (M_l − 1)n + M_l n`.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain

variable {V : Type*} [DecidableEq V]

/-- `#{h ∈ S : hu ∈ F} ≤ deg_F(u)` (distinct `h` give distinct edges `hu`). -/
theorem card_filter_mem_le_degE (S : Finset V) (F : Finset (Sym2 V)) (u : V) :
    (S.filter (fun h => s(h, u) ∈ F)).card ≤ degE F u := by
  unfold degE edgesAt
  refine Finset.card_le_card_of_injOn (fun h => s(h, u)) ?_ ?_
  · intro h hh
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hh
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨hh.2, Sym2.mem_mk_right h u⟩
  · intro h _ h' _ e
    simp only at e
    rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact h1.trans h2

variable (run : Run V) (G : FGraph V) (δ : Designation V)

theorem classedPorts_subset_verts (l : ℕ) : classedPorts run G l ⊆ G.verts := by
  intro u hu
  obtain ⟨a, -, hua⟩ := (mem_classedPorts run G).1 hu
  exact Run.Z0_subset_verts run G l a (classed_subset_Z0 run G l a hua)

/-- `Σ_{Z ∈ Std_l} |Q_Z| ≤ n` (the sets `Q_Z` are disjoint subsets of `V(G)`). -/
theorem sum_card_classed_le (l : ℕ) :
    ∑ a ∈ run.Std G l, (run.classed G l a).card ≤ G.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (classedPorts_subset_verts run G l)
  · intro a ha b hb hab
    exact classed_disjoint run G (Std_subset_prePartAddrs run G l ha)
      (Std_subset_prePartAddrs run G l hb) hab

/-- "`Σ_h c^agg_{h,l} ≤ Σ_{Z∈Std_l} Σ_{u∈Q_Z} deg_{E_l(Z)}(u) ≤ (M_l − 1) Σ_Z |Q_Z|`". -/
theorem sum_cAgg_le (l : ℕ) (S : Finset V)
    (hCap : ∀ a ∈ run.Std G l, ∀ v, degE (run.E G l a) v ≤ run.M G l - 1) :
    ∑ h ∈ S, cAgg run G δ h l ≤
      (run.M G l - 1) * ∑ a ∈ run.Std G l, (run.classed G l a).card := by
  classical
  have h1 : ∀ h, cAgg run G δ h l ≤
      ∑ a ∈ run.Std G l, ((run.classed G l a).filter (fun u => s(h, u) ∈ run.E G l a)).card := by
    intro h
    unfold cAgg cAggClasses
    exact Finset.card_image_le.trans Finset.card_biUnion_le
  calc ∑ h ∈ S, cAgg run G δ h l
      ≤ ∑ h ∈ S, ∑ a ∈ run.Std G l,
          ((run.classed G l a).filter (fun u => s(h, u) ∈ run.E G l a)).card :=
        Finset.sum_le_sum fun h _ => h1 h
    _ = ∑ a ∈ run.Std G l, ∑ u ∈ run.classed G l a,
          (S.filter (fun h => s(h, u) ∈ run.E G l a)).card := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ a ∈ run.Std G l, ∑ u ∈ run.classed G l a, (run.M G l - 1) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun u _ =>
          (card_filter_mem_le_degE S (run.E G l a) u).trans (hCap a ha u)
    _ = (run.M G l - 1) * ∑ a ∈ run.Std G l, (run.classed G l a).card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- "`Σ_v ω_l(v) ≤ Σ_{h∈D_l} c^agg_{h,l} + nM_l`", with the bound on the class counts. -/
theorem sum_poolWeight_le (l : ℕ)
    (hCap : ∀ a ∈ run.Std G l, ∀ v, degE (run.E G l a) v ≤ run.M G l - 1) :
    ∑ v ∈ G.verts, poolWeight run G δ l v ≤ (run.M G l - 1) * G.card + run.M G l * G.card := by
  classical
  have h1 : ∀ v ∈ G.verts, poolWeight run G δ l v ≤ cAgg run G δ v l + run.M G l := by
    intro v _
    unfold poolWeight
    split_ifs <;> omega
  calc ∑ v ∈ G.verts, poolWeight run G δ l v
      ≤ ∑ v ∈ G.verts, (cAgg run G δ v l + run.M G l) := Finset.sum_le_sum h1
    _ = ∑ v ∈ G.verts, cAgg run G δ v l + run.M G l * G.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, FGraph.card]
    _ ≤ (run.M G l - 1) * G.card + run.M G l * G.card := by
        have := (sum_cAgg_le run G δ l G.verts hCap).trans
          (Nat.mul_le_mul_left _ (sum_card_classed_le run G l))
        omega

end EG.Quot
