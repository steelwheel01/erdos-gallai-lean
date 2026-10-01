module

public import EG.Lib.Found.Graph

/-!
# Bucić–Montgomery Proposition 12 (manuscript s1:citProp12)

Proof of `EG.Spec.BMProp12Statement` (used by `EG.Todo.BMProp12`), following [BM]'s proof as
recorded in the blueprint (`formal/work/p2/blueprint_s1.md`, node `s1:citProp12`): if (a) fails,
put `X := Nbr_{G-F}(U) \ N_{G-F,d}(U)` and `F' := E_{G-F}(U,X)`. Then `|F'| ≤ d|X| ≤ s|U|/2`,
so `|F ∪ F'| ≤ s|U|`, and `Nbr_{G-(F ∪ F')}(U) ⊆ N_{G-F,d}(U)`; expansion of `G` at
`(U, F ∪ F')` ([s1:citDef11]) gives (b). The hypothesis `d ≤ s` is not needed.
-/

public section

namespace EG.FGraph

variable {V : Type*} [DecidableEq V]

/-- [s1:citProp12] ([BM, Proposition 12]) "Let `G` be an `n`-vertex `(ε,s)`-expander, `U ⊆ V(G)`
with `1 ≤ |U| ≤ 2n/3`, and `F` a set of at most `s|U|/2` edges. Then for every `0 < d ≤ s`,
either (a) `|Nbr_{G-F}(U)| ≥ s|U|/(2d)`, or (b) `|N_{G-F,d}(U)| ≥ ε|U|/log²n`." (`d ≤ s` is not
used.) -/
theorem IsExpander.bmProp12 {G : FGraph V} {ε s d : ℝ} {U : Finset V} {F : Finset (Sym2 V)}
    (hG : G.IsExpander ε s) (hU : U ⊆ G.verts) (h1 : 1 ≤ U.card)
    (h2 : (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3) (hF : F ⊆ G.edges)
    (hFc : (F.card : ℝ) ≤ s * (U.card : ℝ) / 2) (hd : 0 < d) :
    s * (U.card : ℝ) / (2 * d) ≤ (((G.deleteEdges F).nbrSet U).card : ℝ) ∨
      ε * (U.card : ℝ) / Real.logb 2 (G.card : ℝ) ^ 2 ≤
        (((G.deleteEdges F).nbrSetDeg U d).card : ℝ) := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨ha, hb⟩ := hcon
  set H := G.deleteEdges F with hH
  set X := H.nbrSet U \ H.nbrSetDeg U d with hX
  set F' := H.edges.filter (fun e => ∃ u ∈ U, ∃ x ∈ X, s(u, x) = e) with hF'
  -- every `x ∈ X` has fewer than `d` neighbours in `U`
  have hXlt : ∀ x ∈ X, ((H.nbrs x ∩ U).card : ℝ) < d := by
    intro x hx
    rw [hX, Finset.mem_sdiff] at hx
    by_contra h
    rw [not_lt] at h
    apply hx.2
    unfold nbrSetDeg
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_sdiff.2 ⟨(mem_nbrSet.1 hx.1).1, (mem_nbrSet.1 hx.1).2.1⟩, h⟩
  -- `|F'| ≤ d |X|`
  have hF'sub : F' ⊆ X.biUnion (fun x => (H.nbrs x ∩ U).image (fun u => s(u, x))) := by
    intro e he
    rw [hF', Finset.mem_filter] at he
    obtain ⟨he, u, hu, x, hx, rfl⟩ := he
    rw [Finset.mem_biUnion]
    refine ⟨x, hx, Finset.mem_image.2 ⟨u, Finset.mem_inter.2 ⟨?_, hu⟩, rfl⟩⟩
    rw [mem_nbrs, adj_iff, Sym2.eq_swap]
    exact he
  have hcardF' : (F'.card : ℝ) ≤ d * X.card := by
    have c1 := Finset.card_le_card hF'sub
    have c2 := Finset.card_biUnion_le (s := X)
      (t := fun x => (H.nbrs x ∩ U).image (fun u => s(u, x)))
    have c3 : ∀ x ∈ X, ((((H.nbrs x ∩ U).image (fun u => s(u, x))).card : ℕ) : ℝ) ≤ d :=
      fun x hx => le_trans (by exact_mod_cast Finset.card_image_le) (hXlt x hx).le
    calc (F'.card : ℝ)
        ≤ ((∑ x ∈ X, ((H.nbrs x ∩ U).image (fun u => s(u, x))).card : ℕ) : ℝ) := by
          exact_mod_cast c1.trans c2
      _ = ∑ x ∈ X, ((((H.nbrs x ∩ U).image (fun u => s(u, x))).card : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ _x ∈ X, d := Finset.sum_le_sum c3
      _ = d * X.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hXN : (X.card : ℝ) ≤ ((H.nbrSet U).card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hdX : d * X.card ≤ s * (U.card : ℝ) / 2 := by
    have : d * ((H.nbrSet U).card : ℝ) ≤ s * (U.card : ℝ) / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * d)).1 ha
      nlinarith
    nlinarith
  -- apply expansion to `(U, F ∪ F')`
  have hsub : F ∪ F' ⊆ G.edges := by
    refine Finset.union_subset hF ?_
    intro e he
    exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 he).1).1
  have hcard : ((F ∪ F').card : ℝ) ≤ s * U.card := by
    have : ((F ∪ F').card : ℝ) ≤ F.card + F'.card := by
      exact_mod_cast Finset.card_union_le F F'
    linarith
  have key := hG U (F ∪ F') hU hsub h1 h2 hcard
  have hincl : (G.deleteEdges (F ∪ F')).nbrSet U ⊆ H.nbrSetDeg U d := by
    intro v hv
    obtain ⟨hvV, hvU, u, hu, huv⟩ := mem_nbrSet.1 hv
    rw [deleteEdges_adj, Finset.mem_union, not_or] at huv
    have hvN : v ∈ H.nbrSet U :=
      mem_nbrSet.2 ⟨hvV, hvU, u, hu, deleteEdges_adj.2 ⟨huv.1, huv.2.1⟩⟩
    by_contra hvd
    have hvX : v ∈ X := Finset.mem_sdiff.2 ⟨hvN, hvd⟩
    apply huv.2.2
    rw [hF', Finset.mem_filter]
    exact ⟨Finset.mem_sdiff.2 ⟨huv.1, huv.2.1⟩, u, hu, v, hvX, rfl⟩
  have := Finset.card_le_card hincl
  have : (((G.deleteEdges (F ∪ F')).nbrSet U).card : ℝ) ≤ ((H.nbrSetDeg U d).card : ℝ) := by
    exact_mod_cast this
  linarith

end EG.FGraph
