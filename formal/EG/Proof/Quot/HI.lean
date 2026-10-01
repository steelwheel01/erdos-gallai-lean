module

public import EG.Spec.Quot.HI
public import EG.Lib.Found.FGraphFnum

/-!
# Proof of Theorem HI″, layered quotient induction (manuscript s7:thmHI)

`EG.hi : EG.Spec.HIStatement`, by strong induction on `n = |V(G)|` over all graphs
`G : FGraph V` (`V : Type`); this is the manuscript's minimal-counterexample argument.
Let `c := max(C/(1-2ϑ), N₀/2)`.

0. (`c ≥ 0`.) The manuscript's constants are positive; here `D_*`, `N₀` are arbitrary reals, and
   `c ≥ 0` is derived from the hypothesis: if `c < 0` then `C < 0` and `N₀ < 0`, so the hypothesis
   applies to the single edge `K₂` and gives `1 = f(K₂) ≤ 2C + 2 ∑ f(Q_i)` with
   `∑ |V(Q_i)| ≤ 2ϑ < 1`, so every `Q_i` is empty and `1 ≤ 2C < 0` (`EG.hi_const_nonneg`).
   The graph without vertices has `f = 0`.
1. If `G` has an isolated vertex `v`, then `f(G - v) = f(G)` ([s1:factAdd](d),
   `FGraph.fnum_edges_deleteVerts_singleton_of_deg_eq_zero`) and `|G - v| = n - 1`, so the
   induction hypothesis gives `f(G) ≤ c (n - 1) ≤ c n`.
2. If `n < N₀`: `f(G) ≤ |E(G)| ≤ n(n-1)/2 ≤ (N₀/2) n ≤ c n` ([s1:factAdd](a)).
3. If `d₁ < D_*`: `f(G) ≤ |E(G)| = d₁ n / 2 ≤ (D_*/2) n ≤ C n ≤ c n` — the trivial bound
   `f(G) ≤ |E(G)|` only.
4. Otherwise the hypothesis gives `Q₁,…,Q_k` with `∑ |V(Q_i)| ≤ ϑ n < n`, so each `Q_i` has fewer
   vertices than `G` and `f(Q_i) ≤ c |V(Q_i)|` by the induction hypothesis.
5. `f(G) ≤ C n + 2c ∑ |V(Q_i)| ≤ C n + 2cϑ n ≤ c(1-2ϑ) n + 2cϑ n = c n`.

Also `EG.hi_simpleGraph`: the conclusion for a Mathlib `SimpleGraph` on a `Fintype`.
-/

public section


namespace EG

namespace FGraph

variable {V : Type*} (H : FGraph V)

/-- A graph without vertices has no edges. -/
theorem edges_eq_empty_of_card_eq_zero (h : H.card = 0) : H.edges = ∅ := by
  rw [card_def, Finset.card_eq_zero] at h
  refine Finset.eq_empty_of_forall_notMem fun e he => ?_
  induction e using Sym2.ind with
  | h a b =>
    have := H.edge_verts _ he a (Sym2.mem_mk_left a b)
    simp [h] at this

/-- [s7:thmHI] "The graph without vertices has `f = 0`." -/
theorem fnum_edges_eq_zero_of_card_eq_zero (h : H.card = 0) : fnum H.edges = 0 := by
  rw [H.edges_eq_empty_of_card_eq_zero h, fnum_empty]

/-- `|E(H)| ≤ n(n-1)/2` for a graph `H` with `n` vertices, in the form `2|E(H)| ≤ n(n-1)`
(handshake lemma and `d_H(v) ≤ n - 1`). -/
theorem two_mul_card_edges_le : 2 * H.edges.card ≤ H.card * (H.card - 1) := by
  classical
  rw [← H.sum_deg_eq_two_mul_card_edges]
  calc ∑ v ∈ H.verts, H.deg v ≤ ∑ _v ∈ H.verts, (H.card - 1) :=
        Finset.sum_le_sum fun v hv => Nat.le_sub_one_of_lt (H.deg_lt_card hv)
    _ = H.card * (H.card - 1) := by simp [card_def]

/-- "Without isolated vertices", as written in `EG.Spec.HIHyp` (every vertex is an end of an
edge), is the same as "every vertex has non-zero degree". -/
theorem noIsolated_iff_deg_ne_zero [DecidableEq V] :
    (∀ v ∈ H.verts, ∃ e ∈ H.edges, v ∈ e) ↔ ∀ v ∈ H.verts, H.deg v ≠ 0 := by
  simp only [ne_eq, deg_eq_zero_iff, not_forall, not_not, exists_prop]

end FGraph

/-- The single edge `K₂` on the vertex type `Fin 2`. -/
@[expose] def hiK2 : FGraph (Fin 2) where
  verts := Finset.univ
  edges := {s(0, 1)}
  edge_verts _ _ v _ := Finset.mem_univ v
  loopless e he := by
    rw [Finset.mem_singleton.1 he, Sym2.mk_isDiag_iff]
    decide

theorem hiK2_card : hiK2.card = 2 := rfl

theorem hiK2_card_edges : hiK2.edges.card = 1 := rfl

theorem hiK2_fnum : fnum hiK2.edges = 1 :=
  fnum_singleton (by rw [Sym2.mk_isDiag_iff]; decide)

theorem hiK2_noIsolated : ∀ v ∈ hiK2.verts, ∃ e ∈ hiK2.edges, v ∈ e := by
  intro v _
  refine ⟨s(0, 1), Finset.mem_singleton_self _, ?_⟩
  fin_cases v <;> simp

section HI

variable {Dstar N₀ C ϑ : ℝ}

/-- If `∑_i |V(Q_i)| ≤ b`, then every `|V(Q_i)| ≤ b`. -/
theorem FGraph.card_le_of_sum_card_le {k : ℕ} {W : Fin k → Type} (Q : (i : Fin k) → FGraph (W i))
    {b : ℝ} (h : ∑ i, ((Q i).card : ℝ) ≤ b) (i : Fin k) : ((Q i).card : ℝ) ≤ b :=
  (Finset.single_le_sum (f := fun j => ((Q j).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
    (Finset.mem_univ i)).trans h

/-- [s7:thmHI], implicit in the manuscript (where `N₀, D_* > 0`): under the hypothesis of
Theorem HI″ the constant `c = max(C/(1-2ϑ), N₀/2)` is non-negative. If `c < 0`, the hypothesis
applied to `K₂` is contradictory. -/
theorem hi_const_nonneg (hC : Dstar / 2 ≤ C) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) : 0 ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) := by
  by_contra hneg
  push Not at hneg
  have hpos : 0 < 1 - 2 * ϑ := by linarith
  have h1 : C / (1 - 2 * ϑ) < 0 := lt_of_le_of_lt (le_max_left _ _) hneg
  have h2 : N₀ / 2 < 0 := lt_of_le_of_lt (le_max_right _ _) hneg
  have hCneg : C < 0 := by
    have := (div_lt_iff₀ hpos).1 h1
    linarith
  obtain ⟨k, W, Q, hf, hcard⟩ := h (Fin 2) hiK2 hiK2_noIsolated
    (by rw [hiK2_card]; push_cast; linarith)
    (by rw [hiK2_card, hiK2_card_edges]; push_cast; linarith)
  have hQ : ∀ i, (Q i).card = 0 := by
    intro i
    have hi := FGraph.card_le_of_sum_card_le Q hcard i
    rw [hiK2_card] at hi
    push_cast at hi
    have : ((Q i).card : ℝ) < 1 := by linarith
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  have hsum : ∑ i, (fnum (Q i).edges : ℝ) = 0 := by
    simp [(Q _).fnum_edges_eq_zero_of_card_eq_zero (hQ _)]
  rw [hsum, hiK2_fnum, hiK2_card] at hf
  push_cast at hf
  linarith

/-- [s7:thmHI] The induction, for a fixed constant `c ≥ 0` with `N₀/2 ≤ c` and
`C ≤ c(1-2ϑ)`: every graph `G` satisfies `f(G) ≤ c |V(G)|`. Strong induction on `n = |V(G)|`
(the manuscript's minimal counterexample), steps (1)–(5). -/
theorem hi_induction (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2) (h : Spec.HIHyp Dstar N₀ C ϑ)
    (hC : Dstar / 2 ≤ C) {c : ℝ} (hc0 : 0 ≤ c) (hNc : N₀ / 2 ≤ c)
    (hCc : C ≤ c * (1 - 2 * ϑ)) :
    ∀ (n : ℕ) (V : Type) (G : FGraph V), G.card = n → (fnum G.edges : ℝ) ≤ c * G.card := by
  have hCc' : C ≤ c := by nlinarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V G hn
    subst hn
    classical
    -- the graph without vertices
    rcases Nat.eq_zero_or_pos G.card with h0 | hn0
    · rw [G.fnum_edges_eq_zero_of_card_eq_zero h0, h0]
      simp
    have hnR : (0 : ℝ) < G.card := by exact_mod_cast hn0
    -- (1) `G` has no isolated vertex
    by_cases hiso : ∃ v ∈ G.verts, ∀ e ∈ G.edges, v ∉ e
    · obtain ⟨v, hv, hve⟩ := hiso
      have hdeg : G.deg v = 0 := G.deg_eq_zero_iff.2 hve
      have h1 := G.fnum_edges_deleteVerts_singleton_of_deg_eq_zero hdeg
      have h2 := G.card_deleteVerts_singleton hv
      have := ih (G.card - 1) (by omega) V (G.deleteVerts {v}) h2
      rw [h1, h2] at this
      calc (fnum G.edges : ℝ) ≤ c * ((G.card - 1 : ℕ) : ℝ) := this
        _ ≤ c * G.card := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le _ 1) hc0
    push Not at hiso
    have hfE : (fnum G.edges : ℝ) ≤ G.edges.card := by exact_mod_cast fnum_le_card _
    -- (2) `n ≥ N₀`
    by_cases hN : (G.card : ℝ) < N₀
    · have hE : ((2 * G.edges.card : ℕ) : ℝ) ≤ ((G.card * (G.card - 1) : ℕ) : ℝ) := by
        exact_mod_cast G.two_mul_card_edges_le
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hn0] at hE
      push_cast at hE
      -- `n(n-1)/2 ≤ (N₀/2) n` since `n - 1 < N₀`
      nlinarith
    push Not at hN
    -- (3) `d₁ ≥ D_*`
    by_cases hD : 2 * (G.edges.card : ℝ) / G.card < Dstar
    · have hE : 2 * (G.edges.card : ℝ) < Dstar * G.card := (div_lt_iff₀ hnR).1 hD
      nlinarith
    push Not at hD
    -- (4) the hypothesis applies; minimality for the `Q_i`
    obtain ⟨k, W, Q, hf, hcard⟩ := h V G hiso hN hD
    have hQ : ∀ i, (fnum (Q i).edges : ℝ) ≤ c * (Q i).card := by
      intro i
      have hi := FGraph.card_le_of_sum_card_le Q hcard i
      have hlt : ((Q i).card : ℝ) < G.card := by nlinarith
      exact ih (Q i).card (by exact_mod_cast hlt) (W i) (Q i) rfl
    -- (5)
    calc (fnum G.edges : ℝ) ≤ C * G.card + 2 * ∑ i, (fnum (Q i).edges : ℝ) := hf
      _ ≤ C * G.card + 2 * ∑ i, c * ((Q i).card : ℝ) := by
          gcongr with i
          exact hQ i
      _ = C * G.card + 2 * c * ∑ i, ((Q i).card : ℝ) := by rw [← Finset.mul_sum]; ring
      _ ≤ C * G.card + 2 * c * (ϑ * G.card) := by gcongr
      _ ≤ c * G.card := by nlinarith

end HI

/-- [s7:thmHI] Theorem HI″ (layered quotient induction). "Let `C ≥ D_*/2` and `ϑ ∈ [0,1/2)` be
constants with the following property. Every graph `G` without isolated vertices, with `n ≥ N₀`
vertices and `d₁ = 2|E(G)|/n ≥ D_*`, admits finitely many simple graphs `Q₁,…,Q_k` (`k ≥ 0`) such
that `f(G) ≤ C n + 2 ∑ f(Q_i)` and `∑ |V(Q_i)| ≤ ϑ n`. Then `f(G) ≤ c |V(G)|` for every graph `G`,
where `c := max(C/(1-2ϑ), N₀/2)`." -/
theorem hi : Spec.HIStatement := by
  intro Dstar N₀ C ϑ hC hϑ0 hϑ h V G
  have hpos : 0 < 1 - 2 * ϑ := by linarith
  exact hi_induction hϑ0 hϑ h hC (hi_const_nonneg hC hϑ h) (le_max_right _ _)
    ((div_le_iff₀ hpos).1 (le_max_left _ _)) G.card V G rfl

/-- [s7:thmHI], conclusion for a Mathlib `SimpleGraph` on a finite vertex type:
`f(G) ≤ c |V(G)|` with `c = max(C/(1-2ϑ), N₀/2)`. -/
theorem hi_simpleGraph {Dstar N₀ C ϑ : ℝ} (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) (V : Type) [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    (fnum G.edgeFinset : ℝ) ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * (Fintype.card V : ℝ) := by
  have := hi Dstar N₀ C ϑ hC hϑ0 hϑ h V (FGraph.ofSimpleGraph G)
  simpa [FGraph.card_def] using this

/-- Adapter for producers of the hypothesis of Theorem HI″ (e.g. s7:thmJVps, whose quotients
`Q_3, …, Q_R` are indexed by rounds): `EG.Spec.HIHyp` from a family of graphs indexed by any finite
type `ι`, reindexed to `Fin k` along `Fintype.equivFin`. -/
theorem hiHyp_of_fintype_index {Dstar N₀ C ϑ : ℝ}
    (h : ∀ (V : Type) (G : FGraph V), (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) →
      N₀ ≤ (G.card : ℝ) → Dstar ≤ 2 * (G.edges.card : ℝ) / (G.card : ℝ) →
      ∃ (ι : Type) (_ : Fintype ι) (W : ι → Type) (Q : (i : ι) → FGraph (W i)),
        (fnum G.edges : ℝ) ≤ C * (G.card : ℝ) + 2 * ∑ i, (fnum (Q i).edges : ℝ) ∧
        ∑ i, ((Q i).card : ℝ) ≤ ϑ * (G.card : ℝ)) :
    Spec.HIHyp Dstar N₀ C ϑ := by
  intro V G h1 h2 h3
  obtain ⟨ι, _, W, Q, hf, hc⟩ := h V G h1 h2 h3
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => W (e.symm i), fun i => Q (e.symm i), ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm (fun i => (fnum (Q i).edges : ℝ))]
    exact hf
  · rw [Equiv.sum_comp e.symm (fun i => ((Q i).card : ℝ))]
    exact hc

end EG
