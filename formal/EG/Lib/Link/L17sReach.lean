module

public import EG.Lib.Ext.BMProp8
public import EG.Lib.Found.Graph

/-!
# Lemma 17* (manuscript s3:lemL17s): the reached sets — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemL17s], Step 1: "For `0 ≤ i ≤ ℓ_*`, let `𝓑_i` be
the set of vertices `v ∈ V(G)` that can be reached from `U` by a path in `G−F` of length at most
`i` whose interior vertices (if any) lie in `V_1 ∪ ⋯ ∪ V_{i−1}`."

Here the reached sets are defined with walks (`reach K U S i`: walks of length `≤ i` from `U`
whose vertices other than the two ends lie in `S`); a walk is shortcut to a path with the same
property (`EG.BM8.mem_ball_iff_walk`), so the facts (O1)–(O3) of the TeX hold:
* (O1) `reach_extend`: a neighbour `v` of a reached `w ∈ S'` is reached with one more step;
* (O2) `mem_ball_of_mem_reach`: reached vertices of `T ⊇ S` lie in the ball `B^i_K(U,T)`;
* (O3) `nbrSet_subset_reach`, `subset_reach`: `U ∪ Nbr_K(U) ⊆ reach K U ∅ 1`.
Step 4's growth is `card_growth`.
-/

public section

namespace EG.L17sProof

open Finset BM8

variable {V : Type*} [DecidableEq V]

/-- The vertices of `K` reached from `U` by a walk of length at most `i` whose vertices other
than its two ends lie in `S`. -/
noncomputable def reach (K : FGraph V) (U S : Finset V) (i : ℕ) : Finset V := by
  classical
  exact K.verts.filter (fun v => ∃ u ∈ U, ∃ w : K.toSimpleGraph.Walk u v,
    w.length ≤ i ∧ ∀ z ∈ w.support, z ≠ u → z ≠ v → z ∈ S)

theorem mem_reach {K : FGraph V} {U S : Finset V} {i : ℕ} {v : V} :
    v ∈ reach K U S i ↔ v ∈ K.verts ∧ ∃ u ∈ U, ∃ w : K.toSimpleGraph.Walk u v,
      w.length ≤ i ∧ ∀ z ∈ w.support, z ≠ u → z ≠ v → z ∈ S := by
  classical
  unfold reach
  rw [Finset.mem_filter]

theorem reach_subset_verts (K : FGraph V) (U S : Finset V) (i : ℕ) : reach K U S i ⊆ K.verts :=
  fun _ hv => (mem_reach.1 hv).1

theorem reach_mono {K : FGraph V} {U S S' : Finset V} {i i' : ℕ} (hS : S ⊆ S') (hi : i ≤ i') :
    reach K U S i ⊆ reach K U S' i' := by
  intro v hv
  obtain ⟨hvV, u, hu, w, hwl, hwS⟩ := mem_reach.1 hv
  exact mem_reach.2 ⟨hvV, u, hu, w, hwl.trans hi, fun z hz h1 h2 => hS (hwS z hz h1 h2)⟩

/-- (O3) `U ⊆ 𝓑_i`. -/
theorem subset_reach {K : FGraph V} {U : Finset V} (hU : U ⊆ K.verts) (S : Finset V) (i : ℕ) :
    U ⊆ reach K U S i := by
  intro u hu
  refine mem_reach.2 ⟨hU hu, u, hu, SimpleGraph.Walk.nil, by simp, fun z hz h1 _ => ?_⟩
  simp at hz
  exact absurd hz h1

/-- (O3) `Nbr_K(U) ⊆ 𝓑_1`. -/
theorem nbrSet_subset_reach {K : FGraph V} (U S : Finset V) {i : ℕ} (hi : 1 ≤ i) :
    K.nbrSet U ⊆ reach K U S i := by
  intro v hv
  rw [FGraph.mem_nbrSet] at hv
  obtain ⟨hvV, -, u, hu, hadj⟩ := hv
  have hadj' : K.toSimpleGraph.Adj u v := hadj
  refine mem_reach.2 ⟨hvV, u, hu, SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil,
    by simpa using hi, fun z hz h1 h2 => ?_⟩
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2

/-- (O1) "Let `v ∈ Nbr_{G−F}(𝓑_i)` have a neighbour `w` in `G−F` with `w ∈ 𝓑_i ∩ V_i`. Then
`v ∈ 𝓑_{i+1}`." (With walks: append the edge `wv`.) -/
theorem reach_extend {K : FGraph V} {U S : Finset V} {i : ℕ} {w v : V}
    (hw : w ∈ reach K U S i) (hadj : K.Adj w v) (hvV : v ∈ K.verts) :
    v ∈ reach K U (insert w S) (i + 1) := by
  obtain ⟨-, u, hu, p, hpl, hpS⟩ := mem_reach.1 hw
  have hadj' : K.toSimpleGraph.Adj w v := hadj
  refine mem_reach.2 ⟨hvV, u, hu, p.concat hadj', by rw [SimpleGraph.Walk.length_concat]; omega,
    fun z hz h1 h2 => ?_⟩
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · by_cases hzw : z = w
    · rw [hzw]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hpS z hz h1 hzw)
  · exact absurd rfl h2

/-- (O2) "`𝓑_{ℓ_*} ∩ V_{ℓ_*} ⊆ B^{ℓ_*}_{G−F}(U,V)`": a reached vertex of `T ⊇ S` lies in the
ball `B^i_K(U,T)`. -/
theorem mem_ball_of_mem_reach {K : FGraph V} {U S T : Finset V} {i : ℕ} {v : V}
    (hv : v ∈ reach K U S i) (hvT : v ∈ T) (hST : S ⊆ T) : v ∈ ball K i U T := by
  obtain ⟨-, u, hu, w, hwl, hwS⟩ := mem_reach.1 hv
  have hq := w.bypass_isPath
  have hpb := isPathBetween_support hq
  rw [mem_ball]
  refine ⟨hvT, u, hu, w.bypass.support, hpb, fun z hz => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := ne_of_mem_interior hpb.1.2.1 hpb.2.1 hpb.2.2 hz
    exact hST (hwS z (w.support_bypass_subset_support (interior_subset _ hz)) h1 h2)
  · rw [pathLength_support]
    exact w.length_bypass_le_length.trans hwl

/-- The set `A_i(W)` of the TeX: vertices of `Nbr_K(W)` with a `K`-neighbour in `W ∩ Y`. -/
noncomputable def Aset (K : FGraph V) (W Y : Finset V) : Finset V := by
  classical
  exact (K.nbrSet W).filter (fun v => ∃ w ∈ W, w ∈ Y ∧ K.Adj w v)

theorem mem_Aset {K : FGraph V} {W Y : Finset V} {v : V} :
    v ∈ Aset K W Y ↔ v ∈ K.nbrSet W ∧ ∃ w ∈ W, w ∈ Y ∧ K.Adj w v := by
  classical
  unfold Aset
  rw [Finset.mem_filter]

/-- "`A_i(W) ⊆ 𝓑_{i+1} \ 𝓑_i`" for `W = 𝓑_i` (by (O1), since `A_i(W) ∩ W = ∅`). -/
theorem Aset_subset {K : FGraph V} {U S S' Y : Finset V} {i : ℕ}
    (hS' : S ⊆ S') (hY : Y ⊆ S') :
    Aset K (reach K U S i) Y ⊆ reach K U S' (i + 1) \ reach K U S i := by
  intro v hv
  obtain ⟨hvN, w, hw, hwY, hadj⟩ := mem_Aset.1 hv
  rw [FGraph.mem_nbrSet] at hvN
  refine Finset.mem_sdiff.2 ⟨?_, hvN.2.1⟩
  have := reach_extend hw hadj hvN.1
  exact reach_mono (Finset.insert_subset (hY hwY) hS') le_rfl this

/-- Step 4: "`|𝓑_{i+1}| ≥ (1+g_*)|𝓑_i|` for `1 ≤ i ≤ ℓ_*−1`, and `|𝓑_{ℓ_*}| ≥ (1+g_*)^{ℓ_*−1}`"
(iterated growth). -/
theorem card_growth (c : ℕ → ℝ) (g : ℝ) (hg : 0 ≤ g) :
    ∀ m : ℕ, (∀ j < m, (1 + g) * c j ≤ c (j + 1)) → (1 + g) ^ m * c 0 ≤ c m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h m (by omega)
    have : (1 + g) ^ (m + 1) * c 0 = (1 + g) * ((1 + g) ^ m * c 0) := by ring
    rw [this]
    exact le_trans (mul_le_mul_of_nonneg_left h1 (by linarith)) h2

end EG.L17sProof
