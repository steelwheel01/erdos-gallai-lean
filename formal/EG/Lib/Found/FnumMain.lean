module

public import EG.Spec.Main
public import EG.Lib.Found.FGraphFnum

/-!
# `f(n) = O(n)` is the internal main theorem (manuscript s7:thmMainProof, last step)

The proof of the main theorem ends (s7:thmMainProof): "In particular f(n) ≤ c n for every n, so
f(n) = O(n)." This file shows that the frozen internal statement `EG.Spec.MainInternal` says
exactly this, in terms of `EG.fmax` (the manuscript's f(n), [s1:defObject]):

* `mainInternal_iff_fmax : MainInternal ↔ ∃ c : ℕ, ∀ n, fmax n ≤ c * n`;
* `FGraph` form, the form in which the s7:thmHI endgame bounds f(G) for graphs `G : FGraph V`:
  `mainInternal_iff_fnum_edges : MainInternal ↔ ∃ c : ℕ, ∀ (V : Type u) (H : FGraph V),
  fnum H.edges ≤ c * H.card` (any universe `u`), with the one-directional forms
  `mainInternal_of_fnum_edges_le` (hypothesis only on the graphs on `Fin n`) and
  `fnum_edges_le_of_mainInternal`.

These equivalences are also a permanent fidelity check of `fmax`: neither `fnum` nor `fmax` is
stronger or weaker than the decomposition statement of the internal spec.
-/

public section


namespace EG

universe u

/-- [s7:thmMainProof], last step: "In particular f(n) ≤ c n for every n, so f(n) = O(n)." The
internal main theorem holds iff `f(n) ≤ c n` for some constant `c` and all `n`. -/
theorem mainInternal_iff_fmax : Spec.MainInternal ↔ ∃ c : ℕ, ∀ n, fmax n ≤ c * n := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n => ?_⟩
    classical
    obtain ⟨H, hH⟩ := exists_fnum_eq_fmax n
    rw [← hH]
    obtain ⟨D, hD, hlen⟩ := hc (Fin n) H
    rw [Fintype.card_fin] at hlen
    exact (fnum_edgeFinset_le_iff H).2 ⟨D, hD, hlen⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun V _ _ G => ?_⟩
    classical
    exact (fnum_edgeFinset_le_iff G).1 ((fnum_le_fmax G rfl).trans (hc _))

/-- [s7:thmMainProof], `FGraph` form, sufficient condition: if `f(H) ≤ c |H|` for every graph
`H` on a vertex set `Fin n`, then the internal main theorem holds. -/
theorem mainInternal_of_fnum_edges_le (c : ℕ)
    (h : ∀ (n : ℕ) (H : FGraph (Fin n)), fnum H.edges ≤ c * H.card) : Spec.MainInternal := by
  refine mainInternal_iff_fmax.2 ⟨c, fun n => ?_⟩
  classical
  obtain ⟨G, hG⟩ := exists_fnum_eq_fmax n
  rw [← hG]
  simpa using h n (FGraph.ofSimpleGraph G)

/-- [s7:thmMainProof], `FGraph` form, consequence: the internal main theorem gives
`f(H) ≤ c |H|` for every finite graph `H`, on a vertex type of any universe. -/
theorem fnum_edges_le_of_mainInternal (h : Spec.MainInternal) :
    ∃ c : ℕ, ∀ (V : Type u) (H : FGraph V), fnum H.edges ≤ c * H.card := by
  obtain ⟨c, hc⟩ := mainInternal_iff_fmax.1 h
  exact ⟨c, fun V H => H.fnum_edges_le_fmax.trans (hc _)⟩

/-- [s7:thmMainProof], `FGraph` form: the internal main theorem holds iff `f(H) ≤ c |H|` for some
constant `c` and every finite graph `H` (on a vertex type of any fixed universe `u`). -/
theorem mainInternal_iff_fnum_edges :
    Spec.MainInternal ↔ ∃ c : ℕ, ∀ (V : Type u) (H : FGraph V), fnum H.edges ≤ c * H.card := by
  refine ⟨fnum_edges_le_of_mainInternal, fun ⟨c, hc⟩ => mainInternal_of_fnum_edges_le c ?_⟩
  intro n H
  -- transport `H` to the vertex type `ULift (Fin n)` of universe `u`
  let φ : Fin n ↪ ULift.{u} (Fin n) := Equiv.ulift.symm.toEmbedding
  let H' : FGraph (ULift.{u} (Fin n)) :=
    { verts := H.verts.map φ
      edges := H.edges.map φ.sym2Map
      edge_verts := by
        intro e he v hv
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
        obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hv
        exact Finset.mem_map_of_mem φ (H.edge_verts e' he' w hw)
      loopless := by
        intro e he hd
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
        exact H.loopless e' he' ((Sym2.isDiag_map φ.injective).1 hd) }
  have h1 : fnum H'.edges = fnum H.edges := fnum_map φ H.edges
  have h2 : H'.card = H.card := by simp [H', FGraph.card_def]
  rw [← h1, ← h2]
  exact hc _ H'

end EG
