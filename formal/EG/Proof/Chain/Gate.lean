module

public import EG.Spec.Chain.Gate
public import EG.Lib.Found.Orient

/-!
# Proof of Lemma GATE (manuscript s6:lemGATE)

`EG.gate_precise : EG.Spec.GatePreciseStatement` (the "More precisely" part) and
`EG.gate : EG.Spec.GateStatement` (the decomposition into at most `|𝒲|` cycles of `G`), and
`EG.gate_with_cycles`, which gives both at once (the decomposition `cs.map Obj.cycle` together
with the directed cycles `cs` behind it).

Proof, as in the manuscript:
1. an orientation has no loops and no antiparallel arcs (`EG.IsOrientation.not_mem_swap`; this is
   where "each edge receives exactly one direction" and the simplicity of `G` enter), so the
   balanced digraph `F⃗` is an arc-disjoint union of directed cycles of length `≥ 3`
   (`EG.exists_dirCycle_decomp`);
2. each of these cycles contains an arc of `𝒲`, since `F⃗ - 𝒲` is acyclic;
3. the cycles are arc-disjoint, so there are at most `|𝒲|` of them (a counting lemma private to
   this file);
4. the underlying cycles partition `F`, because distinct arcs of an orientation have distinct
   underlying edges and every edge of `F` is the underlying edge of an arc
   (`EG.isDecomp_map_cycle_of_arcs`). A consumer that needs the directed cycles behind the
   decomposition (e.g. [s6:lemHCCP] Step 4) uses `EG.gate_precise` and then
   `EG.isDecomp_map_cycle_of_arcs` for the decomposition `cs.map Obj.cycle`.
-/

public section


namespace EG

variable {V : Type*}

/-- If the members of a list `cs` carry pairwise disjoint lists `f c`, each meeting the finite set
`W`, then `cs` has at most `|W|` members. -/
private theorem length_le_card_of_pairwise_disjoint {α β : Type*} [DecidableEq β] (f : α → List β) :
    ∀ (cs : List α) (W : Finset β), cs.Pairwise (fun a b => (f a).Disjoint (f b)) →
      (∀ c ∈ cs, ∃ w ∈ W, w ∈ f c) → cs.length ≤ W.card
  | [], _, _, _ => by simp
  | c :: cs, W, hpw, hW => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨w, hwW, hwc⟩ := hW c List.mem_cons_self
    have ih := length_le_card_of_pairwise_disjoint f cs (W.erase w) hpw.2 (by
      intro c' hc'
      obtain ⟨w', hw'W, hw'c'⟩ := hW c' (List.mem_cons_of_mem c hc')
      refine ⟨w', Finset.mem_erase.2 ⟨?_, hw'W⟩, hw'c'⟩
      rintro rfl
      exact hpw.1 c' hc' hwc hw'c')
    rw [Finset.card_erase_of_mem hwW] at ih
    have : 0 < W.card := Finset.card_pos.2 ⟨w, hwW⟩
    simp only [List.length_cons]
    omega

/-- [s6:lemGATE] (forward direction, "More precisely") "`F⃗` is the arc-disjoint union of directed
cycles, each of length at least `3`, each the orientation of a cycle of `G`, and each containing an
arc of `𝒲`; there are at most `|𝒲|` of them." -/
theorem gate_precise : EG.Spec.GatePreciseStatement := by
  intro V _ G F A W hFG hA hbal _ hacyc
  obtain ⟨cs, hcs, hnd, hmem⟩ :=
    exists_dirCycle_decomp A hA.loopless (fun _ _ h => hA.not_mem_swap h) hbal
  -- "Each `C_i` contains an arc of `𝒲`, since otherwise `C_i` would be a directed cycle of
  -- `F⃗ - 𝒲`."
  have hW : ∀ c ∈ cs, ∃ w ∈ W, w ∈ cycleArcs c := by
    intro c hc
    by_contra hno
    push Not at hno
    obtain ⟨hcnd, hlen, hcA⟩ := hcs c hc
    apply hacyc c
    refine ⟨?_, hcnd, fun a ha => Finset.mem_sdiff.2 ⟨hcA a ha, fun haW => hno a haW ha⟩⟩
    rintro rfl
    simp at hlen
  refine ⟨cs, ?_, hnd, hmem, ?_⟩
  · intro c hc
    obtain ⟨hcnd, hlen, hcA⟩ := hcs c hc
    refine ⟨⟨?_, hcnd, hcA⟩, hlen, ⟨hcnd, hlen⟩, ?_, hW c hc⟩
    · rintro rfl
      simp at hlen
    · intro e he
      rw [cycleEdges_eq_map_cycleArcs, List.mem_map] at he
      obtain ⟨a, ha, rfl⟩ := he
      exact hFG (hA.mem a (hcA a ha))
  · -- "The `C_i` are arc-disjoint, so `p ≤ |𝒲|`."
    exact length_le_card_of_pairwise_disjoint cycleArcs cs W (List.nodup_flatMap.1 hnd).2 hW

/-- [s6:lemGATE] (forward direction) "Let `F ⊆ E(G)` and let `F⃗` be an orientation of `F` with
`d⁺_{F⃗}(v) = d⁻_{F⃗}(v)` at every vertex `v`. Let `𝒲` be a set of arcs of `F⃗` such that
`F⃗ - 𝒲` is acyclic. Then `F` decomposes into at most `|𝒲|` cycles of `G`." -/
theorem gate : EG.Spec.GateStatement := by
  intro V _ G F A W hFG hA hbal hWA hacyc
  obtain ⟨cs, hcs, hnd, hmem, hlen⟩ := gate_precise V G F A W hFG hA hbal hWA hacyc
  refine ⟨cs.map Obj.cycle, ?_, by simpa using hlen, ?_⟩
  · -- "Their underlying cycles partition `F`, so they form a decomposition of `F` into cycles in
    -- the sense of Definition [s1:defObject]."
    exact isDecomp_map_cycle_of_arcs hA hnd hmem (fun c hc => (hcs c hc).2.2.1)
  · intro o ho
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    exact ⟨⟨c, rfl⟩, (hcs c hc).2.2.2.1⟩

/-- [s6:lemGATE] (forward direction, both conclusions together) The decomposition of `F` given by
GATE together with the directed cycles behind it: `F` decomposes into the cycles `Obj.cycle c`,
`c ∈ cs`, at most `|𝒲|` of them, and each `c` is a directed cycle of `F⃗` of length at least `3`,
all of whose edges are edges of `G`, containing an arc of `𝒲` (the form used in [s6:lemHCCP]
Step 4: "Each of them is the orientation of a directed cycle `C` of `F⃗` of length at least `3`
containing an arc of `𝒲`"). -/
theorem gate_with_cycles {V : Type*} [DecidableEq V] (G : FGraph V) (F : Finset (Sym2 V))
    (A W : Finset (V × V)) (hFG : F ⊆ G.edges) (hA : IsOrientation F A) (hbal : IsBalanced A)
    (hWA : W ⊆ A) (hacyc : IsAcyclic (A \ W)) :
    ∃ cs : List (List V), IsDecomp (F : Set (Sym2 V)) (cs.map Obj.cycle) ∧ cs.length ≤ W.card ∧
      ∀ c ∈ cs, IsDirCycle A c ∧ 3 ≤ c.length ∧ (∀ e ∈ cycleEdges c, e ∈ G.edges) ∧
        ∃ w ∈ W, w ∈ cycleArcs c := by
  obtain ⟨cs, hcs, hnd, hmem, hlen⟩ := gate_precise V G F A W hFG hA hbal hWA hacyc
  refine ⟨cs, isDecomp_map_cycle_of_arcs hA hnd hmem (fun c hc => (hcs c hc).2.2.1), hlen, ?_⟩
  intro c hc
  obtain ⟨h1, h2, -, h4, h5⟩ := hcs c hc
  exact ⟨h1, h2, h4, h5⟩

end EG
