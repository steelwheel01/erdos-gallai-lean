module

public import EG.Spec.HB.TauRules
public import EG.Lib.HB.Split

/-!
# Proofs: the witness Fact, the `τ`-rules and the split (manuscript s2:defWitness,
s2:defTauRules, s2:eqSplit)

Unit P3A (probe P-3, part 1). Design note `formal/work/p2b/P3A.md`.

* `EG.witnessExists : EG.Spec.WitnessExistsStatement` ([s2:defWitness]: `m ≥ 2`, and a witness
  exists at a non-expander);
* `EG.witnessFact : EG.Spec.WitnessFactStatement` (the Fact of [s2:defWitness]);
* `EG.tauEqSplit : EG.Spec.TauEqSplitStatement` ((eqSplit));
* `EG.tauFactA`, `EG.tauFactB`, `EG.tauFactC` (Facts (a)–(c) of [s2:defTauRules]).

The generic lemmas are in `EG.Lib.HB.Split`.
-/

public section

namespace EG

open EG.HB

/-- [s2:defWitness] "Then `m ≥ 2`, since a graph on one vertex has no set `U` with
`1 ≤ |U| ≤ 2m/3`. … Since `H` is not an `(ε,s)`-expander, a witness exists." -/
theorem witnessExists : EG.Spec.WitnessExistsStatement := by
  intro V _ H s _ hH
  obtain ⟨U, F, hw⟩ := (not_isExpander_iff_exists_isWitness H epsC s).1 hH
  refine ⟨?_, U, F, hw⟩
  obtain ⟨-, -, h1, h23, -, -⟩ := hw
  have h1' : (1 : ℝ) ≤ U.card := by exact_mod_cast h1
  have : (3 : ℝ) / 2 ≤ H.card := by linarith
  have : (1 : ℝ) < H.card := by linarith
  have : 1 < H.card := by exact_mod_cast this
  omega

/-- [s2:defWitness] (Fact) "`F_0 ⊆ F` and `Nbr_{H-F_0}(U) = N`. In particular `(U,F_0)` is again
a witness at `H`, with the same set `N`." -/
theorem witnessFact : EG.Spec.WitnessFactStatement := by
  intro V _ H s U F N _ hw hN
  subst hN
  exact ⟨witF0_witN_subset H U F, witN_witF0 H U F, isWitness_witF0 hw⟩

namespace HB

variable {V : Type*} [DecidableEq V]

/-- (eqSplit), first child: `G_1 = H[U' ∪ N'']` (for all `U`, `N`, `τ`). -/
theorem tauG1_eq (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauG1 H U N τ = splitFst H (tauU1 H U N τ) (tauN2 H U N τ) := by
  apply FGraph.ext
  · rfl
  · show (H.induce _).edges \ tauF2 H U N τ = (splitFst H _ _).edges
    exact Finset.sdiff_eq_self_of_disjoint (disjoint_splitFst_splitDel H _ _)

/-- (eqSplit), second child: `G_2 = H[V \ U'] - E(H[N''])` (for all `U`, `N`, `τ`). -/
theorem tauG2_eq (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauG2 H U N τ = splitSnd H (tauU1 H U N τ) (tauN2 H U N τ) := by
  apply FGraph.ext
  · simp only [tauG2, splitSnd, FGraph.deleteEdges_verts, FGraph.deleteVerts_verts,
      FGraph.induce_verts]
    exact (Finset.inter_eq_right.2 Finset.sdiff_subset).symm
  · ext e
    rw [mem_splitSnd_edges]
    simp only [tauG2, FGraph.deleteEdges_edges, Finset.mem_sdiff, tauG1_eq, mem_splitFst_edges,
      FGraph.deleteVerts, FGraph.mem_induce_edges]
    constructor
    · rintro ⟨⟨⟨he, hv⟩, hn⟩, -⟩
      exact ⟨he, fun v hve => (hv v hve).2,
        fun hN => hn ⟨he, fun v hve => Finset.mem_union_right _ (hN v hve)⟩⟩
    · rintro ⟨he, hU, hN⟩
      refine ⟨⟨⟨he, fun v hve => ⟨H.edge_verts e he v hve, hU v hve⟩⟩, ?_⟩,
        ?_⟩
      · rintro ⟨-, h⟩
        apply hN
        intro v hve
        rcases Finset.mem_union.1 (h v hve) with h' | h'
        · exact absurd h' (hU v hve)
        · exact h'
      · intro hF
        obtain ⟨-, a, ha, b, -, rfl⟩ := mem_splitDel.1 hF
        exact hU a (Sym2.mem_mk_left a b) ha

end HB

/-- [s2:eqSplit] ([s2:defTauRules]) "Every edge of `F''` has one end in `U'` and the other
outside `U'∪N''`, so no edge of `F''` lies inside `U'∪N''`, and every edge of `F''` meets `U'`.
Hence `G_1 = H[U'∪N'']`, `G_2 = H[V\U'] - E(H[N''])`." -/
theorem tauEqSplit : EG.Spec.TauEqSplitStatement := by
  intro V _ H s τ U F N _ _ _ _
  refine ⟨fun e he => ?_, HB.tauG1_eq H U N τ, HB.tauG2_eq H U N τ⟩
  obtain ⟨-, a, ha, b, hb, rfl⟩ := mem_splitDel.1 he
  refine ⟨⟨a, ha, b, hb, rfl⟩, fun hin => ?_, a, ha, Sym2.mem_mk_left a b⟩
  exact (Finset.mem_sdiff.1 hb).2 ((Finset.mem_sym2_iff.1 hin) b (Sym2.mem_mk_right a b))

/-- [s2:defTauRules] Fact (a) "`U' ∩ N'' = ∅`, `U' ∪ N' = U ∪ N`, and `F'' ⊆ F_1 ⊆ F_0 ⊆ F`"
(with the implicit `U', N'' ⊆ V(H)`). -/
theorem tauFactA : EG.Spec.TauFactAStatement := by
  intro V _ H s τ U F N _ hw _ hN
  subst hN
  obtain ⟨h1, h2, h3⟩ := tau_split_wf (τ := τ) hw
  exact ⟨h3, tauU1_union_tauN1 H U _ τ, tauF2_subset_tauF1 H U _ τ, tauF1_subset_witF0 H U _ τ,
    witF0_witN_subset H U F, h1, h2⟩

/-- [s2:defTauRules] Fact (b) "`E(H) = E(G_1) ⊔ E(G_2) ⊔ F''` (disjoint union),
`V(G_1) = U' ∪ N''` and `V(G_2) = V \ U'`. A vertex of `U'` lies only in `G_1`, a vertex of
`N''` lies in both children, and a vertex of `V \ (U' ∪ N'')` lies only in `G_2`." -/
theorem tauFactB : EG.Spec.TauFactBStatement := by
  intro V _ H s τ U F N _ hw _ hN
  subst hN
  obtain ⟨hU, hN, hd⟩ := tau_split_wf (τ := τ) hw
  rw [HB.tauG1_eq, HB.tauG2_eq]
  refine ⟨disjoint_splitFst_splitSnd H _ _, disjoint_splitFst_splitDel H _ _,
    disjoint_splitSnd_splitDel H _ _, splitFst_union_splitSnd_union_splitDel H _ _,
    splitFst_verts_of_subset hU hN, splitSnd_verts H _ _, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_⟩
  · exact ⟨mem_splitFst_verts_of_mem_left hU hv, not_mem_splitSnd_verts_of_mem_left hv⟩
  · exact ⟨mem_splitFst_verts_of_mem_right hN hv, mem_splitSnd_verts_of_mem_right hN hd hv⟩
  · obtain ⟨hvH, hvo⟩ := Finset.mem_sdiff.1 hv
    exact ⟨not_mem_splitFst_verts_of_not_mem hvo, mem_splitSnd_verts_of_not_mem hvH hvo⟩

/-- [s2:defTauRules] Fact (c) "Given the pair `(U,N)`, the objects … depend only on `(U,N)` …
every witness `(U,F)` yields the same split as its minimal part `(U,F_0)`." -/
theorem tauFactC : EG.Spec.TauFactCStatement := by
  intro V _ H s τ U F N N₀ _ hw _ hN hN₀
  have hN₀N : N₀ = N := by rw [hN₀, hN, witN_witF0]
  subst hN₀N
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hN]
  exact isWitness_witF0 hw

end EG
