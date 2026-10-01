module

public import EG.Spec.Quot.RoundStep
public import EG.Lib.Quot.ListsLaw
public import EG.Lib.Quot.Items
public import EG.Lib.Quot.UltraAux

/-!
# P3 stub: `EG.Spec.RoundListsLawStatement` (s7:consRound)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundListsLaw`; consumers import this module.

Proof (manuscript s7:consRound (c)): "The lists of the groups of `h` are pairwise disjoint, and,
since the groups and their numbering are functions of `Past_l` while `η_h` is independent of
`Past_l`, they form a uniformly random sequence of `k_h` pairwise disjoint `3`-subsets of `[4M_l]`.
Lists of distinct hubs are independent." A non-ultra hub has `c^live_h ≤ θ^ult_l ≤ M_lHcd_l/7`, so
`3k_h ≤ 3(8M_l/7 + 1) ≤ 4M_l` and the lists `listOf η_h i` (`i < k_h`) are well defined 3-sets
(`EG.Quot.card_listOf`, `EG.Quot.disjoint_listOf`); their law is `EG.Quot.prob_listOf_eq`. The
list of an item of `h` reads only `η_h` and the `ζ_{h,u}`, so lists of distinct hubs are
independent (`EG.Quot.iIndepFun_listsLaw`).
-/

public section

namespace EG.Todo

open EG.Quot EG.FinDist

/-- Proved in P3. [s7:consRound] see `EG.Spec.RoundListsLawStatement`. -/
theorem RoundListsLaw : EG.Spec.RoundListsLawStatement := by
  intro V _ I hI
  classical
  refine ⟨fun h hh hnu hc => ?_, fun R _ => ?_⟩
  · -- `3k_h ≤ 4M_l`
    have hM : (2 : ℝ) ^ 40 ≤ I.M := by exact_mod_cast hI.M_ge
    have hM0 : (0 : ℝ) < I.M := lt_of_lt_of_le (by positivity) hM
    have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
    have hk : 3 * I.kh h ≤ 4 * I.M := by
      have h1 : (I.clive h : ℝ) ≤ I.M * I.Hcd / 7 := by
        have : I.clive h ≤ I.thult := not_lt.1 hnu
        refine (Nat.cast_le.2 this).trans ?_
        rw [RoundInput.thult_eq]
        exact Nat.floor_le (by positivity)
      have h2 : 8 * (I.clive h : ℝ) / I.Hcd ≤ 8 * I.M / 7 := by
        rw [div_le_iff₀ hH]
        have e : 8 * (I.M : ℝ) / 7 * I.Hcd = 8 * (I.M * I.Hcd / 7) := by ring
        rw [e]
        linarith
      have h3 : (I.kh h : ℝ) < 8 * (I.clive h : ℝ) / I.Hcd + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h4 : ((3 * I.kh h : ℕ) : ℝ) ≤ ((4 * I.M : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h4
    -- `h` is a vertex of `G` (it carries a live item)
    have hv : h ∈ I.G.verts := by
      obtain ⟨p, hp⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one hc)
      rw [Finset.mem_filter] at hp
      have hp' := (I.mem_hubItems).1 hp.1
      have hJ := hI.J_sub (RoundInput.live_mem_J hp'.2.2.1)
      exact I.G.edge_verts _ hJ h (hp.2 ▸ Sym2.mem_mk_left _ _)
    refine ⟨fun L i hi => ⟨listOf_subset_range _ i, card_listOf _ (by omega),
      fun j _ hij => disjoint_listOf _ hij⟩, fun A hA hdisj => ?_⟩
    have hset : {L : Lists I.G I.M | ∀ i < I.kh h, listOf (etaAt L h) i = A i} =
        Prod.fst ⁻¹' {g | g ⟨h, hv⟩ ∈ {η | ∀ i < I.kh h, listOf η i = A i}} := by
      ext L
      simp [etaAt, hv]
    rw [hset]
    unfold listsLaw
    rw [prob_prod_fst, prob_pi_eval]
    exact prob_listOf_eq hk A hA hdisj
  · -- lists of distinct hubs are independent
    refine iIndepFun_listsLaw I.G I.M
      (fun h : ↥I.hubs => if hv : (h : V) ∈ I.G.verts then {⟨h, hv⟩} else ∅) ?_ _ ?_
    · intro h h' hne
      split_ifs with h1 h2
      · rw [Set.disjoint_singleton]
        intro he
        exact hne (Subtype.ext (congrArg Subtype.val he.symm).symm)
      · exact Set.disjoint_empty _
      · exact Set.empty_disjoint _
      · exact Set.empty_disjoint _
    · intro h L L' hL
      funext u
      by_cases hv : (h : V) ∈ I.G.verts
      · obtain ⟨e1, e2⟩ := hL ⟨h, hv⟩ (by simp [hv])
        unfold Rules.hubList etaAt zetaAt
        simp only [dif_pos hv, e1, e2]
      · unfold Rules.hubList etaAt zetaAt
        simp only [dif_neg hv]

end EG.Todo
