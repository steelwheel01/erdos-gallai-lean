module

public import EG.Spec.Chain.PAR
public import EG.Lib.Chain.ParMain
public import EG.Lib.Chain.ParExist

/-!
# Proof of Lemma PAR (manuscript s6:lemPAR)

`EG.parExists : EG.Spec.ParExistsStatement` and `EG.par : EG.Spec.ParStatement`. Probe unit P2E
(probe P-2, part 1), proof round 1; the lemmas are in `EG.Lib.Chain.ParExist` (the chosen edge
exists), `EG.Lib.Chain.ParComp` (even components after deletion), `EG.Lib.Chain.ParTJoin`
(`T`-joins) and `EG.Lib.Chain.ParMain` (the count and the partition).

The manuscript cites [s1:citEuler] (a) (a spanning tree contains a `T`-join). This proof builds
the `T`-join directly from paths (`EG.exists_tJoin`), so it does **not** use the declared input
`EG.eulerTreeTJoin`.
-/

public section

namespace EG

open EG.Chain

/-- [s6:lemPAR] (existence) "In each odd component choose one edge that is either a non-bridge or
a pendant edge (an edge with an end of degree `1`) of that component; such an edge exists." -/
theorem parExists : EG.Spec.ParExistsStatement := by
  intro V _ E Va Vb hVab hbip
  have hloop : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    obtain ⟨a, -, b, -, rfl⟩ := hbip e he
    rw [Sym2.mk_isDiag_iff]
    exact ne_of_bip hVab hbip he
  refine ⟨fun C hC => ?_, exists_isParChoice hloop⟩
  classical
  unfold oddComps at hC
  obtain ⟨-, hodd⟩ := Finset.mem_filter.1 hC
  exact exists_nonBridge_or_pendant hloop (Finset.card_pos.1 (Nat.pos_of_ne_zero fun h => by
    rw [h] at hodd; exact Nat.not_odd_zero hodd))

/-- [s6:lemPAR] "Let `E_ab` be a bipartite graph with sides `V_a, V_b` ... Then, for *every* such
choice, `|J'| ≤ #{odd components} ≤ |V(E_ab)|/2`, and there is a partition
`E_ab ∖ J' = S_a ⊔ S_b` such that every vertex of `V_b` has even `S_a`-degree and every vertex of
`V_a` has even `S_b`-degree." -/
theorem par : EG.Spec.ParStatement := by
  intro V _ E Va Vb hVab hbip J' hJ
  refine ⟨card_le_oddComps hVab hbip hJ, ?_, exists_par_partition hVab hbip hJ⟩
  have h := two_mul_card_oddComps_le hVab hbip
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast (by omega : (oddComps E).card * 2 ≤ (edgeVerts E).card)

end EG
