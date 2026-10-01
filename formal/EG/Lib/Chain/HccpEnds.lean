module

public import EG.Lib.Chain.HCCP
public import EG.Lib.Chain.MedExc

/-!
# HCC-P: path ends and demands (companion of `EG.Defs.Chain.HCCP`)

Probe unit P2E (probe P-2, part 1), proof round 1.
* a vertex outside `LayP_j` is the first vertex of no path of `𝒫_j`, a vertex outside
  `LayP_{j+1}` is the last vertex of none (`Valid.countP_head_eq`, `Valid.countP_last_eq`:
  exact counts `dem⁻`/`dem⁺` or `0`);
* `max(dem⁻(u), dem⁺(u)) = |exc(u)| + pad(u)` (`max_demMinus_demPlus`);
* under (D) and admissibility, `|exc(u)| ≤ deg_{B_𝒦}(u)` for a port `u` of `𝒦`
  (`Valid.natAbs_pexc_le`, from Lemma MED (b)).
-/

public section

namespace EG.Chain

namespace HccpData

variable {V : Type*} [DecidableEq V]

/-- Counting with a disjunction: `#{p : P ∨ Q} ≤ #{p : P} + #{p : Q}`. -/
theorem countP_or_le {α : Type*} (l : List α) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] :
    l.countP (fun a => decide (P a ∨ Q a)) ≤
      l.countP (fun a => decide (P a)) + l.countP (fun a => decide (Q a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ] at ih ⊢ <;> omega

variable {G : FGraph V} {S : HccpData V}

/-- The number of paths of `𝒫_j` starting at `u`: `dem⁻(u)` on `LayP_j`, `0` elsewhere. -/
theorem Valid.countP_head_eq (hS : S.Valid G) (j : Fin S.k) (u : V) :
    (S.P j).countP (fun p => decide (p.head? = some u)) =
      if u ∈ S.layP j then S.demMinus u else 0 := by
  split_ifs with hu
  · exact hS.starts j u hu
  · rw [List.countP_eq_zero]
    intro p hp hpu
    obtain ⟨u', hu', hpu'⟩ := (hS.path_ends j p hp).1
    have : u = u' := Option.some_inj.1 ((of_decide_eq_true hpu).symm.trans hpu')
    exact hu (this ▸ hu')

/-- The number of paths of `𝒫_j` ending at `v`: `dem⁺(v)` on `LayP_{j+1}`, `0` elsewhere. -/
theorem Valid.countP_last_eq (hS : S.Valid G) (j : Fin S.k) (v : V) :
    (S.P j).countP (fun p => decide (p.getLast? = some v)) =
      if v ∈ S.layP (S.succ j) then S.demPlus v else 0 := by
  split_ifs with hv
  · exact hS.ends j v hv
  · rw [List.countP_eq_zero]
    intro p hp hpv
    obtain ⟨v', hv', hpv'⟩ := (hS.path_ends j p hp).2
    have : v = v' := Option.some_inj.1 ((of_decide_eq_true hpv).symm.trans hpv')
    exact hv (this ▸ hv')

omit [DecidableEq V] in
/-- `max(dem⁻(u), dem⁺(u)) = |exc(u)| + pad(u)` (one of `exc(u)^±` is `0`). -/
theorem max_demMinus_demPlus [DecidableEq V] (S : HccpData V) (u : V) :
    max (S.demMinus u) (S.demPlus u) = (S.pexc u).natAbs + S.pad u := by
  unfold demMinus demPlus
  omega

/-- Under (D): `|exc(u)| ≤ deg_{B_𝒦}(u)` for a port `u` of `𝒦_i` (Lemma MED (b)). -/
theorem Valid.natAbs_pexc_le (hS : S.Valid G) {i : Fin S.N} {u : V}
    (hu : u ∈ (S.K i).ports) : (S.pexc u).natAbs ≤ degE (S.K i).beads u := by
  rw [S.pexc_eq hS.D_KK hu]
  exact Cluster.natAbs_exc_le (hS.adm i).orient u

/-- [s6:lemJSLC:proof-claim-c] (engine part) "at a fixed junction a port occurs in at most
`max(dem⁻, dem⁺)` pairs of each system containing it. Centres occur in no pair": a vertex is an
end of at most `max(dem⁻(u), dem⁺(u))` paths of `𝒫_j`. For `k ≥ 2` a vertex is in at most one
of `LayP_j`, `LayP_{j+1}`; for `k = 1` the two sets coincide, `pad = 0` there, and
`exc⁻ + exc⁺ = |exc| = max(exc⁻, exc⁺)`. -/
theorem Valid.countP_end_le (hS : S.Valid G) (j : Fin S.k) (u : V) :
    (S.P j).countP (fun p => decide (p.head? = some u ∨ p.getLast? = some u)) ≤
      max (S.demMinus u) (S.demPlus u) := by
  refine (countP_or_le _ _ _).trans ?_
  rw [hS.countP_head_eq j u, hS.countP_last_eq j u]
  by_cases hk : S.k = 1
  · have hsj : S.succ j = j := S.succ_eq_self hk j
    rw [hsj]
    split_ifs with hu
    · have hp := hS.pad_k1 hk j u hu
      unfold demMinus demPlus
      rw [hp]
      omega
    · omega
  · have hne : S.succ j ≠ j := S.succ_ne_self (by have := hS.k_pos; omega) j
    have hdisj := S.layP_disjoint hS.D_KK hne
    split_ifs with h1 h2 h2
    · exact absurd h1 (Finset.disjoint_left.1 hdisj h2)
    · omega
    · omega
    · omega

end HccpData

end EG.Chain
