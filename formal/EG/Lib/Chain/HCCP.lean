module

public import EG.Defs.Chain.HCCP
public import EG.Lib.Chain.Cluster
public import EG.Lib.Found.Graph

/-!
# HCC-P data: basic API (companion of `EG.Defs.Chain.HCCP`)

* indices modulo `k`: `succ` is the identity for `k = 1` and has no fixed point for `k ≥ 2`;
* `LayP_j` membership; under (D) the layers `LayP_j` are pairwise disjoint and `pexc u` is the
  excess of `u` in the orientation of its own cluster;
* under (D), sums over `LayP_j` split over the clusters of layer `j` (`sum_layP`); the padded
  load is `Φ_j = ∑_{𝒦 ∈ 𝒦_j} Φ(𝒦) + ∑_{LayP_j} pad` (`Phi_eq_sum_load_add_pad`), and similarly for
  `∑_{LayP_j} dem⁻` (`sum_demMinus_eq`);
* `Valid.nodup_flatMap_walkEdges`: the concatenated edge list of `𝒫_j` has no repetition, so
  every edge of `E(𝒫_j)` lies on exactly one path of the family;
* the `k = 1` reading of (JC-P): `EG.Chain.HccpData.jcp_iff_jcpOne` proves that the uniform
  encoding used by `Valid` (paths from `LayP_0` to `LayP_{succ 0} = LayP_0`, counts `dem^∓`) is
  equivalent to the manuscript's explicit `k = 1` reading ("from `X^out` to `X^in`; `u ∈ X^out`
  starts exactly `exc(u)^-` paths and `v ∈ X^in` ends exactly `exc(v)^+` paths").
-/

public section

namespace EG.Chain

namespace HccpData

variable {V : Type*} (S : HccpData V)

@[simp] theorem succ_val (j : Fin S.k) : (S.succ j).val = (j.val + 1) % S.k := rfl

theorem succ_eq_self (hk : S.k = 1) (j : Fin S.k) : S.succ j = j := by
  apply Fin.ext
  have := j.2
  simp only [succ_val, hk]
  omega

theorem succ_ne_self (hk : 2 ≤ S.k) (j : Fin S.k) : S.succ j ≠ j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [succ_val] at h'
  have hj := j.2
  rcases Nat.lt_or_ge (j.val + 1) S.k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h'; omega
  · have : j.val + 1 = S.k := by omega
    rw [this, Nat.mod_self] at h'; omega

variable [DecidableEq V]

theorem mem_layP {j : Fin S.k} {u : V} : u ∈ S.layP j ↔ ∃ i, S.lay i = j ∧ u ∈ (S.K i).ports := by
  simp [layP]

theorem ports_subset_layP (i : Fin S.N) : (S.K i).ports ⊆ S.layP (S.lay i) :=
  fun _ hu => (S.mem_layP).2 ⟨i, rfl, hu⟩

/-- Under (D), different layers have disjoint port sets. -/
theorem layP_disjoint (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts)
    {j j' : Fin S.k} (hjj : j ≠ j') : Disjoint (S.layP j) (S.layP j') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  obtain ⟨i, rfl, hi⟩ := (S.mem_layP).1 hu
  obtain ⟨i', rfl, hi'⟩ := (S.mem_layP).1 hu'
  have hne : i ≠ i' := fun h => hjj (h ▸ rfl)
  exact Finset.disjoint_left.1 (hD i i' hne) ((S.K i).ports_subset_verts hi)
    ((S.K i').ports_subset_verts hi')

/-- Under (D), `exc(u)` of a port `u` of the cluster `𝒦_i` is its excess in the orientation
`O_i` ("the unique cluster containing it"). -/
theorem pexc_eq (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts)
    {i : Fin S.N} {u : V} (hu : u ∈ (S.K i).ports) : S.pexc u = exc (S.O i) u := by
  unfold pexc
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp [hu]
  · intro i' _ hne
    have : u ∉ (S.K i').ports := fun h' =>
      Finset.disjoint_left.1 (hD i i' (Ne.symm hne)) ((S.K i).ports_subset_verts hu)
        ((S.K i').ports_subset_verts h')
    simp [this]

theorem mem_pathEdges {j : Fin S.k} {e : Sym2 V} :
    e ∈ S.pathEdges j ↔ ∃ p ∈ S.P j, e ∈ walkEdges p := by
  simp [pathEdges]

theorem mem_allPathEdges {e : Sym2 V} : e ∈ S.allPathEdges ↔ ∃ j, e ∈ S.pathEdges j := by
  simp [allPathEdges]

theorem mem_beads {e : Sym2 V} : e ∈ S.beads ↔ ∃ i, e ∈ (S.K i).beads := by
  simp [beads]

theorem Valid.nodup_flatMap_walkEdges {G : FGraph V} {S : HccpData V} (hS : S.Valid G)
    (j : Fin S.k) : ((S.P j).flatMap walkEdges).Nodup :=
  List.nodup_flatMap.2 ⟨fun p hp => nodup_walkEdges (hS.path_G j p hp).nodup, hS.path_edisj j⟩

/-- The path conditions of (JC-P) for the family `𝒫_j` as encoded in `Valid` (uniform in `k`):
paths from `LayP_j` to `LayP_{j+1}`, every `u ∈ LayP_j` first vertex of exactly `dem⁻(u)` paths,
every `v ∈ LayP_{j+1}` last vertex of exactly `dem⁺(v)` paths. -/
@[expose] def JcpUniform (j : Fin S.k) : Prop :=
  (∀ p ∈ S.P j, (∃ u ∈ S.layP j, p.head? = some u) ∧
    (∃ v ∈ S.layP (S.succ j), p.getLast? = some v)) ∧
  (∀ u ∈ S.layP j, (S.P j).countP (fun p => p.head? = some u) = S.demMinus u) ∧
  (∀ v ∈ S.layP (S.succ j), (S.P j).countP (fun p => p.getLast? = some v) = S.demPlus v)

/-- The manuscript's explicit `k = 1` reading of the path conditions of (JC-P): "Each path runs
... for `k = 1`, from `X^out` to `X^in`. ... For `k = 1` this reads: `u ∈ X^out` starts exactly
`exc(u)^-` paths and `v ∈ X^in` ends exactly `exc(v)^+` paths." -/
@[expose] def JcpOne (j : Fin S.k) : Prop :=
  (∀ p ∈ S.P j, (∃ u ∈ S.xOut j, p.head? = some u) ∧ (∃ v ∈ S.xIn j, p.getLast? = some v)) ∧
  (∀ u ∈ S.xOut j, (S.P j).countP (fun p => p.head? = some u) = (-S.pexc u).toNat) ∧
  (∀ v ∈ S.xIn j, (S.P j).countP (fun p => p.getLast? = some v) = (S.pexc v).toNat)

theorem Valid.jcpUniform {G : FGraph V} {S : HccpData V} (hS : S.Valid G) (j : Fin S.k) :
    S.JcpUniform j :=
  ⟨hS.path_ends j, hS.starts j, hS.ends j⟩

/-- For `k = 1` (and `pad ≡ 0` on `LayP_0`), the uniform encoding of (JC-P) used by `Valid` is
equivalent to the manuscript's explicit `k = 1` reading. -/
theorem jcp_iff_jcpOne (hk : S.k = 1) (j : Fin S.k) (hpad : ∀ u ∈ S.layP j, S.pad u = 0) :
    S.JcpUniform j ↔ S.JcpOne j := by
  have hsj : S.succ j = j := S.succ_eq_self hk j
  unfold JcpUniform JcpOne
  rw [hsj]
  simp only [xOut, xIn, Finset.mem_filter, demMinus, demPlus]
  constructor
  · rintro ⟨hends, hst, hen⟩
    refine ⟨fun p hp => ⟨?_, ?_⟩, fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨u, hu, hpu⟩ := (hends p hp).1
      have hpos : 0 < (S.P j).countP (fun p => p.head? = some u) :=
        List.countP_pos_iff.2 ⟨p, hp, by simpa using hpu⟩
      rw [hst u hu, hpad u hu] at hpos
      exact ⟨u, ⟨hu, by omega⟩, hpu⟩
    · obtain ⟨v, hv, hpv⟩ := (hends p hp).2
      have hpos : 0 < (S.P j).countP (fun p => p.getLast? = some v) :=
        List.countP_pos_iff.2 ⟨p, hp, by simpa using hpv⟩
      rw [hen v hv, hpad v hv] at hpos
      exact ⟨v, ⟨hv, by omega⟩, hpv⟩
    · rw [hst u hu.1, hpad u hu.1]; rfl
    · rw [hen v hv.1, hpad v hv.1]; rfl
  · rintro ⟨hends, hst, hen⟩
    refine ⟨fun p hp => ⟨?_, ?_⟩, fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨u, hu, hpu⟩ := (hends p hp).1
      exact ⟨u, hu.1, hpu⟩
    · obtain ⟨v, hv, hpv⟩ := (hends p hp).2
      exact ⟨v, hv.1, hpv⟩
    · rw [hpad u hu, Nat.add_zero]
      by_cases hneg : S.pexc u < 0
      · exact hst u ⟨hu, hneg⟩
      · have h0 : (-S.pexc u).toNat = 0 := by omega
        rw [h0, List.countP_eq_zero]
        intro p hp hpu
        obtain ⟨u', hu', hpu'⟩ := (hends p hp).1
        have : u = u' := by
          have := (of_decide_eq_true hpu).symm.trans hpu'
          exact Option.some_inj.1 this
        exact hneg (this ▸ hu'.2)
    · rw [hpad v hv, Nat.add_zero]
      by_cases hpos : 0 < S.pexc v
      · exact hen v ⟨hv, hpos⟩
      · have h0 : (S.pexc v).toNat = 0 := by omega
        rw [h0, List.countP_eq_zero]
        intro p hp hpv
        obtain ⟨v', hv', hpv'⟩ := (hends p hp).2
        have : v = v' := by
          have := (of_decide_eq_true hpv).symm.trans hpv'
          exact Option.some_inj.1 this
        exact hpos (this ▸ hv'.2)

/-- Under (D), a sum over `LayP_j` splits into the sums over the port sets of the clusters of
layer `j` (the union `LayP_j = ⋃_{lay i = j} U_{𝒦_i}` is disjoint). -/
theorem sum_layP {M : Type*} [AddCommMonoid M]
    (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts) (j : Fin S.k) (f : V → M) :
    ∑ u ∈ S.layP j, f u =
      ∑ i ∈ Finset.univ.filter (fun i => S.lay i = j), ∑ u ∈ (S.K i).ports, f u := by
  unfold layP
  refine Finset.sum_biUnion ?_
  intro i _ i' _ hne
  exact Finset.disjoint_of_subset_left ((S.K i).ports_subset_verts)
    (Finset.disjoint_of_subset_right ((S.K i').ports_subset_verts) (hD i i' hne))

/-- Under (D), `dem⁺` summed over the ports of the cluster `𝒦_i` is its load `Φ(𝒦_i)` (in the
orientation `O_i`) plus the padding of its ports. -/
theorem sum_ports_demPlus (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts)
    (i : Fin S.N) :
    ∑ u ∈ (S.K i).ports, S.demPlus u = (S.K i).load (S.O i) + ∑ u ∈ (S.K i).ports, S.pad u := by
  unfold demPlus Cluster.load
  rw [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [S.pexc_eq hD hu]
  rfl

/-- Under (D), `dem⁻` summed over the ports of the cluster `𝒦_i` is `∑_{u ∈ U_{𝒦_i}} exc(u)^-`
(in the orientation `O_i`) plus the padding of its ports. -/
theorem sum_ports_demMinus (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts)
    (i : Fin S.N) :
    ∑ u ∈ (S.K i).ports, S.demMinus u =
      ∑ u ∈ (S.K i).ports, excNeg (S.O i) u + ∑ u ∈ (S.K i).ports, S.pad u := by
  unfold demMinus
  rw [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [S.pexc_eq hD hu]
  rfl

/-- The padded load in terms of the cluster loads (used by HCC-P Step 0 and JS-LC Step 4):
under (D), `Φ_j = ∑_{𝒦 ∈ 𝒦_j} Φ(𝒦) + ∑_{u ∈ LayP_j} pad(u)`. -/
theorem Phi_eq_sum_load_add_pad (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts)
    (j : Fin S.k) :
    S.Phi j = ∑ i ∈ Finset.univ.filter (fun i => S.lay i = j), (S.K i).load (S.O i) +
      ∑ u ∈ S.layP j, S.pad u := by
  unfold Phi
  rw [S.sum_layP hD j S.demPlus, S.sum_layP hD j S.pad, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => S.sum_ports_demPlus hD i

/-- The `dem⁻`-analogue of `Phi_eq_sum_load_add_pad`: under (D),
`∑_{u ∈ LayP_j} dem⁻(u) = ∑_{𝒦 ∈ 𝒦_j} ∑_{u ∈ U_𝒦} exc(u)^- + ∑_{u ∈ LayP_j} pad(u)`.
(Together with `∑_{u ∈ U_𝒦} exc(u) = 0` from Lemma MED(b) this gives `∑ dem⁻ = Φ_j`; that step
is part of the manuscript's proof and is not done here.) -/
theorem sum_demMinus_eq (hD : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts)
    (j : Fin S.k) :
    ∑ u ∈ S.layP j, S.demMinus u =
      ∑ i ∈ Finset.univ.filter (fun i => S.lay i = j), ∑ u ∈ (S.K i).ports, excNeg (S.O i) u +
        ∑ u ∈ S.layP j, S.pad u := by
  rw [S.sum_layP hD j S.demMinus, S.sum_layP hD j S.pad, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => S.sum_ports_demMinus hD i

theorem Valid.Phi_eq_sum_load_add_pad {G : FGraph V} {S : HccpData V} (hS : S.Valid G)
    (j : Fin S.k) :
    S.Phi j = ∑ i ∈ Finset.univ.filter (fun i => S.lay i = j), (S.K i).load (S.O i) +
      ∑ u ∈ S.layP j, S.pad u :=
  S.Phi_eq_sum_load_add_pad hS.D_KK j

theorem Valid.sum_demMinus_eq {G : FGraph V} {S : HccpData V} (hS : S.Valid G) (j : Fin S.k) :
    ∑ u ∈ S.layP j, S.demMinus u =
      ∑ i ∈ Finset.univ.filter (fun i => S.lay i = j), ∑ u ∈ (S.K i).ports, excNeg (S.O i) u +
        ∑ u ∈ S.layP j, S.pad u :=
  S.sum_demMinus_eq hS.D_KK j

/-- The common padded load of a system is unique when `k ≥ 1`: if all `Φ_j` equal `a` and all
equal `b`, then `a = b`. (A statement about "the common value `Φ`" of a system, e.g. the union
lemma [s6:lemHCCglob], can therefore be phrased as `∃ Φ, ∀ j, S.Phi j = Φ ∧ …` without an
accessor for `Φ`.) -/
theorem eq_of_forall_Phi_eq (hk : 1 ≤ S.k) {a b : ℕ} (ha : ∀ j, S.Phi j = a)
    (hb : ∀ j, S.Phi j = b) : a = b :=
  (ha ⟨0, hk⟩).symm.trans (hb ⟨0, hk⟩)

end HccpData

end EG.Chain
