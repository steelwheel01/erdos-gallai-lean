module

public import EG.Defs.Chain.Cluster
public import EG.Defs.Walk

/-!
# Data of Lemma HCC-P: layered cluster systems with path junctions (manuscript s6:lemHCCP)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Lemma [s6:lemHCCP] (HCC-P, layered hub-cluster chaining with path junctions).
The data and hypotheses of the lemma are bundled as `EG.Chain.HccpData V` (the data) and
`EG.Chain.HccpData.Valid S G` (the hypotheses, for the input graph `G`); the conclusions are the
Spec (`EG.Spec.HccpStatement`, not in this file). Design note: `formal/work/p2d/chain.md`.

Encoding decisions (TRIAGE §2.9 "HCC-P: uniform in k, with `succ j := (j+1) mod k`. Path families
are `List (List V)`"; blueprint notes HCCP-*):
* the layers `𝒦_0, …, 𝒦_{k-1}` ("finite families of clusters, each cluster with a fixed admissible
  orientation") are one indexed family `K : Fin N → Cluster V` of clusters with orientations
  `O : Fin N → Finset (V × V)` and a layer map `lay : Fin N → Fin k`; hypothesis (D) is stated for
  distinct *indices* (a family may repeat a cluster, e.g. an empty one);
* the padding `pad : ⋃_j LayP_j → ℤ_{≥0}` is a function `V → ℕ` whose values off the ports are
  never read;
* `exc(u)` of a port `u` is the excess in the orientation of the (under (D) unique) cluster
  containing `u` (`HccpData.pexc`);
* indices of layers and junction sets are taken modulo `k` (`HccpData.succ`); the case `k = 1` is
  the uniform reading with `succ 0 = 0` and `pad ≡ 0`. Its equivalence with the manuscript's
  explicit `k = 1` reading ("from `X^out` to `X^in`; `u ∈ X^out` starts exactly `exc(u)^-` paths
  and `v ∈ X^in` ends exactly `exc(v)^+` paths") is proved in `EG.Lib.Chain.HCCP`
  (`EG.Chain.HccpData.jcp_iff_jcpOne`);
* the path families `𝒫_j` are lists of vertex lists (a family, counted with multiplicity);
  `E(𝒫_j)` is `HccpData.pathEdges j`.

Usage note: for a concrete system `S`, the index type `Fin S.k` has no numeral instances
(`S.Phi 0` does not elaborate); write `S.Phi (0 : Fin 2)` (with `S.k` reducing to `2`), and check
equalities of indices through their values (`(S.succ (1 : Fin 2)).val = 0 := rfl`), since `decide`
does not see through `Fin S.k`; a filter such as `univ.filter (S.lay · = j)` finds its
`DecidablePred` instance only for `j` at type `Fin S.k` (e.g. `(⟨0, by decide⟩ : Fin S.k)`), not
for `(0 : Fin 2)`. The common padded load `Φ` of a system has no accessor: state it as
`∃ Φ, ∀ j, S.Phi j = Φ` (unique for `k ≥ 1`, `EG.Chain.HccpData.eq_of_forall_Phi_eq`).
-/

@[expose] public section

namespace EG.Chain

variable {V : Type*}

/-- [s6:lemHCCP] The data of Lemma HCC-P: "Let `k ≥ 1`, and suppose the following data are given.
* *Layers* `𝒦_0, …, 𝒦_{k-1}`: finite families of clusters, each cluster with a fixed admissible
  orientation. Put `LayP_j := ⋃_{𝒦∈𝒦_j} U_𝒦`.
* *Junction sets* `T_0, …, T_{k-1}`: pairwise disjoint vertex sets.
* A *padding* `pad : ⋃_j LayP_j → ℤ_{≥0}`, with `pad ≡ 0` if `k = 1`."
together with the path families `𝒫_j` of hypothesis (JC-P) ("for each `j` there is a family
`𝒫_j` of pairwise edge-disjoint paths of `G` ..."). The families are data because conclusion
(ii) refers to `E(𝒫_j)`. All conditions (admissibility, disjointness, `k ≥ 1`, ...) are in
`EG.Chain.HccpData.Valid`. -/
structure HccpData (V : Type*) where
  /-- The number `k` of layers. -/
  k : ℕ
  /-- The number of clusters (over all layers). -/
  N : ℕ
  /-- The clusters `𝒦_i`, `i < N`, of all layers. -/
  K : Fin N → Cluster V
  /-- The fixed (admissible) orientation of each cluster. -/
  O : Fin N → Finset (V × V)
  /-- The layer of each cluster: `𝒦_i ∈ 𝒦_{lay i}`. -/
  lay : Fin N → Fin k
  /-- The junction sets `T_0, …, T_{k-1}`. -/
  T : Fin k → Finset V
  /-- The padding (read only at ports). -/
  pad : V → ℕ
  /-- The path families `𝒫_0, …, 𝒫_{k-1}` of (JC-P). -/
  P : Fin k → List (List V)

namespace HccpData

variable (S : HccpData V)

/-- [s6:lemHCCP] "Indices of layers and junction sets are taken modulo `k`": `j + 1 mod k`. -/
def succ (j : Fin S.k) : Fin S.k :=
  ⟨(j.1 + 1) % S.k, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2)⟩

variable [DecidableEq V]

/-- [s6:lemHCCP] "Put `LayP_j := ⋃_{𝒦∈𝒦_j} U_𝒦`." -/
def layP (j : Fin S.k) : Finset V :=
  (Finset.univ.filter (fun i => S.lay i = j)).biUnion (fun i => (S.K i).ports)

/-- [s6:lemHCCP] `exc(u)` for a port `u`: the excess `d⁺(u) − d⁻(u)` in the fixed admissible
orientation of the cluster containing `u` (unique by (D); in general the sum over all clusters
having `u` as a port). -/
def pexc (u : V) : ℤ :=
  ∑ i : Fin S.N, if u ∈ (S.K i).ports then exc (S.O i) u else 0

/-- [s6:lemHCCP] "Define the demands `dem⁻(u) := exc(u)^- + pad(u)`". -/
def demMinus (u : V) : ℕ := (-S.pexc u).toNat + S.pad u

/-- [s6:lemHCCP] "... and `dem⁺(u) := exc(u)^+ + pad(u)`". -/
def demPlus (u : V) : ℕ := (S.pexc u).toNat + S.pad u

/-- [s6:lemHCCP] "the padded loads `Φ_j := ∑_{u∈LayP_j} dem⁺(u)`". -/
def Phi (j : Fin S.k) : ℕ := ∑ u ∈ S.layP j, S.demPlus u

/-- [s6:lemHCCP] "For `k = 1` put `X^out := {u ∈ LayP_0 : exc(u) < 0}`" (here for any layer
`j`; the manuscript uses it only for `k = 1`, `j = 0`). -/
def xOut (j : Fin S.k) : Finset V := (S.layP j).filter (fun u => S.pexc u < 0)

/-- [s6:lemHCCP] "... and `X^in := {u ∈ LayP_0 : exc(u) > 0}`" (for any layer `j`; used only for
`k = 1`, `j = 0`). -/
def xIn (j : Fin S.k) : Finset V := (S.layP j).filter (fun u => 0 < S.pexc u)

/-- [s6:lemHCCP] `E(𝒫_j)`: the set of edges of the paths of `𝒫_j`. -/
def pathEdges (j : Fin S.k) : Finset (Sym2 V) := ((S.P j).flatMap walkEdges).toFinset

/-- [s6:lemHCCP] `E(𝒫_0) ∪ … ∪ E(𝒫_{k-1})`: all path edges of the system (used by the input-level
disjointness hypothesis of the union lemma [s6:lemHCCglob], TRIAGE §1b GLOB-OUTPUT-LEVEL-HYP). -/
def allPathEdges : Finset (Sym2 V) := Finset.univ.biUnion S.pathEdges

/-- [s6:lemHCCP] `⋃_𝒦 B_𝒦`: all beads of all clusters of all layers. -/
def beads : Finset (Sym2 V) := Finset.univ.biUnion (fun i => (S.K i).beads)

/-- [s6:lemHCCP] The hypotheses of Lemma HCC-P for the data `S` and the input graph `G`:
"Let `k ≥ 1` ... each cluster with a fixed admissible orientation ... *Junction sets*
`T_0, …, T_{k-1}`: pairwise disjoint vertex sets. A *padding* `pad : ⋃_j LayP_j → ℤ_{≥0}`, with
`pad ≡ 0` if `k = 1`. ... Assume:
* (D) the sets `A_𝒦` and `U_𝒦` (over all clusters of all layers) and `T_0, …, T_{k-1}` are
  pairwise disjoint;
* (P) every cluster is parity-clean;
* (JC-P) for each `j` there is a family `𝒫_j` of pairwise edge-disjoint paths of `G` with the
  following properties.
  - Each path runs from a vertex of `LayP_j` to a vertex of `LayP_{j+1}`; for `k = 1`, from
    `X^out` to `X^in`.
  - All interior vertices of each path lie in `T_j`.
  - Every `u ∈ LayP_j` is the first vertex of exactly `dem⁻(u)` paths of `𝒫_j`, and every
    `v ∈ LayP_{j+1}` is the last vertex of exactly `dem⁺(v)` paths of `𝒫_j`. For `k = 1` this
    reads: `u ∈ X^out` starts exactly `exc(u)^-` paths and `v ∈ X^in` ends exactly `exc(v)^+`
    paths.

  The edge sets `E(𝒫_0), …, E(𝒫_{k-1})` and all bead sets `B_𝒦` are pairwise disjoint."
Clusters are subsets of the input graph: "`B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])`" ([s6:defCluster]) gives
`beads_G` (the rest is part of `EG.Chain.Cluster`). (D) for the hubs and ports of one cluster is
the field `Cluster.disjoint`. For `k = 1` the fields `path_ends`, `starts`, `ends` are the uniform
reading (`succ 0 = 0`, `pad = 0`); `EG.Chain.HccpData.jcp_iff_jcpOne` proves that it is equivalent
to the manuscript's `k = 1` reading. -/
structure Valid (G : FGraph V) : Prop where
  /-- "Let `k ≥ 1`". -/
  k_pos : 1 ≤ S.k
  /-- "each cluster with a fixed admissible orientation". -/
  adm : ∀ i, (S.K i).IsAdmissible (S.O i)
  /-- `B_𝒦 ⊆ E(G)` (from "`B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])`", [s6:defCluster]). -/
  beads_G : ∀ i, (S.K i).beads ⊆ G.edges
  /-- "*Junction sets* `T_0, …, T_{k-1}`: pairwise disjoint vertex sets"; part of (D). -/
  T_disj : ∀ j j', j ≠ j' → Disjoint (S.T j) (S.T j')
  /-- "`pad ≡ 0` if `k = 1`" (on its domain `⋃_j LayP_j`). -/
  pad_k1 : S.k = 1 → ∀ j, ∀ u ∈ S.layP j, S.pad u = 0
  /-- (D) for two different clusters: their hub and port sets are pairwise disjoint. -/
  D_KK : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts
  /-- (D) for a cluster and a junction set. -/
  D_KT : ∀ i j, Disjoint (S.K i).verts (S.T j)
  /-- (P) "every cluster is parity-clean". -/
  parityClean : ∀ i, (S.K i).ParityClean
  /-- (JC-P) "paths of `G`". -/
  path_G : ∀ j, ∀ p ∈ S.P j, IsPathIn G.edges p
  /-- (JC-P) "Each path runs from a vertex of `LayP_j` to a vertex of `LayP_{j+1}`". -/
  path_ends : ∀ j, ∀ p ∈ S.P j,
    (∃ u ∈ S.layP j, p.head? = some u) ∧ (∃ v ∈ S.layP (S.succ j), p.getLast? = some v)
  /-- (JC-P) "All interior vertices of each path lie in `T_j`." -/
  path_T : ∀ j, ∀ p ∈ S.P j, IsThrough (S.T j) p
  /-- (JC-P) "Every `u ∈ LayP_j` is the first vertex of exactly `dem⁻(u)` paths of `𝒫_j`". -/
  starts : ∀ j, ∀ u ∈ S.layP j, (S.P j).countP (fun p => p.head? = some u) = S.demMinus u
  /-- (JC-P) "every `v ∈ LayP_{j+1}` is the last vertex of exactly `dem⁺(v)` paths of `𝒫_j`". -/
  ends : ∀ j, ∀ v ∈ S.layP (S.succ j),
    (S.P j).countP (fun p => p.getLast? = some v) = S.demPlus v
  /-- (JC-P) "a family `𝒫_j` of pairwise edge-disjoint paths" (distinct members of the family,
  i.e. distinct positions of the list, share no edge). -/
  path_edisj : ∀ j, (S.P j).Pairwise (fun p q => (walkEdges p).Disjoint (walkEdges q))
  /-- (JC-P) "The edge sets `E(𝒫_0), …, E(𝒫_{k-1})` ... are pairwise disjoint". -/
  pp_disj : ∀ j j', j ≠ j' → Disjoint (S.pathEdges j) (S.pathEdges j')
  /-- (JC-P) "The edge sets `E(𝒫_j)` and all bead sets `B_𝒦` are pairwise disjoint" (paths
  against beads). -/
  pb_disj : ∀ j i, Disjoint (S.pathEdges j) (S.K i).beads
  /-- (JC-P) "... all bead sets `B_𝒦` are pairwise disjoint" (beads of two different clusters;
  also implied by (D)). -/
  bb_disj : ∀ i i', i ≠ i' → Disjoint (S.K i).beads (S.K i').beads

end HccpData

end EG.Chain
