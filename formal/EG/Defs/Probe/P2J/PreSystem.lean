module

public import EG.Defs.Chain.HCCP

/-!
# HCC-P systems before routing; junction pairs (manuscript s6:lemJSLC, Step 6)

NEW Defs file of probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`).
Namespace `EG.Chain.HccpData` (it extends the locked `EG.Chain.HccpData` of
`EG.Defs.Chain.HCCP`, which it does not change).

Why a new file. In the proof of Lemma JS-LC [s6:lemJSLC] the systems of a pair `(Y,l)` are built
(Steps 4 and 5) **before** their path families exist: the junction pairs are formed from the
layers, the excesses and the padding (Step 6), their multiplicity is checked, and only then are
the paths routed (joint-routing claim (d)) and Lemma HCC-P applied (Step 7). The locked
`EG.Chain.HccpData.Valid` bundles the hypotheses of HCC-P *including* (JC-P), which mentions the
paths. The joint-routing checks of Step 6 (claim (a): "The bijections exist", distinct pair ends;
claim (c): the joint multiplicity) need exactly the hypotheses of HCC-P that do not mention the
paths. They are `HccpData.PreValid` below: the fields of `HccpData.Valid` other than those of
(JC-P), copied with the same names and the same quoted text; the field `P` of the data is not read.

Manuscript v6.1, proof of [s6:lemJSLC], Step 6: "The *systems of `(Y,l)`* are `𝒮_0(Y,l)` (if
non-empty) and the cherry classes `𝒮_i(Y,l)`. For a system `𝒮` of depth `k_𝒮` and a junction
`j < k_𝒮`, its *junction-`j` pairs* are the pairs of a fixed bijection between two multisets:
* if `k_𝒮 ≥ 2`: the out-units of layer `j` (`dem⁻(u)` copies of each `u ∈ LayP_j`) and the
  in-units of layer `j+1` modulo `k_𝒮` (`dem⁺(v)` copies of each `v ∈ LayP_{j+1}`);
* if `k_𝒮 = 1` and `j = 0`: `exc(u)^-` copies of each `u ∈ X^out` and `exc(v)^+` copies of each
  `v ∈ X^in`.
Let `𝔓_j(Y,l)` be the multiset union of the junction-`j` pairs of all systems of `(Y,l)` of depth
`> j`."

* `HccpData.junctionOcc S j u` is the number of junction-`j` pairs of the system `S` that contain
  the vertex `u` (with multiplicity): `[u ∈ LayP_j]·dem⁻(u) + [u ∈ LayP_{j+1}]·dem⁺(u)`, and `0`
  if `j ≥ k_𝒮` (no junction `j`). For `k_𝒮 = 1` (so `LayP_{j+1} = LayP_0`, and `pad ≡ 0` by
  `PreValid.pad_k1`) this is `exc(u)^- + exc(u)^+`, which is the number of copies of `u` in the
  two multisets of the `k = 1` clause (`u ∈ X^out` iff `exc(u) < 0`, `u ∈ X^in` iff `exc(u) > 0`).
  The two ends of a pair are distinct (claim (a); `EG.Spec.JslcPairsDistinctStatement`), so this
  is also the number of pairs containing `u`, as in "every vertex lies in at most `t` pairs"
  (Definition 7 of B–M, `EG.FGraph.IsPathConnected`).
* `HccpData.IsPort S u`: `u` is a port of some cluster of `S` ("a port of `𝒮`").
-/

@[expose] public section

namespace EG.Chain

namespace HccpData

variable {V : Type*} [DecidableEq V] (S : HccpData V)

/-- [s6:lemJSLC] (proof, Step 6) "`u` is a port of the system `𝒮`": a port of one of its
clusters (`u ∈ ⋃_j LayP_j`). -/
def IsPort (u : V) : Prop := ∃ i, u ∈ (S.K i).ports

/-- [s6:lemJSLC] (proof, Step 6) the number of junction-`j` pairs of the system `S` in which the
vertex `u` occurs: "the out-units of layer `j` (`dem⁻(u)` copies of each `u ∈ LayP_j`) and the
in-units of layer `j+1` modulo `k_𝒮` (`dem⁺(v)` copies of each `v ∈ LayP_{j+1}`)", and for
`k_𝒮 = 1`, `j = 0`, "`exc(u)^-` copies of each `u ∈ X^out` and `exc(v)^+` copies of each
`v ∈ X^in`" (the same number, since `pad ≡ 0` for `k = 1`); `0` if `j ≥ k_𝒮` ("systems of depth
`> j`"). -/
def junctionOcc (j : ℕ) (u : V) : ℕ :=
  if h : j < S.k then
    (if u ∈ S.layP ⟨j, h⟩ then S.demMinus u else 0) +
      (if u ∈ S.layP (S.succ ⟨j, h⟩) then S.demPlus u else 0)
  else 0

/-- [s6:lemHCCP] The hypotheses of Lemma HCC-P that do not mention the path families `𝒫_j`
(everything except (JC-P)), for the data `S` and the input graph `G`: "Let `k ≥ 1` ... each
cluster with a fixed admissible orientation ... *Junction sets* `T_0, …, T_{k-1}`: pairwise
disjoint vertex sets. A *padding* `pad : ⋃_j LayP_j → ℤ_{≥0}`, with `pad ≡ 0` if `k = 1`. ...
Assume: (D) the sets `A_𝒦` and `U_𝒦` (over all clusters of all layers) and `T_0, …, T_{k-1}` are
pairwise disjoint; (P) every cluster is parity-clean". The fields are those of
`EG.Chain.HccpData.Valid` with the same names (so `Valid G → PreValid G` field by field); the
data field `P` is not read. This is the state of a system of JS-LC after Steps 4–5 and before the
routing of Step 6. -/
structure PreValid (G : FGraph V) : Prop where
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

end HccpData

end EG.Chain
