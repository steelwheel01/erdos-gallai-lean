module

public import EG.Defs.Vortex
public import EG.Defs.Graph

/-!
# The fixed data of Lemma PV (manuscript s4:lemPV)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s4.tex`, Lemma [s4:lemPV]: "Let `Z` be a set of `N ≥ N_0` vertices and
`L := log₂N`. Put `J := ⌊log₂(L/8)⌋`, `m := ⌈L^6⌉`, `b := ⌈2^7L^2m⌉`, `t := 2^9L^8`. The
following data are fixed (not random):
* a spanning `(2^{-6},s_O)`-expander `O` on `Z` with `2m ≤ s_O`, and sets `A(w) ⊆ N_O(w)`
  (`w ∈ Z`) with `|A(w)| = m` such that every vertex lies in at most `b` of them …;
* pairwise edge-disjoint graphs `R_{j,c}` (`0 ≤ j < J`, `c ∈ [4]`) and `M` on `Z`, the *own
  classes*, each a spanning `(2^{-6},s')`-expander on `Z` with `s' ≥ 2^{145}L^{41}`;
* a partition `Z = Rt ⊔ Pl` into *rooted* and *parentless* vertices;
* an external phase map `ext : Z → [4] ∪ {*}`."

`PVData V` is the **canonical record** of these data (TRIAGE §2.8, decision PV-DATA-RECORD, P2-D
[light] fix round 1, review item MINOR-2): the s4 PV Spec takes a `D : PVData V` and states its
hypotheses (expansion, `A`-family, edge-disjointness, partition, (E1')) about the fields; the s5
instantiation `EG.Light.childData ω Z : PVData V` ([s5:lemChild]) is passed to it with no bridge.

Encodings (blueprint_s4 PV-OWNCLASS-INDEX, PV-EXT-ENCODING):
* the own classes `R_{j,c}` are indexed by `Fin (pvJ Z.card) × Fin 4`, where `Z` is the
  vertex-set **field** (not `O.card`): `J` is not a datum but the run parameter
  `EG.Vortex.pvJ N = ⌊log₂(L/8)⌋₊` at `N = |Z|`, so it is not a field; the Stage-1 colouring
  indexes its named own classes by the same `pvJ` (`EG.Stage1.JY`), so the s5 instance needs no
  cast;
* `ext : V → Option (Fin 4)`, `none` = `*`, phases `c ∈ [4]` as `Fin 4`;
* `m`, `b` are `EG.Vortex.pvM Z.card`, `EG.Vortex.pvB Z.card` (not fields);
* the expansion parameters `s_O`, `s'` are fields (`sO`, `sOwn`), since the hypotheses
  `2m ≤ s_O`, `s' ≥ 2^{145}L^{41}` are about them.
A plain record: every constraint of the lemma is a hypothesis of the Spec, not part of the type.
-/

@[expose] public section

namespace EG.Vortex

/-- [s4:lemPV] the fixed (not random) data of Lemma PV: the vertex set `Z`; the graph `O` and its
expansion parameter `s_O` ("a spanning `(2^{-6},s_O)`-expander `O` on `Z`"); the sets `A(w)`
(`w ∈ Z`); the own classes `R_{j,c}` (`0 ≤ j < J`, `c ∈ [4]`, `J = pvJ |Z|`) and `M` with their
expansion parameter `s'`; the partition `Z = Rt ⊔ Pl`; the external phase map
`ext : Z → [4] ∪ {*}` (`none` = `*`). -/
structure PVData (V : Type*) where
  /-- the vertex set `Z` of the run -/
  Z : Finset V
  /-- the graph `O` ("a spanning `(2^{-6},s_O)`-expander `O` on `Z`") -/
  O : FGraph V
  /-- the expansion parameter `s_O` of `O` -/
  sO : ℝ
  /-- the sets `A(w) ⊆ N_O(w)`, `w ∈ Z` -/
  A : V → Finset V
  /-- the own classes `R_{j,c}`, `0 ≤ j < J := ⌊log₂(L/8)⌋ = pvJ |Z|`, `c ∈ [4]` -/
  R : Fin (pvJ Z.card) × Fin 4 → FGraph V
  /-- the own class `M` -/
  M : FGraph V
  /-- the expansion parameter `s'` of the own classes -/
  sOwn : ℝ
  /-- the rooted vertices `Rt` -/
  Rt : Finset V
  /-- the parentless vertices `Pl` -/
  Pl : Finset V
  /-- the external phase map `ext : Z → [4] ∪ {*}` (`none` = `*`) -/
  ext : V → Option (Fin 4)

end EG.Vortex
