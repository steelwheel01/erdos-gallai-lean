module

public import EG.Defs.Graph
public import EG.Defs.Orient
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Clusters, admissible orientations, excess, load, median orientation (manuscript s6:defCluster)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Definition [s6:defCluster] (clusters), quoted in full in the docstrings below.
Design note: `formal/work/p2d/chain.md`.

Representation (TRIAGE §2.9 "Clusters: G-free and indexed by `Fin N` with a layer map.
Admissibility is balance at hubs (never `IsBalanced`)"):
* `EG.Chain.Cluster V`: hubs `A_𝒦`, ports `U_𝒦`, beads `B_𝒦` together with the axioms of the
  definition. The cluster does not mention the input graph `G`: "`B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])`" is
  split into the G-free part (every bead is a non-loop with both ends in `A_𝒦 ∪ U_𝒦`, fields
  `loopless`, `ends_mem`) and the inclusion `B_𝒦 ⊆ E(G)`, which is a hypothesis wherever the
  manuscript uses `G` (e.g. `EG.Chain.HccpData.Valid.beads_G`);
* `Cluster.verts` (`V(𝒦)`), `Cluster.portBeads` (`B_𝒦[U_𝒦]`), `Cluster.beadCount` (`b(𝒦)`, a real
  number, since `deg/2` is a half-integer in general), `Cluster.ParityClean`;
* `Cluster.IsAdmissible O`: `O` is an acyclic orientation of `B_𝒦`, balanced at every **hub**
  (pointwise `outDeg`/`inDeg` on the hubs; ports are unbalanced by design, so `EG.IsBalanced`
  must not be used, CONVENTIONS "Orientations");
* `EG.Chain.exc O u` (`exc(u) ∈ ℤ`), `excPos` / `excNeg` (`exc(u)^+`, `exc(u)^-` as natural
  numbers), `Cluster.load` (`Φ(𝒦)`); the manuscript suppresses the orientation in `exc(u)` and
  `Φ(𝒦)`, here it is an explicit argument;
* the median orientation `MED(≺)` as `Cluster.medOrient rk`, where the linear order `≺` on `U_𝒦`
  is given by a rank `rk : V → ℕ` (`u ≺ v` iff `rk u < rk v`; injective on `U_𝒦` in every
  statement about `MED`). Every linear order of a finite set is of this form. The definition is
  total; the manuscript defines `MED(≺)` only for parity-clean clusters and linear orders, and
  Lemma MED ([s6:lemMED]) is stated under those hypotheses.
-/

@[expose] public section

namespace EG.Chain

variable {V : Type*}

/-- [s6:defCluster] "A *cluster* is a triple `𝒦 = (A_𝒦, U_𝒦, B_𝒦)` with the following parts.
* `A_𝒦` (the *hubs* of `𝒦`) and `U_𝒦` (the *ports* of `𝒦`) are disjoint vertex sets. Put
  `V(𝒦) := A_𝒦 ∪ U_𝒦`.
* `B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])` is the set of *beads*. No bead has both ends in `A_𝒦`."

G-free encoding (TRIAGE §2.9, blueprint note CL-G-FREE): "`B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])`" is recorded
as "every bead is a non-loop (`G` is simple) with both ends in `A_𝒦 ∪ U_𝒦`"; the remaining part
`B_𝒦 ⊆ E(G)` is a separate hypothesis where the input graph matters (HCC-P:
`HccpData.Valid.beads_G`).

Generalization (harmless): the manuscript's "vertex sets" are subsets of `V(G)`; here the hubs and
ports are not required to lie in `V(G)` (nor, in `HccpData.Valid`, the junction sets `T_j`). All
conclusions about clusters and HCC-P systems concern edges only, and the ends of beads and of path
edges lie in `V(G)` anyway (`beads_G`, `path_G`), so this only admits extra isolated junk
vertices. -/
@[ext]
structure Cluster (V : Type*) where
  /-- The hubs `A_𝒦`. -/
  hubs : Finset V
  /-- The ports `U_𝒦`. -/
  ports : Finset V
  /-- The beads `B_𝒦`. -/
  beads : Finset (Sym2 V)
  /-- "`A_𝒦` ... and `U_𝒦` ... are disjoint vertex sets." -/
  disjoint : Disjoint hubs ports
  /-- Beads are edges of the simple graph `G`, hence not loops. -/
  loopless : ∀ e ∈ beads, ¬ e.IsDiag
  /-- "`B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])`": both ends of a bead lie in `A_𝒦 ∪ U_𝒦`. -/
  ends_mem : ∀ e ∈ beads, ∀ v ∈ e, v ∈ hubs ∨ v ∈ ports
  /-- "No bead has both ends in `A_𝒦`." -/
  no_hub_hub : ∀ e ∈ beads, ¬ ∀ v ∈ e, v ∈ hubs

/-- [s6:defCluster] "Given an admissible orientation, put for every port `u`
`exc(u) := d⁺(u) − d⁻(u)`." The excess of `u` in the arc set `O` (an integer). It depends only on
the orientation `O` (the manuscript suppresses `O` in the notation); it is defined for every
vertex, and the manuscript reads it only at ports. -/
def exc [DecidableEq V] (O : Finset (V × V)) (u : V) : ℤ :=
  (outDeg O u : ℤ) - (inDeg O u : ℤ)

/-- [s6:defCluster] "`exc(u)^+ := max(exc(u), 0)`", as a natural number (`Int.toNat x` is
`max x 0`, see `EG.Chain.excPos_cast`). -/
def excPos [DecidableEq V] (O : Finset (V × V)) (u : V) : ℕ := (exc O u).toNat

/-- [s6:defCluster] "`exc(u)^- := max(−exc(u), 0)`", as a natural number (see
`EG.Chain.excNeg_cast`). -/
def excNeg [DecidableEq V] (O : Finset (V × V)) (u : V) : ℕ := (-exc O u).toNat

namespace Cluster

variable [DecidableEq V] (K : Cluster V)

/-- [s6:defCluster] "Put `V(𝒦) := A_𝒦 ∪ U_𝒦`." -/
def verts : Finset V := K.hubs ∪ K.ports

/-- [s6:defCluster] `B_𝒦[U_𝒦]`: the beads with both ends in `U_𝒦` (the port–port beads); its
cardinality is `e(B_𝒦[U_𝒦])`. -/
def portBeads : Finset (Sym2 V) := K.beads.filter (fun e => e ∈ K.ports.sym2)

/-- [s6:defCluster] "The *bead count* is `b(𝒦) := ∑_{h∈A_𝒦} deg_{B_𝒦}(h)/2 + e(B_𝒦[U_𝒦])`."
A real number (a half-integer in general); it is a natural number when `𝒦` is parity-clean
(`EG.Chain.Cluster.beadCount_eq_natCast`). -/
noncomputable def beadCount : ℝ :=
  (∑ h ∈ K.hubs, (degE K.beads h : ℝ) / 2) + ((K.portBeads.card : ℕ) : ℝ)

/-- [s6:defCluster] "The cluster `𝒦` is *parity-clean* if every hub has even `B_𝒦`-degree." -/
def ParityClean : Prop := ∀ h ∈ K.hubs, Even (degE K.beads h)

instance : Decidable K.ParityClean := inferInstanceAs (Decidable (∀ h ∈ K.hubs, _))

/-- [s6:defCluster] "An *admissible orientation* of `𝒦` is an acyclic orientation of `B_𝒦` in
which every hub `h` has `d⁺(h) = d⁻(h)`." Balance is required at the hubs only (not at the ports),
so this is not `EG.IsBalanced` (CONVENTIONS, "Orientations"). -/
structure IsAdmissible (O : Finset (V × V)) : Prop where
  /-- `O` is an orientation of `B_𝒦` (every bead receives exactly one direction). -/
  orient : IsOrientation K.beads O
  /-- `O` is acyclic. -/
  acyclic : IsAcyclic O
  /-- "every hub `h` has `d⁺(h) = d⁻(h)`". -/
  hub_bal : ∀ h ∈ K.hubs, outDeg O h = inDeg O h

/-- [s6:defCluster] "define the *load* `Φ(𝒦) := ∑_{u∈U_𝒦} exc(u)^+`" (for the admissible
orientation `O`, which the manuscript suppresses in the notation). -/
def load (O : Finset (V × V)) : ℕ := ∑ u ∈ K.ports, excPos O u

/-- [s6:defCluster] The `B_𝒦`-neighbours of a vertex `h`: the vertices `w` of `𝒦` with
`hw ∈ B_𝒦`. (Every end of a bead lies in `V(𝒦)`, so this is the set of all `w` with
`hw ∈ B_𝒦`.) For a hub these are "its `B_𝒦`-neighbours `u_1 ≺ … ≺ u_{2d}`"; their number is
`deg_{B_𝒦}(h)` (`EG.Chain.Cluster.card_beadNbrs`). -/
def beadNbrs (h : V) : Finset V := K.verts.filter (fun w => s(h, w) ∈ K.beads)

/-- [s6:defCluster] The position `i` of the neighbour `u = u_i` in the increasing list `u_1 ≺ … ≺ u_{2d}` of the
`B_𝒦`-neighbours of the hub `h`: the number of neighbours `w` with `rk w ≤ rk u` (for `rk`
injective on the ports, `≺` is the order `rk w < rk u`). -/
def medPos (rk : V → ℕ) (h u : V) : ℕ := ((K.beadNbrs h).filter (fun w => rk w ≤ rk u)).card

/-- [s6:defCluster] The rule of the median orientation for the arc `x → y` (for a bead `xy`):
* `x` a port, `y` a hub, `x = u_i` with `i ≤ d` (i.e. `2i ≤ 2d = #neighbours of y`);
* `x` a hub, `y` a port, `y = u_i` with `i > d`;
* `x`, `y` ports with `x ≺ y`. -/
def medRule (rk : V → ℕ) (x y : V) : Prop :=
  (x ∈ K.ports ∧ y ∈ K.hubs ∧ 2 * K.medPos rk y x ≤ (K.beadNbrs y).card) ∨
  (x ∈ K.hubs ∧ y ∈ K.ports ∧ (K.beadNbrs x).card < 2 * K.medPos rk x y) ∨
  (x ∈ K.ports ∧ y ∈ K.ports ∧ rk x < rk y)

instance (rk : V → ℕ) (x y : V) : Decidable (K.medRule rk x y) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- [s6:defCluster] "Let `𝒦` be parity-clean and let `≺` be a linear order on `U_𝒦`. The *median
orientation* `MED(≺)` orients `B_𝒦` as follows.
* At a hub `h` with `B_𝒦`-neighbours `u_1 ≺ u_2 ≺ … ≺ u_{2d}`, it orients `u_i → h` for `i ≤ d`
  and `h → u_i` for `i > d`. These neighbours are ports, since no bead joins two hubs.
* A port–port bead `uv` with `u ≺ v` is oriented `u → v` (`≺`-upwards)."

The linear order `≺` is given by the rank `rk` (`u ≺ v` iff `rk u < rk v`). The arc `x → y` is in
`MED(≺)` iff `xy` is a bead and `EG.Chain.Cluster.medRule` holds; `u_i` is the neighbour with
`medPos = i`. Total: for a cluster that is not parity-clean, or `rk` not injective on the ports,
the value is some arc set on which Lemma MED claims nothing. -/
def medOrient (rk : V → ℕ) : Finset (V × V) :=
  (K.verts ×ˢ K.verts).filter (fun a => s(a.1, a.2) ∈ K.beads ∧ K.medRule rk a.1 a.2)

end Cluster

end EG.Chain
