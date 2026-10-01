module

public import EG.Defs.HB.SplitTree
public import EG.Defs.Objects
public import EG.Defs.Constants

/-!
# One round of the hierarchy `HB*^{τ+}` (manuscript s2:defHBtp, rules (R0)–(R5), (GC))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s2.tex`, Definition [s2:defHBtp] (quoted in the docstrings below).
Design note: `formal/work/p2d/hb.md`. Namespace `EG.HB` (parameters) and `EG.HB.Round`.

Round-local model (TRIAGE §2.2, decision DR-ROUND-LOCAL). Every object of round `l` is a function
of the input graph `H = G_l` of the round and of the round's **choices** `c : RoundChoice V`
(PLAN §3 decision 5: a run records its choices only; everything else is derived):
* parameters (R0)–(R2), (GC) as functions of the real `d = d_l`: `lamOf` (`λ_l`), `tHBOf`
  (`t^HB_l`), `TOf` (`T_l = t^HB_l d_l`), `MOf` (`M_l ∈ ℕ`, v6.1 (R2) with the ceiling),
  `LamOf` (`Λ_l`), `sOf` (`s_l`), `POf` (`P_l`), `tauOf` (`τ_l`), `thetaGC` (`θ^GC_l(Z^0)`);
* `RoundChoice V`: the long cycles `Cyc_l` (R1), the `s = 0` tree (R3, first level), the
  `τ`-run trees indexed by piece address (R3, second level), the home order (R4);
* round objects (`H`, `c` explicit): `Round.d`, `cycEdges`, `graph'` (`G'_l`), `pieceAddrs`,
  `piece`, `bigPieceAddrs`, `twoLevel`, `X0` (`X^0_Z`), `Z0` (`Z^0`), `prePartAddrs`,
  `DupStar` (`Dup*_l`), `mu` (`μ_l`), `D` (`D_l`), `home`, `guests` (`S_Z`), `isL1`, `isL2`,
  `isGC`, `isLight`, `isGCPart`, `Std` (`Std_l`), `partVerts` (`V(Z)`), `X` (`X_Z`),
  `partGraph` (`X_Z` or `X^0_Z`), `assign` ((R5) steps (1)–(3); `none` = passes down),
  `E` (`E_l(Z)`), `passed`, `next` (`G_{l+1}`), `pieceOf`;
* `Round.CyclesValid` and `Round.Valid` (all conditions a valid run imposes on one round).

Design constraint (TRIAGE §2.2, lemGC(i), EX-GC-DEFINITIONAL): `prePartAddrs`, `D`, `home`,
`guests` do not reference `isLight`/`isGC`; lightness is computed from them.

Totality. All definitions accept every graph, every choice and every real `d` (junk values, e.g.
`thetaGC` for `λ ≤ 0`, are never used: statements assume `D_* ≤ d_l` with `Γ`). Addresses are
`EG.HB.Addr = List Bool` into the tree of the round.
-/

@[expose] public section

namespace EG.HB

/-! ### Round parameters ((R0)–(R2), (GC)) -/

/-- [s2:defHBtp] (R0) "Otherwise put `λ_l := log d_l`" (`log = log₂`). -/
noncomputable def lamOf (d : ℝ) : ℝ := Real.logb 2 d

/-- [s2:defHBtp] (R1) "`t^HB_l := log² d_l`". -/
noncomputable def tHBOf (d : ℝ) : ℝ := Real.logb 2 d ^ 2

/-- [s2:defHBtp] (R1) "a cycle of length at least `t^HB_l d_l`": the threshold
`T_l := t^HB_l d_l = d_l log² d_l` (TRIAGE §2.1 `TOf`). -/
noncomputable def TOf (d : ℝ) : ℝ := tHBOf d * d

/-- [s2:defHBtp] (R2) (v6.1) "`M_l := ⌈max(2^{40}, 2^{16} t^HB_l d_l log⁴(t^HB_l d_l))⌉ ∈ ℕ`".
A natural number (TRIAGE §1a M-INTEGER, §2.1); real inequalities use the cast `(MOf d : ℝ)`. -/
noncomputable def MOf (d : ℝ) : ℕ :=
  ⌈max (2 ^ 40) (2 ^ 16 * TOf d * Real.logb 2 (TOf d) ^ 4)⌉₊

/-- [s2:defHBtp] (R2) "`Λ_l := log M_l`" (the logarithm of the integer `M_l`). -/
noncomputable def LamOf (d : ℝ) : ℝ := Real.logb 2 (MOf d : ℝ)

/-- [s2:defHBtp] (R2) "`s_l := ⌈Λ_l^σ⌉`" (`σ = EG.sigmaC = 100`). -/
noncomputable def sOf (d : ℝ) : ℕ := ⌈LamOf d ^ sigmaC⌉₊

/-- [s2:defHBtp] (R2) "`P_l := ⌈λ_l^{C'}⌉`" (`C' = EG.Cp = 103`). Junk value `POf d = 0` for
`d ≤ 1` (`λ_l ≤ 0`; `C'` is odd): then every leaf of the two-level recursion, even one with an
empty graph, counts as a pre-part. Unreachable in statements: a valid run has `d_l ≥ D_*`, and
`D_* ≥ 2^{117}` under `Γ`. -/
noncomputable def POf (d : ℝ) : ℕ := ⌈lamOf d ^ Cp⌉₊

/-- [s2:defHBtp] (R2) "`τ_l := ⌈128 s_l log² M_l⌉`". -/
noncomputable def tauOf (d : ℝ) : ℕ := ⌈128 * (sOf d : ℝ) * Real.logb 2 (MOf d : ℝ) ^ 2⌉₊

/-- [s2:defHBtp] (GC) "`θ^GC_l(Z^0) := ⌈|Z^0| λ_l^{-1/2}⌉`", with `z = |Z^0|`. `λ_l^{-1/2}` is
`Real.rpow` (junk for `λ_l ≤ 0`; `λ_l > 1` under `Γ`). -/
noncomputable def thetaGC (d : ℝ) (z : ℕ) : ℕ := ⌈(z : ℝ) * lamOf d ^ (-(1 / 2 : ℝ))⌉₊

/-! ### Choices of a round -/

/-- The choices of one round of a valid `HB*^{τ+}` run ([s2:defHBtp]: "A *valid `HB*^{τ+}` run*
is an execution of this procedure with any witnesses in both levels of (R3), any vertex order in
(R1), and any home orders in (R4)"):
* `cycles`: the deleted long cycles `Cyc_l` of (R1), each as its cyclic vertex list (the vertex
  order of (R1) is replaced by *any* maximal family, TRIAGE §2.12 "(R1) as any maximal family");
* `tree0`: the `s = 0` recursion of (R3) on `G'_l` (first level);
* `tauRun a`: the tree of the `τ`-run of the piece at address `a` of `tree0` (second level; read
  only at the big pieces `a ∈ Round.bigPieceAddrs H c`, `|𝒫| ≥ P_l`; elsewhere unconstrained);
* `homeOrder`: the home order of (R4), a list of pre-part addresses. -/
structure RoundChoice (V : Type*) where
  /-- The long cycles `Cyc_l` of (R1). -/
  cycles : List (List V)
  /-- The `s = 0` recursion of (R3). -/
  tree0 : STree V
  /-- The `τ`-run trees of (R3), indexed by the address of the piece in `tree0`. -/
  tauRun : Addr → STree V
  /-- The home order of (R4). -/
  homeOrder : List Addr

instance {V : Type*} : Inhabited (RoundChoice V) := ⟨⟨[], .nil, fun _ => .nil, []⟩⟩

namespace Round

variable {V : Type*} [DecidableEq V]

/-! ### (R0), (R1) -/

/-- [s2:defHBtp] (R0) "`d_l := 2|E(G_l)|/n`". Here `H = G_l`; "All graphs `G_l`, `G'_l` below
have vertex set `V(G)`", so `n = |V(G)| = |H|` (`EG.HB.Run.graph_verts`). For `n = 0` Lean gives
`d = 0`. -/
noncomputable def d (H : FGraph V) : ℝ := 2 * (H.edges.card : ℝ) / H.card

/-- The edge set `E(Cyc_l)` of the deleted cycles of (R1). -/
def cycEdges (c : RoundChoice V) : Finset (Sym2 V) :=
  (c.cycles.flatMap cycleEdges).toFinset

/-- [s2:defHBtp] (R1) "The deleted cycles form `Cyc_l`; the remaining graph is `G'_l`":
`G'_l = G_l - E(Cyc_l)`. -/
def graph' (H : FGraph V) (c : RoundChoice V) : FGraph V :=
  H.deleteEdges (cycEdges c)

/-- [s2:defHBtp] (R1) "`t^HB_l := log² d_l`. As long as the current graph contains a cycle of
length at least `t^HB_l d_l`, delete one (the lexicographically first, for a fixed order of
`V(G)`). The deleted cycles form `Cyc_l`; the remaining graph is `G'_l`. Thus `G'_l` has no cycle
of length at least `t^HB_l d_l`."

Encoded as *any* maximal family (TRIAGE §2.12, blueprint HB-R1-ENCODING; this enlarges the set
of valid runs, so every statement about all valid runs becomes stronger): every listed cycle is a
well-formed cycle object (distinct vertices, length `≥ 3`) with all its edges in `E(G_l)` and
length (= number of vertices = number of edges) at least `T_l`; the edge lists of the listed
cycles are pairwise disjoint and duplicate free (the flattened list is `Nodup`); and `G'_l` has no
well-formed cycle of length `≥ T_l`. -/
def CyclesValid (H : FGraph V) (c : RoundChoice V) : Prop :=
  (∀ cyc ∈ c.cycles, (Obj.cycle cyc).WF ∧ (∀ e ∈ cycleEdges cyc, e ∈ H.edges) ∧
      TOf (d H) ≤ (cyc.length : ℝ)) ∧
    (c.cycles.flatMap cycleEdges).Nodup ∧
    ∀ cyc : List V, (Obj.cycle cyc).WF → (∀ e ∈ cycleEdges cyc, e ∈ (graph' H c).edges) →
      (cyc.length : ℝ) < TOf (d H)

/-! ### (R3): pieces, the two-level recursion, pre-parts -/

/-- [s2:defHBtp] (R3) "Its leaves are the *`s = 0` pieces* `𝒫` of round `l`": the addresses of
the leaves of the `s = 0` recursion. -/
def pieceAddrs (c : RoundChoice V) : Finset Addr := c.tree0.leafAddrs

/-- The graph of the piece at address `a` (a node graph of the `s = 0` recursion on `G'_l`). -/
def piece (H : FGraph V) (c : RoundChoice V) (a : Addr) : FGraph V :=
  c.tree0.graphAtD (graph' H c) a

/-- [s2:defHBtp] (R3) "Inside every piece with `|𝒫| ≥ P_l`, run the `τ`-run of `𝒫`": the
addresses of the *big* pieces (`|𝒫| ≥ P_l`), at which `c.tauRun` is grafted (`twoLevel`) and
constrained (`Valid`). -/
noncomputable def bigPieceAddrs (H : FGraph V) (c : RoundChoice V) : Finset Addr :=
  (pieceAddrs c).filter (fun a => POf (d H) ≤ (piece H c a).card)

/-- [s2:defHBtp] (R3) "The *two-level recursion* of round `l` is the split recursion obtained
from the `s = 0` recursion by attaching, at every piece `𝒫` with `|𝒫| ≥ P_l`, the tree of its
`τ`-run." Small pieces stay leaves. -/
noncomputable def twoLevel (H : FGraph V) (c : RoundChoice V) : STree V :=
  c.tree0.graft (fun a => if POf (d H) ≤ (piece H c a).card then c.tauRun a else .nil)

/-- [s2:defHBtp] (R3) "For a pre-part named `Z`, `Z^0` denotes its vertex set and `X^0_Z` its
leaf graph, a graph on `Z^0`": the node graph at address `a` of the two-level recursion (rooted at
`G'_l`). -/
noncomputable def X0 (H : FGraph V) (c : RoundChoice V) (a : Addr) : FGraph V :=
  (twoLevel H c).graphAtD (graph' H c) a

/-- [s2:defHBtp] (R3) "`Z^0` denotes its vertex set". -/
noncomputable def Z0 (H : FGraph V) (c : RoundChoice V) (a : Addr) : Finset V :=
  (X0 H c a).verts

/-- [s2:defHBtp] (R3) "The *round-`l` pre-parts* are the leaves of the `τ`-runs with at least
`P_l` vertices; equivalently, the leaves of the two-level recursion with at least `P_l`
vertices." Defined by the second form (leaf addresses of `twoLevel` whose leaf graph has at least
`P_l` vertices); the first form is a lemma (a leaf of `twoLevel` below a small piece is that piece,
with fewer than `P_l` vertices). A pre-part is named by its address. -/
noncomputable def prePartAddrs (H : FGraph V) (c : RoundChoice V) : Finset Addr :=
  (twoLevel H c).leafAddrs.filter (fun a => POf (d H) ≤ (X0 H c a).card)

/-- [s2:defHBtp] (R3) "Finally `Dup*_l :=` the set of vertices lying in at least two leaves (of any
size, singletons included) of the two-level recursion of round `l`." -/
noncomputable def DupStar (H : FGraph V) (c : RoundChoice V) : Finset V :=
  (twoLevel H c).dup (graph' H c)

/-- [s2:defAncestors] "`μ_r(w)` is the number of round-`r` pre-parts containing `w`" (pre-parts
counted by address). -/
noncomputable def mu (H : FGraph V) (c : RoundChoice V) (w : V) : ℕ :=
  ((prePartAddrs H c).filter (fun a => w ∈ Z0 H c a)).card

/-! ### (R4): duplicated vertices, home, guests, light pre-parts -/

/-- [s2:defHBtp] (R4) "`D_l :=` the set of vertices lying in at least two round-`l` pre-parts"
(so `D_r = {w : μ_r(w) ≥ 2}`, [s2:defAncestors]). -/
noncomputable def D (H : FGraph V) (c : RoundChoice V) : Finset V :=
  ((prePartAddrs H c).biUnion (Z0 H c)).filter (fun v => 2 ≤ mu H c v)

/-- [s2:defHBtp] (R4) "Fix an order of the round-`l` pre-parts (the *home order*). For a vertex
`v` lying in some pre-part, `home(v) = home_l(v) :=` the first pre-part containing `v`": the first
address in `c.homeOrder` that is a pre-part containing `v`; `none` if there is none. (A valid
round lists every pre-part exactly once in `homeOrder`, `Round.Valid`.) -/
noncomputable def home (H : FGraph V) (c : RoundChoice V) (v : V) : Option Addr :=
  c.homeOrder.find? (fun a => decide (a ∈ prePartAddrs H c ∧ v ∈ Z0 H c a))

/-- [s2:defHBtp] (R4) "The *guests* of a pre-part `Z` are `S_Z := {v ∈ Z^0 ∩ D_l : home(v) ≠ Z}`".
-/
noncomputable def guests (H : FGraph V) (c : RoundChoice V) (a : Addr) : Finset V :=
  (Z0 H c a ∩ D H c).filter (fun v => home H c v ≠ some a)

/-- [s2:defHBtp] (R4) "(L1) `|S_Z| ≤ |Z^0|/2`" (as `2|S_Z| ≤ |Z^0|` in `ℕ`). -/
noncomputable def isL1 (H : FGraph V) (c : RoundChoice V) (a : Addr) : Prop :=
  2 * (guests H c a).card ≤ (Z0 H c a).card

/-- [s2:defHBtp] (R4) "(L2) every `u ∈ Z^0` has at most `s_l/2` neighbours in `S_Z` in the graph
`G'_l[Z^0]`" (`s_l/2` is real; the graph is `G'_l[Z^0]`, not `X^0_Z`, blueprint HB-L2-GRAPH). -/
noncomputable def isL2 (H : FGraph V) (c : RoundChoice V) (a : Addr) : Prop :=
  ∀ u ∈ Z0 H c a, ((((graph' H c).induce (Z0 H c a)).nbrs u ∩ guests H c a).card : ℝ) ≤
    (sOf (d H) : ℝ) / 2

/-- [s2:defHBtp] (R4) "(GC) no `x ∈ S_Z` has at least `θ^GC_l(Z^0)` neighbours in
`Z^0 \ S_Z` in the graph `X^0_Z` (the *guest cap*)". -/
noncomputable def isGC (H : FGraph V) (c : RoundChoice V) (a : Addr) : Prop :=
  ∀ x ∈ guests H c a, ((X0 H c a).nbrs x ∩ (Z0 H c a \ guests H c a)).card <
    thetaGC (d H) (Z0 H c a).card

/-- [s2:defHBtp] (R4) "The pre-part `Z` is *light* iff (L1), (L2), (GC). Otherwise `Z` is
*standalone*." -/
noncomputable def isLight (H : FGraph V) (c : RoundChoice V) (a : Addr) : Prop :=
  isL1 H c a ∧ isL2 H c a ∧ isGC H c a

/-- [s2:defHBtp] (R4) "A pre-part satisfying (L1) and (L2) but failing (GC) is a *GC-part*; it is
standalone." -/
noncomputable def isGCPart (H : FGraph V) (c : RoundChoice V) (a : Addr) : Prop :=
  isL1 H c a ∧ isL2 H c a ∧ ¬ isGC H c a

open Classical in
/-- [s2:defHBtp] (R4) "`Std_l` is the set of round-`l` standalone pre-parts; it contains the
GC-parts and the pre-parts failing (L1) or (L2)". -/
noncomputable def Std (H : FGraph V) (c : RoundChoice V) : Finset Addr :=
  (prePartAddrs H c).filter (fun a => ¬ isLight H c a)

open Classical in
/-- [s2:defHBtp] (R4) "A light pre-part `Z` gives the *light part* with vertex set `Z^0 \ S_Z`"
and (Naming) "A round-`l` part is a light part or a standalone pre-part": the vertex set `V(Z)` of
the part of the pre-part `a` (`Z^0 \ S_Z` if light, `Z^0` if standalone). -/
noncomputable def partVerts (H : FGraph V) (c : RoundChoice V) (a : Addr) : Finset V :=
  if isLight H c a then Z0 H c a \ guests H c a else Z0 H c a

/-- [s2:defHBtp] (R4) "… and graph `X_Z := X^0_Z - S_Z`". -/
noncomputable def X (H : FGraph V) (c : RoundChoice V) (a : Addr) : FGraph V :=
  (X0 H c a).deleteVerts (guests H c a)

open Classical in
/-- The graph of the part of the pre-part `a`: `X_Z` if `Z` is light, `X^0_Z` if standalone
((R5) step (1); `H_Y` of [s2:defAncestors]). -/
noncomputable def partGraph (H : FGraph V) (c : RoundChoice V) (a : Addr) : FGraph V :=
  if isLight H c a then X H c a else X0 H c a

/-! ### (R5): assignment of the edges of `G'_l` -/

open Classical in
/-- [s2:defHBtp] (R5) "The edges of `G'_l` are assigned in this order.
(1) For every light pre-part `Z` the edges of `X_Z` are assigned to the light part `Z`; for every
standalone pre-part `Z` the edges of `X^0_Z` are assigned to `Z`. …
(2) Every edge not yet assigned whose ends both lie in some light part is assigned to the first
such light part (in the home order).
(3) Every edge not yet assigned whose ends both lie in `Z^0` for some standalone pre-part `Z` is
assigned to the first such pre-part.
(4) Every other edge of `G'_l` passes down".

`assign H c e` is the address of the part receiving `e`, and `none` if `e` passes down. Step (1)
takes the first pre-part in the home order whose part graph contains `e` (well defined without
the disjointness of the `X^0_Z`, which is a lemma: blueprint HB-EMBEDDED-CLAIMS); the "first such
pre-part" of step (3) is the first in the **home order** (TRIAGE §2.12, HB-R5-ORDER). Only
addresses in `prePartAddrs H c` are returned. Meaningful for `e ∈ E(G'_l)` (see `Round.E`). -/
noncomputable def assign (H : FGraph V) (c : RoundChoice V) (e : Sym2 V) : Option Addr :=
  (c.homeOrder.find? (fun a => decide (a ∈ prePartAddrs H c ∧ e ∈ (partGraph H c a).edges))).or
    ((c.homeOrder.find? (fun a => decide (a ∈ prePartAddrs H c ∧ isLight H c a ∧
        e ∈ (partVerts H c a).sym2))).or
      (c.homeOrder.find? (fun a => decide (a ∈ prePartAddrs H c ∧ ¬ isLight H c a ∧
        e ∈ (Z0 H c a).sym2))))

/-- [s2:defHBtp] (R5) "`E_l(Z)` denotes the set of edges assigned at round `l` to `Z` (a light
part or a standalone pre-part)". -/
noncomputable def E (H : FGraph V) (c : RoundChoice V) (a : Addr) : Finset (Sym2 V) :=
  (graph' H c).edges.filter (fun e => assign H c e = some a)

/-- [s2:defHBtp] (R5) "(4) Every other edge of `G'_l` passes down: `E(G_{l+1})` is the set of these
edges." -/
noncomputable def passed (H : FGraph V) (c : RoundChoice V) : Finset (Sym2 V) :=
  (graph' H c).edges.filter (fun e => assign H c e = none)

/-- [s2:defHBtp] "All graphs `G_l`, `G'_l` below have vertex set `V(G)`" and (R5)(4)
"`E(G_{l+1})` is the set of these edges": the input graph of the next round, with the vertex set
of `H` and edge set `passed H c`. -/
noncomputable def next (H : FGraph V) (c : RoundChoice V) : FGraph V where
  verts := H.verts
  edges := passed H c
  edge_verts e he v hv := (graph' H c).edge_verts e (Finset.mem_filter.1 he).1 v hv
  loopless e he := (graph' H c).loopless e (Finset.mem_filter.1 he).1

/-- The piece above the node at address `a` of the two-level recursion: the leaf of the `s = 0`
recursion on the path `a` (s2:propOrigin "the piece `𝒫` containing `Y`"). -/
def pieceOf (c : RoundChoice V) (a : Addr) : Addr := c.tree0.leafPrefix a

/-! ### Validity of one round -/

/-- All conditions that [s2:defHBtp] imposes on the choices of one round with input graph
`H = G_l` (the stopping test `d_l ≥ D_*` of (R0) is part of `EG.HB.Run.Valid`):
* (R1): `CyclesValid` (any maximal family of edge-disjoint long cycles);
* (R3) first level: "Run an `s = 0` recursion (Lemma [s2:lemOVgeneric]) on `G'_l` that stops
  exactly at `(ε,0)`-expanders: a node is a leaf iff its graph is an `(ε,0)`-expander, and
  otherwise any witness with parameter `0` is used" (`ε = EG.epsC = 2^{-5}`);
* (R3) second level: "Inside every piece with `|𝒫| ≥ P_l`, run the `τ`-run of `𝒫` with `s = s_l`
  and `τ = τ_l` (Lemma [s2:lem14tau]), with any witnesses" (`IsTauRun` includes the stopping rule
  "leaf iff `(ε,s_l)`-expander", both directions, blueprint HB-STOPRULE);
* (R4): the home order is "an order of the round-`l` pre-parts": a duplicate-free list whose
  entries are exactly the pre-part addresses.
The hypotheses of Lemma 14^τ (`τ_l ≥ 128 s_l log² |𝒫|`) are not required (they follow from
s2:lemCap(ii) under `Γ2(a)`; blueprint HB-VALID-NO-TERMINATION). -/
def Valid (H : FGraph V) (c : RoundChoice V) : Prop :=
  CyclesValid H c ∧
    c.tree0.IsS0Rec epsC (graph' H c) ∧
    c.tree0.StopsAt (graph' H c) (fun Q => Q.IsExpander epsC 0) ∧
    (∀ a ∈ c.tree0.leafAddrs, POf (d H) ≤ (piece H c a).card →
      (c.tauRun a).IsTauRun epsC (sOf (d H)) (tauOf (d H)) (piece H c a)) ∧
    c.homeOrder.Nodup ∧ c.homeOrder.toFinset = prePartAddrs H c

end Round

end EG.HB
