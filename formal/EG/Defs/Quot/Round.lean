module

public import EG.Defs.Quot.Cand
public import EG.Defs.Quot.Schedule
public import EG.Defs.Chain.JSet
public import EG.Defs.Objects
public import EG.Defs.Fnum

/-!
# The JV⁺* round step, the quotient `Q_l` and its lift (manuscript s7:consRound)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`, Construction [s7:consRound] ("The JV⁺* round step at round `l ≥ 3`;
the J-consumer"), including the v6.1 paragraph *Fixed rules* (patch set R of TRIAGE §1a), quoted
in the docstrings below. Design note: `formal/work/p2d/quot.md`. Namespace `EG.Quot`; TRIAGE §2.10,
§3 item 31.

## Architecture (TRIAGE §2.10, binding)
* **The past is a parameter.** `RoundInput V` is the past `Past_l` *as read by the round step*:
  the graph, `l`, `M_l ∈ ℕ`, `λ_{l-2}`, the ancestors with vertex sets, `LJV_{Y,l}` and
  lend-goodness, the pool `Pool_l` with `r(w)`, the four role sets (hubs `D_l`, fresh centres
  `⋃F_Z`, ports `⋃Q*_Z`, lost centres `Lost_l`), the class map `Y(·)`, JV-badness and the four
  J-classes. `RoundInput.Valid` lists the properties of the past the round lemmas use (the
  `JPlusProps` fields in the form of `EG.Chain.JPlusProps.J1hub_ports` / `degE_types_le`, the
  role and typing facts, the pool/candidate/LJV facts and the Γ consequences). `Hcd` and `Cand`
  are *defined* from the fields. `RoundInput.ofPast` instantiates the record from a run,
  a designation `δ`, stage data `S`, pool labels `π`, a round `l` and a set `J`, with the choices
  recorded in TRIAGE §3 item 31 (MINOR-A of work/p2d/design.md).
* **Fixed rules** are the structure `Rules I`. The argument types *are* the v6.1 restrictions:
  the pairing and unpaired leg of (b), the colouring order of (b) and the grouping of (c) are data
  (functions of `Past_l` alone: no argument); the SDR of (d), the processing order and the order
  of `V(G)` of (e1), and the order of `E'(u)` of (e2) take the lists `L : Lists` only ("functions of
  `Past_l` and of the lists", so none reads the orders `≺_u`); the rank order of (g) and the rule
  choosing `Dec_l` of (h) take all of `ξ : Xi` ("not restricted"). `Rules.Valid` holds the
  correctness side conditions of each rule. Every round Spec reads `∀ R : Rules I, R.Valid → …`.
  For the run-level J-consumer one valid rule is fixed once (`RoundInput.chosenRules`); the output
  `roundOut` and the quotient `roundQuotient` of a round both use it and the same chosen `ξ_l`.
* **Total construction with fallbacks.** Every step is total: greedy colouring without a free
  colour leaves the object uncoloured, a failed (e1) search leaves the item without a junction, a
  missing (e2) candidate leaves the end without a junction; Lemma [s7:lemWellDef] says (under
  `Valid`) that no fallback is taken.
* **The quotient** `Q ξ : FGraph (QVert V)`, `QVert V := QTag × V`,
  `QTag := Bool × ℕ × ℕ × Bool` = (kind: `false` PAR / `true` HUB, colour `κ`, rank `ι`,
  side: `true` hub copy / `false` junction copy). A PAR layer edge exists only for an object whose
  two ends have distinct junctions, and a HUB edge joins a hub copy to a junction copy, so
  `FGraph.loopless` holds by construction; `Q.verts` is the set of ends of edges, so isolated
  vertices are deleted by definition.

## Encodings of the objects of the construction
* Items (the edges of `J_l \ J^lost_l`): a `J^hub` item is the pair `(h, u) ∈ D_l × ports`, a
  `J^fr` item at the fresh centre `x` is its port `u` (`s(x, u)`), a `J^par` item is an edge. The
  vertices of an item are its two ends (port ends and centre).
* PAR objects: `ParObj.par u v` (a live `J^par` item `s(u, v)`, with `(u, v) = Quot.out e`) and
  `ParObj.cherry x u u'` (middle `x`, ends `u`, `u'`). Ends are indexed by `Bool`.
* The pairing at a fresh centre `x` is a list of the live `J^fr` ports at `x`; its consecutive
  pairs are the cherries and a last odd element is the unpaired fresh leg (every pairing together
  with a choice of unpaired leg has this form).
* Colours: PAR colours `κ ∈ [3M]` and HUB colours `κ ∈ [4M]` are natural numbers `< 3M`, `< 4M`
  (0-based). The `i`-th group (0-based `i`) of a non-ultra hub `h` receives the list
  `{η_h(3i), η_h(3i+1), η_h(3i+2)}` (manuscript, 1-based: `{η_h(3i-2), η_h(3i-1), η_h(3i)}`).
* Ends that receive junctions: `REnd.par o b` (the end `b` of the PAR object `o`) and
  `REnd.hub h u` (the port end of the hub item `(h, u)`).
-/

@[expose] public section

namespace EG.Quot

open EG.HB EG.Chain

/-! ## The past, as read by the round step -/

/-- [s7:consRound] "Fix `3 ≤ l ≤ R` and the past `Past_l`. The input is the set
`J_l = J^lost_l ∪ J^hub_l ∪ J^fr_l ∪ J^par_l` produced by JS-LC at round `l`, with the properties
(J1)–(J3) and (i)–(v) of Lemma [s6:lemJplus]": the data of the past that the round step reads
(TRIAGE §2.10). Instantiated from a run by `RoundInput.ofPast`. -/
structure RoundInput (V : Type*) where
  /-- The graph `G`. -/
  G : FGraph V
  /-- The round `l`. -/
  l : ℕ
  /-- `M_l` (a natural number, v6.1 (R2)). -/
  M : ℕ
  /-- `λ_{l-2}`. -/
  lam : ℝ
  /-- The ancestors (classes are ancestors). -/
  ancs : Finset PartId
  /-- `V(Y)` for an ancestor `Y`. -/
  ancVerts : PartId → Finset V
  /-- `LJV_{Y,l}` of the fixed stage-1 outcome. -/
  ljv : PartId → Finset (Sym2 V)
  /-- `Y` is lend-good. -/
  lendGood : PartId → Prop
  /-- `Pool_l`. -/
  pool : Finset V
  /-- `r(w)` for `w ∈ Pool_l`. -/
  poolRound : V → ℕ
  /-- The hubs `D_l`. -/
  hubs : Finset V
  /-- The fresh centres `⋃_{Z ∈ Std_l} F_Z`. -/
  fresh : Finset V
  /-- The ports: the classed non-lost ports `⋃_{Z ∈ Std_l} Q*_Z`. -/
  ports : Finset V
  /-- The lost centres `Lost_l = ⋃_{Z ∈ Std_l} Lost_Z`. -/
  lost : Finset V
  /-- The class `Y(u)` of a port `u`. -/
  cls : V → PartId
  /-- `u` is JV-bad. -/
  jvBad : V → Prop
  /-- `J^lost_l`. -/
  Jlost : Finset (Sym2 V)
  /-- `J^hub_l`. -/
  Jhub : Finset (Sym2 V)
  /-- `J^fr_l`. -/
  Jfr : Finset (Sym2 V)
  /-- `J^par_l`. -/
  Jpar : Finset (Sym2 V)

namespace RoundInput

variable {V : Type*} [DecidableEq V] (I : RoundInput V)

/-- [s7:consRound] "`J_l = J^lost_l ∪ J^hub_l ∪ J^fr_l ∪ J^par_l`". -/
def J : Finset (Sym2 V) := I.Jlost ∪ I.Jhub ∪ I.Jfr ∪ I.Jpar

/-- [s7:defCand] "`Hcd_l := λ_{l-2}^{95}/(8M_l^2)`" (defined from the fields). -/
noncomputable def Hcd : ℝ := HcdOf I.M I.lam

/-- [s7:consRound] (c) "`θ^ult_l := ⌊M_l Hcd_l/7⌋`". -/
noncomputable def thult : ℕ := thultOf I.M I.Hcd

/-- [s7:consRound] (c) "`K^HUB_l := 4M_l`". -/
def KHUB : ℕ := 4 * I.M

/-- [s7:defCand] "`Cand_l(u) := {w ∈ Pool_{l,r(u)} : uw ∈ LJV_{Y,l}}`" with `Y = Y(u)` and
`r(u) = r(Y)` (defined from the fields: `Pool_{l,r} = {w ∈ Pool_l : r(w) = r}`). -/
def cand (u : V) : Finset V :=
  I.pool.filter (fun w => I.poolRound w = (I.cls u).1 ∧ s(u, w) ∈ I.ljv (I.cls u))

/-- [s2:defAncestors] "`mult_r(w)` is the number of ancestors `Y` of round `r` with `w ∈ V(Y)`"
(read from the fields; used by Lemma [s7:lemMULT]). -/
def multAt (r : ℕ) (w : V) : ℕ := (I.ancs.filter (fun Y => Y.1 = r ∧ w ∈ I.ancVerts Y)).card

/-- The properties of the past that the round step and the round lemmas use (TRIAGE §2.10):
Γ consequences, the role and typing facts of [s6:lemJplus] (J3) and (i), (J1) aggregated over all
parts, (J2), the class, LJV and lend-goodness facts, and "every JV-good port has
`|Cand_l(u)| ≥ Hcd_l`" ([s7:lemCand] (iv)). The instantiation `RoundInput.ofPast` must satisfy
it for every valid run (a Spec obligation, reviewed jointly with work/p2d/design.md). -/
structure Valid : Prop where
  /-- "`M_l ≥ 2^{40}` by the definition of `M_l`". -/
  M_ge : 2 ^ 40 ≤ I.M
  /-- [s7:lemCand] (iv) "`Hcd_l ≥ 2^{10} M_l^{10}`". -/
  Hcd_ge : (2 : ℝ) ^ 10 * (I.M : ℝ) ^ 10 ≤ I.Hcd
  /-- [s6:lemJplus] (J3): hubs, fresh centres, ports and lost centres are pairwise disjoint. -/
  roles : Disjoint I.hubs I.fresh ∧ Disjoint I.hubs I.ports ∧ Disjoint I.hubs I.lost ∧
    Disjoint I.fresh I.ports ∧ Disjoint I.fresh I.lost ∧ Disjoint I.ports I.lost
  /-- [s6:lemJplus] "a `J^hub`-edge is an edge `hu` with `h ∈ A_Z ⊆ D_l` and `u ∈ Q*_Z`". -/
  hub_typed : ∀ e ∈ I.Jhub, ∃ h ∈ I.hubs, ∃ u ∈ I.ports, e = s(h, u)
  /-- [s6:lemJplus] "a `J^fr`-edge is an edge `xu` with `x ∈ F_Z` and `u ∈ Q*_Z`". -/
  fr_typed : ∀ e ∈ I.Jfr, ∃ x ∈ I.fresh, ∃ u ∈ I.ports, e = s(x, u)
  /-- [s6:lemJplus] "a `J^par`-edge has both ends in `Q*_Z`". -/
  par_typed : ∀ e ∈ I.Jpar, ∃ u ∈ I.ports, ∃ v ∈ I.ports, e = s(u, v)
  /-- [s6:lemJplus] "a `J^lost`-edge is an edge `vu` with `v ∈ Lost_Z` … and `u ∈ Q*_Z`". -/
  lost_typed : ∀ e ∈ I.Jlost, ∃ v ∈ I.lost, ∃ u ∈ I.ports, e = s(v, u)
  /-- `J_l ⊆ E(G)`. -/
  J_sub : I.J ⊆ I.G.edges
  /-- (J1) "For each hub `h` and each class `Y`, `J_l` contains at most one `J^hub`-edge of class
  `Y` at `h`, aggregated over all parts of round `l`". -/
  J1 : ∀ (h : V) (Y : PartId),
    (I.Jhub.filter (fun e => ∃ u ∈ I.ports, e = s(h, u) ∧ I.cls u = Y)).card ≤ 1
  /-- (J2) "a port or a fresh centre (a vertex outside `D_l`) carries at most `M_l − 1` J-edges of
  round `l`". -/
  J2 : ∀ v ∉ I.hubs, degE I.J v ≤ I.M - 1
  /-- (J2) "`|J_l| ≤ n(M_l − 1)`". -/
  J2tot : I.J.card ≤ I.G.card * (I.M - 1)
  /-- The class of a port is an ancestor. -/
  cls_anc : ∀ u ∈ I.ports, I.cls u ∈ I.ancs
  /-- "`r(u) ≤ l − 2`" (and `r(u) ≥ 1`). -/
  cls_round : ∀ u ∈ I.ports, 1 ≤ (I.cls u).1 ∧ (I.cls u).1 + 2 ≤ I.l
  /-- "`u ∈ V(Y(u))`". -/
  cls_mem : ∀ u ∈ I.ports, u ∈ I.ancVerts (I.cls u)
  /-- "`LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)` and `H_Y` is a graph on `V(Y)`" (and `E(H_Y) ⊆ E(G)`). -/
  ljv_in : ∀ Y ∈ I.ancs, ∀ e ∈ I.ljv Y, e ∈ I.G.edges ∧ ∀ v ∈ e, v ∈ I.ancVerts Y
  /-- The graphs `H_Y` of distinct ancestors are edge-disjoint ([s2:propStructure] (iii)). -/
  ljv_disj : ∀ Y ∈ I.ancs, ∀ Y' ∈ I.ancs, Y ≠ Y' → Disjoint (I.ljv Y) (I.ljv Y')
  /-- Junction edges are not J-edges ([s6:lemJplus] (iii): `E(H_Y) ∩ E_l(Z) = ∅`). -/
  ljv_J : ∀ Y ∈ I.ancs, Disjoint (I.ljv Y) I.J
  /-- "`Lost_Z` contains every classed port whose class is lend-bad": ports have lend-good
  classes. -/
  lendGood_ports : ∀ u ∈ I.ports, I.lendGood (I.cls u)
  /-- [s7:lemCand] (iv) "if `u` is JV-good then `|Cand_l(u)| ≥ Hcd_l`". -/
  good_cand : ∀ u ∈ I.ports, ¬ I.jvBad u → I.Hcd ≤ ((I.cand u).card : ℝ)
  /-- `Pool_l ⊆ V(G)`. -/
  pool_sub : I.pool ⊆ I.G.verts
  /-- The ports are vertices of `G` ("there are at most `n` ports", [s7:lemPay] (c)). -/
  ports_sub : I.ports ⊆ I.G.verts

/-- [s7:consRound] the past of round `l` read from a run: `hubs := D_l`, `fresh := ⋃_Z F_Z`,
`ports := ⋃_Z Q*_Z`, `lost := Lost_l`, `Y(u) := δ l u`, `LJV_{Y,l} := S.ljv Y l`,
`lendGood := ¬ lendBad`, `Pool_l`, `r(w)` from the pool labels `π`, JV-badness from
[s7:defCand], and the four classes of `J` (TRIAGE §3 item 31; work/p2d/design.md MINOR-A). -/
noncomputable def ofPast (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V)
    (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V)) : RoundInput V where
  G := G
  l := l
  M := run.M G l
  lam := run.lam G (l - 2)
  ancs := run.ancestors G
  ancVerts := run.ancVerts G
  ljv Y := S.ljv Y l
  lendGood Y := ¬ lendBad run G S Y
  pool := Stage1.poolL G π l
  poolRound := Stage1.poolRound π
  hubs := run.D G l
  fresh := freshCentres run G l
  ports := qsRound run G δ S l
  lost := lostRound run G δ S l
  cls := δ l
  jvBad := JVBad run G δ S π l
  Jlost := Chain.Jlost run G δ S l J
  Jhub := Chain.Jhub run G δ S l J
  Jfr := Chain.Jfr run G δ S l J
  Jpar := Chain.Jpar run G δ S l J

/-! ## (a) Items and payments bounded by stage-1 weights -/

/-- [s7:consRound] "The *items* are the edges of `J_l \ J^lost_l`." -/
def items : Finset (Sym2 V) := I.J \ I.Jlost

open Classical in
/-- [s7:consRound] (a2) "every item with a vertex in `Pool_l`" (the vertices of an item are its
two ends: its port end or ends and its centre). -/
noncomputable def paidPool : Finset (Sym2 V) := I.items.filter (fun e => ∃ v ∈ e, v ∈ I.pool)

open Classical in
/-- [s7:consRound] (a3) "every item with a JV-bad port end". -/
noncomputable def paidJVBad : Finset (Sym2 V) :=
  I.items.filter (fun e => ∃ u ∈ e, u ∈ I.ports ∧ I.jvBad u)

/-- [s7:consRound] (a) "The following are *paid*, that is, output as single edges: (a1) every edge
of `J^lost_l`; (a2) every item with a vertex in `Pool_l`; (a3) every item with a JV-bad port end." -/
noncomputable def paidA : Finset (Sym2 V) := I.Jlost ∪ I.paidPool ∪ I.paidJVBad

/-- [s7:consRound] (a) "The remaining items are *live*." -/
noncomputable def live : Finset (Sym2 V) := I.items \ (I.paidPool ∪ I.paidJVBad)

/-- [s7:consRound] (a) "A vertex is *live* if it is a vertex of a live item, and `Live` denotes the
set of live vertices." -/
noncomputable def liveVerts : Finset V := I.live.biUnion Sym2.toFinset

/-- The live `J^hub` items `(h, u)`: `h ∈ D_l`, `u` a port, `hu` a live item of `J^hub_l`
([s7:consRound] "A `J^hub` item is written `(h,u)`, with `h` its hub and `u` its port"). -/
noncomputable def hubItems : Finset (V × V) :=
  (I.hubs ×ˢ I.ports).filter (fun p => s(p.1, p.2) ∈ I.live ∧ s(p.1, p.2) ∈ I.Jhub)

/-- The live hub items at the port `u` ("its live hub items", (d)). -/
noncomputable def hubItemsAt (u : V) : Finset (V × V) := I.hubItems.filter (fun p => p.2 = u)

/-- The ports `u` of the live `J^fr` items `xu` at the fresh centre `x` ((b) "the live `J^fr`
items at `x`"). -/
noncomputable def frPorts (x : V) : Finset V :=
  I.ports.filter (fun u => s(x, u) ∈ I.live ∧ s(x, u) ∈ I.Jfr)

/-- The live `J^par` items ((b) "Every live `J^par` item `u`–`v` is a PAR object"). -/
noncomputable def parItems : Finset (Sym2 V) := I.live.filter (fun e => e ∈ I.Jpar)

/-! ## (c) Ultra hubs (functions of the past) -/

/-- [s7:consRound] (c) "For a hub `h ∈ D_l` let `c^live_h` be its number of live `J^hub` items." -/
noncomputable def clive (h : V) : ℕ := (I.hubItems.filter (fun p => p.1 = h)).card

/-- [s7:consRound] (c) "The hub `h` is *ultra* if `c^live_h > θ^ult_l`, and *non-ultra*
otherwise." -/
def ultra (h : V) : Prop := I.thult < I.clive h

/-- [s7:consRound] (c) "`k_h := ⌈8 c^live_h / Hcd_l⌉`" (the number of groups of a non-ultra hub). -/
noncomputable def kh (h : V) : ℕ := ⌈8 * (I.clive h : ℝ) / I.Hcd⌉₊

/-- [s7:consRound] (c) the group size bound "`⌈Hcd_l/8⌉`". -/
noncomputable def groupCap : ℕ := ⌈I.Hcd / 8⌉₊

end RoundInput

/-! ## PAR objects, ends, layer edges, quotient vertices -/

/-- [s7:consRound] (b) a *PAR object*: a live `J^par` item `u`–`v` (`par u v`, ends `u`, `v`), or a
*cherry* `u`–`x`–`u'` (`cherry x u u'`, ends `u`, `u'`, *middle* `x`). -/
inductive ParObj (V : Type*) where
  | par (u v : V)
  | cherry (x u u' : V)
  deriving DecidableEq

namespace ParObj

variable {V : Type*}

/-- The two ends of a PAR object (indexed by `Bool`): the ports `u` (`false`) and `v`, resp. `u'`
(`true`). -/
def endAt : ParObj V → Bool → V
  | par u v, b => if b then v else u
  | cherry _ u u', b => if b then u' else u

/-- The middle of a cherry (`none` for a `J^par` item). -/
def middle : ParObj V → Option V
  | par _ _ => none
  | cherry x _ _ => some x

/-- The J-edges of a PAR object: its one `J^par` edge, or the two edges `xu`, `xu'` of a cherry. -/
def edgeList : ParObj V → List (Sym2 V)
  | par u v => [s(u, v)]
  | cherry x u u' => [s(x, u), s(x, u')]

/-- [s7:consRound] (b) "two PAR objects sharing a port, or sharing a middle". -/
def Conflict (o o' : ParObj V) : Prop :=
  (∃ b b' : Bool, o.endAt b = o'.endAt b') ∨ (∃ x, o.middle = some x ∧ o'.middle = some x)

end ParObj

/-- An end that receives a junction in (e): the end `b` of the PAR object `o`, or the (port) end of
the hub item `(h, u)`. -/
inductive REnd (V : Type*) where
  | par (o : ParObj V) (b : Bool)
  | hub (h u : V)
  deriving DecidableEq

/-- The port at which an end lies. -/
def REnd.port {V : Type*} : REnd V → V
  | par o b => o.endAt b
  | hub _ u => u

/-- A layer edge: an (unpaid) PAR object (PAR layers) or a coloured hub item `(h, u)` (HUB
layers). -/
abbrev LayerEdge (V : Type*) : Type _ := ParObj V ⊕ (V × V)

/-- The tag of a vertex of `Q_l`: (kind: `false` = PAR, `true` = HUB; colour `κ`; rank `ι`;
side: `true` = hub copy, `false` = junction copy `[w]`) (TRIAGE §2.10 QVert). -/
abbrev QTag : Type := Bool × ℕ × ℕ × Bool

/-- The vertices of the quotient: tagged copies of vertices of `G` (TRIAGE §2.10). -/
abbrev QVert (V : Type*) : Type _ := QTag × V

/-- The tag of the junction copies of the PAR sub-layer `B^{P,(ι)}_κ`. -/
def parTag (κ ι : ℕ) : QTag := (false, κ, ι, false)

/-- The tag of the hub copies (`side = true`) and junction copies (`side = false`) of the HUB
sub-layer `B^{H,(ι)}_κ`. -/
def hubTag (κ ι : ℕ) (side : Bool) : QTag := (true, κ, ι, side)

/-- Consecutive pairs of a list: `[a, b, c, d, e] ↦ [(a, b), (c, d)]` (the cherries of a
pairing list). -/
def pairUp {α : Type*} : List α → List (α × α)
  | a :: b :: t => (a, b) :: pairUp t
  | _ => []

/-- The last element of a list of odd length (the unpaired fresh leg of a pairing list). -/
def leftover {α : Type*} : List α → Option α
  | _ :: _ :: t => leftover t
  | [a] => some a
  | [] => none

/-- The `i`-th list of a non-ultra hub (0-based `i`): `{η(3i), η(3i+1), η(3i+2)}` (manuscript,
1-based: "`{η_h(3i-2), η_h(3i-1), η_h(3i)}`"), as a set of natural numbers `< K`. -/
def listOf {K : ℕ} (η : Equiv.Perm (Fin K)) (i : ℕ) : Finset ℕ :=
  ((Finset.univ.filter (fun a : Fin K => a.val / 3 = i)).image η).image Fin.val

/-- State of the sequential step (e1): `Used(u)`, `Used_κ(h)` and the junctions assigned so far. -/
structure E1State (V : Type*) where
  /-- `Used(u)`. -/
  used : V → Finset V
  /-- `Used_κ(h)`. -/
  usedK : V → ℕ → Finset V
  /-- The junction of the hub item `(h, u)`, once assigned. -/
  junc : V × V → Option V

/-! ## The fixed rules -/

/-- [s7:consRound] *Fixed rules* (v6.1): "The rules and orders called fixed in steps (b)–(e), (g)
and (h) below are deterministic functions, chosen once and for all before any randomness is
drawn, with the following arguments.
* *Functions of `Past_l` alone:* the pairing of the live `J^fr` items at a fresh centre and the
  choice of its unpaired fresh leg, and the order in which the PAR objects are coloured, in (b);
  the split of the live items of a non-ultra hub into groups, together with the numbering of the
  groups, in (c). In particular these rules do not read `ξ_l`.
* *Functions of `Past_l` and of the lists*, that is, of the variables `η_h` and `ζ_{h,u}` of
  `ξ_l`: the choice of the system of distinct representatives in (d); the processing order and the
  order of `V(G)` in (e1); and the order `e_1,…,e_q` of `E'(u)` in (e2).
* None of the rules of steps (b)–(e) reads the orders `≺_u` of `ξ_l`; …
* The rank order in (g) and the rule choosing `Dec_l` in (h) are not restricted: they are
  arbitrary deterministic functions of `Past_l` and `ξ_l`."

The past is the parameter `I`; a field without argument is a function of `Past_l` alone, a field
taking `Lists I.G I.M` reads the lists, a field taking `Xi I.G I.M` reads all of `ξ_l`. -/
structure Rules {V : Type*} [DecidableEq V] (I : RoundInput V) where
  /-- (b) at the fresh centre `x`: the live `J^fr` items at `x` (by their ports) in a list; its
  consecutive pairs are the cherries, and a last element of an odd list is the unpaired fresh
  leg ("the pairing … and the choice of its unpaired fresh leg"). -/
  pairing : V → List V
  /-- (b) "the order in which the PAR objects are coloured". -/
  parOrder : List (ParObj V)
  /-- (c) "the split of the live items of a non-ultra hub into groups, together with the
  numbering of the groups": the group number (0-based) of each live hub item `(h, u)`. -/
  group : V × V → ℕ
  /-- (d) "the choice of the system of distinct representatives": the colour of each live hub
  item, given the lists. -/
  sdr : Lists I.G I.M → V × V → ℕ
  /-- (e1) "the processing order", given the lists. -/
  e1Order : Lists I.G I.M → List (V × V)
  /-- (e1) "the order of `V(G)`", given the lists. -/
  vertOrder : Lists I.G I.M → List V
  /-- (e2) "the order `e_1,…,e_q` of `E'(u)`", given the lists. -/
  e2Order : Lists I.G I.M → V → List (REnd V)
  /-- (g) "The rank order": in every layer, the edges joining the same two vertices are listed in
  the order in which they occur in this list. -/
  rankOrder : Xi I.G I.M → List (LayerEdge V)
  /-- (h) "the rule choosing `Dec_l`". -/
  dec : Xi I.G I.M → List (Obj (QVert V))

namespace Rules

variable {V : Type*} [DecidableEq V] {I : RoundInput V} (R : Rules I)

/-! ### (b) PAR objects and their colouring (functions of the past) -/

/-- [s7:consRound] (b) "At each fresh centre `x`, the live `J^fr` items at `x` are paired, by a
fixed rule, into *cherries* `u`–`x`–`u'`". -/
def cherries : Finset (ParObj V) :=
  I.fresh.biUnion (fun x => ((pairUp (R.pairing x)).map (fun p => ParObj.cherry x p.1 p.2)).toFinset)

/-- [s7:consRound] (b) "If the number of live `J^fr` items at `x` is odd, one of them, chosen by a
fixed rule, is paid: it is the *unpaired fresh leg* of `x`." -/
def unpairedLegs : Finset (Sym2 V) :=
  I.fresh.biUnion (fun x => ((leftover (R.pairing x)).map (fun u => s(x, u))).toFinset)

/-- [s7:consRound] (b) "Every live `J^par` item `u`–`v` is a *PAR object* with *ends* at `u` and at
`v`" (the ends `(u, v) = Quot.out e` of the edge `e`; core `_root_.Quot.out`, since the
namespace `EG.Quot` shadows `Quot` here). -/
noncomputable def parObjsPar (I : RoundInput V) : Finset (ParObj V) :=
  I.parItems.image (fun e => ParObj.par (_root_.Quot.out e).1 (_root_.Quot.out e).2)

/-- [s7:consRound] (b) the PAR objects: the live `J^par` items and the cherries. -/
noncomputable def parObjs : Finset (ParObj V) := parObjsPar I ∪ R.cherries

open Classical in
/-- One step of the greedy colouring of (b): the object `o` receives the least colour of `[3M]`
not used by a PAR object sharing a port or a middle with it (none if all are used). -/
noncomputable def colourStep (col : ParObj V → Option ℕ) (o : ParObj V) :
    ParObj V → Option ℕ :=
  Function.update col o ((List.range (3 * I.M)).find? (fun c =>
    decide (∀ o' ∈ R.parObjs, o' ≠ o → ParObj.Conflict o o' → col o' ≠ some c)))

/-- [s7:consRound] (b) "The PAR objects are then coloured greedily, in a fixed order, with colours
from `[3M_l]`, so that two PAR objects sharing a port, or sharing a middle, receive different
colours." (`none` = not coloured: an object outside the order, or the fallback when no colour is
free, which Lemma [s7:lemWellDef] (i) excludes.) -/
noncomputable def parColour : ParObj V → Option ℕ :=
  R.parOrder.foldl R.colourStep (fun _ => none)

/-! ### (c), (d) HUB lists and the SDR (functions of the past and the lists) -/

open Classical in
/-- [s7:consRound] (c) the list of the live hub item `(h, u)`: for a non-ultra `h`, the list
`{η_h(3i), η_h(3i+1), η_h(3i+2)}` of its group `i`; for an ultra `h`, "every live item `(h,u)` is
its own group, with list `ζ_{h,u}`". -/
noncomputable def hubList (L : Lists I.G I.M) (it : V × V) : Finset ℕ :=
  if I.ultra it.1 then (zetaAt L it.1 it.2).image Fin.val else listOf (etaAt L it.1) (R.group it)

/-- [s7:consRound] (d) at the port `u` "a choice [of] pairwise distinct colours for its live hub
items, each item's colour taken from the list of its group (a system of distinct
representatives)" exists. -/
def SDRExists (L : Lists I.G I.M) (u : V) : Prop :=
  ∃ f : V × V → ℕ, (∀ it ∈ I.hubItemsAt u, f it ∈ R.hubList L it) ∧
    Set.InjOn f (I.hubItemsAt u : Set (V × V))

open Classical in
/-- [s7:consRound] (d) the colour of a live hub item: the one chosen by the SDR rule at its port,
if an SDR exists there (a *coloured hub item*); `none` otherwise ("If no such choice exists, all
live hub items of `u` are paid (an *SDR failure* at `u`)"). -/
noncomputable def hubColour (L : Lists I.G I.M) (it : V × V) : Option ℕ :=
  if it ∈ I.hubItems ∧ R.SDRExists L it.2 then some (R.sdr L it) else none

open Classical in
/-- [s7:consRound] (d) "The items that receive a colour are the *coloured hub items*." -/
noncomputable def colouredHub (L : Lists I.G I.M) : Finset (V × V) :=
  I.hubItems.filter (fun it => R.SDRExists L it.2)

open Classical in
/-- [s7:consRound] (d) the edges paid for SDR failures: all live hub items of a port without an
SDR. -/
noncomputable def sdrPaid (L : Lists I.G I.M) : Finset (Sym2 V) :=
  (I.hubItems.filter (fun it => ¬ R.SDRExists L it.2)).image (fun it => s(it.1, it.2))

/-! ### (e1) the greedy junctions of non-ultra hubs -/

/-- The candidates still free for the hub item `(h, u)` of colour `κ` in the state `st` of (e1):
`Cand_l(u) \ Used(u) \ Used_κ(h)`. -/
def e1Free (I : RoundInput V) (st : E1State V) (it : V × V) (κ : ℕ) : Finset V :=
  (I.cand it.2 \ st.used it.2) \ st.usedK it.1 κ

open Classical in
/-- One step of (e1): "The item `(h,u)` of colour `κ` receives as its *junction* the first vertex
`w`, in a fixed order of `V(G)`, of `Cand_l(u) \ Used(u) \ Used_κ(h)`. Then `w` is added to
`Used(u)` and to `Used_κ(h)`." Items that are not coloured items of non-ultra hubs are skipped;
if no such `w` exists (excluded by Lemma [s7:lemWellDef] (iv)), the item gets no junction. -/
noncomputable def e1Step (L : Lists I.G I.M) (st : E1State V) (it : V × V) : E1State V :=
  match R.hubColour L it with
  | none => st
  | some κ =>
    if I.ultra it.1 then st else
    match (R.vertOrder L).find? (fun w => decide (w ∈ e1Free I st it κ)) with
    | none => st
    | some w =>
      { used := Function.update st.used it.2 (insert w (st.used it.2))
        usedK := Function.update st.usedK it.1
          (Function.update (st.usedK it.1) κ (insert w (st.usedK it.1 κ)))
        junc := Function.update st.junc it (some w) }

/-- [s7:consRound] (e), (e1) "Initially `Used(u) := ∅` for every port `u` and `Used_κ(h) := ∅` for
every hub `h` and every `κ ∈ [4M_l]`. (e1) The coloured hub items of non-ultra hubs are processed
in a fixed order." The state after (e1). -/
noncomputable def e1State (L : Lists I.G I.M) : E1State V :=
  (R.e1Order L).foldl (R.e1Step L) ⟨fun _ => ∅, fun _ _ => ∅, fun _ => none⟩

/-- `Used(u)` after (e1). -/
noncomputable def used (L : Lists I.G I.M) (u : V) : Finset V := (R.e1State L).used u

/-! ### (e2), (e3) the random injections and loops -/

open Classical in
/-- [s7:consRound] (e2) "For every port `u` let `E'(u)` be the set of the ends at `u` of the PAR
objects and of the coloured hub items `(h,u)` with `h` ultra". -/
noncomputable def E' (L : Lists I.G I.M) (u : V) : Finset (REnd V) :=
  (R.parObjs.biUnion (fun o =>
      (Finset.univ.filter (fun b : Bool => o.endAt b = u)).image (REnd.par o))) ∪
    ((R.colouredHub L).filter (fun it => it.2 = u ∧ I.ultra it.1)).image
      (fun it => REnd.hub it.1 it.2)

/-- [s7:consRound] (e2) "listed in a fixed order `e_1,…,e_q`. Let `w_1 ≺_u w_2 ≺_u ⋯` be the
elements of `Cand_l(u) \ Used(u)` in the order `≺_u`; the end `e_i` receives the junction `w_i`."
(`none` if the end is not in the list, or if there are fewer candidates, which Lemma
[s7:lemWellDef] (v) excludes.) -/
noncomputable def e2Junc (ξ : Xi I.G I.M) (e : REnd V) : Option V :=
  match (R.e2Order ξ.1 e.port).idxOf? e with
  | none => none
  | some i => (inOrder ξ.2 e.port (I.cand e.port \ R.used ξ.1 e.port))[i]?

open Classical in
/-- [s7:consRound] (e) the junction of an end: by (e1) for a coloured hub item of a non-ultra hub,
by (e2) for a coloured hub item of an ultra hub and for an end of a PAR object. -/
noncomputable def junction (ξ : Xi I.G I.M) : REnd V → Option V
  | .par o b => R.e2Junc ξ (.par o b)
  | .hub h u => if I.ultra h then R.e2Junc ξ (.hub h u) else (R.e1State ξ.1).junc (h, u)

/-- [s7:consRound] (e3) "A PAR object whose two ends received the same junction". -/
def Looped (ξ : Xi I.G I.M) (o : ParObj V) : Prop :=
  ∃ w, R.junction ξ (.par o false) = some w ∧ R.junction ξ (.par o true) = some w

open Classical in
/-- [s7:consRound] (e3) "*Loops.* A PAR object whose two ends received the same junction is paid.
A looped `J^par` item costs one single edge; a looped cherry costs its two edges." -/
noncomputable def loopPaid (ξ : Xi I.G I.M) : Finset (Sym2 V) :=
  (R.parObjs.filter (R.Looped ξ)).biUnion (fun o => o.edgeList.toFinset)

open Classical in
/-- The unpaid PAR objects (not looped). -/
noncomputable def unpaidPar (ξ : Xi I.G I.M) : Finset (ParObj V) :=
  R.parObjs.filter (fun o => ¬ R.Looped ξ o)

/-- [s7:consRound] (e) "Every end of a coloured hub item or of an unpaid PAR object now has a
junction `w`. … The edge `uw` is the *junction edge* of that end." -/
noncomputable def junctionEdges (ξ : Xi I.G I.M) : Finset (Sym2 V) :=
  (R.colouredHub ξ.1).biUnion (fun it =>
      (R.junction ξ (.hub it.1 it.2)).toFinset.image (fun w => s(it.2, w))) ∪
    (R.unpaidPar ξ).biUnion (fun o => (Finset.univ : Finset Bool).biUnion (fun b =>
      (R.junction ξ (.par o b)).toFinset.image (fun w => s(o.endAt b, w))))

/-! ### (g) layers, ranks and the quotient -/

/-- The edge of `Q_l` of a layer edge in the sub-layer of rank `ι`: for a PAR object of colour `κ`
whose ends have the junctions `w₁ ≠ w₂`, the edge `[w₁][w₂]` of `B^{P,(ι)}_κ`; for a coloured hub
item `(h,u)` of colour `κ` with junction `w`, the edge `h[w]` of `B^{H,(ι)}_κ` (none otherwise). -/
noncomputable def qEdge (ξ : Xi I.G I.M) (ι : ℕ) : LayerEdge V → Option (Sym2 (QVert V))
  | .inl o =>
    match R.parColour o, R.junction ξ (.par o false), R.junction ξ (.par o true) with
    | some κ, some w₁, some w₂ =>
      if w₁ = w₂ then none else some s((parTag κ ι, w₁), (parTag κ ι, w₂))
    | _, _, _ => none
  | .inr it =>
    match R.hubColour ξ.1 it, R.junction ξ (.hub it.1 it.2) with
    | some κ, some w => some s((hubTag κ ι true, it.1), (hubTag κ ι false, w))
    | _, _ => none

/-- [s7:consRound] (g) the layer edges: "For `κ ∈ [3M_l]` the *PAR layer* `B^P_κ` … has one edge
`[w_1][w_2]` for every unpaid PAR object of colour `κ` whose ends have the junctions `w_1` and
`w_2`" and "For `κ ∈ [4M_l]` the *HUB layer* `B^H_κ` … has one edge `h[w]` for every coloured hub
item `(h,u)` of colour `κ` whose junction is `w`." -/
noncomputable def layerEdges (ξ : Xi I.G I.M) : Finset (LayerEdge V) :=
  (R.unpaidPar ξ).image Sum.inl ∪ (R.colouredHub ξ.1).image Sum.inr

/-- [s7:consRound] (g) "*Rank split:* in every layer, the edges joining the same two vertices are
listed in a fixed order, and the `i`-th edge of such a list has *rank* `i`": one more than the
number of earlier edges of the rank order with the same layer and the same two vertices (compared
through their rank-`0` `Q`-edge `qEdge ξ 0`, i.e. the same kind, colour and end pair). The prefix
test is the decidable inequality `decide (e' ≠ e)` (fix round 2: not `e' != e`, whose instance
`Sum.instBEq` has no `LawfulBEq` and an unexposed body, so no module proof could rewrite it). -/
noncomputable def rank (ξ : Xi I.G I.M) (e : LayerEdge V) : ℕ :=
  (((R.rankOrder ξ).takeWhile (fun e' => decide (e' ≠ e))).filter
    (fun e' => decide (R.qEdge ξ 0 e' = R.qEdge ξ 0 e))).length + 1

theorem qEdge_not_isDiag (ξ : Xi I.G I.M) (ι : ℕ) (e : LayerEdge V) (q : Sym2 (QVert V))
    (h : R.qEdge ξ ι e = some q) : ¬ q.IsDiag := by
  rcases e with o | it
  · simp only [qEdge] at h
    split at h
    · split_ifs at h with hw
      cases h
      simp only [Sym2.mk_isDiag_iff, Prod.mk.injEq, true_and]
      exact hw
    · cases h
  · simp only [qEdge] at h
    split at h
    · cases h
      simp [hubTag]
    · cases h

/-- The edges of the quotient: the layer edges, each in the sub-layer of its rank. -/
noncomputable def qEdges (ξ : Xi I.G I.M) : Finset (Sym2 (QVert V)) :=
  (R.layerEdges ξ).biUnion (fun e => (R.qEdge ξ (R.rank ξ e) e).toFinset)

/-- [s7:consRound] (g) "The *quotient* `Q_l` is the vertex-disjoint union of all sub-layers
`B^{P,(ι)}_κ` (`κ ∈ [3M_l]`, `ι ≥ 1`) and `B^{H,(ι)}_κ` (`κ ∈ [4M_l]`, `ι ≥ 1`), with the isolated
vertices of each sub-layer deleted. Vertices of distinct sub-layers are distinct vertices of
`Q_l`". A vertex of the sub-layer `(kind, κ, ι)` is a tagged copy; the vertex set is the set of
ends of edges (isolated vertices deleted). -/
noncomputable def Q (ξ : Xi I.G I.M) : FGraph (QVert V) where
  verts := (R.qEdges ξ).biUnion Sym2.toFinset
  edges := R.qEdges ξ
  edge_verts e he v hv := Finset.mem_biUnion.2 ⟨e, he, Sym2.mem_toFinset.2 hv⟩
  loopless e he := by
    obtain ⟨le, -, hle⟩ := Finset.mem_biUnion.1 he
    exact R.qEdge_not_isDiag ξ _ le e (Option.mem_toFinset.1 hle)

/-- [s7:lemMULT] "For a HUB colour `κ`, a hub `h` and `w ∈ Pool_l`, let `m_κ(h,w)` be the number of
edges `h[w]` of `B^H_κ`, that is, the number of coloured hub items `(h,u)` of colour `κ` with
junction `w`." -/
noncomputable def mHub (ξ : Xi I.G I.M) (κ : ℕ) (h w : V) : ℕ :=
  ((R.colouredHub ξ.1).filter (fun it => it.1 = h ∧ R.hubColour ξ.1 it = some κ ∧
    R.junction ξ (.hub it.1 it.2) = some w)).card

open Classical in
/-- [s7:lemCC] "For a PAR colour `κ` and `w ≠ w'` in `Pool_l`, let `m_κ(w,w')` be the number of
edges `[w][w']` of `B^P_κ`." -/
noncomputable def mPar (ξ : Xi I.G I.M) (κ : ℕ) (w w' : V) : ℕ :=
  ((R.unpaidPar ξ).filter (fun o => R.parColour o = some κ ∧ ∃ w₁ w₂,
    R.junction ξ (.par o false) = some w₁ ∧ R.junction ξ (.par o true) = some w₂ ∧
      s(w₁, w₂) = s(w, w'))).card

/-! ### (f) the Markov choice -/

/-- [s7:consRound] (f) "`copies_l := |V(Q_l)|`". -/
noncomputable def copies (ξ : Xi I.G I.M) : ℕ := (R.Q ξ).card

/-- [s7:consRound] (f) "Let `pay^rd_l` be the number of edges paid in (d) and (e3)". -/
noncomputable def payrd (ξ : Xi I.G I.M) : ℕ := (R.sdrPaid ξ.1 ∪ R.loopPaid ξ).card

/-- [s7:consRound] (f) "The round randomness `ξ_l` is chosen in the event
`{copies_l ≤ 4 E[copies_l | Past_l]} ∩ {pay^rd_l ≤ 4 E[pay^rd_l | Past_l]}`" (`E[·|Past_l]` is
the expectation under `roundLaw`, the past being the parameter `I`). -/
def MarkovEvent (ξ : Xi I.G I.M) : Prop :=
  (R.copies ξ : ℝ) ≤ 4 * (roundLaw I.G I.M).expect (fun ξ' => (R.copies ξ' : ℝ)) ∧
    (R.payrd ξ : ℝ) ≤ 4 * (roundLaw I.G I.M).expect (fun ξ' => (R.payrd ξ' : ℝ))

open Classical in
/-- [s7:consRound] (f), [s7:lemOneOutcome] (iii) "draw `ξ_l` and choose it in the event of
Construction (f)": an outcome of positive weight in the Markov event (TRIAGE §2.10: `if h : ∃ ξ,
0 < w ξ ∧ markovEvent … then Classical.choose h else default`; the event has probability
`≥ 1/2`, a Spec obligation, so the fallback is never taken). -/
noncomputable def xiChosen : Xi I.G I.M :=
  if h : ∃ ξ, 0 < (roundLaw I.G I.M).w ξ ∧ R.MarkovEvent ξ then Classical.choose h
  else Classical.arbitrary _

/-! ### (h) decompose and lift -/

/-- The layer edge of an edge `q` of `Q_l` (unique by Lemma [s7:lemSimple]; the first one in
`Finset.toList` order otherwise). -/
noncomputable def layerOf (ξ : Xi I.G I.M) (q : Sym2 (QVert V)) : Option (LayerEdge V) :=
  open Classical in
  ((R.layerEdges ξ).filter (fun e => R.qEdge ξ (R.rank ξ e) e = some q)).toList.head?

open Classical in
/-- The part of a lifted closed walk contributed by a layer edge entered at the vertex `a`: for a
PAR object `o_i` entered at its junction `w_i`, "`p_i (x_i) q_i`" (`p_i` the end with junction
`w_i`, `x_i` the middle if `o_i` is a cherry, `q_i` the other end); for a hub item `(h,u)`, the
port `u`. -/
noncomputable def interior (ξ : Xi I.G I.M) : LayerEdge V → V → List V
  | .inl o, a =>
    if R.junction ξ (.par o false) = some a then
      o.endAt false :: (o.middle.toList ++ [o.endAt true])
    else o.endAt true :: (o.middle.toList ++ [o.endAt false])
  | .inr it, _ => [it.2]

/-- [s7:consRound] (h) the lift of a member of `Dec_l`:
* "A single edge of a PAR sub-layer is a PAR object. It is output as its one (`J^par`) or two
  (cherry) J-edges, each as a single edge. A single edge `h[w]` of a HUB sub-layer is a coloured
  hub item `(h,u)`, and it is output as the single edge `hu`."
* "A cycle `[w_0][w_1]⋯[w_{m-1}]` of a PAR sub-layer … The lift is the closed walk
  `w_0 p_0 (x_0) q_0 w_1 p_1 (x_1) q_1 w_2 ⋯ q_{m-1} w_0`" and "A cycle
  `h_0[w_0]h_1[w_1]⋯h_{m-1}[w_{m-1}]h_0` of a HUB sub-layer … The lift is the closed walk
  `h_0 u_0 w_0 u'_0 h_1 u_1 w_1 u'_1 h_2 ⋯ u'_{m-1} h_0`": each edge `ab` of the cycle (in cyclic
  order) contributes `a` followed by the interior of its layer edge entered at `a`. -/
noncomputable def liftObj (ξ : Xi I.G I.M) : Obj (QVert V) → List (Obj V)
  | .edge q =>
    match R.layerOf ξ q with
    | some (.inl o) => o.edgeList.map Obj.edge
    | some (.inr it) => [Obj.edge s(it.1, it.2)]
    | none => []
  | .cycle c =>
    [Obj.cycle ((c.zip (c.rotate 1)).flatMap (fun ab => ab.1.2 ::
      (match R.layerOf ξ s(ab.1, ab.2) with
        | some e => R.interior ξ e ab.1.2
        | none => [])))]

/-- [s7:consRound] (h) "`LentJV_l` [is] the set of junction edges that lie on lifted cycles". -/
noncomputable def lentJV (ξ : Xi I.G I.M) : Finset (Sym2 V) :=
  open Classical in
  (R.junctionEdges ξ).filter (fun e => ∃ c ∈ R.dec ξ, c.isEdge = false ∧
    ∃ o ∈ R.liftObj ξ c, e ∈ o.edges)

/-- [s7:consRound] (h) "the single edges paid in (a), (b), (d) and (e3)". -/
noncomputable def paidEdges (ξ : Xi I.G I.M) : Finset (Sym2 V) :=
  I.paidA ∪ R.unpairedLegs ∪ R.sdrPaid ξ.1 ∪ R.loopPaid ξ

/-- [s7:consRound] (h) "Put `Obj_l :=` (the single edges paid in (a), (b), (d) and (e3)) together
with (the lifted objects of all members of `Dec_l`)". -/
noncomputable def objs (ξ : Xi I.G I.M) : List (Obj V) :=
  (R.paidEdges ξ).toList.map Obj.edge ++ (R.dec ξ).flatMap (R.liftObj ξ)

/-- The output `(Obj_l, LentJV_l)` of the round step on the chosen `ξ_l` (the J-consumer's
`out l J_l`, s6:defJconsumer). -/
noncomputable def out : List (Obj V) × Finset (Sym2 V) :=
  (R.objs R.xiChosen, R.lentJV R.xiChosen)

/-- The quotient `Q_l` on the chosen `ξ_l`. -/
noncomputable def quotient : FGraph (QVert V) := R.Q R.xiChosen

/-! ### The correctness conditions of the fixed rules -/

/-- The coloured hub items of non-ultra hubs (processed in (e1)). -/
noncomputable def e1Items (L : Lists I.G I.M) : Finset (V × V) :=
  open Classical in (R.colouredHub L).filter (fun it => ¬ I.ultra it.1)

/-- [s7:consRound] the side conditions of the fixed rules ("Rules with these arguments exist",
`Rules.exists_valid` in Lib):
* (b) the pairing list at a fresh centre enumerates its live `J^fr` items once each, and the
  colouring order enumerates the PAR objects once each;
* (c) the live items of a non-ultra hub `h` are split into (at most) `k_h` groups, numbered
  `0,…,k_h − 1`, "of at most `⌈Hcd_l/8⌉` items each";
* (d) where an SDR exists, the rule chooses one;
* (e1) the processing order enumerates the coloured hub items of non-ultra hubs once each, and
  the order of `V(G)` is an enumeration of `V(G)`;
* (e2) the order of `E'(u)` enumerates `E'(u)` once each;
* (g) the rank order enumerates the layer edges once each;
* (h) "`Dec_l` [is] a decomposition of `E(Q_l)` into `f(Q_l)` objects". -/
structure Valid : Prop where
  pairing : ∀ x ∈ I.fresh, (R.pairing x).Nodup ∧ (R.pairing x).toFinset = I.frPorts x
  parOrder : R.parOrder.Nodup ∧ R.parOrder.toFinset = R.parObjs
  group : ∀ h, ¬ I.ultra h →
    (∀ it ∈ I.hubItems, it.1 = h → R.group it < I.kh h) ∧
    ∀ i, (I.hubItems.filter (fun it => it.1 = h ∧ R.group it = i)).card ≤ I.groupCap
  sdr : ∀ L u, R.SDRExists L u →
    (∀ it ∈ I.hubItemsAt u, R.sdr L it ∈ R.hubList L it) ∧
      Set.InjOn (R.sdr L) (I.hubItemsAt u : Set (V × V))
  e1Order : ∀ L, (R.e1Order L).Nodup ∧ (R.e1Order L).toFinset = R.e1Items L
  vertOrder : ∀ L, (R.vertOrder L).Nodup ∧ (R.vertOrder L).toFinset = I.G.verts
  e2Order : ∀ L u, (R.e2Order L u).Nodup ∧ (R.e2Order L u).toFinset = R.E' L u
  rankOrder : ∀ ξ, (R.rankOrder ξ).Nodup ∧ (R.rankOrder ξ).toFinset = R.layerEdges ξ
  dec : ∀ ξ, IsDecomp ((R.Q ξ).edges : Set (Sym2 (QVert V))) (R.dec ξ) ∧
    (R.dec ξ).length = fnum (R.Q ξ).edges

end Rules

/-! ## The chosen fixed rules and the J-consumer of s7 (JV-SAME-Q) -/

namespace RoundInput

variable {V : Type*} [DecidableEq V] (I : RoundInput V)

/-- Junk rules (all lists empty, all numbers `0`): used by `chosenRules` only when no valid rule
exists, which never happens for a valid input (`Rules.exists_valid`, `chosenRules_valid` in Lib). -/
def junkRules : Rules I where
  pairing _ := []
  parOrder := []
  group _ := 0
  sdr _ _ := 0
  e1Order _ := []
  vertOrder _ := []
  e2Order _ _ := []
  rankOrder _ := []
  dec _ := []

open Classical in
/-- [s7:consRound] *Fixed rules*: "the steps below use fixed deterministic rules …". One fixed
choice of valid rules for the past `I` (junk if none exists; for a valid input one exists,
`Rules.exists_valid`). The J-consumer output `out` and the quotient `quotient` of the same round
are both taken with these rules and the same `ξ_l` (`Rules.xiChosen`), so the objects and the
quotient graph used by Theorem [s7:thmJVps] belong to one and the same run of the round step
(JV-SAME-Q, blueprint s7b). -/
noncomputable def chosenRules : Rules I :=
  if h : ∃ R : Rules I, R.Valid then Classical.choose h else I.junkRules

end RoundInput

section consumer

variable {V : Type*} [DecidableEq V]

/-- [s7:consRound] "the J-consumer": the rule `(l, J_l) ↦ (Obj_l, LentJV_l)` of the round step on
the past read from a run (`RoundInput.ofPast`), with the chosen fixed rules and the chosen `ξ_l`.
It has the type of the field `EG.Chain.JConsumer.out` (for fixed `run, G, δ, S, π`). -/
noncomputable def roundOut (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V)
    (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V)) :
    List (Obj V) × Finset (Sym2 V) :=
  (RoundInput.ofPast run G δ S π l J).chosenRules.out

/-- [s7:consRound] (g) "the quotient `Q_l`" of the same round step as `roundOut` (same rules, same
`ξ_l`). -/
noncomputable def roundQuotient (run : Run V) (G : FGraph V) (δ : Designation V)
    (S : StageData V) (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V)) :
    FGraph (QVert V) :=
  (RoundInput.ofPast run G δ S π l J).chosenRules.quotient

end consumer

end EG.Quot
