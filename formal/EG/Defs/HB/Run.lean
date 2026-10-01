module

public import EG.Defs.HB.Round

/-!
# Valid `HB*^{τ+}` runs, ancestors and multiplicities
(manuscript s2:defHBtp, s2:defAncestors; `ε_A`, `ψ` of s2:lemTower; (H) of s2:lemLacunary)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s2.tex`. Design note: `formal/work/p2d/hb.md`. Namespace `EG.HB`.

Data model (TRIAGE §2.1, §2.2; PLAN §3 decision 5):
* `EG.HB.Run V` records the **choices** only: one `RoundChoice` per round `1, …, R`
  (`run.rounds`, `R = run.R = run.rounds.length`). Rounds are **1-indexed**: round `l` uses
  `run.choice l = run.rounds[l-1]` (TRIAGE §2.1; offsets are written `r + 2 ≤ l`, never with
  `ℕ`-subtraction);
* every object of round `l` is the round-local object of `EG.HB.Round` applied to
  `(run.graph G l, run.choice l)` (decision DR-ROUND-LOCAL), where `run.graph G l = G_l` is
  defined by recursion over the rounds (`G_1 = G`, `G_{l+1} = Round.next G_l c_l` for
  `1 ≤ l ≤ R`; stationary for `l ≥ R + 1`);
* the index sets of parts are guarded: for `l ∉ [1,R]` there are no pieces, no pre-parts, no
  parts, `D_l = ∅`, `Dup*_l = ∅`, `E_l = ∅`, every edge passes down (`assign = none`), and
  `Cyc_l = []` (TRIAGE §2.1 "Stationarity");
* parts, ancestors and light parts are `PartId = ℕ × Addr` (round, pre-part address); this is the
  one index type for pre-parts, parts, light parts, ancestors and classes (TRIAGE §2.1 "Part
  identity"); never a vertex set;
* `Run.Valid run G Dstar` (TRIAGE §2.2): every round `l ∈ [1,R]` has `D_* ≤ d_l` and valid
  choices (`Round.Valid`), and `d_{R+1} < D_*`.

Derived objects are ordinary `@[expose]` definitions (the Defs are locked; `irreducible_def` is
not used because it expands to a declaration form that the project lint forbids); the
characterization lemmas are in `EG.Lib.HB.Run`.
-/

@[expose] public section

namespace EG.HB

/-- [s2:defHBtp] "A *valid `HB*^{τ+}` run* is an execution of this procedure with any witnesses in
both levels of (R3), any vertex order in (R1), and any home orders in (R4)": the choices of an
execution, one `RoundChoice` per round (`rounds[l-1]` is round `l`). Validity is `Run.Valid`. -/
structure Run (V : Type*) where
  /-- The choices of rounds `1, …, R`. -/
  rounds : List (RoundChoice V)

/-- The identity of a part / pre-part / ancestor / light part: (round, pre-part address in the
two-level recursion of that round) (TRIAGE §2.1). -/
abbrev PartId := ℕ × Addr

namespace Run

variable {V : Type*} (run : Run V)

/-- [s2:defHBtp] (R0) "If `d_l < D_*`, stop, and put … `R := l - 1`": the number of rounds, the
length of the list of choices (a valid run stops exactly after round `R`, `Run.Valid`). -/
def R : ℕ := run.rounds.length

/-- The choices of round `l` (1-indexed: `rounds[l-1]`); the default (empty) choice for
`l > R`. At `l = 0`, `ℕ`-subtraction gives `0 - 1 = 0`, so `run.choice 0 = run.choice 1` (the
choices of round 1): a junk value, harmless because there is no round `0` (every guarded index
set is empty at `l = 0`, and statements bound `l` by `run.IsRound l`, i.e. `1 ≤ l ≤ R`). -/
def choice (l : ℕ) : RoundChoice V := run.rounds.getD (l - 1) default

/-- `l` is a round of the run: `1 ≤ l ≤ R`. -/
def IsRound (l : ℕ) : Prop := 1 ≤ l ∧ l ≤ run.R

instance (l : ℕ) : Decidable (run.IsRound l) := inferInstanceAs (Decidable (_ ∧ _))

variable [DecidableEq V]

/-- [s2:defHBtp] "Put `G_1 := G`. All graphs `G_l`, `G'_l` below have vertex set `V(G)`" and (R5)
"(4) … `E(G_{l+1})` is the set of these edges": `run.graph G l = G_l`. `G_1 = G`,
`G_{l+1} = Round.next G_l c_l` for `1 ≤ l ≤ R`; stationary afterwards (`G_l = G_{R+1}` for
`l ≥ R + 1`, carrying `E_0`). `run.graph G 0 = G` is a junk value (there is no round `0`). -/
noncomputable def graph (G : FGraph V) : ℕ → FGraph V
  | 0 => G
  | l + 1 => if run.IsRound l then Round.next (graph G l) (run.choice l) else graph G l

/-- [s2:defHBtp] (R0) "`d_l := 2|E(G_l)|/n`" (`n = |V(G)| = |V(G_l)|`). -/
noncomputable def d (G : FGraph V) (l : ℕ) : ℝ := Round.d (run.graph G l)

/-- [s2:defHBtp] (R0) "`λ_l := log d_l`". -/
noncomputable def lam (G : FGraph V) (l : ℕ) : ℝ := lamOf (run.d G l)

/-- [s2:defHBtp] (R1) "`t^HB_l := log² d_l`". -/
noncomputable def tHB (G : FGraph V) (l : ℕ) : ℝ := tHBOf (run.d G l)

/-- [s2:defHBtp] (R1) the long-cycle threshold `T_l = t^HB_l d_l`. -/
noncomputable def T (G : FGraph V) (l : ℕ) : ℝ := TOf (run.d G l)

/-- [s2:defHBtp] (R2) "`M_l := ⌈max(2^{40}, 2^{16} t^HB_l d_l log⁴(t^HB_l d_l))⌉ ∈ ℕ`". -/
noncomputable def M (G : FGraph V) (l : ℕ) : ℕ := MOf (run.d G l)

/-- [s2:defHBtp] (R2) "`Λ_l := log M_l`". -/
noncomputable def Lam (G : FGraph V) (l : ℕ) : ℝ := LamOf (run.d G l)

/-- [s2:defHBtp] (R2) "`s_l := ⌈Λ_l^σ⌉`". -/
noncomputable def s (G : FGraph V) (l : ℕ) : ℕ := sOf (run.d G l)

/-- [s2:defHBtp] (R2) "`P_l := ⌈λ_l^{C'}⌉`". -/
noncomputable def P (G : FGraph V) (l : ℕ) : ℕ := POf (run.d G l)

/-- [s2:defHBtp] (R2) "`τ_l := ⌈128 s_l log² M_l⌉`". -/
noncomputable def tau (G : FGraph V) (l : ℕ) : ℕ := tauOf (run.d G l)

/-! ### Round objects of round `l` -/

/-- [s2:defHBtp] (R1) "The deleted cycles form `Cyc_l`" (`[]` outside `[1,R]`). -/
def cycles (l : ℕ) : List (List V) := if run.IsRound l then (run.choice l).cycles else []

/-- [s2:defHBtp] (R1) `E(Cyc_l)`, the edge set of the deleted cycles of round `l` (`∅` outside
`[1,R]`, as `cycles`). For a round `l`, `run.graph' G l = run.graph G l - run.cycEdges l`
(`EG.HB.Run.graph'_eq_deleteEdges`); s2:propStructure (iii) and s2:lemCap (ii) read it. -/
def cycEdges (l : ℕ) : Finset (Sym2 V) := ((run.cycles l).flatMap cycleEdges).toFinset

/-- [s2:defHBtp] (R1) "the remaining graph is `G'_l`". -/
noncomputable def graph' (G : FGraph V) (l : ℕ) : FGraph V :=
  Round.graph' (run.graph G l) (run.choice l)

/-- The `s = 0` recursion of round `l` ((R3), first level). -/
def tree0 (l : ℕ) : STree V := (run.choice l).tree0

/-- The `τ`-run tree of round `l` at the piece address `a` ((R3), second level). Only meaningful
at the **big** pieces `a ∈ run.bigPieceAddrs G l` (`|𝒫| ≥ P_l`): at a small piece, or at an
address that is not a piece, it is an unconstrained choice (`Round.Valid` says nothing about it
and the two-level recursion does not graft it). Statements read `tauRun` only at big pieces. -/
def tauRun (l : ℕ) (a : Addr) : STree V := (run.choice l).tauRun a

/-- [s2:defHBtp] (R3) the addresses of the `s = 0` pieces of round `l` (`∅` outside `[1,R]`). -/
def pieceAddrs (l : ℕ) : Finset Addr :=
  if run.IsRound l then Round.pieceAddrs (run.choice l) else ∅

/-- [s2:defHBtp] (R3) the graph of the piece at address `a` of round `l`. -/
noncomputable def piece (G : FGraph V) (l : ℕ) (a : Addr) : FGraph V :=
  Round.piece (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R3) "Inside every piece with `|𝒫| ≥ P_l`, run the `τ`-run of `𝒫`": the
addresses of the *big* pieces of round `l` (`∅` outside `[1,R]`, as `pieceAddrs`). These are the
pieces whose `τ`-run (`run.tauRun l a`) is part of the two-level recursion. -/
noncomputable def bigPieceAddrs (G : FGraph V) (l : ℕ) : Finset Addr :=
  (run.pieceAddrs l).filter (fun a => run.P G l ≤ (run.piece G l a).card)

/-- [s2:defHBtp] (R3) the two-level recursion of round `l`. -/
noncomputable def twoLevel (G : FGraph V) (l : ℕ) : STree V :=
  Round.twoLevel (run.graph G l) (run.choice l)

/-- [s2:defHBtp] (R3) `X^0_Z`, the leaf graph at address `a` of round `l`. -/
noncomputable def X0 (G : FGraph V) (l : ℕ) (a : Addr) : FGraph V :=
  Round.X0 (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R3) `Z^0`, the vertex set of the pre-part at address `a` of round `l`. -/
noncomputable def Z0 (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  Round.Z0 (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (GC) "`θ^GC_l(Z^0) := ⌈|Z^0| λ_l^{-1/2}⌉`" for the pre-part at address `a` of
round `l` (address form, as in blueprint s6b `run.thetaGC G r a`; it is
`EG.HB.thetaGC (run.d G l) (run.Z0 G l a).card`, `EG.HB.Run.thetaGC_eq`). -/
noncomputable def thetaGC (G : FGraph V) (l : ℕ) (a : Addr) : ℕ :=
  EG.HB.thetaGC (run.d G l) (run.Z0 G l a).card

/-- [s2:defHBtp] (R3) the addresses of the round-`l` pre-parts (`∅` outside `[1,R]`). -/
noncomputable def prePartAddrs (G : FGraph V) (l : ℕ) : Finset Addr :=
  if run.IsRound l then Round.prePartAddrs (run.graph G l) (run.choice l) else ∅

/-- [s2:defHBtp] (R3) `Dup*_l` (`∅` outside `[1,R]`). -/
noncomputable def DupStar (G : FGraph V) (l : ℕ) : Finset V :=
  if run.IsRound l then Round.DupStar (run.graph G l) (run.choice l) else ∅

/-- [s2:defAncestors] "`μ_r(w)` is the number of round-`r` pre-parts containing `w`" (`0` outside
`[1,R]`). -/
noncomputable def mu (G : FGraph V) (r : ℕ) (w : V) : ℕ :=
  if run.IsRound r then Round.mu (run.graph G r) (run.choice r) w else 0

/-- [s2:defHBtp] (R4) "`D_l :=` the set of vertices lying in at least two round-`l` pre-parts"
(`∅` outside `[1,R]`). -/
noncomputable def D (G : FGraph V) (l : ℕ) : Finset V :=
  if run.IsRound l then Round.D (run.graph G l) (run.choice l) else ∅

/-- [s2:defHBtp] (R4) `home_l(v)`, the first pre-part of the home order containing `v`. -/
noncomputable def home (G : FGraph V) (l : ℕ) (v : V) : Option Addr :=
  Round.home (run.graph G l) (run.choice l) v

/-- [s2:defHBtp] (R4) the guests `S_Z` of the pre-part at address `a` of round `l`. -/
noncomputable def guests (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  Round.guests (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R4) (L1) for the pre-part `a` of round `l`. -/
noncomputable def isL1 (G : FGraph V) (l : ℕ) (a : Addr) : Prop :=
  Round.isL1 (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R4) (L2) for the pre-part `a` of round `l`. -/
noncomputable def isL2 (G : FGraph V) (l : ℕ) (a : Addr) : Prop :=
  Round.isL2 (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R4) (GC) for the pre-part `a` of round `l`. -/
noncomputable def isGC (G : FGraph V) (l : ℕ) (a : Addr) : Prop :=
  Round.isGC (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R4) the pre-part `a` of round `l` is light ((L1), (L2), (GC)). -/
noncomputable def isLight (G : FGraph V) (l : ℕ) (a : Addr) : Prop :=
  Round.isLight (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R4) the pre-part `a` of round `l` is a GC-part. -/
noncomputable def isGCPart (G : FGraph V) (l : ℕ) (a : Addr) : Prop :=
  Round.isGCPart (run.graph G l) (run.choice l) a

open Classical in
/-- [s2:defHBtp] (R4) "`Std_l` is the set of round-`l` standalone pre-parts" (addresses; `∅`
outside `[1,R]`). -/
noncomputable def Std (G : FGraph V) (l : ℕ) : Finset Addr :=
  (run.prePartAddrs G l).filter (fun a => ¬ run.isLight G l a)

/-- [s2:defHBtp] the vertex set `V(Z)` of the part of the pre-part `a` of round `l`
(`Z^0 \ S_Z` if light, `Z^0` if standalone). -/
noncomputable def partVerts (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  Round.partVerts (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R4) `X_Z = X^0_Z - S_Z` for the pre-part `a` of round `l`. -/
noncomputable def X (G : FGraph V) (l : ℕ) (a : Addr) : FGraph V :=
  Round.X (run.graph G l) (run.choice l) a

/-- The graph of the part of the pre-part `a` of round `l` (`X_Z` if light, `X^0_Z` if
standalone). -/
noncomputable def partGraph (G : FGraph V) (l : ℕ) (a : Addr) : FGraph V :=
  Round.partGraph (run.graph G l) (run.choice l) a

/-- [s2:defHBtp] (R5) the part receiving the edge `e` of `G'_l` (`none`: `e` passes down; always
`none` outside `[1,R]`). -/
noncomputable def assign (G : FGraph V) (l : ℕ) (e : Sym2 V) : Option Addr :=
  if run.IsRound l then Round.assign (run.graph G l) (run.choice l) e else none

/-- [s2:defHBtp] (R5) "`E_l(Z)` denotes the set of edges assigned at round `l` to `Z`" (`∅`
outside `[1,R]`). -/
noncomputable def E (G : FGraph V) (l : ℕ) (a : Addr) : Finset (Sym2 V) :=
  if run.IsRound l then Round.E (run.graph G l) (run.choice l) a else ∅

/-- [s2:defHBtp] (R0) "If `d_l < D_*`, stop, and put `E_0 := E(G_l)`": for a valid run the
stopping round is `R + 1`, so `E_0 = E(G_{R+1})`. -/
noncomputable def E0 (G : FGraph V) : Finset (Sym2 V) := (run.graph G (run.R + 1)).edges

/-- The piece above the node at address `a` of the two-level recursion of round `l`. -/
def pieceOf (l : ℕ) (a : Addr) : Addr := Round.pieceOf (run.choice l) a

/-! ### Validity -/

/-- [s2:defHBtp] "A *valid `HB*^{τ+}` run* is an execution of this procedure with any witnesses
in both levels of (R3), any vertex order in (R1), and any home orders in (R4)", with the loop of
(R0): "For `l = 1, 2, …`: (R0) `d_l := 2|E(G_l)|/n`. If `d_l < D_*`, stop, and put
`E_0 := E(G_l)` and `R := l - 1`."

Formal reading (TRIAGE §2.2): every round `l ∈ [1,R]` has `D_* ≤ d_l` and choices satisfying
`Round.Valid` (on its input graph `G_l`), and the run stops at `R + 1`: `d_{R+1} < D_*`. `D_*`
enters only through this stopping rule; the conditions `Γ` on `D_*` are hypotheses of the
statements, never of `Valid` (blueprint HB-DSTAR-PARAM). The existence of a valid run is
s2:propExists (a statement). -/
def Valid (G : FGraph V) (Dstar : ℝ) : Prop :=
  (∀ l ∈ Finset.Icc 1 run.R, Dstar ≤ run.d G l ∧ Round.Valid (run.graph G l) (run.choice l)) ∧
    run.d G (run.R + 1) < Dstar

/-! ### Parts and ancestors ([s2:defHBtp] Naming, [s2:defAncestors]) -/

/-- [s2:defHBtp] (Naming) "A *round-`l` part* is a light part or a standalone pre-part of round
`l`": every pre-part gives exactly one part (its light part if light, itself if standalone), so
the parts of all rounds are indexed by `(l, a)` with `l ∈ [1,R]` and `a` a round-`l` pre-part
address. -/
noncomputable def parts (G : FGraph V) : Finset PartId :=
  (Finset.Icc 1 run.R).biUnion (fun l => (run.prePartAddrs G l).image (fun a => (l, a)))

/-- [s2:defAncestors] "An *ancestor of round `r`* is either a light part `Y` of round `r` … or a
standalone pre-part `Y ∈ Std_r`, GC-parts included": the ancestors are exactly the parts
(`run.ancestors G = run.parts G`); "Every ancestor corresponds to a distinct pre-part
`Y^0 ⊇ V(Y)` of its round" is definitional (indexing by pre-part address). -/
noncomputable def ancestors (G : FGraph V) : Finset PartId := run.parts G

open Classical in
/-- The light parts of all rounds (s5 `LP`; TRIAGE §2.1 `run.lightParts G : Finset PartId`). -/
noncomputable def lightParts (G : FGraph V) : Finset PartId :=
  (run.parts G).filter (fun Y => run.isLight G Y.1 Y.2)

open Classical in
/-- The standalone pre-parts of all rounds, `{(l, a) : a ∈ Std_l}`. -/
noncomputable def stdParts (G : FGraph V) : Finset PartId :=
  (run.parts G).filter (fun Y => ¬ run.isLight G Y.1 Y.2)

/-- The ancestors of rounds at most `k` (s6:defDesign `c^agg` ranges over the ancestors of rounds
`≤ l - 2`; write `run.ancestorsUpTo G k` with `k + 2 = l`). -/
noncomputable def ancestorsUpTo (G : FGraph V) (k : ℕ) : Finset PartId :=
  (run.ancestors G).filter (fun Y => Y.1 ≤ k)

/-- [s2:defAncestors] "`V(Y) := Y` (the vertex set `Y^0 \ S_Y`)" for a light part and
"`V(Y) := Y^0`" for a standalone pre-part. -/
noncomputable def ancVerts (G : FGraph V) (Y : PartId) : Finset V := run.partVerts G Y.1 Y.2

/-- [s2:defAncestors] "`H_Y := X_Y`" for a light part and "`H_Y := X^0_Y`" for a standalone
pre-part. -/
noncomputable def ancGraph (G : FGraph V) (Y : PartId) : FGraph V := run.partGraph G Y.1 Y.2

open Classical in
/-- [s2:defAncestors] "`ε_Y := 2^{-6}`" (light) and "`ε_Y := 2^{-5}`" (standalone). -/
noncomputable def ancEps (G : FGraph V) (Y : PartId) : ℝ :=
  if run.isLight G Y.1 Y.2 then 2 ^ (-6 : ℤ) else 2 ^ (-5 : ℤ)

open Classical in
/-- [s2:defAncestors] "`s_Y := s_r/2`" (light; a real number, `s_r` may be odd) and
"`s_Y := s_r`" (standalone), with `r = r(Y)`. -/
noncomputable def ancS (G : FGraph V) (Y : PartId) : ℝ :=
  if run.isLight G Y.1 Y.2 then (run.s G Y.1 : ℝ) / 2 else (run.s G Y.1 : ℝ)

/-- [s2:defAncestors] "We write `r(Y)` for the round of `Y`". -/
def ancRound (Y : PartId) : ℕ := Y.1

/-- [s2:defAncestors] "`L_Y := log |V(Y)|`". -/
noncomputable def LY (G : FGraph V) (Y : PartId) : ℝ := Real.logb 2 (run.ancVerts G Y).card

/-- [s2:defAncestors] "For `l ≥ 3` and a vertex `x`,
`anc_l(x) := {Y : Y an ancestor of a round r ≤ l - 2 with x ∈ V(Y)}`, and `anc_l(x) := ∅` for
`l ≤ 2`." Written with `r(Y) + 2 ≤ l` (TRIAGE §2.1; rounds start at `1`, so this is `∅` for
`l ≤ 2`). -/
noncomputable def anc (G : FGraph V) (l : ℕ) (x : V) : Finset PartId :=
  (run.ancestors G).filter (fun Y => Y.1 + 2 ≤ l ∧ x ∈ run.ancVerts G Y)

/-- [s2:defAncestors] "the *hubs* of `Z` are `A_Z := Z^0 ∩ D_l`" (for `Z ∈ Std_l`; total). -/
noncomputable def hubs (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  run.Z0 G l a ∩ run.D G l

/-- [s2:defAncestors] "the *ports* of `Z` are `U_Z := Z^0 \ D_l`" (for `Z ∈ Std_l`; total). -/
noncomputable def ports (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  run.Z0 G l a \ run.D G l

/-- [s2:defAncestors] "the *fresh ports* are `F_Z := {x ∈ U_Z : anc_l(x) = ∅}` (so all ports are
fresh for `l ≤ 2`)". -/
noncomputable def fresh (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  (run.ports G l a).filter (fun x => run.anc G l x = ∅)

/-- [s2:defAncestors] "the *classed ports* are `Q_Z := U_Z \ F_Z`". -/
noncomputable def classed (G : FGraph V) (l : ℕ) (a : Addr) : Finset V :=
  run.ports G l a \ run.fresh G l a

/-- [s2:defAncestors] "`dup_r := Σ_w (μ_r(w) - 1)^+`" (over `w ∈ V(G)`; truncated subtraction in
`ℕ` is `(·)^+`). -/
noncomputable def dup (G : FGraph V) (r : ℕ) : ℕ := ∑ w ∈ G.verts, (run.mu G r w - 1)

/-- [s2:defAncestors] "`mult_r(w)` is the number of ancestors `Y` of round `r` with `w ∈ V(Y)`". -/
noncomputable def mult (G : FGraph V) (r : ℕ) (w : V) : ℕ :=
  ((run.prePartAddrs G r).filter (fun a => w ∈ run.partVerts G r a)).card

/-- [s2:propOV] (K1) "the number `ν_l` of ancestors of rounds at most `l - 2`" (written
`r(Y) + 2 ≤ l`; `0` for `l ≤ 2`). -/
noncomputable def nuAnc (G : FGraph V) (l : ℕ) : ℕ :=
  ((run.ancestors G).filter (fun Y => Y.1 + 2 ≤ l)).card

/-- [s2:defAncestors] "`j_0(x)` is the first round in which `x` lies in a pre-part" (`⊤` if there
is none; the manuscript gives no value in that case, all uses have `x` in a pre-part). -/
noncomputable def j0 (G : FGraph V) (x : V) : WithTop ℕ :=
  ((Finset.Icc 1 run.R).filter (fun r => ∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a)).min

open Classical in
/-- [s2:defAncestors] "`j_1(x)` the first round in which `x` lies in a light part (`∞` if there is
none)". -/
noncomputable def j1 (G : FGraph V) (x : V) : WithTop ℕ :=
  ((Finset.Icc 1 run.R).filter
    (fun r => ∃ a ∈ run.prePartAddrs G r, run.isLight G r a ∧ x ∈ run.partVerts G r a)).min

end Run

/-! ### Functions of `D_*` and of reals used by later sections -/

/-- [s2:lemTower] (e) "Put `ε_A := 31 ε / (C' log log D_*)`, a function of `D_*` alone (it depends
neither on the run nor on `n`)" (`ε = EG.epsC`, `C' = EG.Cp`, `log = log₂`). -/
noncomputable def epsA (Dstar : ℝ) : ℝ :=
  31 * epsC / ((Cp : ℝ) * Real.logb 2 (Real.logb 2 Dstar))

/-- [s2:lemTower] (b) "`ψ(x) := (6 log x + 12)/x`" (the pool term of `ε_X`, s7). -/
noncomputable def psiPool (x : ℝ) : ℝ := (6 * Real.logb 2 x + 12) / x

/-- [s2:lemLacunary] (iii) "if `F : [x_0, ∞) → [0, ∞)` satisfies
(H) `F(y) ≤ F(x)/2` whenever `x ≥ x_0` and `y ≥ 2^{x/A}`" (`A = EG.Aexp = 105`, `2^{x/A}` is
`Real.rpow`). `F` is a total function `ℝ → ℝ`; its domain `[x_0, ∞)` is kept as the hypothesis
`x_0 ≤ y` (and `x_0 ≤ x`); nonnegativity is a separate hypothesis of the statements. -/
def HypH (x0 : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x0 ≤ x → x0 ≤ y → (2 : ℝ) ^ (x / (Aexp : ℝ)) ≤ y → F y ≤ F x / 2

end EG.HB
