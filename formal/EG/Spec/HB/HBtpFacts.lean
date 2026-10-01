module

public import EG.Defs.HB.Run

/-!
# Statements: claims embedded in the definitions of the hierarchy (manuscript s2:defHBtp,
s2:defAncestors)

Statement file (`EG/Spec/**`), unit P2 specs chunk s2a. Status note `formal/work/p2s/s2a.md`.
Blueprint `formal/work/p2/blueprint_s2a.md`, hazard HB-EMBEDDED-CLAIMS ("The definition's text
contains claims that are lemmas, not definitions … Put them in the Run API with proofs"). The
definitions themselves are the locked Defs `EG/Defs/HB/Round.lean`, `EG/Defs/HB/Run.lean`; this
file states, as proof obligations, the sentences of the two definitions that assert something
about the defined objects (and are not definitional in the Lean model):
* `HBMCeilStatement`: (R2) "only two facts about the ceiling are used";
* `HBTwoLevelStatement`: (R3) the leaves of the two-level recursion, and "equivalently" in the
  definition of pre-parts;
* `HBStdStatement`: (R4) "`Std_l` … contains the GC-parts and the pre-parts failing (L1) or
  (L2)";
* `HBStep1Statement`: (R5)(1) "no edge is assigned twice in this step";
* `AncestorFactsStatement`: the "so"-claims of [s2:defAncestors].
Sentences that are definitional in the Lean model are not restated: (R1) "Thus `G'_l` has no cycle
of length at least `t^HB_l d_l`" (a field of `Round.CyclesValid`), "`X^0_Z` its leaf graph, a graph
on `Z^0`" (`Z0 := (X0 …).verts`), "`Std_l` … is a deterministic function of the run", "Every
ancestor corresponds to a distinct pre-part" (ancestors are indexed by pre-part addresses; its
content "`Y^0 ⊇ V(Y)`" is a conjunct of `AncestorFactsStatement`).

Formal reading (common).
* Round-level statements take the input graph `H = G_l` and the choices `c : RoundChoice V` of
  the round. `HBStep1Statement` assumes `Round.Valid H c` (the disjointness rests on Lemma SEP (i)
  for the two-level recursion, which needs its split conditions); the other round-level claims hold
  for every execution of the procedure and are stated without a validity hypothesis (stronger).
* "small piece" = a piece `q` with `|𝒫| < P_l` (`q ∉ bigPieceAddrs`); a leaf `b` of the `τ`-run of
  the big piece `q` has address `q ++ b` in the two-level recursion (`STree.graft`).
* `AncestorFactsStatement` assumes a valid run (the context "Fix a valid `HB^tp` run").
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:defHBtp] (R2) "`M_l := ⌈max(2^{40}, 2^{16} t^HB_l d_l log⁴(t^HB_l d_l))⌉ ∈ ℕ` … Besides
integrality, only two facts about the ceiling are used:
`M_l ≥ max(2^{40}, 2^{16} t^HB_l d_l log⁴(t^HB_l d_l))`, and
`M_l ≤ max(2^{40}, 2^{16} t^HB_l d_l log⁴(t^HB_l d_l)) + 1`." (For every real `d = d_l`;
`t^HB_l d_l = TOf d`.) -/
def HBMCeilStatement : Prop :=
  ∀ d : ℝ,
    max (2 ^ 40) (2 ^ 16 * TOf d * Real.logb 2 (TOf d) ^ 4) ≤ (MOf d : ℝ) ∧
    (MOf d : ℝ) ≤ max (2 ^ 40) (2 ^ 16 * TOf d * Real.logb 2 (TOf d) ^ 4) + 1

/-- [s2:defHBtp] (R3) "The *two-level recursion* of round `l` is the split recursion obtained from
the `s = 0` recursion by attaching, at every piece `𝒫` with `|𝒫| ≥ P_l`, the tree of its `τ`-run.
Its leaves are the pieces of size less than `P_l` and the leaves of the `τ`-runs. The *round-`l`
pre-parts* are the leaves of the `τ`-runs with at least `P_l` vertices; equivalently, the leaves of
the two-level recursion with at least `P_l` vertices."
Conjuncts: (1) the leaf addresses of the two-level recursion are the small pieces and the
addresses `q ++ b` of the leaves `b` of the `τ`-runs of the big pieces `q`; (2) their graphs are
the piece graph, resp. the leaf graph of the `τ`-run (rooted at the piece graph); (3) the
pre-parts (defined in `Round.prePartAddrs` by the second form) are exactly the leaves of the
`τ`-runs with at least `P_l` vertices. -/
def HBTwoLevelStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V),
    (∀ a : Addr, a ∈ (Round.twoLevel H c).leafAddrs ↔
      (a ∈ Round.pieceAddrs c ∧ (Round.piece H c a).card < POf (Round.d H)) ∨
      ∃ q ∈ Round.bigPieceAddrs H c, ∃ b ∈ (c.tauRun q).leafAddrs, a = q ++ b) ∧
    (∀ q ∈ Round.pieceAddrs c, (Round.piece H c q).card < POf (Round.d H) →
      Round.X0 H c q = Round.piece H c q) ∧
    (∀ q ∈ Round.bigPieceAddrs H c, ∀ b ∈ (c.tauRun q).leafAddrs,
      Round.X0 H c (q ++ b) = (c.tauRun q).graphAtD (Round.piece H c q) b) ∧
    ∀ a : Addr, a ∈ Round.prePartAddrs H c ↔
      ∃ q ∈ Round.bigPieceAddrs H c, ∃ b ∈ (c.tauRun q).leafAddrs, a = q ++ b ∧
        POf (Round.d H) ≤ ((c.tauRun q).graphAtD (Round.piece H c q) b).card

/-- [s2:defHBtp] (R4) "A pre-part satisfying (L1) and (L2) but failing (GC) is a *GC-part*; it is
standalone. … `Std_l` is the set of round-`l` standalone pre-parts; it contains the GC-parts and
the pre-parts failing (L1) or (L2)". -/
def HBStdStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V),
    ∀ a ∈ Round.prePartAddrs H c,
      (Round.isGCPart H c a ∨ ¬ Round.isL1 H c a ∨ ¬ Round.isL2 H c a) → a ∈ Round.Std H c

/-- [s2:defHBtp] (R5) "(1) For every light pre-part `Z` the edges of `X_Z` are assigned to the
light part `Z`; for every standalone pre-part `Z` the edges of `X^0_Z` are assigned to `Z`. (The
graphs `X^0_Z` of distinct pre-parts are edge-disjoint, being distinct leaves of the two-level
recursion, Lemma s2:lemSEP(i), and `X_Z ⊆ X^0_Z`; so no edge is assigned twice in this step.)"
Conjuncts: the `X^0_Z` of distinct pre-part addresses are edge-disjoint; `E(X_Z) ⊆ E(X^0_Z)`; an
edge lies in the step-(1) graph (`X_Z` if light, `X^0_Z` if standalone: `Round.partGraph`) of at
most one pre-part. (For a valid round.) -/
def HBStep1Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V), Round.Valid H c →
    (∀ a ∈ Round.prePartAddrs H c, ∀ b ∈ Round.prePartAddrs H c, a ≠ b →
      Disjoint (Round.X0 H c a).edges (Round.X0 H c b).edges) ∧
    (∀ a : Addr, (Round.X H c a).edges ⊆ (Round.X0 H c a).edges) ∧
    ∀ e : Sym2 V, ∀ a ∈ Round.prePartAddrs H c, ∀ b ∈ Round.prePartAddrs H c,
      e ∈ (Round.partGraph H c a).edges → e ∈ (Round.partGraph H c b).edges → a = b

/-- [s2:defAncestors] "Fix a valid `HB^tp` run. An *ancestor of round `r`* is either a light part
`Y` of round `r` … or a standalone pre-part `Y ∈ Std_r` … Every ancestor corresponds to a distinct
pre-part `Y^0 ⊇ V(Y)` of its round. For `l ≥ 3` and a vertex `x`, `anc_l(x) := …`, and
`anc_l(x) := ∅` for `l ≤ 2`. … the *fresh ports* are `F_Z := {x ∈ U_Z : anc_l(x) = ∅}` (so all
ports are fresh for `l ≤ 2`) … `μ_r(w)` is the number of round-`r` pre-parts containing `w` (so
`D_r = {w : μ_r(w) ≥ 2}`)".
Conjuncts: (0) the ancestors of round `r` are indexed exactly by the round-`r` pre-parts, `r` a
round; (1) `V(Y) ⊆ Y^0`; (2) `anc_l(x) = ∅` for `l ≤ 2` (the definition `run.anc` is the uniform
form `r(Y) + 2 ≤ l`); (3) all ports are fresh for `l ≤ 2`; (4) `D_r = {w : μ_r(w) ≥ 2}`. -/
def AncestorFactsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    run.Valid G Dstar →
      (∀ (r : ℕ) (a : Addr), (r, a) ∈ run.ancestors G ↔
        run.IsRound r ∧ a ∈ run.prePartAddrs G r) ∧
      (∀ Y ∈ run.ancestors G, run.ancVerts G Y ⊆ run.Z0 G Y.1 Y.2) ∧
      (∀ l : ℕ, l ≤ 2 → ∀ x : V, run.anc G l x = ∅) ∧
      (∀ l : ℕ, l ≤ 2 → ∀ a : Addr, run.fresh G l a = run.ports G l a) ∧
      ∀ (r : ℕ) (w : V), w ∈ run.D G r ↔ 2 ≤ run.mu G r w

end EG.Spec
