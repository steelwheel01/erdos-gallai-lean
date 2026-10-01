module

public import EG.Defs.Vortex
public import EG.Defs.Expander
public import EG.Defs.Objects

/-!
# The hypotheses and the conclusion of Lemma TPV as named predicates (manuscript s4:lemTPV)

NEW DEFS FILE of the P2 s4 Spec unit (`formal/work/p2s/s4.md`). No locked Defs file provides
them. They exist so that the consumer of Lemma TPV (s6:thmMIXC, bullet "Lemma TPV at step (1)" of
(a), and s7:lemOneOutcome (2); blueprint s6b `S4.TPVHyps` / `S4.TPVGood`, TRIAGE §2.8
"MIX-C applies the deterministic TPV Spec, plus `MixCTPVApplicable` for its hypotheses") can name
the hypotheses and the conclusion of the lemma for the data `(Z^0_Z, O_Z, Ret_Z)` without copying
them. The Spec `EG.Spec.TPVStatement` (`EG/Spec/Vortex/TPV.lean`) is stated with these predicates.

Manuscript v6.1, `s4.tex`, Lemma [s4:lemTPV]: "Let `Z` be a set of `N ≥ N_0` vertices and
`L := log₂N`. Let `O` be a spanning `(ε_O,s)`-expander on `Z` with `ε_O ∈ [2^{-7},2^{-5}]` (only
`ε_O ≥ 2^{-7}` is used in the proof) and `s ≥ 2^{150}L^{42}`, and let `Z = P ⊔ Q` be a partition.
… such that on `𝒢_TPV` the following holds for *every* edge set `E` with `E(O) ⊆ E` all of whose
edges have both ends in `Z`: there is a partition `E = E^V ⊔ E^Q` with the properties
(T1) every edge of `E` with both ends in `P` lies in `E^V`;
(T2) every edge of `E^V` with an end in `Q` is an edge of `O`;
(T3) `E^V` decomposes into at most `169|P|` objects, and `E^V = ∅` if `P = ∅`;
(T4) (no arcs) all objects of (T3) consist of edges of `E`; every path formed during the run is
closed into a cycle within the step in which it is formed, so the run leaves no path ("arc") to be
closed by any other device."

Formal reading.
* "`N ≥ N_0`": `EG.Vortex.TPVSize Z.card` (the size conditions (i), (ii), (iv) of the proof;
  TRIAGE §2.4, as `PVHyp` for Lemma PV: `N_0` is *defined* through these conditions, and
  `N0Cond N0 → N0 ≤ N → TPVSize N` gives the manuscript form).
* "spanning `(ε_O,s)`-expander on `Z`": `O.verts = Z ∧ O.IsExpander εO s` (CONVENTIONS).
  `L = EG.Vortex.L Z.card = log₂ N`; `2^{-7}`, `2^{-5}` are integer powers of the real `2`.
* "a partition `Z = P ⊔ Q`": `P ⊆ Z`, and `Q := Z \ P` (so `Q` is not a separate argument).
* Admissible `E`: loopless (T0: "an edge set of a simple graph", CONVENTIONS "Objects and f"),
  all ends in `Z`, `E(O) ⊆ E`.
* "a partition `E = E^V ⊔ E^Q`": `Disjoint EV EQ ∧ EV ∪ EQ = E`.
* (T2) "an end in `Q`": `∃ v ∈ e, v ∈ Z \ P`.
* (T3) "`E^V` decomposes into at most `169|P|` objects": a list `D` of objects with
  `IsDecomp ↑EV D` and `D.length ≤ 169 * P.card`.
* (T4): "all objects of (T3) consist of edges of `E`" follows from `IsDecomp ↑EV D` and
  `EV ⊆ E`; "no arc is left" is the fact that the objects of `D` cover `E^V` exactly (there is no
  other output). It is not a separate conjunct.
-/

@[expose] public section

namespace EG.Vortex

variable {V : Type*} [DecidableEq V]

/-- [s4:lemTPV] the hypotheses of Lemma TPV on the fixed data: "Let `Z` be a set of `N ≥ N_0`
vertices and `L := log₂N`. Let `O` be a spanning `(ε_O,s)`-expander on `Z` with
`ε_O ∈ [2^{-7},2^{-5}]` … and `s ≥ 2^{150}L^{42}`, and let `Z = P ⊔ Q` be a partition"
(`Q = Z \ P`; `N ≥ N_0` as `TPVSize N`, module docstring). -/
def TPVHyp (Z : Finset V) (O : FGraph V) (P : Finset V) (εO s : ℝ) : Prop :=
  TPVSize Z.card ∧
  O.verts = Z ∧ O.IsExpander εO s ∧
  (2 : ℝ) ^ (-7 : ℤ) ≤ εO ∧ εO ≤ (2 : ℝ) ^ (-5 : ℤ) ∧
  (2 : ℝ) ^ 150 * L Z.card ^ 42 ≤ s ∧
  P ⊆ Z

/-- [s4:lemTPV] the admissible edge sets: "every edge set `E` with `E(O) ⊆ E` all of whose edges
have both ends in `Z`" (loopless: an edge set of a simple graph). -/
def TPVAdm (Z : Finset V) (O : FGraph V) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ (∀ e ∈ E, ∀ v ∈ e, v ∈ Z) ∧ O.edges ⊆ E

/-- [s4:lemTPV] the conclusion for one edge set `E`: "there is a partition `E = E^V ⊔ E^Q` with
(T1) every edge of `E` with both ends in `P` lies in `E^V`; (T2) every edge of `E^V` with an end in
`Q` is an edge of `O`; (T3) `E^V` decomposes into at most `169|P|` objects, and `E^V = ∅` if
`P = ∅`; (T4) all objects of (T3) consist of edges of `E`" (`Q = Z \ P`). -/
def TPVConcl (Z : Finset V) (O : FGraph V) (P : Finset V) (E : Finset (Sym2 V)) : Prop :=
  ∃ EV EQ : Finset (Sym2 V), Disjoint EV EQ ∧ EV ∪ EQ = E ∧
    -- (T1)
    (∀ e ∈ E, (∀ v ∈ e, v ∈ P) → e ∈ EV) ∧
    -- (T2)
    (∀ e ∈ EV, (∃ v ∈ e, v ∈ Z \ P) → e ∈ O.edges) ∧
    -- (T3), (T4)
    (∃ D : List (Obj V), IsDecomp (EV : Set (Sym2 V)) D ∧ D.length ≤ 169 * P.card) ∧
    (P = ∅ → EV = ∅)

end EG.Vortex
