module

public import EG.Defs.PathDecomp
public import EG.Defs.Graph
public import EG.Defs.Vortex

/-!
# Statements of the PV(c) core: one phase of a PV step, the step cost, the stripping finish and
the per-vertex arc bound (manuscript s4:lemPV, proof; CR1-PV)

Statement file (`EG/Spec/**`) of probe unit P4A (probe P-4, part 1): probe nodes. Design note
`formal/work/p2b/P4A.md`. Proofs (stage 2): `EG/Proof/Vortex/PVCore.lean`.

These are the deterministic parts of the proof of Lemma PV ([s4:lemPV]) that CR1-PV changed or
that feed the per-vertex bound of (c): the case analysis of the trails of a step (types (1),
(2) and the arcs), the per-step cost (s4:eqPVstep), the multiplicity bound (s4:eqPVt), the
finish with stripping, and the per-vertex bound of (c). None of them mentions the random labels:
the good event `𝒢_PV` enters Lemma PV only through (G2), (G4), (G5), which these statements take
as hypotheses where they need them ((G5) in the finish) or do not need.

Manuscript v6.1, `s4.tex`, proof of Lemma PV (quoted in each docstring). Notation of the proof:
`U_j := Rt ∪ {v ∈ Pl : lev(v) ≥ j}`, `W_j := {v ∈ Pl : lev(v) = j}` (so `U_j = U_{j+1} ⊔ W_j`),
`F_j` the edges of `H_j` meeting `W_j`, `F_{j,c}` its non-reserved edges of phase `c`,
`e^{c,1}_w, e^{c,2}_w` the reserved `M`-edges at `w ∈ W_j` (far ends in `Z_j ⊆ U_{j+1}`),
`Paths_{j,c}` a Corollary-22 decomposition of `F_{j,c}`.

Formal reading of one phase `c` of one step `j` (`PVStepPhaseStatement`):
* `Rt`, `W` (`= W_j`) and `Up` (`= Pl ∩ U_{j+1}`) are pairwise disjoint, so
  `U_j = Rt ⊔ W ⊔ Up` and `U_{j+1} = Rt ⊔ Up` (as `W_j ⊆ Pl`, `W_j ∩ U_{j+1} = ∅`,
  `Rt ⊆ U_{j+1}`);
* `F` (`= F_{j,c}`) is loopless, every edge has both ends in `U_j` ((Inv1)) and meets `W`
  (definition of `F_j`);
* `P` (`= Paths_{j,c}`) is a Corollary-22 decomposition of `F`;
* the reserved edges of phase `c` at `w ∈ W` are `s(w, u₁ w)`, `s(w, u₂ w)`, with distinct far
  ends in `U_{j+1}` ("eight distinct edges … `u ∈ Z_j ⊆ U_{j+1}`"), and are not edges of `F`
  (`F_{j,c}` consists of non-reserved edges);
* the output of steps (iv)–(vi) for this phase: the output objects `D` (split cycles and single
  edges), the arcs `A`, and the paths `Q` of `PathsQ_{j,c}` that are closed in (vi) (each closed
  path gives one more object, the closed cycle, so the objects of the phase are `D` and one cycle
  per member of `Q`); their edges are exactly `F` and the reserved edges, each once.
The per-step cost (s4:eqPVstep) sums this over the four phases.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s4:lemPV] (proof, steps (iv)–(vi) for one phase `c` of step `j`, and the case analysis of
"Cost of step `j`"; CR1-PV). Steps: "(iv) *Ends in `W_j`.* … for every `w ∈ W_j` and `c ∈ [4]`:
if `w` is an end of two paths of `Paths_{j,c}`, append `e^{c,1}_w` to one and `e^{c,2}_w` to the
other at `w`; if of one, append `e^{c,1}_w` and output `e^{c,2}_w` as a single edge; if of none,
form the cherry `u_1wu_2` from `e^{c,1}_w = wu_1` and `e^{c,2}_w = wu_2`. (v) *Splitting.* By (S)
each trail splits into at most two cycles (output) and at most one path with the same ends as the
trail; let `PathsQ_{j,c}` be the set of these paths. … (P2) its two ends are distinct and lie in
`U_{j+1}` …; (P3) it has length at least `2`; (P4) every vertex is an end of at most `2 + b ≤ t`
paths of `PathsQ_{j,c}`. … (vi) *Arcs and closing.* A path `Q ∈ PathsQ_{j,c}` that does not come
from a cherry and has both ends in `Rt` is declared an *arc of phase `c`* …. Every other path of
`PathsQ_{j,c}` (one with an end in `Pl`, or one coming from a cherry) is closed". Cost: "For a
phase `c`, a trail produces objects only if (1) it is a cherry or has an appended edge, or (2) it
is a path of `Paths_{j,c}` without appended edges having an end in `Pl`. … there are at most
`2|W_j|` such trails. … there are at most `2|Pl ∩ U_{j+1}|` such trails. Every remaining trail is
a path of `Paths_{j,c}` with both ends in `Rt` and without appended edges; it is not split
(`rep = 0`), and it becomes an arc. Each trail of type (1) or (2) gives at most three objects (at
most two split cycles and at most one closed cycle)." Also (c): "At step `j`, each arc of phase
`c` comes from a distinct path of `Paths_{j,c}`", and (P5)/(b): the vertices of an arc are
vertices of `F_{j,c}` or far ends.

Conclusion, in order: objects well formed; the edges of `D`, `A`, `Q` are `F` plus the reserved
edges, each once; the arcs are paths with `≥ 1` edge, both ends in `Rt`, all vertices in `V(F)`
or far ends, at most `|P|` of them; the paths of `Q` satisfy (P2), (P3), have all vertices in
`V(F)`, `W` or far ends (the input of (P1)), and (P4) with the far-end count in place of `b`;
the cost: single edges and split cycles (`D`) plus closed cycles (one per member of `Q`) number
at most `|W| + 3(2|W| + 2|Up|)`. -/
def PVStepPhaseStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (Rt W Up : Finset V) (F : Finset (Sym2 V))
    (P : List (List V)) (u₁ u₂ : V → V),
    Disjoint Rt W → Disjoint Rt Up → Disjoint W Up →
    (∀ e ∈ F, ¬ e.IsDiag) → (∀ e ∈ F, ∀ v ∈ e, v ∈ Rt ∪ W ∪ Up) → (∀ e ∈ F, ∃ w ∈ W, w ∈ e) →
    IsPathDecomp (F : Set (Sym2 V)) P → (∀ v : V, pathEndCount P v ≤ 2) →
    (∀ w ∈ W, u₁ w ≠ u₂ w ∧ u₁ w ∈ Rt ∪ Up ∧ u₂ w ∈ Rt ∪ Up ∧
      s(w, u₁ w) ∉ F ∧ s(w, u₂ w) ∉ F) →
    ∃ (D : List (Obj V)) (A Q : List (List V)),
      -- the output objects are objects
      (∀ o ∈ D, o.WF) ∧
      -- "The edges used at step `j` are exactly the edges of `F_j` …": each edge of `F` and each
      -- reserved edge lies in exactly one object, arc or closed path
      (D.flatMap Obj.edges ++ A.flatMap walkEdges ++ Q.flatMap walkEdges).Nodup ∧
      (∀ e, e ∈ D.flatMap Obj.edges ++ A.flatMap walkEdges ++ Q.flatMap walkEdges ↔
        e ∈ F ∨ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w)) ∧
      -- arcs: paths of length `≥ 1` with both ends in `Rt`, vertices in `V(F)` or far ends
      -- ((P5) with (s4:eqPVclass)), at most one per path of `Paths_{j,c}`
      (∀ a ∈ A, a.Nodup ∧ 2 ≤ a.length ∧ (∃ x ∈ Rt, a.head? = some x) ∧
        (∃ y ∈ Rt, a.getLast? = some y) ∧
        ∀ x ∈ a, (∃ e ∈ F, x ∈ e) ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
      A.length ≤ P.length ∧
      -- the closed paths: (P2), (P3), vertices (input of (P1)), (P4)
      (∀ q ∈ Q, q.Nodup ∧ 2 ≤ pathLength q ∧ (∃ x ∈ Rt ∪ Up, q.head? = some x) ∧
        (∃ y ∈ Rt ∪ Up, q.getLast? = some y) ∧
        ∀ x ∈ q, (∃ e ∈ F, x ∈ e) ∨ x ∈ W ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
      (∀ v : V, pathEndCount Q v ≤ 2 + (W.filter fun w => v = u₁ w ∨ v = u₂ w).card) ∧
      -- the cost of the phase
      D.length + Q.length ≤ W.card + 3 * (2 * W.card + 2 * Up.card)

/-- [s4:lemPV] (s4:eqPVstep) "Hence, using `W_j ⊔ (Pl ∩ U_{j+1}) = Pl ∩ U_j`, step `j` outputs at
most `4|W_j| + 4·3(2|Pl ∩ U_{j+1}| + 2|W_j|) ≤ 28|Pl ∩ U_j|` objects." (The arithmetic, for
disjoint `W = W_j` and `Up = Pl ∩ U_{j+1}`.) -/
def PVStepCostStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (W Up : Finset V), Disjoint W Up →
    4 * W.card + 4 * 3 * (2 * Up.card + 2 * W.card) ≤ 28 * (W ∪ Up).card

/-- [s4:lemPV] (s4:eqPVt) "Since `b ≤ 2^7L^2(L^6+1)+1`,
`2 + b ≤ 2^7L^8 + 2^7L^2 + 3 ≤ 2^9L^8 = t`", with `b = ⌈2^7L^2m⌉`, `m = ⌈L^6⌉`, under size
condition (i) `L ≥ 2^{10}` (`L = EG.Vortex.L N`, `b = EG.Vortex.pvB N`). This is the bound
`2 + b ≤ t` through which (P4) feeds the multiplicity `t` of (G2). -/
def PVtStatement : Prop :=
  ∀ N : ℕ, (2 : ℝ) ^ 10 ≤ Vortex.L N →
    (2 + Vortex.pvB N : ℝ) ≤ 2 ^ 7 * Vortex.L N ^ 8 + 2 ^ 7 * Vortex.L N ^ 2 + 3 ∧
      2 ^ 7 * Vortex.L N ^ 8 + 2 ^ 7 * Vortex.L N ^ 2 + 3 ≤ 2 ^ 9 * Vortex.L N ^ 8

/-- [s4:lemPV] (proof, "Finish", stripping; CR1-PV) "Let `T` be one of its paths. If an end `p` of
`T` lies in `Pl_J`, the edge of `T` at `p` lies in `E_2`, so its other end lies in `Rt`; output this
edge as a single edge (*stripping*). After stripping at the ends of `T` lying in `Pl_J`, what
remains of `T` has no edges or is a path of length at least `1` with two distinct ends in `Rt`
(every end of `T` lies in `Rt ⊔ Pl_J`, and a stripped end is replaced by a vertex of `Rt`)".

Formal reading: `T` is a path (no repeated vertex, `≥ 2` vertices) with all vertices in
`Rt ⊔ Pl_J` ((Inv1) at `j = J`) and every edge with an end in `Rt` (an edge of `E_2`); the
stripped edges `S` (one per end of `T` in `Pl_J`) and the rest `T'` (a contiguous piece of `T`)
split the edges of `T`; `T'` has no edge or is a path with `≥ 1` edge and both ends in `Rt`. -/
def PVStripStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (Rt PlJ : Finset V) (T : List V),
    Disjoint Rt PlJ → T.Nodup → 2 ≤ T.length → (∀ x ∈ T, x ∈ Rt ∪ PlJ) →
    (∀ e ∈ walkEdges T, ∃ x ∈ Rt, x ∈ e) →
    ∃ (S : List (Sym2 V)) (T' : List V),
      List.Perm (S ++ walkEdges T') (walkEdges T) ∧
      S.length ≤ (PlJ.filter fun p => T.head? = some p ∨ T.getLast? = some p).card ∧
      T'.IsInfix T ∧
      (T'.length ≤ 1 ∨
        (2 ≤ T'.length ∧ (∃ x ∈ Rt, T'.head? = some x) ∧ ∃ y ∈ Rt, T'.getLast? = some y))

/-- [s4:lemPV] (proof, "Finish"; CR1-PV) "By (Inv1) for `j = J`, every edge of `H_J` has both ends
in `U_J = Rt ⊔ Pl_J`, where `Pl_J := Pl ∩ U_J`. Split `H_J = E_1 ⊔ E_2`, where `E_1` is the set of
edges with both ends in `Pl_J`; every edge of `E_2` has an end in `Rt`.
* By (G5), `|Pl_J| ≤ 64|Pl|/L`. Apply Fact s1:factEG0(b) with `F := E_1`, `W := Pl_J`, `β := 64`
  and `α := |Pl| ≤ N` …. So `E_1` decomposes into at most `64|Pl|` objects, which are output.
* Give every edge `xy ∈ E_2` a phase `c ∈ [4] \ {ext(x), ext(y)}` … Take a Corollary-22
  decomposition of each `E_{2,c}`. … [stripping] … in the latter case it is declared an arc of
  phase `c`. Every vertex `y` of such an arc is an end of an edge of phase `c`, so `ext(y) ≠ c`.
  … at most `8|Pl_J|` … single edges in total";
and (c) "in the finish there are at most `|U_J| ≤ N` arcs per phase by (E)", (d) "If `Pl = ∅` …
`Pl_J = ∅`, and `E_1 = ∅`; no edge is stripped, and all of `H_0 = H_J = E_2` is partitioned into
arcs, so `H^obj = ∅`" (here: `Pl_J = ∅` gives no object).

Formal reading: `N` with size condition (i) `2^{10} ≤ L = log₂ N` (it gives `N > 1` and
`4·64 ≤ L`, the hypotheses of Fact EG0(b)); `Pl_J ⊆ Pl`, `|Pl| ≤ N`, `Rt ∩ Pl = ∅`, (G5)
`|Pl_J| ≤ 64|Pl|/L`; `H_J` loopless with both ends of every edge in `Rt ∪ Pl_J`. Conclusion:
`H_J = H^obj ⊔ H^arc` with `H^obj` decomposed into at most `64|Pl| + 8|Pl_J|` objects and `H^arc`
into arcs with a phase, both ends in `Rt`, `ext ≠` phase on every vertex, at most `4|U_J|` arcs. -/
def PVFinishStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (N : ℕ) (Rt Pl PlJ : Finset V) (HJ : Finset (Sym2 V))
    (ext : V → Option (Fin 4)),
    (2 : ℝ) ^ 10 ≤ Vortex.L N → Pl.card ≤ N → PlJ ⊆ Pl → Disjoint Rt Pl →
    (PlJ.card : ℝ) ≤ 64 * Pl.card / Vortex.L N →
    (∀ e ∈ HJ, ¬ e.IsDiag) → (∀ e ∈ HJ, ∀ v ∈ e, v ∈ Rt ∪ PlJ) →
    ∃ (Hobj : Finset (Sym2 V)) (D : List (Obj V)) (arcs : List (List V × Fin 4)),
      Hobj ⊆ HJ ∧ IsDecomp (Hobj : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ 64 * Pl.card + 8 * PlJ.card ∧
      IsPathDecomp ((HJ \ Hobj : Finset (Sym2 V)) : Set (Sym2 V)) (arcs.map Prod.fst) ∧
      (∀ a ∈ arcs, (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ Rt) ∧
        ∀ x ∈ a.1, ext x ≠ some a.2) ∧
      arcs.length ≤ 4 * (Rt ∪ PlJ).card ∧
      (PlJ = ∅ → Hobj = ∅)

/-- [s4:lemPV] (c), the per-vertex bound (CR1-PV): "every vertex `x` is an end of at most
`deg_{H_0}(x) ≤ |Z| - 1` arcs"; proof: "By (b) the arcs are pairwise edge-disjoint paths with two
distinct ends, and their edges lie in `H^arc ⊆ H_0`. An arc with end `x` contains exactly one edge
at `x` (a path meets each of its two ends in exactly one edge), and distinct arcs are
edge-disjoint; so `x` is an end of at most `deg_{H_0}(x)` arcs. Every edge of `H_0` at `x` joins
`x` to a vertex of `Z \ {x}`, and distinct edges at `x` have distinct other ends (edge sets are
sets of edges of a simple graph, Convention s1:convGraphs(a)); hence `deg_{H_0}(x) ≤ |Z| - 1`."

Formal reading: `H_0` loopless with both ends of every edge in `Z`; the arcs form a path
decomposition (`EG.IsPathDecomp`: pairwise edge-disjoint paths with `≥ 1` edge) of some
`H^arc ⊆ H_0`. Only these properties of (b) are used.

Scope as refutation target (review P4A.review1 re-dispatch, m1): this is a general fact about path
decompositions and does not involve the PV procedure, so proving it cannot refute anything. The
refutation-relevant comparisons of probe P-4 (the per-vertex pair multiplicity per bundle
`(l, c, slot)` and `|Z| - 1 ≤ M_l - 1 < t_Y`, s5:lemParent Step 5) are P4B nodes. -/
def PVArcEndsDegStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (Z : Finset V) (H0 Harc : Finset (Sym2 V))
    (arcs : List (List V)),
    (∀ e ∈ H0, ¬ e.IsDiag) → (∀ e ∈ H0, ∀ v ∈ e, v ∈ Z) → Harc ⊆ H0 →
    IsPathDecomp (Harc : Set (Sym2 V)) arcs →
    ∀ x : V, pathEndCount arcs x ≤ degE H0 x ∧ degE H0 x ≤ Z.card - 1

end EG.Spec
