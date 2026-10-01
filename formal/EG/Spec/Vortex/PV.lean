module

public import EG.Defs.Probe.P4A.PVHyp
public import EG.Defs.PathDecomp

/-!
# Statement of Lemma PV, the four-phase P-vortex, deterministic form (manuscript s4:lemPV)

Statement file (`EG/Spec/**`) written by probe unit P4A (probe P-4, part 1) as the anchor of the
PV(c) core; design note `formal/work/p2b/P4A.md`. **It is not a P4A probe node and P4A does not
prove it** (the whole of Lemma PV, with the good event `𝒢_PV` and Theorem 16*, is about 1600
lines; blueprint s4). Its consumer, s5:lemChild (probe P-4, part 2), will declare it as an input.
P4A proves the parts of its proof listed in `EG/Spec/Vortex/PVCore.lean` and
`EG/Spec/Vortex/Observations.lean`, in particular the per-vertex bound of (c)
(`PVArcEndsDegStatement`), which gives the corresponding conjunct below from the (b) conjunct.
Ownership (review P4A.review1 re-dispatch, c3): this is the natural path of the Lemma-PV Spec; the
s4 statement owner adopts this file (and may revise it through the usual review) rather than
writing a second Lemma-PV Spec elsewhere.

Manuscript v6.1, `s4.tex`, Lemma [s4:lemPV] (data and hypotheses: `EG/Defs/Probe/P4A/PVHyp.lean`):
"… On `𝒢_PV`, for *every* edge set `H_0` all of whose edges have both ends in `Z` and which
contains `E(M)` and every `E(R_{j,c})`, there is a partition `H_0 = H^obj ⊔ H^arc` and a family
`𝔄` of paths (*arcs*) such that:
(a) `H^obj` decomposes into at most `369|Pl|` objects;
(b) `H^arc` is the disjoint union of the edge sets of the arcs; the arcs are pairwise
    edge-disjoint paths of length at least `1`, each has two distinct ends, both in `Rt`, and each
    carries a phase `c ∈ [4]` such that every vertex `x` of a phase-`c` arc, ends included,
    satisfies `ext(x) ≠ c`;
(c) `|𝔄| ≤ 4(J+1)N`, and every vertex `x` is an end of at most `deg_{H_0}(x) ≤ |Z|-1` arcs;
(d) if `Rt = ∅` then `𝔄 = ∅`; if `Pl = ∅` then `H^obj = ∅`.
The partition, the decomposition and the arcs are obtained from `H_0` and the labels by a
deterministic procedure."

Formal reading (TRIAGE §2.8, decision PV-DET-SPEC; blueprint s4 lemPV).
* **Deterministic form.** The conclusion does not mention the labels, and the manuscript proves
  `P(𝒢_PV) ≥ 1/2 - η_PV(N) > 0`, so `𝒢_PV` is non-empty and the lemma implies "for every
  admissible `H_0` there are `H^obj`, `𝔄` with (a)–(d)"; conversely that statement gives the
  lemma with `𝒢_PV` replaced by the whole space. The consumers use only non-emptiness
  (s5:lemChild "`≥ 1/3`", s7:lemOneOutcome). The explicit event and its probability are proof
  internals. The meta-claim "deterministic procedure" is realised by `Classical.choose`.
* The data are a record `D : EG.Vortex.PVData V` (TRIAGE PV-DATA-RECORD) with
  `EG.Vortex.PVHyp D`; `N = |Z| = D.Z.card`, `J = EG.Vortex.pvJ N`.
* `H^obj` is a finset `Hobj ⊆ H_0`, decomposed by the object list `Dobj` (`EG.IsDecomp`);
  `H^arc = H_0 \ Hobj` (the partition). An arc is a vertex list with its phase
  (`List V × Fin 4`, as `EG.Light.Arc`); "`H^arc` is the disjoint union of the edge sets of the
  arcs; the arcs are pairwise edge-disjoint paths of length at least `1`, each has two distinct
  ends" is `EG.IsPathDecomp ↑(H_0 \ Hobj) (arcs.map Prod.fst)`.
* "every vertex `x` is an end of at most `deg_{H_0}(x)` arcs": `EG.pathEndCount … x ≤ EG.degE H0 x`
  for every `x : V` (`0` off `Z`); "`deg_{H_0}(x) ≤ |Z| - 1`" for every `x : V` (natural
  subtraction; `N ≥ 2` under `PVSize`).
* (d) "`Pl = ∅`" is `D.Pl = ∅`.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s4:lemPV] Lemma PV (the four-phase P-vortex), deterministic form: for data `D` satisfying
the hypotheses of the lemma and every admissible `H_0`, there are `H_0 = H^obj ⊔ H^arc` and arcs
with (a)–(d) (module docstring). -/
def PVStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (D : Vortex.PVData V), Vortex.PVHyp D →
    ∀ H0 : Finset (Sym2 V), Vortex.PVAdm D H0 →
      ∃ (Hobj : Finset (Sym2 V)) (Dobj : List (Obj V)) (arcs : List (List V × Fin 4)),
        Hobj ⊆ H0 ∧
        -- (a)
        IsDecomp (Hobj : Set (Sym2 V)) Dobj ∧ Dobj.length ≤ 369 * D.Pl.card ∧
        -- (b)
        IsPathDecomp ((H0 \ Hobj : Finset (Sym2 V)) : Set (Sym2 V)) (arcs.map Prod.fst) ∧
        (∀ a ∈ arcs, (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ D.Rt) ∧
          ∀ x ∈ a.1, D.ext x ≠ some a.2) ∧
        -- (c)
        arcs.length ≤ 4 * (Vortex.pvJ D.Z.card + 1) * D.Z.card ∧
        (∀ x : V, pathEndCount (arcs.map Prod.fst) x ≤ degE H0 x) ∧
        (∀ x : V, degE H0 x ≤ D.Z.card - 1) ∧
        -- (d)
        (D.Rt = ∅ → arcs = []) ∧ (D.Pl = ∅ → Hobj = ∅)

end EG.Spec
