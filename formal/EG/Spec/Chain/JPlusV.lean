module

public import EG.Defs.Stage1.Law

/-!
# Statement of item (v) of Lemma J⁺ (manuscript s6:lemJplus (v))

Statement file (`EG/Spec/**`) of the P2 Spec unit s6b (`formal/work/p2s/s6b.md`); blueprint s6b,
node `s6:lemJplus`, hazard JPLUS-V-PROB.

Manuscript v6.1, `s6.tex`, Lemma J⁺ [s6:lemJplus]: "In addition, the following interface facts
hold. … (v) In the colourings of Definition s3:defCOL, colours of distinct edges are independent."
Proof: "(v) holds because every colouring in Definition s3:defCOL is uniform and independent over
edges."

Formal reading. The other items of Lemma J⁺ are `EG.Chain.JPlusProps` (a conjunct of
`EG.Spec.JSLCStatement`, `EG/Spec/Chain/JSLC.lean`) and `EG.Spec.JplusFactsStatement`
(`EG/Spec/Chain/JPlus.lean`, which leaves (v) to the stage-1 law, TRIAGE §2.9). Item (v) is a
property of the stage-1 law `EG.Stage1.law G run` (TRIAGE §2.7): the colourings of s3:defCOL are
component (1a) of the outcome, one label triple `ω.col Y e` (bit, lent index, own label) per
ancestor `Y` and per edge `e` of `H_Y`. "Colours of distinct edges are independent" is stated for
the whole family indexed by the pairs `(Y, e)` (mutual independence, `FinDist.iIndepFun`), which
contains the per-ancestor family (`EG.Stage1.iIndepFun_col_edges`, proved in
`EG.Lib.Stage1.Law`). The edge sets `E(H_Y)` of distinct ancestors are disjoint on a valid run
(s2:propStructure(iii)), so a pair `(Y, e)` is the same as an edge of `⋃_Y E(H_Y)` there; the
statement needs no hypothesis on the run (the law is a product for every run).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s6:lemJplus] (v) "In the colourings of Definition s3:defCOL, colours of distinct edges are
independent": under the stage-1 law, the label triples `ω.col Y e` of all pairs (ancestor `Y`,
edge `e` of `H_Y`) are mutually independent. -/
def JplusVStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (run : Run V),
    (Stage1.law G run).iIndepFun
      (fun (p : Σ Y : ↥(run.ancestors G), ↥(run.ancGraph G Y).edges)
        (ω : Stage1.Outcome G run) => ω.col p.1 p.2)

end EG.Spec
