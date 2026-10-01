module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages
public import EG.Defs.Chain.Constants
public import EG.Defs.Probe.S5.KRED

/-!
# Statement of Lemma K-RED (manuscript s5:lemKRED)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemKRED.

Manuscript v6.1, `s5.tex`, Lemma [s5:lemKRED]: "Fix the valid run, a stage-1 outcome, and stage-3
outcomes in the good events of all light parts …. Let `(Lent_ext(Y))_Y` be *any* family, indexed by
the light parts `Y`, such that for every light part `Y`
`Lent_ext(Y) ⊆ (⋃_{l,j} LJS_{Y,l,j}) ∪ (⋃_l LJV_{Y,l})`, and `Lent_ext(Y) = ∅` if `Y` is demoted.
Process the rounds `l = R, R−1, …, 1` (children before parents). At round `l`: (1) … (2) … (3) ….
Output the long cycles `⋃_l Cyc_l` and the edges of `E_0` (as single edges) directly. Then the
objects produced form a decomposition of `E(G) \ K_std \ ⋃_Y Lent_ext(Y)` into at most
`(D_*/2 + c_KRED + ε_K(D_*)) n + c_VX dem + c_PV lp` objects, where `ε_K(D_*) := ε_ch(D_*)`.
Itemized: … The exact sum of these items is at most
`(D_*/2 + c^exact_KRED + ε_K(D_*)) n + c_VX dem + c_PV lp`; the constant `c_KRED` is kept for the
cost line. No edge of `K_std` and no edge of any `Lent_ext(Y)` is used. Moreover, the objects
produced at round `l` depend only on the stage-1 and stage-3 outcomes, on the sets `Lent_ext(Z)` of
the light parts `Z` of round `l`, and on what was produced at the rounds `> l`."

Formal reading (TRIAGE §2.8 "K-RED is pure existence for any admissible family Lentext", §2.9,
§2.12).
* Setting: `EG.RunHyp N0 Dstar G run` (Γ4 is not needed: the lemma carries `ε_K` separately,
  s5:remConstants (b)); "a stage-1 outcome": `ω ∈ (Stage1.law G run).supp`.
* The family: `Lext : PartId → Finset (Sym2 V)` with `EG.Light.LentExtHyp ω Lext`
  (`EG/Defs/Probe/S5/KRED.lean`); `⋃_Y Lent_ext(Y)` over the light parts.
* `K_std = EG.Light.Kstd G run`; `n = G.card`; `c_KRED = 745`, `c_VX = 80`, `c_PV = 369`
  (numerals); `ε_K = EG.Chain.epsK` (the locked copy; `EG.Light.epsChain` is the same term).
* "the objects produced form a decomposition of …": `∃ D, IsDecomp ↑(E(G) \ K_std \ ⋃ Lent_ext) D`
  (this also gives "no edge of `K_std` and no edge of any `Lent_ext(Y)` is used", and every object
  is a cycle of length `≥ 3` or a single edge).
* **T0 (TRIAGE §2.12: "s5:lemParent/K-RED 'depends only on' clauses are dropped: pure existence,
  and MIX-C is restructured").** The stage-3 outcomes are quantified away (the child and demoted
  decompositions are the existence forms of s5:lemChild, s5:lemDemoted), the round-by-round
  procedure is proof-internal, and the causality clause ("the objects produced at round `l`
  depend only on …") is not stated. The sharper itemized total with `c^exact_KRED = 739` is not a
  separate statement (it implies the stated bound; no consumer uses it).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemKRED] Lemma K-RED, existence form: for every stage-1 outcome and every admissible
family `Lent_ext`, `E(G) \ K_std \ ⋃_Y Lent_ext(Y)` decomposes into at most
`(D_*/2 + 745 + ε_K(D_*)) n + 80 dem + 369 lp` objects, in the setting of Section s5
(`RunHyp`). -/
def LemKREDStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ Lext : PartId → Finset (Sym2 V), LentExtHyp ω Lext →
      ∃ D : List (Obj V),
        IsDecomp (((G.edges \ Kstd G run) \ (run.lightParts G).biUnion Lext : Finset (Sym2 V)) :
          Set (Sym2 V)) D ∧
        (D.length : ℝ) ≤ (Dstar / 2 + 745 + Chain.epsK Dstar) * (G.card : ℝ) +
          80 * (dem ω : ℝ) + 369 * (lp ω : ℝ)

end EG.Spec
