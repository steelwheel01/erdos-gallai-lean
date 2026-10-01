module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages
public import EG.Defs.Probe.P4A.PVHyp

/-!
# Statement of Lemma child side (manuscript s5:lemChild), deterministic (Tier-1) form

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemChild.

Manuscript v6.1, `s5.tex`, Lemma [s5:lemChild]: "Fix a stage-1 outcome and a non-demoted light
part `Z` of round `l`. Apply Lemma s4:lemPV to the vertex set `Z` with the following data: [the
data `childData`]. Then all hypotheses of Lemma s4:lemPV hold, including (E1′). Let `𝒢_Z` be its
good event `G_PV` for these data. It is an event over the stage-3 labels of `Z` …; it is determined
by the stage-1 outcome and these labels; and its conditional probability given the stage-1
outcome is at least `1/2 − o(1) ≥ 1/3`. On `𝒢_Z` the following holds for *every* edge set
`H_0(Z)` with `Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`: there is a partition
`H_0(Z) = H^obj(Z) ⊔ H^arc(Z)` such that
(a) `H^obj(Z)` decomposes into at most `c_PV|Pl(Z)|` objects;
(b) `H^arc(Z)` is the edge set of a family of pairwise edge-disjoint paths (the *arcs* of `Z`),
each with at least one edge and both ends in `Rt(Z)`, and each carrying a phase `c ∈ [4]`, such
that every vertex of a phase-`c` arc, ends included, lies in no round-`l` phase-`c` zone;
(c) `Z` has at most `14(J_Z+1)|Z|` arcs, and every vertex `x` is an end of at most
`deg_{H_0(Z)}(x) ≤ |Z|−1` arcs of `Z`;
(d) if `Rt(Z) = ∅`, in particular if `l ≤ 2`, then `Z` has no arcs."

Formal reading (TRIAGE §2.8: "s5 lemChild and lemDemoted: a Tier-1 existence form (∀ H_0 ∃
decomposition)"; PV-DATA-RECORD; design note `work/p2d/light.md` D-L-5, D-L-6).
* Setting: `EG.RunHyp N0 Dstar G run`; "a stage-1 outcome": `ω ∈ (Stage1.law G run).supp`;
  "a non-demoted light part `Z` of round `l`": `Z ∈ run.lightParts G`, `¬ demoted ω Z`, `l = Z.1`.
* "all hypotheses of Lemma PV hold, including (E1′)": `EG.Vortex.PVHyp (childData ω Z)` (the
  named hypothesis predicate of the PV Spec `EG.Spec.PVStatement`, `EG/Defs/Probe/P4A/PVHyp.lean`,
  which contains `PVE1'`).
* **Stage 3 (T0, TRIAGE §2.8 / §2.12 "TPV, PV and VX⁺ are deterministic").** The good event
  `𝒢_Z`, its probability bound `≥ 1/3` and "determined by the stage-1 outcome and these labels"
  are not stated: the PV Spec is deterministic (its good event is proof-internal), and every
  consumer (s5:lemParent, s5:lemKRED, s6:thmMIXC) uses only that for every admissible `H_0(Z)`
  a partition with (a)–(d) exists. The conclusion is therefore "for every admissible `H_0` there
  are `H^obj`, arcs …" (this is implied by the lemma, since `𝒢_Z` has positive probability).
* "`Own_Z ⊆ H_0(Z) ⊆ E_l(Z)`": `EG.Light.H0Adm ω Z H0`.
* The partition: `Disjoint Hobj (arcEdges as) ∧ Hobj ∪ arcEdges as = H0`.
* (a): `IsDecomp ↑Hobj Dobj` with `Dobj.length ≤ 369 |Pl(Z)|` (`c_PV = 369`).
* (b)–(d): `EG.Light.ArcSys ω Z H0 as` (the per-part Def written for this conclusion; it states
  (b) with "lies in no round-`l` phase-`c` zone" literally as `x ∉ Zone_{Y,l,c,σ}` for all `Y`,
  `σ`, and keeps the redundant clauses of (c), (d) for literalness).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemChild] Lemma child side, deterministic form: for every stage-1 outcome and every
non-demoted light part `Z`, the child data satisfy the hypotheses of Lemma PV (including (E1′)),
and every admissible `H_0(Z)` has a partition `H^obj(Z) ⊔ H^arc(Z)` with (a)–(d), in the setting
of Section s5 (`RunHyp`). -/
def LemChildStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ Z ∈ run.lightParts G, ¬ demoted ω Z →
      Vortex.PVHyp (childData ω Z) ∧
      ∀ H0 : Finset (Sym2 V), H0Adm ω Z H0 →
        ∃ (Hobj : Finset (Sym2 V)) (Dobj : List (Obj V)) (as : List (Arc V)),
          Disjoint Hobj (arcEdges as) ∧ Hobj ∪ arcEdges as = H0 ∧
          -- (a)
          IsDecomp (Hobj : Set (Sym2 V)) Dobj ∧ Dobj.length ≤ 369 * (Pl ω Z).card ∧
          -- (b)–(d)
          ArcSys ω Z H0 as

end EG.Spec
