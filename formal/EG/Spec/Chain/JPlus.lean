module

public import EG.Defs.Chain.JSet

/-!
# Statement of the `J`-independent items of Lemma J⁺ (manuscript s6:lemJplus (J3), (i), (iii), (iv))

Statement file of probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`).

Manuscript v6.1, Lemma J⁺ [s6:lemJplus] ("the J-interface"), the items that do not mention `J_l`:
"(J3) The sets `D_l` (hubs), `⋃_Z F_Z` (fresh centres) and `⋃_Z Q*_Z` (classed non-lost ports) are
pairwise disjoint. Each vertex outside `D_l` that lies in a round-`l` pre-part lies in exactly one
such pre-part, so it has one role and, if classed, one class.
In addition, the following interface facts hold.
(i) The types above are exhaustive and exclusive.
…
(iii) (Disjointness from (R5).) `E(H_Y) ⊆ E_r(Y)` for every ancestor `Y` of round `r`, and the sets
`E_r(Y)` (`Y` light) and `E_l(Z)` (`Z ∈ Std_l`) are pairwise disjoint.
(iv) `u ∈ V(Y(u))` for every classed port `u`.
(v) In the colourings of Definition s3:defCOL, colours of distinct edges are independent."

Formal reading (TRIAGE §2.9; blueprint s6b JPLUS-J3-III-IV, JPLUS-V-PROB; design note
`work/p2d/design.md` D-DES-7). The items about `J_l` — (i) exhaustive, (J1), (J2), (ii) — are the
predicate `EG.Chain.JPlusProps`, a conjunct of `EG.Spec.JSLCStatement` (`J_l` exists only inside
JS-LC). The items here hold for every run, designation and stage data, independently of `J_l`:
* (J3): the three role sets of round `l` are pairwise disjoint (`D_l = run.D G l`,
  `⋃_Z F_Z = freshCentres`, `⋃_Z Q*_Z = qsRound`), and a vertex outside `D_l` lies in at most one
  round-`l` pre-part ("exactly one" for a vertex that lies in one; "one role and one class" follow);
* (i), exclusive: no edge is of two of the four types (for the four typed predicates of
  `EG/Defs/Chain/JSet.lean`);
* (iii): `E(H_Y) ⊆ E_{r(Y)}(Y)` for every ancestor, and the sets `E_{r(Y)}(Y)` of distinct
  ancestors are pairwise disjoint (every ancestor is a light part or a standalone pre-part);
* (iv): `u ∈ V(Y(u))` for every classed port `u ∈ Q_Z`, `Z ∈ Std_l`, `l ≥ 3`, of a designation.
* (v) is a property of the stage-1 law (independence of the per-edge colours), not of `J_l` or of
  a run; it belongs to the Stage1 law API (TRIAGE §2.7, §2.9) and is not stated here.
Hypotheses: `run.Valid G Dstar` (for (iii), s2:propStructure(iii)) and a designation (for (iv)).
The manuscript's `n ≥ N_0`, `d_1 ≥ D_*` and Γ are unused by these items and are dropped
(strengthening).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

/-- [s6:lemJplus] (J3), (i) (exclusive), (iii), (iv): "(J3) The sets `D_l` (hubs), `⋃_Z F_Z`
(fresh centres) and `⋃_Z Q*_Z` (classed non-lost ports) are pairwise disjoint. Each vertex outside
`D_l` that lies in a round-`l` pre-part lies in exactly one such pre-part … (i) The types above are
exhaustive and exclusive. … (iii) (Disjointness from (R5).) `E(H_Y) ⊆ E_r(Y)` for every ancestor
`Y` of round `r`, and the sets `E_r(Y)` (`Y` light) and `E_l(Z)` (`Z ∈ Std_l`) are pairwise
disjoint. (iv) `u ∈ V(Y(u))` for every classed port `u`." (The exhaustive half of (i) is
`JPlusProps.types`; (v) is a stage-1 law fact; module docstring.) -/
def JplusFactsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V)
    (δ : Designation V) (S : StageData V),
    run.Valid G Dstar → IsDesignation run G δ →
      (∀ l : ℕ,
        Disjoint (run.D G l) (freshCentres run G l) ∧
        Disjoint (run.D G l) (qsRound run G δ S l) ∧
        Disjoint (freshCentres run G l) (qsRound run G δ S l) ∧
        ∀ v ∉ run.D G l, ∀ a ∈ run.prePartAddrs G l, ∀ b ∈ run.prePartAddrs G l,
          v ∈ run.Z0 G l a → v ∈ run.Z0 G l b → a = b) ∧
      (∀ (l : ℕ) (e : Sym2 V),
        ¬ (IsJparEdge run G δ S l e ∧ ∃ h Y, IsJhubEdge run G δ S l h Y e) ∧
        ¬ (IsJparEdge run G δ S l e ∧ ∃ x Y, IsJfrEdge run G δ S l x Y e) ∧
        ¬ (IsJparEdge run G δ S l e ∧ ∃ v Y, IsJlostEdge run G δ S l v Y e) ∧
        ¬ ((∃ h Y, IsJhubEdge run G δ S l h Y e) ∧ ∃ x Y, IsJfrEdge run G δ S l x Y e) ∧
        ¬ ((∃ h Y, IsJhubEdge run G δ S l h Y e) ∧ ∃ v Y, IsJlostEdge run G δ S l v Y e) ∧
        ¬ ((∃ x Y, IsJfrEdge run G δ S l x Y e) ∧ ∃ v Y, IsJlostEdge run G δ S l v Y e)) ∧
      (∀ Y ∈ run.ancestors G, (run.ancGraph G Y).edges ⊆ run.E G Y.1 Y.2) ∧
      (∀ Y ∈ run.ancestors G, ∀ Y' ∈ run.ancestors G, Y ≠ Y' →
        Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2)) ∧
      (∀ l, 3 ≤ l → ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a, u ∈ run.ancVerts G (δ l u))

end EG.Spec
