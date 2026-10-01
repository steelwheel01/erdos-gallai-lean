module

public import EG.Defs.Graph

/-!
# Lemma-HB families (manuscript s3:lemHB, conclusion shape)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemHB]: "Then every vertex `w` has a set `A(w) ⊆ N_X(w)` with
`|A(w)| = m`, such that every vertex of `X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`."

The same predicate is the conclusion of the s3 Lemma-HB Spec, hypothesis (first bullet) of
Lemma [s4:lemPV] ("sets `A(w) ⊆ N_O(w)` (`w ∈ Z`) with `|A(w)| = m` such that every vertex lies in
at most `b` of them"), and the property of the fixed sets `A_Y` of [s5:defStages]
(`EG.Light.AY`). It lives in this low module (neutral namespace `EG`) so that the s3, s4 and s5
statements share one copy (P2-D [light] fix round 1, review item MINOR-3; design note
`formal/work/p2d/light.md`).
-/

@[expose] public section

namespace EG

variable {V : Type*} [DecidableEq V]

/-- [s3:lemHB] the conclusion shape of Lemma HB: "every vertex `w` has a set `A(w) ⊆ N_X(w)` with
`|A(w)| = m`, such that every vertex of `X` lies in at most `b` of the sets `A(w)`, `w ∈ V(X)`".
The count is over the indices `w ∈ V(X)` (the family of sets, as the text says); "every vertex"
is written `∀ u : V`, which is equivalent to `∀ u ∈ V(X)` because `A w ⊆ N_X(w) ⊆ V(X)`
(`N_X(w) = X.nbrs w`). -/
def IsHBFamily (X : FGraph V) (m b : ℕ) (A : V → Finset V) : Prop :=
  (∀ w ∈ X.verts, A w ⊆ X.nbrs w ∧ (A w).card = m) ∧
    ∀ u : V, (X.verts.filter (fun w => u ∈ A w)).card ≤ b

end EG
