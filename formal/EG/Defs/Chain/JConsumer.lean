module

public import EG.Defs.Chain.JSet
public import EG.Defs.Objects

/-!
# J-consumers (manuscript s6:defJconsumer)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, Definition [s6:defJconsumer] ("round-`l` J-consumer"), quoted below. Design
note: `formal/work/p2d/design.md`. Namespace `EG.Chain`.

Encoding (TRIAGE §2.9 "J-consumer"; blueprint s6b JCONS-TYPE, JCONS-CONDITIONAL, JCONS-JC3):
* a J-consumer is a **function** `out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)`,
  `(l, J_l) ↦ (Obj_l, LentJV_l)`, inside a fixed context (run, designation, stage data). "Given
  everything constructed at rounds `> l`, the stage-1 outcome and the set `J_l`": the stage-1
  data are the context; the past enters through `J_l` only (checked for the s7 instance,
  blueprint s6b JCONS-TYPE); "possibly fresh randomness" is resolved inside the consumer (the s7
  instance picks its `ξ_l` by choice);
* (JC1), (JC2) are required **only for `J` with `JPlusProps`** and rounds `3 ≤ l ≤ R` ("Here `J_l`
  has the properties of Lemma s6:lemJplus"; the s7 round step is not a J-consumer on arbitrary
  edge sets);
* (JC2) "pairwise edge-disjoint cycles and single edges …, and their union is exactly
  `J_l ∪ LentJV_l`" is `IsDecomp (J ∪ LentJV) Obj` (objects well formed, edge lists disjoint and
  duplicate free, union exactly `J ∪ LentJV`); this is the predicate s7:lemLift(iv) produces.
  "of `G`" is not a separate clause: the union is `J_l ∪ LentJV_l ⊆ E(G)` (`J_l` by `JPlusProps`,
  `LentJV_l` by (JC1) and `LJV_{Y,l} ⊆ E(H_Y) ⊆ E(G)`);
* (JC3) "`Obj_l` uses no other edge" is implied by (JC2) (`EG.Chain.JC3_of_JC2`); it is defined
  here for fidelity but is not a field.
-/

@[expose] public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-- [s6:defJconsumer] "(JC1) `LentJV_l ⊆ ⋃{LJV_{Y,l} : Y a lend-good ancestor of a round
`≤ l − 2`}`". -/
def JC1 (l : ℕ) (L : Finset (Sym2 V)) : Prop :=
  L ⊆ (lendGoodAnc run G S l).biUnion (fun Y => S.ljv Y l)

/-- [s6:defJconsumer] "(JC2) the objects of `Obj_l` are pairwise edge-disjoint cycles and single
edges of `G`, and their union is exactly `J_l ∪ LentJV_l`" (as `IsDecomp`; see the module
docstring for "of `G`"). -/
def JC2 (J L : Finset (Sym2 V)) (Ob : List (Obj V)) : Prop :=
  IsDecomp ((J ∪ L : Finset (Sym2 V)) : Set (Sym2 V)) Ob

/-- [s6:defJconsumer] "(JC3) `Obj_l` uses no other edge" (implied by `JC2`). -/
def JC3 (J L : Finset (Sym2 V)) (Ob : List (Obj V)) : Prop :=
  ∀ o ∈ Ob, ∀ e ∈ o.edges, e ∈ J ∪ L

/-- [s6:defJconsumer] "A *J-consumer* is a rule that acts at each round `3 ≤ l ≤ R`. Given
everything constructed at rounds `> l`, the stage-1 outcome and the set `J_l` (and possibly fresh
randomness), it outputs a family `Obj_l` of objects and a set `LentJV_l` of edges such that
(JC1) `LentJV_l ⊆ ⋃{LJV_{Y,l} : Y a lend-good ancestor of a round ≤ l − 2}`; (JC2) the objects of
`Obj_l` are pairwise edge-disjoint cycles and single edges of `G`, and their union is exactly
`J_l ∪ LentJV_l`; (JC3) `Obj_l` uses no other edge. … Here `J_l` has the properties of Lemma
s6:lemJplus."

`out l J = (Obj_l, LentJV_l)`; the obligations are required for `3 ≤ l ≤ R` and every `J` with
`JPlusProps` (the context — run, designation `δ`, stage data `S` — is fixed). -/
structure JConsumer where
  /-- The rule: `(l, J_l) ↦ (Obj_l, LentJV_l)`. -/
  out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)
  /-- (JC1) for every admissible input. -/
  jc1 : ∀ l J, 3 ≤ l → l ≤ run.R → JPlusProps run G δ S l J → JC1 run G S l (out l J).2
  /-- (JC2) (hence (JC3)) for every admissible input. -/
  jc2 : ∀ l J, 3 ≤ l → l ≤ run.R → JPlusProps run G δ S l J → JC2 J (out l J).2 (out l J).1

end EG.Chain
