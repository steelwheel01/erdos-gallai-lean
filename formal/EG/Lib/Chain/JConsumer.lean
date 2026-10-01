module

public import EG.Defs.Chain.JConsumer
public import EG.Lib.Chain.JSet

/-!
# J-consumers: basic API (companion of `EG.Defs.Chain.JConsumer`)

* (JC3) follows from (JC2) (`JC3_of_JC2`);
* the objects of a J-consumer's output on an admissible `J` are edges of `J ∪ LentJV`
  (`JConsumer.edges_subset`);
* [s6:defJconsumer] "For example, the rule `Obj_l :=` the edges of `J_l` as single edges,
  `LentJV_l := ∅` is a J-consumer": `trivialConsumer` (non-vacuity of `JConsumer`).
-/

public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-- [s6:defJconsumer] "(JC3) `Obj_l` uses no other edge" follows from (JC2). -/
theorem JC3_of_JC2 {J L : Finset (Sym2 V)} {Ob : List (Obj V)} (h : JC2 J L Ob) : JC3 J L Ob := by
  intro o ho e he
  have hmem : e ∈ Ob.flatMap Obj.edges := List.mem_flatMap.2 ⟨o, ho, he⟩
  have := (h.2.2 e).1 hmem
  exact_mod_cast this

variable {run G δ S}

theorem JConsumer.jc3 (C : JConsumer run G δ S) {l : ℕ} {J : Finset (Sym2 V)} (hl : 3 ≤ l)
    (hlR : l ≤ run.R) (hJ : JPlusProps run G δ S l J) :
    JC3 J (C.out l J).2 (C.out l J).1 :=
  JC3_of_JC2 (C.jc2 l J hl hlR hJ)

variable (run G δ S)

omit [DecidableEq V] in
/-- The edges of `J` as single edges. -/
theorem flatMap_edges_map_edge (J : Finset (Sym2 V)) :
    (J.toList.map Obj.edge).flatMap Obj.edges = J.toList := by
  induction J.toList with
  | nil => rfl
  | cons e t ih => simp [Obj.edges, ih]

/-- [s6:defJconsumer] "For example, the rule `Obj_l :=` the edges of `J_l` as single edges,
`LentJV_l := ∅` is a J-consumer." -/
noncomputable def trivialConsumer : JConsumer run G δ S where
  out _ J := (J.toList.map Obj.edge, ∅)
  jc1 := by
    intro l J _ _ _
    exact Finset.empty_subset _
  jc2 := by
    intro l J _ _ hJ
    refine ⟨?_, ?_, ?_⟩
    · intro o ho
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ho
      exact hJ.not_isDiag (Finset.mem_toList.1 he)
    · rw [flatMap_edges_map_edge]
      exact J.nodup_toList
    · intro e
      rw [flatMap_edges_map_edge, Finset.mem_toList, Finset.union_empty]
      rfl

/-- J-consumers exist (non-vacuity of the structure `JConsumer`). -/
theorem nonempty_jConsumer : Nonempty (JConsumer run G δ S) := ⟨trivialConsumer run G δ S⟩

end EG.Chain
