module

public import EG.Lib.Vortex.Strip
public import EG.Lib.Vortex.StepCount

/-!
# Helpers for the PV finish (manuscript s4:lemPV, proof, "Finish")

Unit P4A, stage 3.
* `EG.exists_phase`: an edge `xy` has a phase `c ∈ [4] \ {ext(x), ext(y)}`;
* `EG.flatMap2_perm`: concatenation of two `flatMap`s against a per-element permutation;
* `EG.sum_card_filter_ends`: the stripped-edge count (`Σ_T #{ends of T in Pl_J}` is
  `Σ_{p ∈ Pl_J} pec(𝒫, p)`).
-/

public section

namespace EG

open List

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- "Give every edge `xy ∈ E_2` a phase `c ∈ [4] \ {ext(x), ext(y)}` (at most two values are
excluded)". -/
theorem exists_phase (ext : V → Option (Fin 4)) (e : Sym2 V) :
    ∃ c : Fin 4, ∀ v ∈ e, ext v ≠ some c := by
  induction e using Sym2.ind with
  | _ x y =>
    have key : ∀ a b : Option (Fin 4), ∃ c : Fin 4, a ≠ some c ∧ b ≠ some c := by decide
    obtain ⟨c, hx, hy⟩ := key (ext x) (ext y)
    refine ⟨c, fun v hv => ?_⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hx
    · exact hy

theorem flatMap2_perm {α β : Type*} [DecidableEq β] (l : List α) (f g a : α → List β)
    (h : ∀ x ∈ l, List.Perm (f x ++ g x) (a x)) :
    List.Perm (l.flatMap f ++ l.flatMap g) (l.flatMap a) := by
  rw [List.perm_iff_count]
  intro e
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := (h x (List.mem_cons_self ..)).count_eq e
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons, List.count_append] at h1 h2 ⊢
    omega

/-- `Σ_{T ∈ 𝒫} #{p ∈ S : p an end of T} = Σ_{p ∈ S} pec(𝒫, p)`. -/
theorem sum_card_filter_ends (P : List (List V)) (S : Finset V) :
    (P.map fun T => (S.filter fun p => T.head? = some p ∨ T.getLast? = some p).card).sum =
      ∑ p ∈ S, pathEndCount P p := by
  have e1 : ∀ T : List V, (S.filter fun p => T.head? = some p ∨ T.getLast? = some p).card =
      ∑ p ∈ S, (if endAt p T then 1 else 0) := fun T => by
    rw [Finset.card_filter]
  simp only [e1]
  rw [PVStep.sum_map_finset_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [PVStep.sum_map_ite_eq_countP]
  rfl

end EG
