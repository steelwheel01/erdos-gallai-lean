module

public import EG.Spec.Quot.Ultra
public import EG.Lib.Quot.Injection
public import EG.Lib.Quot.Junction
public import EG.Lib.Quot.Items

/-!
# P3 stub: `EG.Spec.UltraIndepStatement` (s7:lemUltra)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UltraIndep`; consumers import this module.

Proof (manuscript s7:lemUltra (i)): "Items of ultra hubs receive their junctions in (e2). The
junction of the item `(h,u_i)` is the image of its end under the uniformly random injection at
`u_i`, so it is uniform on `Cand_l(u_i) \ Used(u_i)` (`EG.Quot.Rules.prob_e2Junc_eq`), a set of size
at least `Hcd_l/2` by Lemma s7:lemWellDef (v) (`EG.Quot.Rules.wellDefE2_ineqs`). The ports `u_i` are
distinct, and injections at distinct ports are independent" (the junction at `u_i` is a function
of the coordinate `≺_{u_i}` of the orders).
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist

open EG.Spec in
/-- [s7:lemUltra] `EG.Spec.UltraIndepStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem UltraIndep_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (h : V) (κ : ℕ), h ∈ I.hubs → I.ultra h → κ < 4 * I.M →
      Set.InjOn Prod.snd (ultraItems R L h κ : Set (V × V)) ∧
      (ordersLaw I.G).iIndepFun
        (fun (it : ↥(ultraItems R L h κ)) (O : Orders I.G) =>
          R.junction (L, O) (.hub (it : V × V).1 (it : V × V).2)) ∧
      ∀ it ∈ ultraItems R L h κ,
        I.Hcd / 2 ≤ ((I.cand it.2 \ R.used L it.2).card : ℝ) ∧
        ∀ w : V, (ordersLaw I.G).prob {O | R.junction (L, O) (.hub it.1 it.2) = some w} =
          (if w ∈ I.cand it.2 \ R.used L it.2
            then 1 / ((I.cand it.2 \ R.used L it.2).card : ℝ) else 0) := by
  intro V _ I hI R hR L h κ hh hult hκ
  classical
  have hmem : ∀ it ∈ Spec.ultraItems R L h κ,
      it ∈ R.colouredHub L ∧ it.1 = h := fun it hit => by
    unfold Spec.ultraItems at hit
    rw [Finset.mem_filter] at hit
    exact ⟨hit.1, hit.2.1⟩
  have hport : ∀ it ∈ Spec.ultraItems R L h κ, it.2 ∈ I.ports := fun it hit =>
    (I.mem_hubItems.1 (Rules.mem_colouredHub.1 (hmem it hit).1).1).2.1
  have hE' : ∀ it ∈ Spec.ultraItems R L h κ, REnd.hub it.1 it.2 ∈ R.E' L it.2 := by
    intro it hit
    obtain ⟨hc, h1⟩ := hmem it hit
    exact Rules.mem_E'.2 (Or.inr ⟨it, hc, rfl, h1 ▸ hult, rfl⟩)
  have hjunc : ∀ it ∈ Spec.ultraItems R L h κ, ∀ O : Orders I.G,
      R.junction (L, O) (.hub it.1 it.2) = R.e2Junc (L, O) (.hub it.1 it.2) := by
    intro it hit O
    have hu : I.ultra it.1 := (hmem it hit).2 ▸ hult
    simp only [Rules.junction, if_pos hu]
  have hinj : Set.InjOn Prod.snd (Spec.ultraItems R L h κ : Set (V × V)) := by
    intro it hit it' hit' he
    exact Prod.ext (((hmem it hit).2).trans ((hmem it' hit').2).symm) he
  refine ⟨hinj, ?_, ?_⟩
  · -- independence: the junction of `(h, u_i)` is a function of the coordinate `≺_{u_i}`
    unfold ordersLaw
    refine iIndepFun_pi_of_dependsOn _
      (fun it => {⟨(it : V × V).2, hI.ports_sub (hport it.1 it.2)⟩}) ?_ _ ?_
    · intro it it' hne
      rw [Set.disjoint_singleton]
      intro he
      exact hne (Subtype.ext (hinj it.2 it'.2 (Subtype.mk.inj he)))
    · intro it O O' hO
      have hO' : O ⟨(it : V × V).2, hI.ports_sub (hport it.1 it.2)⟩ =
          O' ⟨(it : V × V).2, hI.ports_sub (hport it.1 it.2)⟩ := hO _ (Set.mem_singleton _)
      show R.junction (L, O) (.hub (it : V × V).1 (it : V × V).2) =
        R.junction (L, O') (.hub (it : V × V).1 (it : V × V).2)
      rw [hjunc it.1 it.2 O, hjunc it.1 it.2 O', Rules.e2Junc_eq hR L O (hE' it.1 it.2),
        Rules.e2Junc_eq hR L O' (hE' it.1 it.2), Rules.inOrder_eq_map hI O (hport it.1 it.2),
        Rules.inOrder_eq_map hI O' (hport it.1 it.2), hO']
  · -- uniformity on a set of size at least `Hcd/2`
    intro it hit
    have hu := hport it hit
    have hlive : ∃ e ∈ I.live, it.2 ∈ e :=
      ⟨s(it.1, it.2), (I.mem_hubItems.1 (Rules.mem_colouredHub.1 (hmem it hit).1).1).2.2.1,
        Sym2.mem_mk_right _ _⟩
    obtain ⟨O0⟩ : Nonempty (Orders I.G) := inferInstance
    obtain ⟨h1, h2, h3, h4⟩ := Rules.wellDefE2_ineqs hI hR (L, O0) hu hlive
    have h1' : I.Hcd - ((I.M : ℝ) - 1) ≤ ((I.cand it.2 \ R.used L it.2).card : ℝ) := h1
    have h4' : (R.E' L it.2).card < I.M := h4
    refine ⟨by linarith, fun w => ?_⟩
    have hset : {O : Orders I.G | R.junction (L, O) (.hub it.1 it.2) = some w} =
        {O | R.e2Junc (L, O) (.hub it.1 it.2) = some w} := by
      ext O; simp only [Set.mem_ofPred_eq, hjunc it hit O]
    rw [hset]
    by_cases hw : w ∈ I.cand it.2 \ R.used L it.2
    · rw [if_pos hw]
      have hle : (R.E' L it.2).card ≤ (I.cand it.2 \ R.used L it.2).card := by
        have : ((R.E' L it.2).card : ℝ) ≤ ((I.cand it.2 \ R.used L it.2).card : ℝ) := by
          have : ((R.E' L it.2).card : ℝ) < I.M := by exact_mod_cast h4'
          linarith
        exact_mod_cast this
      exact Rules.prob_e2Junc_eq hI hR L hu (hE' it hit) hle hw
    · rw [if_neg hw]
      have : {O : Orders I.G | R.e2Junc (L, O) (.hub it.1 it.2) = some w} = ∅ := by
        ext O
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro he
        have hm := Rules.e2Junc_mem he
        have hp : (REnd.hub it.1 it.2 : REnd V).port = it.2 := rfl
        rw [hp] at hm
        exact hw hm
      rw [this, prob_empty]

/-- Proved in P3. [s7:lemUltra] see `EG.Spec.UltraIndepStatement`. -/
theorem UltraIndep : EG.Spec.UltraIndepStatement := UltraIndep_univ.{0}

end EG.Todo
