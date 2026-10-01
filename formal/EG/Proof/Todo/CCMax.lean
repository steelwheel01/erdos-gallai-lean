module

public import EG.Spec.Quot.CC
public import EG.Proof.Todo.CCPartner
public import EG.Lib.Prob.MaxLoad

/-!
# P3 stub: `EG.Spec.CCMaxStatement` (s7:lemCC)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CCMax`; consumers import this module.

Proof (manuscript s7:lemCC (ii)): "The edges at `[w]` in `B^P_κ` are exactly the objects in `S_w`.
Indeed, an object with both ends at junction `w` is looped and was paid in (e3), and an object with
no end at junction `w` is not incident to `[w]`. So `m_κ(w,w')` is the number of `o ∈ S_w` whose
partner end has junction `w'`." By (i) (`EG.Todo.CCPartner`) these partner junctions are
independent under the conditioning and each equals a given `w'` with probability at most
`3/Hcd_l`; the bound is `EG.FinDist.maxLoad_le_t` (`EG/Lib/Prob/MaxLoad.lean`: the threshold
`T = max(t, ⌈6e|S_w|/Hcd_l⌉)`, `max_{w'} m ≤ (T − 1) + Σ_{w'} m 1{m ≥ T}` and
`E[m 1{m ≥ T}] ≤ 4eμ_{w'}2^{-T}`).
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist Finset

/-- On the atom of the indicators, `m_κ(w,w')` (`w' ≠ w`) is the number of objects of `S_w` whose
partner junction is `w'`. -/
theorem mPar_eq_load {V : Type*} [DecidableEq V] {I : RoundInput V} (hI : I.Valid) {R : Rules I}
    (hR : R.Valid) (L : Lists I.G I.M) (κ : ℕ) (w : V) (b : ParObj V → Bool → Bool)
    {O : Orders I.G} (hO : O ∈ Spec.ccAtom R L κ w b) {w' : V} (hw' : w' ≠ w) :
    R.mPar (L, O) κ w w' = load (Spec.ccS R κ b)
      (fun o O => R.junction (L, O) (.par o (Spec.ccPartner b o))) w' O := by
  classical
  unfold Rules.mPar load
  congr 1
  ext o
  simp only [mem_filter, Spec.ccS, Spec.parObjsOfColour, Rules.unpaidPar]
  constructor
  · rintro ⟨⟨ho, hnl⟩, hcol, w₁, w₂, h1, h2, hs⟩
    have hK : o ∈ Spec.parObjsOfColour R κ := by
      rw [Spec.parObjsOfColour, mem_filter]; exact ⟨ho, hcol⟩
    have hbF := hO o hK false
    have hbT := hO o hK true
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- the `false` end at `w`, the `true` end at `w'`
      have e1 : b o false = true := hbF.1 h1
      have e2 : b o true = false := by
        by_contra hc
        have := hbT.2 (by simpa using hc)
        rw [h2] at this
        exact hw' (Option.some.inj this)
      refine ⟨⟨⟨ho, hcol⟩, by rw [e1, e2]; decide⟩, ?_⟩
      simp only [Spec.ccPartner, e1]
      exact h2
    · -- the `false` end at `w'`, the `true` end at `w`
      have e2 : b o true = true := hbT.1 h2
      have e1 : b o false = false := by
        by_contra hc
        have := hbF.2 (by simpa using hc)
        rw [h1] at this
        exact hw' (Option.some.inj this)
      refine ⟨⟨⟨ho, hcol⟩, by rw [e1, e2]; decide⟩, ?_⟩
      simp only [Spec.ccPartner, e1]
      exact h1
  · rintro ⟨⟨⟨ho, hcol⟩, hne⟩, hj⟩
    have hK : o ∈ Spec.parObjsOfColour R κ := by
      rw [Spec.parObjsOfColour, mem_filter]; exact ⟨ho, hcol⟩
    have hbF := hO o hK false
    have hbT := hO o hK true
    simp only [Spec.ccPartner] at hj
    cases hF : b o false <;> cases hT : b o true <;> rw [hF, hT] at hne <;> simp at hne
    · -- partner end `false`, the `true` end at `w`
      rw [hF] at hj
      have h2 : R.junction (L, O) (.par o true) = some w := hbT.2 hT
      refine ⟨⟨ho, ?_⟩, hcol, w', w, hj, h2, Sym2.eq_swap⟩
      rintro ⟨u, hu1, hu2⟩
      rw [hj] at hu1; rw [h2] at hu2
      exact hw' ((Option.some.inj hu1).trans (Option.some.inj hu2).symm)
    · -- partner end `true`, the `false` end at `w`
      rw [hF] at hj
      have h1 : R.junction (L, O) (.par o false) = some w := hbF.2 hF
      refine ⟨⟨ho, ?_⟩, hcol, w, w', h1, hj, rfl⟩
      rintro ⟨u, hu1, hu2⟩
      rw [h1] at hu1; rw [hj] at hu2
      exact hw' ((Option.some.inj hu2).trans (Option.some.inj hu1).symm)

open EG.Spec in
/-- [s7:lemCC] `EG.Spec.CCMaxStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem CCMax_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (κ : ℕ) (w : V), κ < 3 * I.M → w ∈ I.pool →
    ∀ (b : ParObj V → Bool → Bool) (hb : 0 < (ordersLaw I.G).prob (ccAtom R L κ w b)),
    ∀ t : ℕ, 1 ≤ t →
      ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).expect
          (fun O => (((I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') : ℕ) : ℝ)) ≤
        (t : ℝ) * (if (ccS R κ b).Nonempty then 1 else 0) +
          6 * Real.exp 1 * ((ccS R κ b).card : ℝ) / I.Hcd +
          4 * Real.exp 1 * (2 : ℝ) ^ (-(t : ℤ)) * ((ccS R κ b).card : ℝ) := by
  intro V _ I hI R hR L κ w hκ hw b hb t ht
  classical
  obtain ⟨-, hind, hlaw⟩ := Todo.CCPartner_univ V I hI R hR L κ w hκ hw b hb
  have hM : (0 : ℝ) < I.M := by exact_mod_cast lt_of_lt_of_le (by norm_num) hI.M_ge
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  -- almost surely under the conditioning, `max_{w'} m_κ(w,w')` is the maximal load
  have hae : ((ordersLaw I.G).cond (Spec.ccAtom R L κ w b) hb).expect
      (fun O => (((I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') : ℕ) : ℝ)) =
      ((ordersLaw I.G).cond (Spec.ccAtom R L κ w b) hb).expect
      (fun O => (((I.pool.erase w).sup (fun w' => load (Spec.ccS R κ b)
        (fun o O => R.junction (L, O) (.par o (Spec.ccPartner b o))) w' O) : ℕ) : ℝ)) := by
    refine expect_congr _ fun O hO => ?_
    rw [cond_w_pos_iff] at hO
    have hs : (I.pool.erase w).sup (fun w' => R.mPar (L, O) κ w w') =
        (I.pool.erase w).sup (fun w' => load (Spec.ccS R κ b)
          (fun o O => R.junction (L, O) (.par o (Spec.ccPartner b o))) w' O) :=
      Finset.sup_congr rfl fun w' hw' =>
        mPar_eq_load hI hR L κ w b hO.1 (Finset.ne_of_mem_erase hw')
    rw [hs]
  rw [hae]
  have h := maxLoad_le_t ((ordersLaw I.G).cond (Spec.ccAtom R L κ w b) hb) (Spec.ccS R κ b)
    (I.pool.erase w) (fun o O => R.junction (L, O) (.par o (Spec.ccPartner b o))) hind
    (p := 3 / I.Hcd) (by positivity) (fun o ho w' => (hlaw o ho w').2) ht
  refine h.trans (le_of_eq ?_)
  ring

/-- Proved in P3. [s7:lemCC] see `EG.Spec.CCMaxStatement`. -/
theorem CCMax : EG.Spec.CCMaxStatement := CCMax_univ.{0}

end EG.Todo
