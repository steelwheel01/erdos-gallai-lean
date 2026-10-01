module

public import EG.Spec.Quot.CC
public import EG.Lib.Quot.Injection
public import EG.Lib.Quot.Colour
public import EG.Lib.Quot.Items
public import EG.Lib.Prob.PiCond

/-!
# P3 stub: `EG.Spec.CCPartnerStatement` (s7:lemCC)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CCPartner`; consumers import this module.

Proof (manuscript s7:lemCC (i)): "A PAR object has its two ends at distinct ports, and every port
carries at most one PAR object of colour `κ` (Lemma s7:lemWellDef(i); `EG.Quot.Rules.parObj_eq_of_end_colour`).
… the junction of the `κ`-end at a port `x` is a function of `≺_x` alone
(`EG.Quot.Rules.e2Junc_eq_endJunc`), and the orders of distinct ports are independent. So
conditioning on `(I_x)_x` keeps the partner ends independent (`EG.FinDist.pi_cond_forall`), and it
conditions the partner end at `v_o` only on the event `I_{v_o} = 0`. The junction of that end is
uniform on `C(v_o)` (`EG.Quot.Rules.prob_endJunc`). Given `I_{v_o} = 0` it is therefore uniform on
`C(v_o) \ {w}`. By Lemma s7:lemWellDef(v), `|C(v_o) \ {w}| ≥ Hcd_l/2 − 1 ≥ Hcd_l/3`."
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist Finset

/-- A conditioned law only depends on the event (the positivity proof is irrelevant). -/
theorem cond_congr_eq {Ω : Type*} (μ : FinDist Ω) {E F : Set Ω} (hE : 0 < μ.prob E) (h : E = F) :
    μ.cond E hE = μ.cond F (h ▸ hE) := by
  subst h; rfl

-- The assembly below is one long proof (three parts of Lemma CC (i) over the same setting);
-- it needs more than the default heartbeat budget.

set_option maxHeartbeats 1000000 in
open EG.Spec in
/-- [s7:lemCC] `EG.Spec.CCPartnerStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem CCPartner_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ (L : Lists I.G I.M) (κ : ℕ) (w : V), κ < 3 * I.M → w ∈ I.pool →
    ∀ (b : ParObj V → Bool → Bool) (hb : 0 < (ordersLaw I.G).prob (ccAtom R L κ w b)),
      -- the partner ports are pairwise distinct
      Set.InjOn (fun o => o.endAt (ccPartner b o)) (ccS R κ b : Set (ParObj V)) ∧
      -- under the conditioning, the partner junctions are independent
      ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).iIndepFun
        (fun (o : ↥(ccS R κ b)) (O : Orders I.G) =>
          R.junction (L, O) (.par (o : ParObj V) (ccPartner b o))) ∧
      -- … each uniform on `(Cand_l(v_o) \ Used(v_o)) \ {w}`, hence each value has probability
      -- at most `3/Hcd_l`
      ∀ o ∈ ccS R κ b, ∀ w' : V,
        ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).prob
            {O | R.junction (L, O) (.par o (ccPartner b o)) = some w'} =
          (if w' ∈ (I.cand (o.endAt (ccPartner b o)) \ R.used L (o.endAt (ccPartner b o))).erase w
            then 1 / (((I.cand (o.endAt (ccPartner b o)) \
                R.used L (o.endAt (ccPartner b o))).erase w).card : ℝ)
            else 0) ∧
        ((ordersLaw I.G).cond (ccAtom R L κ w b) hb).prob
            {O | R.junction (L, O) (.par o (ccPartner b o)) = some w'} ≤ 3 / I.Hcd := by
  intro V _ I hI R hR L κ w hκ hw b hb
  classical
  obtain ⟨K, hKdef⟩ : ∃ K, K = Spec.parObjsOfColour R κ := ⟨_, rfl⟩
  have hK : ∀ o ∈ K, o ∈ R.parObjs ∧ R.parColour o = some κ := fun o ho => by
    rw [hKdef, Spec.parObjsOfColour, mem_filter] at ho; exact ho
  have hport : ∀ o ∈ K, ∀ c, o.endAt c ∈ I.ports := fun o ho c =>
    Rules.parObj_end_port hI hR (hK o ho).1 c
  have hvert : ∀ o ∈ K, ∀ c, o.endAt c ∈ I.G.verts := fun o ho c => hI.ports_sub (hport o ho c)
  have hmemE : ∀ o ∈ K, ∀ c, REnd.par o c ∈ R.E' L (o.endAt c) := fun o ho c =>
    Rules.mem_E'.2 (Or.inl ⟨o, (hK o ho).1, c, rfl, rfl⟩)
  have huniq : ∀ o ∈ K, ∀ c, ∀ o' ∈ K, ∀ c', o.endAt c = o'.endAt c' → o = o' ∧ c = c' := by
    intro o ho c o' ho' c' he
    have hoo : o = o' := Rules.parObj_eq_of_end_colour hI hR (hK o ho).1 (hK o' ho').1 he
      (hK o ho).2 (hK o' ho').2
    subst hoo
    exact ⟨rfl, Rules.parObj_end_inj hI hR (hK o ho).1 he⟩
  -- the junction of a `κ`-end, read at the coordinate of its port
  obtain ⟨F, hF⟩ : ∃ F : V → (↥I.G.verts ≃ Fin I.G.card) → REnd V → Option V,
      F = fun x σ e => ((rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
        Subtype.val)[(R.e2Order L x).idxOf e]? := ⟨_, rfl⟩
  have hj : ∀ o (ho : o ∈ K), ∀ c, ∀ O : Orders I.G, R.junction (L, O) (.par o c) =
      F (o.endAt c) (O ⟨o.endAt c, hvert o ho c⟩) (.par o c) := by
    intro o ho c O
    rw [hF]
    exact Rules.e2Junc_eq_endJunc hI hR L O (hport o ho c) (hmemE o ho c)
  -- the atom is a product event
  obtain ⟨A, hA⟩ : ∃ A : ↥I.G.verts → Set (↥I.G.verts ≃ Fin I.G.card), A = fun x =>
      {σ | ∀ o ∈ K, ∀ c, o.endAt c = x.1 → (F x.1 σ (.par o c) = some w ↔ b o c = true)} :=
    ⟨_, rfl⟩
  have hatom : Spec.ccAtom R L κ w b = {O | ∀ x, O x ∈ A x} := by
    ext O
    rw [hA]
    simp only [Spec.ccAtom, Set.mem_ofPred_eq, ← hKdef]
    constructor
    · intro h x o ho c hc
      have := h o ho c
      rw [hj o ho c O] at this
      have hx : (⟨o.endAt c, hvert o ho c⟩ : ↥I.G.verts) = x := Subtype.ext hc
      rw [hx, hc] at this
      exact this
    · intro h o ho c
      rw [hj o ho c O]
      exact h ⟨o.endAt c, hvert o ho c⟩ o ho c rfl
  have hb' : 0 < (ordersLaw I.G).prob {O | ∀ x, O x ∈ A x} := hatom ▸ hb
  have hcond : (ordersLaw I.G).cond (Spec.ccAtom R L κ w b) hb =
      FinDist.pi (fun x => (FinDist.uniform (↥I.G.verts ≃ Fin I.G.card)).cond (A x)
        (prob_pos_of_prob_pi_pos _ A hb' x)) := by
    rw [cond_congr_eq _ hb hatom]
    exact pi_cond_forall _ A _
  -- the partner ends
  have hS : ∀ o ∈ Spec.ccS R κ b, o ∈ K ∧ b o (Spec.ccPartner b o) = false := by
    intro o ho
    rw [Spec.ccS, mem_filter, ← hKdef] at ho
    refine ⟨ho.1, ?_⟩
    simp only [Spec.ccPartner]
    cases h1 : b o false <;> cases h2 : b o true <;> simp_all
  have hinj : Set.InjOn (fun o => o.endAt (Spec.ccPartner b o)) (Spec.ccS R κ b : Set (ParObj V)) :=
    fun o ho o' ho' he => (huniq o (hS o ho).1 _ o' (hS o' ho').1 _ he).1
  refine ⟨hinj, ?_, ?_⟩
  · -- independence under the conditioning
    rw [hcond]
    refine iIndepFun_pi_of_dependsOn _
      (fun o => {⟨(o : ParObj V).endAt (Spec.ccPartner b o),
        hvert o (hS o o.2).1 _⟩}) ?_ _ ?_
    · intro o o' hne
      rw [Set.disjoint_singleton]
      intro he
      exact hne (Subtype.ext (hinj o.2 o'.2 (Subtype.mk.inj he)))
    · intro o O O' hO
      have h1 := hO _ (Set.mem_singleton _)
      show R.junction (L, O) (.par (o : ParObj V) (Spec.ccPartner b o)) =
        R.junction (L, O') (.par (o : ParObj V) (Spec.ccPartner b o))
      rw [hj o (hS o o.2).1 _ O, hj o (hS o o.2).1 _ O', h1]
  · -- the law of one partner junction under the conditioning
    intro o ho w'
    obtain ⟨hoK, hbp⟩ := hS o ho
    obtain ⟨p, hp⟩ : ∃ p, p = Spec.ccPartner b o := ⟨_, rfl⟩
    rw [← hp] at hbp ⊢
    obtain ⟨x, hx⟩ : ∃ x, x = o.endAt p := ⟨_, rfl⟩
    rw [← hx]
    have hxp : x ∈ I.ports := hx ▸ hport o hoK p
    have hxv : x ∈ I.G.verts := hI.ports_sub hxp
    have hmemx : REnd.par o p ∈ R.E' L x := hx ▸ hmemE o hoK p
    have hjx : ∀ O : Orders I.G, R.junction (L, O) (.par o p) = F x (O ⟨x, hxv⟩) (.par o p) := by
      intro O
      rw [hj o hoK p O]
      subst hx
      rfl
    have huniqx : ∀ o' ∈ K, ∀ c', o'.endAt c' = x → o' = o ∧ c' = p := fun o' ho' c' hc' =>
      huniq o' ho' c' o hoK p (hc'.trans hx)
    have hCv := Rules.sdiff_used_subset_verts (R := R) hI L x
    obtain ⟨O0⟩ : Nonempty (Orders I.G) := inferInstance
    obtain ⟨h1, h2, h3, h4⟩ := Rules.wellDefE2_ineqs hI hR (L, O0) hxp
      (hx ▸ Rules.parObj_end_live hI hR (hK o hoK).1 p)
    obtain ⟨m, hm⟩ : ∃ m, m = (I.cand x \ R.used L x).card := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = (R.E' L x).card := ⟨_, rfl⟩
    have h1' : I.Hcd - ((I.M : ℝ) - 1) ≤ (m : ℝ) := by rw [hm]; exact h1
    have h4' : q < I.M := by rw [hq]; exact h4
    clear h1 h4
    have hle' : q ≤ m := by
      have h5 : (q : ℝ) < I.M := by exact_mod_cast h4'
      have : (q : ℝ) ≤ (m : ℝ) := le_trans h5.le (le_trans h3 (le_trans h2 h1'))
      exact_mod_cast this
    have hle : (R.E' L x).card ≤ (I.cand x \ R.used L x).card := by rw [← hm, ← hq]; exact hle'
    have hH : (2 : ℝ) ^ 10 ≤ I.Hcd := by
      have h := hI.Hcd_ge
      have hM1 : (1 : ℝ) ≤ I.M := by exact_mod_cast le_trans (by norm_num) hI.M_ge
      have h10 : (1 : ℝ) ≤ (I.M : ℝ) ^ 10 := one_le_pow₀ hM1
      calc (2 : ℝ) ^ 10 = 2 ^ 10 * 1 := by ring
        _ ≤ 2 ^ 10 * (I.M : ℝ) ^ 10 := mul_le_mul_of_nonneg_left h10 (by norm_num)
        _ ≤ I.Hcd := h
    have hCbig : I.Hcd / 2 ≤ (m : ℝ) := le_trans h2 h1'
    obtain ⟨H, hHd⟩ : ∃ H, H = I.Hcd := ⟨_, rfl⟩
    rw [← hHd] at hCbig hH
    have hC2' : 2 ≤ m := by
      have : (2 : ℝ) ≤ (m : ℝ) := by linarith only [hCbig, hH]
      exact_mod_cast this
    have hC2 := hC2'
    rw [hm] at hC2
    -- the position of the partner end is below `|C(v_o)|`
    have hidx : (R.e2Order L x).idxOf (.par o p) < (I.cand x \ R.used L x).card := by
      have hmem : REnd.par o p ∈ R.e2Order L x := by
        rw [← List.mem_toFinset, (hR.e2Order L _).2]; exact hmemx
      have h6 := List.idxOf_lt_length_of_mem hmem
      rw [← List.toFinset_card_of_nodup (hR.e2Order L _).1, (hR.e2Order L _).2, ← hq] at h6
      rw [← hm]
      exact lt_of_lt_of_le h6 hle'
    -- the conditioning event at the partner port is `{junction ≠ w}`
    have hAx : A ⟨x, hxv⟩ = {σ | F x σ (.par o p) ≠ some w} := by
      rw [hA]
      ext σ
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h hw'
        have := (h o hoK p hx.symm).1 hw'
        rw [hbp] at this
        exact Bool.false_ne_true this
      · intro h o' ho' c' hc'
        obtain ⟨rfl, rfl⟩ := huniqx o' ho' c' hc'
        rw [hbp]
        simp only [Bool.false_eq_true, iff_false]
        exact h
    -- reduce to the coordinate `≺_x`
    have hset : {O : Orders I.G | R.junction (L, O) (.par o p) = some w'} =
        {O | O ⟨x, hxv⟩ ∈ {σ | F x σ (.par o p) = some w'}} := by
      ext O
      simp only [Set.mem_ofPred_eq]
      rw [hjx O]
    rw [hcond, hset, prob_pi_eval, prob_cond, hAx]
    have hunif : ∀ u ∈ I.cand x \ R.used L x,
        (FinDist.uniform (↥I.G.verts ≃ Fin I.G.card)).prob {σ | F x σ (.par o p) = some u} =
        1 / ((I.cand x \ R.used L x).card : ℝ) := by
      intro u hu
      rw [hF]
      exact Rules.prob_endJunc hI hR L hxp hmemx hle hu
    have hsome : ∀ σ, ∃ u ∈ I.cand x \ R.used L x, F x σ (.par o p) = some u := by
      intro σ
      rw [hF]
      exact Rules.endJunc_isSome hI L x hCv σ hidx
    rw [cond_uniform_erase _ _ _ hsome hunif hC2 w w']
    refine ⟨rfl, ?_⟩
    split_ifs with hw'
    · obtain ⟨m', hm'⟩ : ∃ m', m' = ((I.cand x \ R.used L x).erase w).card := ⟨_, rfl⟩
      rw [← hm']
      have hE1 : (m : ℝ) - 1 ≤ (m' : ℝ) := by
        have h7 := Finset.pred_card_le_card_erase (s := I.cand x \ R.used L x) (a := w)
        rw [← hm, ← hm'] at h7
        have h8 : ((m - 1 : ℕ) : ℝ) ≤ (m' : ℝ) := by exact_mod_cast h7
        rw [Nat.cast_sub (by omega)] at h8
        simpa using h8
      have hpos : (0 : ℝ) < (m' : ℝ) := by linarith only [hE1, hCbig, hH]
      rw [← hHd, div_le_div_iff₀ hpos (by linarith only [hH])]
      linarith only [hE1, hCbig, hH]
    · have : (0 : ℝ) < H := by linarith only [hH]
      rw [← hHd]
      positivity

/-- Proved in P3. [s7:lemCC] see `EG.Spec.CCPartnerStatement`. -/
theorem CCPartner : EG.Spec.CCPartnerStatement := CCPartner_univ.{0}

end EG.Todo
