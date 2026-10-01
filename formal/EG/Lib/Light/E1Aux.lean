module

public import EG.Defs.Light.Stages
public import EG.Lib.Stage1.Law
public import EG.Lib.Prob.Basic
public import EG.Lib.Prob.Named
public import EG.Lib.Prob.Indep
public import EG.Spec.Found.Chernoff

/-!
# Probability facts for Lemma bad probabilities (s5:lemE1 (a))

Library of the P3-s5 unit (`formal/work/p3/s5.md`). Manuscript v6.1, `s5.tex`, proof of
[s5:lemE1] (a): "For `u ∈ A_Y(w)` let `χ_u` be the indicator of the event that `wu ∈ M_Y` and `u`
carries no round-`l` zone. … the `χ_u`, `u ∈ A_Y(w)`, are independent. By the uniform split and
the uniform own colouring of Definition s3:defCOL(i),(iii), `P(wu ∈ M_Y) = (1/2)(1/k_own)` …. By
Lemma s5:lemZones(i), `P(u carries a round-l zone) ≤ P(choice(u) ≠ none) ≤ 1/2`."

Here the indicator is taken of the (smaller) event "`wu ∈ M_Y` and `choice(u) = none`", whose
probability is `(1/2)(1/k_own)(1 − Σ_Y zp_Y)`; its count is at most the count of (E1).

* `prob_col_own`: `P((bit, own label) of e = (false, o)) = (1/2)(1/k_own)`;
* `prob_zone_none`: `P(zone label of u = none) = 1 − zpSum(u)` (when `zpSum(u) ≤ 1`);
* `prob_col_own_zone_none`: the product formula (the colour of an edge and the zone label of a
  vertex are functions of distinct stage-1 coordinates).
-/

public section

namespace EG.Light

open EG.HB EG.Stage1 FinDist

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- The event "the label triple of the edge `e` of `H_Y` has fair bit `false` (own) and own
label `o`" has probability `(1/2)(1/k_own)`. -/
theorem prob_col_own (Y : ↥(run.ancestors G)) (e : ↥(run.ancGraph G Y).edges)
    (o : Fin (kown G run Y)) :
    (law G run).prob {ω | (ω.col Y e).1 = false ∧ (ω.col Y e).2.2 = o} =
      1 / 2 * ((kown G run Y : ℝ))⁻¹ := by
  have h1 : {ω : Outcome G run | (ω.col Y e).1 = false ∧ (ω.col Y e).2.2 = o} =
      (fun ω => ω.col Y e) ⁻¹' (({false} : Set Bool) ×ˢ ((Set.univ : Set (Option LentTag)) ×ˢ
        ({o} : Set (Fin (kown G run Y))))) := by
    ext ω
    simp [Set.mem_prod]
  rw [h1, ← prob_map, map_col_apply, edgeLaw, prob_prod_set_prod, prob_prod_set_prod,
    prob_univ, prob_singleton, prob_singleton, ownLaw, uniform_w, bitLaw, bernoulli_w_false,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

/-- The zone label of the vertex `u` is `none` with probability `1 − zpSum(u)` (if
`zpSum(u) ≤ 1`). -/
theorem prob_zone_none (u : ↥G.verts) (h : zpSum G run u ≤ 1) :
    (law G run).prob {ω | ω.zone u = none} = 1 - zpSum G run u := by
  have h1 : {ω : Outcome G run | ω.zone u = none} =
      Outcome.zone ⁻¹' ((fun z : ↥G.verts → Option ZIdx => z u) ⁻¹' ({none} : Set (Option ZIdx))) := by
    ext ω
    rfl
  rw [h1, ← prob_map, map_zone, zoneLaw, ← prob_map, map_eval_pi, prob_singleton, zoneLabelLaw,
    dif_pos h]
  rfl

/-- The colour of the edge `e` of `H_Y` and the zone label of the vertex `u` are independent
(functions of distinct stage-1 coordinates): the product formula. -/
theorem prob_col_own_zone_none (Y : ↥(run.ancestors G)) (e : ↥(run.ancGraph G Y).edges)
    (o : Fin (kown G run Y)) (u : ↥G.verts) :
    (law G run).prob {ω | ((ω.col Y e).1 = false ∧ (ω.col Y e).2.2 = o) ∧ ω.zone u = none} =
      (law G run).prob {ω | (ω.col Y e).1 = false ∧ (ω.col Y e).2.2 = o} *
        (law G run).prob {ω | ω.zone u = none} := by
  have hind : (law G run).IndepFun (fun ω => ω.col Y e) (fun ω => ω.zone u) := by
    refine indepFun_of_dependsOn G run (fun c => c = Sum.inl ⟨Y, e⟩) ?_ ?_
    · intro ω ω' h
      exact h _ rfl
    · intro ω ω' h
      exact h (Sum.inr (Sum.inl u)) (by simp)
  have := hind {x | x.1 = false ∧ x.2.2 = o} {none}
  simpa [Set.preimage, Set.inter_def] using this

/-- [s5:lemE1] (a), the Chernoff step for one round `l` and one vertex `w`: if every `u ∈ A` is a
vertex of `G` with `wu ∈ E(H_Y)` and `zpSum(u) ≤ 1/2`, `k_own ≤ L` and `L^5/4 ≤ |A|/(4L)`, then
`P(#{u ∈ A : wu ∈ M_Y, u carries no round-l zone} < L^5/8) ≤ exp(−L^5/32)`. The Chernoff lower
tail (Cited result s1:citChernoffGen) is passed as the hypothesis `hC`. -/
theorem prob_count_lt_le.{u} {V : Type u} [DecidableEq V] {G : FGraph V} {run : Run V}
    (hC : EG.Spec.ChernoffGenStatement.{u, u})
    {Y : PartId} (hY : Y ∈ run.ancestors G) (w : V) (l : ℕ) (A : Finset V) (L : ℝ) (hL : 0 < L)
    (hA : ∀ u ∈ A, u ∈ G.verts ∧ s(w, u) ∈ (run.ancGraph G Y).edges)
    (hz : ∀ u : ↥G.verts, (u : V) ∈ A → zpSum G run u ≤ 1 / 2)
    (hk : (kown G run Y : ℝ) ≤ L) (hμ : L ^ 5 / 4 ≤ (A.card : ℝ) / (4 * L)) :
    (law G run).prob {ω | (((A.filter fun u =>
        s(w, u) ∈ (ownM G run Y (ω.colAt Y)).edges ∧ zonePhase ω.zone l u = none).card : ℕ) : ℝ) <
          L ^ 5 / 8} ≤ Real.exp (-(L ^ 5 / 32)) := by
  classical
  set Ysub : ↥(run.ancestors G) := ⟨Y, hY⟩ with hYsub
  set o : Fin (kown G run Y) := ownIdx (run.ancVerts G Y).card none with ho
  let ι := {u : ↥G.verts // s(w, (u : V)) ∈ (run.ancGraph G Ysub).edges}
  let cond : ι → Outcome G run → Prop := fun u ω =>
    (u.1 : V) ∈ A ∧ (((ω.col Ysub ⟨s(w, (u.1 : V)), u.2⟩).1 = false ∧
      (ω.col Ysub ⟨s(w, (u.1 : V)), u.2⟩).2.2 = o) ∧ ω.zone u.1 = none)
  let I : ι → Outcome G run → ℝ := fun u ω => if cond u ω then 1 else 0
  have h01 : ∀ u ω, I u ω = 0 ∨ I u ω = 1 := by
    intro u ω
    by_cases h : cond u ω
    · right; simp [I, h]
    · left; simp [I, h]
  have hind : (law G run).iIndepFun I := by
    have := (iIndepFun_edge_zone G run Ysub w).comp
      (fun (u : ι) (p : EdgeLabel G run Ysub × Option ZIdx) =>
        if (u.1 : V) ∈ A ∧ ((p.1.1 = false ∧ p.1.2.2 = o) ∧ p.2 = none) then (1 : ℝ) else 0)
    exact this
  -- the expectation
  have hEu : ∀ u : ι, (law G run).expect (I u) =
      if (u.1 : V) ∈ A then 1 / 2 * ((kown G run Y : ℝ))⁻¹ * (1 - zpSum G run u.1) else 0 := by
    intro u
    by_cases hu : (u.1 : V) ∈ A
    · rw [if_pos hu]
      have hI : I u = ({ω | ((ω.col Ysub ⟨s(w, (u.1 : V)), u.2⟩).1 = false ∧
          (ω.col Ysub ⟨s(w, (u.1 : V)), u.2⟩).2.2 = o) ∧ ω.zone u.1 = none} :
            Set (Outcome G run)).indicator 1 := by
        funext ω
        simp only [I, cond, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, hu, true_and]
      rw [hI, ← prob_eq_expect, prob_col_own_zone_none, prob_col_own,
        prob_zone_none _ ((hz u.1 hu).trans (by norm_num))]
    · rw [if_neg hu]
      have hI : I u = fun _ => 0 := by
        funext ω
        simp [I, cond, hu]
      rw [hI, expect_const]
  have hcardι : ((Finset.univ : Finset ι).filter fun u => (u.1 : V) ∈ A).card = A.card := by
    symm
    refine Finset.card_bij (fun a ha => ⟨⟨a, (hA a ha).1⟩, (hA a ha).2⟩) ?_ ?_ ?_
    · intro a ha
      simp [ha]
    · intro a _ b _ h
      exact congrArg (fun x : ι => (x.1 : V)) h
    · intro u hu
      refine ⟨u.1.1, (Finset.mem_filter.1 hu).2, ?_⟩
      rfl
  have hE : L ^ 5 / 4 ≤ (law G run).expect (fun ω => ∑ u, I u ω) := by
    rw [(law G run).expect_sum Finset.univ I]
    have hle : ∀ u : ι, (if (u.1 : V) ∈ A then 1 / (4 * L) else 0) ≤ (law G run).expect (I u) := by
      intro u
      rw [hEu u]
      by_cases hu : (u.1 : V) ∈ A
      · rw [if_pos hu, if_pos hu]
        have hk0 : (0 : ℝ) < kown G run Y := by exact_mod_cast (Nat.succ_pos _)
        have hzu := hz u.1 hu
        have h1 : (2 * L)⁻¹ ≤ 1 / 2 * ((kown G run Y : ℝ))⁻¹ := by
          rw [one_div, ← mul_inv]
          exact inv_anti₀ (by positivity) (by linarith)
        have h2 : (1 : ℝ) / 2 ≤ 1 - zpSum G run u.1 := by linarith
        have h3 : 0 ≤ (2 * L)⁻¹ := by positivity
        calc 1 / (4 * L) = (2 * L)⁻¹ * (1 / 2) := by field_simp; ring
          _ ≤ 1 / 2 * ((kown G run Y : ℝ))⁻¹ * (1 - zpSum G run u.1) :=
            mul_le_mul h1 h2 (by norm_num) (by positivity)
      · rw [if_neg hu, if_neg hu]
    calc L ^ 5 / 4 ≤ (A.card : ℝ) / (4 * L) := hμ
      _ = ∑ u : ι, (if (u.1 : V) ∈ A then 1 / (4 * L) else 0) := by
        rw [← Finset.sum_filter, Finset.sum_const, hcardι, nsmul_eq_mul]
        ring
      _ ≤ ∑ u, (law G run).expect (I u) := Finset.sum_le_sum fun u _ => hle u
  have hCh := (hC (Outcome G run) (law G run) ι I (1 / 2) (L ^ 5 / 4) h01 hind (by norm_num)
    (by norm_num)).2 (by positivity) hE
  -- the event of (E1) is contained in the Chernoff event
  have hsub : {ω : Outcome G run | (((A.filter fun u =>
        s(w, u) ∈ (ownM G run Y (ω.colAt Y)).edges ∧ zonePhase ω.zone l u = none).card : ℕ) : ℝ) <
          L ^ 5 / 8} ⊆ {ω | ∑ u, I u ω ≤ (1 - 1 / 2) * (L ^ 5 / 4)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hsum : ∑ u, I u ω = (((Finset.univ : Finset ι).filter fun u => cond u ω).card : ℝ) := by
      simp only [I]
      rw [Finset.sum_boole]
    have hcol : ω.colAt Y = ω.col Ysub := by
      simp [Outcome.colAt, hY, Ysub]
    have hinj : ((Finset.univ : Finset ι).filter fun u => cond u ω).card ≤
        (A.filter fun u => s(w, u) ∈ (ownM G run Y (ω.colAt Y)).edges ∧
          zonePhase ω.zone l u = none).card := by
      refine Finset.card_le_card_of_injOn (fun u => (u.1 : V)) ?_ ?_
      · intro u hu
        obtain ⟨huA, ⟨hb, hown⟩, hzn⟩ := (Finset.mem_filter.1 hu).2
        refine Finset.mem_filter.2 ⟨huA, ?_, ?_⟩
        · rw [hcol]
          simp only [ownM, ownClass, FGraph.restrictEdges, Finset.mem_filter]
          refine ⟨u.2, ?_⟩
          rw [FinDist.mem_selectSet]
          refine ⟨u.2, ?_⟩
          simp only [decide_eq_true_eq]
          rw [hb, hown]
        · have hz' : zoneOf ω.zone (u.1 : V) = none := by
            simp only [zoneOf, u.1.2, dif_pos]
            exact hzn
          simp only [zonePhase, hz']
      · intro u _ u' _ h
        exact Subtype.ext (Subtype.ext h)
    rw [hsum]
    have : (((Finset.univ : Finset ι).filter fun u => cond u ω).card : ℝ) ≤
        ((A.filter fun u => s(w, u) ∈ (ownM G run Y (ω.colAt Y)).edges ∧
          zonePhase ω.zone l u = none).card : ℝ) := by exact_mod_cast hinj
    linarith
  calc _ ≤ (law G run).prob {ω | ∑ u, I u ω ≤ (1 - 1 / 2) * (L ^ 5 / 4)} := prob_mono _ hsub
    _ ≤ Real.exp (-((1 / 2) ^ 2 * (L ^ 5 / 4) / 2)) := hCh
    _ = Real.exp (-(L ^ 5 / 32)) := by congr 1; ring

end EG.Light
