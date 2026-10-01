module

public import EG.Lib.Quot.Cand
public import EG.Lib.Stage1.Law
public import EG.Lib.Stage1.COL
public import EG.Lib.Stage1.PoolLaw
public import EG.Lib.Stage1.PoolExpect
public import EG.Lib.Chain.Design
public import EG.Lib.HB.Run
public import EG.Lib.Prob.Indep

/-!
# Candidate counts as sums of independent indicators (manuscript s7:lemCand (i), (ii) first part)

"`|Cand_l(u)| = Σ_{w ∈ N_{H_Y}(u)} 1[plab(w) = (l,r)] · 1[uw ∈ LJV_{Y,l}]`. The pool labels are
independent across vertices. The colours of the edges of `H_Y` are independent across edges, and the
edges `uw` for distinct `w` are distinct. The two families are independent of each other. … For a
fixed `w` the two indicators are independent, with `P(plab(w) = (l,r)) = q_l π_{l,r}`. Moreover
`P(uw ∈ LJV_{Y,l}) = p_Y`."

* `ancGraph_le`: `H_Y ≤ G`;
* `card_cand_eq_sum`: the sum of indicators;
* `mem_LJV_colAt_iff`: membership in `LJV_{Y,l}` read from the colour of the edge;
* `iIndepFun_candSummand`: the summands are mutually independent;
* `prob_candSummand_eq_one`: each is `1` with probability `q_l π_{l,r} p_Y`;
* `expect_card_cand`: `E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u) = candMean`.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain EG.Stage1 EG.FinDist

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- `H_Y ≤ G` for every `Y`. -/
theorem ancGraph_le (Y : PartId) : run.ancGraph G Y ≤ G := by
  have h1 : run.partGraph G Y.1 Y.2 ≤ run.graph' G Y.1 := Run.partGraph_le_graph' run G Y.1 Y.2
  have h2 : run.graph' G Y.1 ≤ run.graph G Y.1 := Round.graph'_le _ _
  have h3 : run.graph G Y.1 ≤ G := by
    simpa using Run.graph_le_of_le run G (Nat.zero_le Y.1)
  exact le_trans h1 (le_trans h2 h3)

/-- [s7:lemCand] (i) "`|Cand_l(u)| = Σ_{w ∈ N_{H_Y}(u)} 1[plab(w) = (l,r)] · 1[uw ∈ LJV_{Y,l}]`",
for stage data whose class `LJV_{Y,l}` lies in `E(H_Y)`. -/
theorem card_cand_eq_sum (δ : Designation V) (S : StageData V) (π : ↥G.verts → Option (ℕ × ℕ))
    (l : ℕ) (u : V) (hS : S.ljv (δ l u) l ⊆ (run.ancGraph G (δ l u)).edges) :
    ((cand G δ S π l u).card : ℝ) =
      ∑ w ∈ (run.ancGraph G (δ l u)).nbrs u,
        (if plabOf π w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, w) ∈ S.ljv (δ l u) l then (1 : ℝ) else 0) := by
  classical
  have e : ∀ w ∈ (run.ancGraph G (δ l u)).nbrs u,
      (if plabOf π w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, w) ∈ S.ljv (δ l u) l then (1 : ℝ) else 0) =
        if plabOf π w = some (l, (δ l u).1) ∧ s(u, w) ∈ S.ljv (δ l u) l then 1 else 0 := by
    intro w _
    by_cases h1 : plabOf π w = some (l, (δ l u).1) <;>
      by_cases h2 : s(u, w) ∈ S.ljv (δ l u) l <;> simp [h1, h2]
  rw [Finset.sum_congr rfl e, Finset.sum_boole]
  norm_cast
  congr 1
  ext w
  have hn : w ∈ (run.ancGraph G (δ l u)).nbrs u ↔
      w ∈ (run.ancGraph G (δ l u)).verts ∧ s(u, w) ∈ (run.ancGraph G (δ l u)).edges :=
    Finset.mem_filter
  rw [mem_cand, Stage1.mem_poolSet, Finset.mem_filter, hn]
  constructor
  · rintro ⟨⟨-, hp⟩, hl⟩
    have he := hS hl
    exact ⟨⟨(run.ancGraph G (δ l u)).edge_verts _ he w (Sym2.mem_mk_right u w), he⟩, hp, hl⟩
  · rintro ⟨-, hp, hl⟩
    refine ⟨⟨?_, hp⟩, hl⟩
    by_contra hw
    simp [plabOf, hw] at hp

/-- Membership of an edge of `H_Y` in `LJV_{Y,l}` of the colouring of an ancestor `Y` in `ω`,
read from the colour of that edge. -/
theorem mem_LJV_colAt_iff (ω : Outcome G run) {Y : PartId} (hY : Y ∈ run.ancestors G) (l : ℕ)
    {e : Sym2 V} (he : e ∈ (run.ancGraph G Y).edges) :
    e ∈ (LJV G run Y (ω.colAt Y) l).edges ↔
      ((ω.col ⟨Y, hY⟩ ⟨e, he⟩).1 = true ∧
        (ω.col ⟨Y, hY⟩ ⟨e, he⟩).2.1 = some (LentTag.JV l)) := by
  have hc : ω.colAt Y = ω.col ⟨Y, hY⟩ := by simp [Outcome.colAt, hY]
  unfold LJV
  rw [mem_lentClass_edges, hc]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨he, h⟩⟩

/-- The stage data of a stage-1 outcome have `LJV_{Y,l} ⊆ E(H_Y)`. -/
theorem ljv_subset_ancGraph {Sω : Outcome G run → StageData V}
    (hS : ∀ ω Y l, (Sω ω).ljv Y l = (LJV G run Y (ω.colAt Y) l).edges) (ω : Outcome G run)
    (Y : PartId) (l : ℕ) : (Sω ω).ljv Y l ⊆ (run.ancGraph G Y).edges := by
  intro e he
  rw [hS] at he
  unfold LJV at he
  exact ((mem_lentClass_edges G run Y (ω.colAt Y)).1 he).1

variable (δ : Designation V) (Sω : Outcome G run → StageData V)

/-- [s7:lemCand] (i) "the summands for distinct `w` are functions of disjoint sets of independent
variables, hence independent". -/
theorem iIndepFun_candSummand
    (hS : ∀ ω Y l, (Sω ω).ljv Y l = (LJV G run Y (ω.colAt Y) l).edges)
    (l : ℕ) (u : V) (hY : δ l u ∈ run.ancestors G) :
    (law G run).iIndepFun
      (fun (w : ↥((run.ancGraph G (δ l u)).nbrs u)) (ω : Outcome G run) =>
        (if plabOf ω.pool (w : V) = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, (w : V)) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) := by
  classical
  have hew : ∀ w : ↥((run.ancGraph G (δ l u)).nbrs u),
      s(u, (w : V)) ∈ (run.ancGraph G (δ l u)).edges := fun w => (Finset.mem_filter.1 w.2).2
  have hwG : ∀ w : ↥((run.ancGraph G (δ l u)).nbrs u), (w : V) ∈ G.verts :=
    fun w => (ancGraph_le _).1 (Finset.mem_filter.1 w.2).1
  refine iIndepFun_of_dependsOn G run
    (fun w => {Sum.inl ⟨⟨δ l u, hY⟩, ⟨s(u, (w : V)), hew w⟩⟩,
      Sum.inr (Sum.inr (Sum.inr ⟨(w : V), hwG w⟩))}) ?_ _ ?_
  · intro w w' hww'
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Sigma.mk.inj_iff, heq_eq_eq,
        true_and, Subtype.mk.injEq, Sym2.eq_iff] at h
    · apply hww'
      rcases h with h | ⟨h1, h2⟩
      · exact Subtype.ext h
      · exact Subtype.ext (h2.trans h1)
    · exact hww' (Subtype.ext h)
  · intro w ω ω' h
    have hp : ω.pool ⟨(w : V), hwG w⟩ = ω'.pool ⟨(w : V), hwG w⟩ :=
      h (Sum.inr (Sum.inr (Sum.inr ⟨(w : V), hwG w⟩))) (by simp)
    have hc : ω.col ⟨δ l u, hY⟩ ⟨s(u, (w : V)), hew w⟩ =
        ω'.col ⟨δ l u, hY⟩ ⟨s(u, (w : V)), hew w⟩ :=
      h (Sum.inl ⟨⟨δ l u, hY⟩, ⟨s(u, (w : V)), hew w⟩⟩) (by simp)
    have e1 : plabOf ω.pool (w : V) = plabOf ω'.pool (w : V) := by
      simp only [plabOf, dif_pos (hwG w)]; exact hp
    have e2 : (s(u, (w : V)) ∈ (Sω ω).ljv (δ l u) l) ↔ (s(u, (w : V)) ∈ (Sω ω').ljv (δ l u) l) := by
      rw [hS, hS, mem_LJV_colAt_iff ω hY l (hew w), mem_LJV_colAt_iff ω' hY l (hew w), hc]
    simp only [e1, e2]

/-- [s7:lemCand] (i) "For a fixed `w` the two indicators are independent, with
`P(plab(w) = (l,r)) = q_l π_{l,r}`. Moreover `P(uw ∈ LJV_{Y,l}) = p_Y`." (For `1 ≤ r`,
`r + 2 ≤ l ≤ R` and a probability law of pool labels.) -/
theorem prob_candSummand_eq_one
    (hS : ∀ ω Y l, (Sω ω).ljv Y l = (LJV G run Y (ω.colAt Y) l).edges)
    (hm : poolMass G run ≤ 1) (l : ℕ) (u : V) (hY : δ l u ∈ run.ancestors G)
    (hr1 : 1 ≤ (δ l u).1) (hr2 : (δ l u).1 + 2 ≤ l) (hlR : l ≤ run.R)
    {w : V} (hw : w ∈ (run.ancGraph G (δ l u)).nbrs u) :
    (law G run).prob {ω |
        (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) = 1} =
      qPool G run l * piPool l (δ l u).1 * pY G run (δ l u) := by
  classical
  have he : s(u, w) ∈ (run.ancGraph G (δ l u)).edges := (Finset.mem_filter.1 hw).2
  have hwG : w ∈ G.verts := (ancGraph_le _).1 (Finset.mem_filter.1 hw).1
  set Yc : ↥(run.ancestors G) := ⟨δ l u, hY⟩
  set SA : Set (Option (ℕ × ℕ)) := {o | o = some (l, (δ l u).1)}
  set SB : Set (Colouring G run (δ l u)) := {c | (c ⟨s(u, w), he⟩).1 = true ∧
    (c ⟨s(u, w), he⟩).2.1 = some (LentTag.JV l)}
  have hset : {ω : Outcome G run |
      (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
        (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) = 1} =
      (fun ω : Outcome G run => ω.pool ⟨w, hwG⟩) ⁻¹' SA ∩
        (fun ω : Outcome G run => ω.col Yc) ⁻¹' SB := by
    ext ω
    have e1 : plabOf ω.pool w = ω.pool ⟨w, hwG⟩ := by simp only [plabOf, dif_pos hwG]
    have e2 := mem_LJV_colAt_iff ω hY l he
    rw [← hS] at e2
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, SA, SB, Yc]
    rw [← e1, ← e2]
    by_cases h1 : plabOf ω.pool w = some (l, (δ l u).1) <;>
      by_cases h2 : s(u, w) ∈ (Sω ω).ljv (δ l u) l <;> simp [h1, h2]
  have hind : (law G run).IndepFun (fun ω : Outcome G run => ω.pool ⟨w, hwG⟩)
      (fun ω : Outcome G run => ω.col Yc) :=
    ((indepFun_rest_pool G run).comp (fun p => p.1 Yc) (fun π => π ⟨w, hwG⟩)).symm
  rw [hset, hind SA SB]
  -- the pool factor
  have hA : (law G run).prob ((fun ω : Outcome G run => ω.pool ⟨w, hwG⟩) ⁻¹' SA) =
      qPool G run l * piPool l (δ l u).1 := by
    have e : (fun ω : Outcome G run => ω.pool ⟨w, hwG⟩) ⁻¹' SA =
        {ω | plabOf ω.pool w = some (l, (δ l u).1)} := by
      ext ω; simp [SA, plabOf, hwG]
    rw [e, prob_plabOf_eq G run hwG]
    exact prob_poolLabelLaw_some G run hm ((mem_poolIdx run).2 ⟨by omega, hlR, hr1, hr2⟩)
  -- the colour factor
  have hB : (law G run).prob ((fun ω : Outcome G run => ω.col Yc) ⁻¹' SB) = pY G run (δ l u) := by
    rw [← prob_map, map_col G run Yc]
    have e : SB = {c | s(u, w) ∈ (LJV G run (δ l u) c l).edges} := by
      ext c
      simp only [SB, Set.mem_ofPred_eq, LJV, mem_lentClass_edges]
      exact ⟨fun h => ⟨he, h⟩, fun ⟨_, h⟩ => h⟩
    rw [e]
    exact prob_mem_LJV G run (δ l u) (Finset.mem_Icc.2 ⟨hr2, hlR⟩) ⟨s(u, w), he⟩
  rw [hA, hB]

/-- [s7:lemCand] (ii), first equality: "`E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u)`". -/
theorem expect_card_cand
    (hS : ∀ ω Y l, (Sω ω).ljv Y l = (LJV G run Y (ω.colAt Y) l).edges)
    (hm : poolMass G run ≤ 1) (l : ℕ) (u : V) (hY : δ l u ∈ run.ancestors G)
    (hr1 : 1 ≤ (δ l u).1) (hr2 : (δ l u).1 + 2 ≤ l) (hlR : l ≤ run.R) :
    (law G run).expect (fun ω => ((cand G δ (Sω ω) ω.pool l u).card : ℝ)) =
      candMean run G δ l u := by
  classical
  have hsub : ∀ ω, (Sω ω).ljv (δ l u) l ⊆ (run.ancGraph G (δ l u)).edges :=
    fun ω => ljv_subset_ancGraph hS ω (δ l u) l
  have e1 : (fun ω : Outcome G run => ((cand G δ (Sω ω) ω.pool l u).card : ℝ)) = fun ω =>
      ∑ w ∈ (run.ancGraph G (δ l u)).nbrs u,
        (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
          (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) := by
    funext ω; exact card_cand_eq_sum δ (Sω ω) ω.pool l u (hsub ω)
  rw [e1, expect_sum]
  have e2 : ∀ w ∈ (run.ancGraph G (δ l u)).nbrs u, (law G run).expect (fun ω =>
      (if plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
        (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) =
      qPool G run l * piPool l (δ l u).1 * pY G run (δ l u) := by
    intro w hw
    rw [← prob_candSummand_eq_one δ Sω hS hm l u hY hr1 hr2 hlR hw, ← FinDist.expect_ite]
    congr 1
    funext ω
    by_cases h1 : plabOf ω.pool w = some (l, (δ l u).1) <;>
      by_cases h2 : s(u, w) ∈ (Sω ω).ljv (δ l u) l <;> simp [h1, h2]
  rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul, candMean, FGraph.deg]
  ring

/-! ### The arithmetic of (ii) and (iv) -/

/-- [s7:lemCand] (ii) "`E|Cand_l(u)| ≥ M_l^{-2} 2^{-(l-1-r)} λ_r^{-4} λ_r^{100}/2 =
λ_r^{96} 2^{-(l-r)}/M_l^2`" (with `π = 2t`, `t = 2^{-(l-r)}`). -/
theorem candMean_lower_arith {q π p d M L t : ℝ} (hM : 0 < M) (hL : 0 < L) (ht : 0 < t)
    (hq : q = 1 / M ^ 2) (hπ : π = 2 * t) (hp : 1 / L ^ 4 ≤ p) (hd : L ^ 100 / 2 ≤ d) :
    L ^ 96 * t / M ^ 2 ≤ q * π * p * d := by
  subst hq hπ
  have h1 : 0 ≤ 1 / M ^ 2 * (2 * t) := by positivity
  have h2 : 0 ≤ 1 / L ^ 4 := by positivity
  calc L ^ 96 * t / M ^ 2 = 1 / M ^ 2 * (2 * t) * (1 / L ^ 4) * (L ^ 100 / 2) := by
        field_simp
    _ ≤ 1 / M ^ 2 * (2 * t) * p * (L ^ 100 / 2) := by gcongr
    _ ≤ 1 / M ^ 2 * (2 * t) * p * d := by
        apply mul_le_mul_of_nonneg_left hd
        exact mul_nonneg h1 (le_trans h2 hp)

/-- [s7:lemCand] (ii) "`λ_r^{96} 2^{-(l-r)}/M_l^2 ≥ 2Hcd_l`": from `λ_r ≥ λ_{l-2} > 0` and
`λ_r ≥ 2^{l-r}` (here `λ_r t ≥ 1`, `t = 2^{-(l-r)}`). -/
theorem twoHcd_le_arith {L L' M t : ℝ} (hM : 0 < M) (hL' : 0 < L') (hLL' : L' ≤ L)
    (hLt : 1 ≤ L * t) :
    2 * (L' ^ 95 / (8 * M ^ 2)) ≤ L ^ 96 * t / M ^ 2 := by
  have hL : 0 < L := lt_of_lt_of_le hL' hLL'
  have h95 : L' ^ 95 ≤ L ^ 95 := pow_le_pow_left₀ hL'.le hLL' 95
  have hkey : L' ^ 95 ≤ L ^ 96 * t := by
    calc L' ^ 95 ≤ L ^ 95 * 1 := by rw [mul_one]; exact h95
      _ ≤ L ^ 95 * (L * t) := mul_le_mul_of_nonneg_left hLt (by positivity)
      _ = L ^ 96 * t := by ring
  have e : 2 * (L' ^ 95 / (8 * M ^ 2)) = L' ^ 95 / 4 / M ^ 2 := by field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ L' ^ 95 := by positivity
  linarith

/-- [s7:lemCand] (iv) "`Hcd_l ≥ 2^{10}M_l^{10}` … follows directly from `M_l ≤ λ_{l-2}^{1.6}`:
`8M_l^2·2^{10}M_l^{10} = 2^{13}M_l^{12} ≤ 2^{13}λ_{l-2}^{19.2} ≤ λ_{l-2}^{95}`". -/
theorem Hcd_ge_arith {M L : ℝ} (hM : 1 ≤ M) (hML : M ≤ L ^ (1.6 : ℝ)) (hL : 2 ≤ L) :
    (2 : ℝ) ^ 10 * M ^ 10 ≤ L ^ 95 / (8 * M ^ 2) := by
  have hM0 : 0 < M := by linarith
  have hL0 : 0 < L := by linarith
  have h12 : M ^ 12 ≤ L ^ (19.2 : ℝ) := by
    calc M ^ 12 ≤ (L ^ (1.6 : ℝ)) ^ 12 := pow_le_pow_left₀ hM0.le hML 12
      _ = L ^ (19.2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hsplit : L ^ 95 = L ^ (19.2 : ℝ) * L ^ (75.8 : ℝ) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_natCast]; norm_num
  have h13 : (2 : ℝ) ^ 13 ≤ L ^ (75.8 : ℝ) := by
    calc (2 : ℝ) ^ 13 = (2 : ℝ) ^ ((13 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (75.8 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ L ^ (75.8 : ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  rw [le_div_iff₀ (by positivity), hsplit]
  have h19 : 0 ≤ L ^ (19.2 : ℝ) := Real.rpow_nonneg hL0.le _
  calc (2 : ℝ) ^ 10 * M ^ 10 * (8 * M ^ 2) = (2 : ℝ) ^ 13 * M ^ 12 := by ring
    _ ≤ L ^ (75.8 : ℝ) * L ^ (19.2 : ℝ) := mul_le_mul h13 h12 (by positivity) (by positivity)
    _ = L ^ (19.2 : ℝ) * L ^ (75.8 : ℝ) := by ring

end EG.Quot
