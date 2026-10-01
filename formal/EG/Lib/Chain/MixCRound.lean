module

public import EG.Spec.Chain.MixC
public import EG.Spec.Chain.JSLC
public import EG.Spec.Vortex.TPV
public import EG.Spec.HB.StructureHY
public import EG.Lib.Chain.MixCTPV
public import EG.Lib.Chain.StageInst
public import EG.Lib.Found.Fnum

/-!
# The round step of Construction s6:consOrder (manuscript s6:thmMIXC)

Unit P3-s6, round 1. The standalone chain of Construction s6:consOrder, rounds `R, R-1, …, 1`
(decision ORDER-DECOUPLE of blueprint s6b: light parts are handled once, by K-RED, with the final
family `Lent_ext`). The stage data are `S = stageOf ω` for a stage-1 outcome `ω` of positive
weight. At round `l`, with `F` the set of edges lent at the rounds `> l`:
(1) for every `Z ∈ Std_l`, Lemma s4:lemTPV is applied to `(Z^0, O_Z, E := E_l(Z) \ F, P := Ret_Z)`,
giving `E = E^V(Z) ⊔ E^Q(Z)` and a decomposition of `E^V(Z)` into at most `169|Ret_Z|` objects;
(3) if `3 ≤ l ≤ R`, Lemma s6:lemJSLC is applied with `B_Z := E^Q(Z)`, giving `J_l`, `LentJS_l` and
the cycles; (4) the J-consumer acts on `J_l` (its output is `C.out l J_l`, no choice).

* `goodLent S l`: the edges of the classes `LJS_{Y,l,j}` (`j < K^JS_l`) and `LJV_{Y,l}` of the
  lend-good ancestors `Y` of rounds `≤ l − 2`;
* `RoundOut`, `RoundSpec`: the data produced at round `l` and their properties;
* `round_exists`: the round step (uses the Specs of s4:lemTPV, s6:lemJSLC and the TPV bullet of
  s6:thmMIXC (a) as hypotheses);
* `lent C l o`: `LentJS_l ∪ LentJV_l` (empty outside `[3, R]`), `lent_subset_goodLent`;
* `chain_exists`: the whole chain, by descending induction on the rounds.

The Specs are taken as hypotheses (`hTPV`, `hJSLC`, `hApp`, `hHY`), so this file imports no proof.
-/

public section

namespace EG.Chain.MixCA

open EG.HB EG.Chain EG.Quot

universe u

variable {V : Type u} [DecidableEq V]

/-- The edges of the lent classes of round `l` of the lend-good ancestors of rounds `≤ l − 2`:
`⋃_{Y} (⋃_{j < K^JS_l} LJS_{Y,l,j} ∪ LJV_{Y,l})`. -/
@[expose] noncomputable def goodLent (run : Run V) (G : FGraph V) (S : StageData V) (l : ℕ) :
    Finset (Sym2 V) :=
  (lendGoodAnc run G S l).biUnion fun Y =>
    (Finset.range (Stage1.KJS G run l)).biUnion (S.ljs Y l) ∪ S.ljv Y l

/-- The data produced at one round of the chain. -/
structure RoundOut (V : Type u) where
  /-- `E^V(Z)` (TPV), by address. -/
  EV : Addr → Finset (Sym2 V)
  /-- `E^Q(Z)` (TPV), by address. -/
  EQ : Addr → Finset (Sym2 V)
  /-- The TPV decomposition of `E^V(Z)`. -/
  DV : Addr → List (Obj V)
  /-- `J_l` (JS-LC). -/
  J : Finset (Sym2 V)
  /-- `LentJS_l` (JS-LC). -/
  LJS : Finset (Sym2 V)
  /-- The JS-LC cycles. -/
  DC : List (Obj V)

open Classical in
/-- The properties of the data of round `l`, given the set `F` of edges lent at later rounds. -/
@[expose] def RoundSpec (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V) (l : ℕ)
    (F : Finset (Sym2 V)) (o : RoundOut V) : Prop :=
  (∀ a ∈ run.Std G l,
    Disjoint (o.EV a) (o.EQ a) ∧ o.EV a ∪ o.EQ a = run.E G l a \ F ∧
    IsDecomp (o.EV a : Set (Sym2 V)) (o.DV a) ∧
    (o.DV a).length ≤ 169 * (ret run G δ S l a).card ∧
    ∀ e ∈ o.EQ a, ∃ u ∈ qs run G δ S l a, u ∈ e) ∧
  (3 ≤ l → l ≤ run.R →
    o.J ⊆ (run.Std G l).biUnion o.EQ ∧
    o.LJS ⊆ (lendGoodAnc run G S l).biUnion
        (fun Y => (Finset.range (Stage1.KJS G run l)).biUnion (S.ljs Y l)) ∧
    IsDecomp ((((run.Std G l).biUnion o.EQ ∪ o.LJS) \ o.J : Finset (Sym2 V)) : Set (Sym2 V))
      o.DC ∧
    (o.DC.length : ℝ) ≤ 126 * (G.card : ℝ) / (run.M G l : ℝ) +
        1.5 * ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l),
          (mY run G δ Y l : ℝ) ∧
    JPlusProps run G δ S l o.J)

/-- `LentJS_l ∪ LentJV_l` (with `LentJV_l` the consumer's lent edges), empty outside `[3, R]`. -/
@[expose] noncomputable def lent {run : Run V} {G : FGraph V} {δ : Designation V} {S : StageData V}
    (C : JConsumer run G δ S) (l : ℕ) (o : RoundOut V) : Finset (Sym2 V) :=
  if 3 ≤ l ∧ l ≤ run.R then o.LJS ∪ (C.out l o.J).2 else ∅

/-- The edges lent at the rounds `l' ∈ (l, R]`. -/
@[expose] noncomputable def futLent {run : Run V} {G : FGraph V} {δ : Designation V} {S : StageData V}
    (C : JConsumer run G δ S) (outs : ℕ → RoundOut V) (l : ℕ) : Finset (Sym2 V) :=
  (Finset.Ioc l run.R).biUnion fun l' => lent C l' (outs l')

section

variable {run : Run V} {G : FGraph V} {δ : Designation V} {S : StageData V}

theorem lent_subset_goodLent (C : JConsumer run G δ S) {l : ℕ} {F : Finset (Sym2 V)}
    {o : RoundOut V} (h : RoundSpec run G δ S l F o) : lent C l o ⊆ goodLent run G S l := by
  unfold lent
  split_ifs with hl
  · obtain ⟨-, hLJS, -, -, hJ⟩ := h.2 hl.1 hl.2
    have hjc1 := C.jc1 l o.J hl.1 hl.2 hJ
    intro e he
    unfold goodLent
    rw [Finset.mem_biUnion]
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨Y, hY, he⟩ := Finset.mem_biUnion.1 (hLJS he)
      exact ⟨Y, hY, Finset.mem_union_left _ he⟩
    · obtain ⟨Y, hY, he⟩ := Finset.mem_biUnion.1 (hjc1 he)
      exact ⟨Y, hY, Finset.mem_union_right _ he⟩
  · exact Finset.empty_subset _

/-- A good lent edge of round `l` lies in `H_Y` for a lend-good ancestor `Y` of round `≤ l − 2`. -/
theorem mem_goodLent {l : ℕ} {e : Sym2 V} (hS : S.Coherent run G) (he : e ∈ goodLent run G S l) :
    ∃ Y ∈ run.ancestors G, Y.1 + 2 ≤ l ∧ ¬ lendBad run G S Y ∧
      e ∈ (run.ancGraph G Y).edges := by
  classical
  unfold goodLent at he
  obtain ⟨Y, hY, he⟩ := Finset.mem_biUnion.1 he
  unfold lendGoodAnc at hY
  obtain ⟨hYa, hYl, hYg⟩ := Finset.mem_filter.1 hY
  refine ⟨Y, hYa, hYl, hYg, ?_⟩
  rcases Finset.mem_union.1 he with he | he
  · obtain ⟨j, -, he⟩ := Finset.mem_biUnion.1 he
    exact hS.ljs_sub Y l j he
  · exact hS.ljv_sub Y l he

theorem futLent_congr (C : JConsumer run G δ S) {outs outs' : ℕ → RoundOut V} {l : ℕ}
    (h : ∀ l', l < l' → outs' l' = outs l') : futLent C outs' l = futLent C outs l := by
  unfold futLent
  refine Finset.biUnion_congr rfl (fun l' hl' => ?_)
  rw [h l' (Finset.mem_Ioc.1 hl').1]

end

/-- `E_l(Z) ⊆ E(G)`. -/
theorem E_subset_edges (run : Run V) (G : FGraph V) (l : ℕ) (a : Addr) :
    run.E G l a ⊆ G.edges := by
  intro e he
  have h1 := Run.E_subset_graph'_edges run G l a he
  have h2 : (run.graph' G l).edges ⊆ (run.graph G l).edges :=
    (Round.graph'_le (run.graph G l) (run.choice l)).2
  exact Run.graph_edges_subset_of_le run G (Nat.zero_le l) (h2 h1)

/-- The edges of `E_l(Z)` are not loops. -/
theorem not_isDiag_of_mem_E (run : Run V) (G : FGraph V) {l : ℕ} {a : Addr} {e : Sym2 V}
    (he : e ∈ run.E G l a) : ¬ e.IsDiag :=
  G.loopless e (E_subset_edges run G l a he)

/-- **The round step.** For every round `l ∈ [1, R]` and every set `F` of good lent edges (of
any rounds), the data of round `l` exist. -/
theorem round_exists (hTPV : EG.Spec.TPVStatement.{u}) (hJSLC : EG.Spec.JSLCStatement.{u})
    (hApp : EG.Spec.MixCTPVApplicableStatement.{u}) (hHY : EG.Spec.StructureHYStatement.{u})
    {G : FGraph V} {N0 Dstar : ℝ} {run : Run V} {δ : Designation V}
    (hrun : RunHyp N0 Dstar G run) (hδ : IsDesignation run G δ)
    {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp) (l : ℕ)
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ∃ l', e ∈ goodLent run G (stageOf ω) l') :
    ∃ o : RoundOut V, RoundSpec run G δ (stageOf ω) l F o := by
  classical
  set S := stageOf ω with hSdef
  have hS : S.Coherent run G := coherent_ofOutcome hω _ _ _
  have hv := hrun.valid
  have hHY' := hHY V G Dstar run hv
  -- the TPV step at every address
  have htpv : ∀ a : Addr, ∃ (EV EQ : Finset (Sym2 V)) (DV : List (Obj V)),
      a ∈ run.Std G l →
        Disjoint EV EQ ∧ EV ∪ EQ = run.E G l a \ F ∧ IsDecomp (EV : Set (Sym2 V)) DV ∧
        DV.length ≤ 169 * (ret run G δ S l a).card ∧
        ∀ e ∈ EQ, ∃ u ∈ qs run G δ S l a, u ∈ e := by
    intro a
    by_cases ha : a ∈ run.Std G l
    · obtain ⟨hpre, hnl⟩ := (Run.mem_Std_iff run G).1 ha
      have hY : ((l, a) : PartId) ∈ run.ancestors G := (Run.mem_ancestors run G).2 hpre
      -- the hypotheses of TPV
      have hHyp : ∃ εO s : ℝ, Vortex.TPVHyp (run.Z0 G l a) (OZ run G S l a)
          (ret run G δ S l a) εO s := by
        have h := hApp V G N0 Dstar run δ hrun hδ ω hω l a ha
        by_cases hb : lendBad run G S (l, a)
        · exact ⟨_, _, h.2 hb⟩
        · exact ⟨_, _, h.1 hb⟩
      obtain ⟨εO, s, hHyp⟩ := hHyp
      -- admissibility of `E := E_l(Z) \ F`
      have hOZ : (OZ run G S l a).edges ⊆ (run.ancGraph G (l, a)).edges := by
        by_cases hb : lendBad run G S (l, a)
        · rw [OZ_of_lendBad run G S hb, ancGraph_std run G hnl]
        · rw [OZ_of_not_lendBad run G S hb]
          intro e he
          exact hS.own_sub (l, a) (FGraph.mem_ofEdges_edges.1 he).1
      have hadm : Vortex.TPVAdm (run.Z0 G l a) (OZ run G S l a) (run.E G l a \ F) := by
        refine ⟨fun e he => not_isDiag_of_mem_E run G (Finset.mem_sdiff.1 he).1, ?_, ?_⟩
        · intro e he v hv'
          have h1 := Run.E_subset_sym2 run G l a (Finset.mem_sdiff.1 he).1
          have h2 : v ∈ run.partVerts G l a := Finset.mem_sym2_iff.1 h1 v hv'
          have h3 : run.partVerts G l a = run.Z0 G l a := ancVerts_std run G hnl
          rwa [h3] at h2
        · intro e he
          have heH := hOZ he
          refine Finset.mem_sdiff.2 ⟨hHY'.1 _ hY heH, fun heF => ?_⟩
          obtain ⟨l', hl'⟩ := hF e heF
          obtain ⟨Y, hYa, -, hYg, heY⟩ := mem_goodLent hS hl'
          have hYZ : Y = (l, a) := by
            by_contra hne
            exact Finset.disjoint_left.1 (hHY'.2.2.2 Y hYa (l, a) hY hne) heY heH
          subst hYZ
          rw [OZ_of_not_lendBad run G S hYg] at he
          have heown := (FGraph.mem_ofEdges_edges.1 he).1
          unfold goodLent at hl'
          obtain ⟨Y', hY', he'⟩ := Finset.mem_biUnion.1 hl'
          -- `e` lies in a lent class of `Y'`, and in `H_{(l,a)}`; so `Y' = (l, a)`
          have hY'a : Y' ∈ run.ancestors G := (Finset.mem_filter.1 hY').1
          have heY' : e ∈ (run.ancGraph G Y').edges := by
            rcases Finset.mem_union.1 he' with he' | he'
            · obtain ⟨j, -, he'⟩ := Finset.mem_biUnion.1 he'
              exact hS.ljs_sub Y' l' j he'
            · exact hS.ljv_sub Y' l' he'
          have hY'Z : Y' = (l, a) := by
            by_contra hne
            exact Finset.disjoint_left.1 (hHY'.2.2.2 Y' hY'a (l, a) hY hne) heY' heH
          subst hY'Z
          rcases Finset.mem_union.1 he' with he' | he'
          · obtain ⟨j, -, he'⟩ := Finset.mem_biUnion.1 he'
            exact Finset.disjoint_left.1 (hS.own_ljs_disj _ l' j) heown he'
          · exact Finset.disjoint_left.1 (hS.own_ljv_disj _ l') heown he'
      obtain ⟨EV, EQ, hdisj, hunion, hT1, -, ⟨DV, hDV, hDVlen⟩, -⟩ :=
        hTPV V (run.Z0 G l a) (OZ run G S l a) (ret run G δ S l a) εO s hHyp _ hadm
      refine ⟨EV, EQ, DV, fun _ => ⟨hdisj, hunion, hDV, hDVlen, ?_⟩⟩
      intro e he
      have heE : e ∈ run.E G l a \ F := hunion ▸ Finset.mem_union_right _ he
      have hnotV : e ∉ EV := Finset.disjoint_right.1 hdisj he
      have hex : ∃ v ∈ e, v ∉ ret run G δ S l a := by
        by_contra hall
        push_neg at hall
        exact hnotV (hT1 e heE hall)
      obtain ⟨v, hve, hvr⟩ := hex
      have hvZ : v ∈ run.Z0 G l a := hadm.2.1 e heE v hve
      rw [← ret_union_qs run G δ S l a] at hvZ
      rcases Finset.mem_union.1 hvZ with h | h
      · exact absurd h hvr
      · exact ⟨v, h, hve⟩
    · exact ⟨∅, ∅, [], fun h => absurd h ha⟩
  choose EV EQ DV hspec using htpv
  -- the JS-LC step
  by_cases hl : 3 ≤ l ∧ l ≤ run.R
  · have hB : ∀ a ∈ run.Std G l, EQ a ⊆ run.E G l a ∧ ∀ e ∈ EQ a, ∃ u ∈ qs run G δ S l a, u ∈ e := by
      intro a ha
      obtain ⟨-, hunion, -, -, hq⟩ := hspec a ha
      refine ⟨fun e he => ?_, hq⟩
      have : e ∈ run.E G l a \ F := hunion ▸ Finset.mem_union_right _ he
      exact (Finset.mem_sdiff.1 this).1
    obtain ⟨J, LJS, DC, hJ, hLJS, hDC, -, hlen, -, -, hJP⟩ :=
      hJSLC V G N0 Dstar run δ S l EQ hrun hδ hS hl.1 hl.2 hB
    exact ⟨⟨EV, EQ, DV, J, LJS, DC⟩, hspec, fun _ _ => ⟨hJ, hLJS, hDC, hlen, hJP⟩⟩
  · refine ⟨⟨EV, EQ, DV, ∅, ∅, []⟩, hspec, fun h3 hR => absurd ⟨h3, hR⟩ hl⟩

/-- **The chain** (Construction s6:consOrder, standalone part): data for every round `l ∈ [1, R]`,
each built from the edges lent at the rounds `> l`. -/
theorem chain_exists (hTPV : EG.Spec.TPVStatement.{u}) (hJSLC : EG.Spec.JSLCStatement.{u})
    (hApp : EG.Spec.MixCTPVApplicableStatement.{u}) (hHY : EG.Spec.StructureHYStatement.{u})
    {G : FGraph V} {N0 Dstar : ℝ} {run : Run V} {δ : Designation V}
    (hrun : RunHyp N0 Dstar G run) (hδ : IsDesignation run G δ)
    {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp)
    (C : JConsumer run G δ (stageOf ω)) :
    ∃ outs : ℕ → RoundOut V, ∀ l, 1 ≤ l → l ≤ run.R →
      RoundSpec run G δ (stageOf ω) l (futLent C outs l) (outs l) := by
  classical
  suffices h : ∀ k : ℕ, ∃ outs : ℕ → RoundOut V, ∀ l, run.R - k < l → l ≤ run.R →
      RoundSpec run G δ (stageOf ω) l (futLent C outs l) (outs l) by
    obtain ⟨outs, h⟩ := h run.R
    exact ⟨outs, fun l h1 hR => h l (by omega) hR⟩
  intro k
  induction k with
  | zero =>
    exact ⟨fun _ => ⟨fun _ => ∅, fun _ => ∅, fun _ => [], ∅, ∅, []⟩,
      fun l h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    obtain ⟨outs, hk⟩ := ih
    by_cases hkR : run.R ≤ k
    · exact ⟨outs, fun l h1 h2 => hk l (by omega) h2⟩
    · set l0 := run.R - k with hl0
      have hF : ∀ e ∈ futLent C outs l0, ∃ l', e ∈ goodLent run G (stageOf ω) l' := by
        intro e he
        unfold futLent at he
        obtain ⟨l', hl', he⟩ := Finset.mem_biUnion.1 he
        have hl'1 := Finset.mem_Ioc.1 hl'
        exact ⟨l', lent_subset_goodLent C (hk l' (by omega) hl'1.2) he⟩
      obtain ⟨o0, ho0⟩ := round_exists hTPV hJSLC hApp hHY hrun hδ hω l0 _ hF
      refine ⟨Function.update outs l0 o0, fun l h1 h2 => ?_⟩
      have hcongr : futLent C (Function.update outs l0 o0) l = futLent C outs l :=
        futLent_congr C (fun l' hl' => by
          rw [Function.update_of_ne]
          by_contra h
          subst h
          omega)
      by_cases hll : l = l0
      · subst hll
        rw [hcongr, Function.update_self]
        exact ho0
      · rw [hcongr, Function.update_of_ne hll]
        exact hk l (by omega) h2

end EG.Chain.MixCA
