import EG.Spec.Stage1.Pool
import EG.Spec.Quot.Cand
import EG.Spec.Quot.CandDef
import EG.Spec.Quot.RoundStep
import EG.Spec.Quot.CC
import EG.Spec.Quot.Ultra
import EG.Lib.Quot.Round
import EG.Lib.Prob.Basic
import EG.Lib.Prob.Named
import EG.Lib.Quot.Colour
import EG.Lib.Quot.Schedule
import EGTest.Quot

/-! Cheap non-vacuity checks for the s7a Specs written by chunk s7a (`formal/work/p2s/s7a.md`):
`EG/Spec/Stage1/Pool.lean`, `EG/Spec/Quot/{Cand,CandDef,RoundStep,CC,Ultra}.lean`. (The s7a Specs
of probe units P1 and NUM have their own checks, `EGTest/ProbeP1.lean`, `EGTest/ProbeNUM.lean`.)

* `RoundRulesExistStatement` is proved here (it is `Rules.exists_valid` and
  `RoundInput.clive_le_kh_mul_groupCap` of `EG.Lib.Quot.Round`).
* The round-level hypotheses `I.Valid`, `R.Valid` hold on the valid input `EGTest.Quot.Live.I`
  (hub `0`, port `1`, `Pool_l = [2, 2^500)`, `M = 2^40`, one live `J^hub` item `01`) with its
  chosen rules; on it:
  - `RoundListsLawStatement`: the hub `0` is non-ultra with `c^live_0 = 1`, `k_0 = 1`, and the
    sequence `A_0 = {0,1,2}` is an admissible sequence of disjoint `3`-subsets of `[4M]`;
  - `RoundInjectionStatement`: the port `1` has `E'(1) = ∅`, so every map is an admissible
    injection (the non-trivial case needs PAR objects or an ultra hub, see below);
  - `CCPartnerStatement`, `CCMaxStatement`: there are no PAR objects, so the indicator atom of
    every value pattern is the whole sample space, of probability `1 > 0`; `κ = 0 < 3M`,
    `w = 2 ∈ Pool_l`.
* The non-trivial case of the CC hypotheses (fix round, `ParLive`): on the valid input
  `ParLive.I` (ports `0`, `1`, one live `J^par` item `01`, `Pool_l = [2, 2^500)`), for every valid
  rule and every value of the lists, the PAR object of `01` has a colour `κ < 3M`, and the atom
  "end `false` receives junction `2`, end `true` does not" has positive probability, with
  `S_2 = {o}` and a nonempty partner set (`ParLive.ccAtom_nontrivial`). At its ports
  `|E'(u)| = 1 ≤ |Cand(u) \ Used(u)|`, so the uniform clause of `RoundInjectionStatement` has
  content there.
* The stage-1 quantifier "`∀ ω`" of `CandCountStatement`, `CandSubsetStatement` ranges over a
  nonempty type (the support of `Stage1.law G run` is nonempty), and the stage-data hypothesis `hS`
  is satisfiable (take the record whose JV-lent classes are those of `ω`, the other fields free).

Not checked here:
* `RunHyp` (hypothesis of `PoolLawStatement`, `CandCountStatement`, `CandSubsetStatement`): it
  needs a valid run with `d_1 ≥ D_*` for `D_*` satisfying Γ1 (see `EGTest/Spec_s5.lean`); a
  classed port of a round `l ≥ 3` needs a valid run with `R ≥ 3`, not available in the tests;
* an ultra hub (hypothesis of `UltraIndepStatement`, `UltraMaxStatement`, `UltraCopiesStatement`)
  under `I.Valid`: it needs `c^live_h > ⌊M Hcd/7⌋ ≥ 2^{447}` live items at one hub, hence as many
  ports; `UltraSumStatement` and `CCCopiesStatement` have only the hypotheses `I.Valid`, `R.Valid`,
  which hold on `Live.I`.
-/

open EG EG.HB EG.Chain EG.Quot

namespace EGTest.Spec_s7a

/-- [s7:consRound] "Rules with these arguments exist" and "`k_h⌈Hcd_l/8⌉ ≥ c^live_h`": proved from
the Lib lemmas. -/
theorem roundRulesExist : EG.Spec.RoundRulesExistStatement := by
  intro V _ I hI
  have hM : (0 : ℝ) < I.M := by exact_mod_cast lt_of_lt_of_le (by norm_num) hI.M_ge
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  exact ⟨fun h _ _ _ => RoundInput.clive_le_kh_mul_groupCap I hH h, Rules.exists_valid hI⟩

section stage1

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- The quantifier over stage-1 outcomes ranges over a nonempty set. -/
example : (Stage1.law G run).supp.Nonempty := FinDist.supp_nonempty _

/-- The stage-data hypothesis `hS` of `CandCountStatement` / `CandSubsetStatement` is satisfiable:
any record family with the JV-lent classes of the outcome. -/
example (S0 : StageData V) : ∃ Sω : Stage1.Outcome G run → StageData V,
    ∀ ω Y l, (Sω ω).ljv Y l = (Stage1.LJV G run Y (ω.colAt Y) l).edges :=
  ⟨fun ω => { S0 with ljv := fun Y l => (Stage1.LJV G run Y (ω.colAt Y) l).edges },
    fun _ _ _ => rfl⟩

end stage1

section live

open EGTest.Quot.Live

noncomputable section

/-- The chosen fixed rules of the valid input `Live.I`. -/
def R0 : Rules I := I.chosenRules

theorem R0_valid : R0.Valid := RoundInput.chosenRules_valid I_valid

/-- One value of the lists. -/
def L0 : Lists I.G I.M := (fun _ => 1, fun _ => ∅)

/-- `Live.I` has no PAR objects (no `J^par` items, no fresh centres). -/
theorem parObjs_eq (R : Rules I) : R.parObjs = ∅ := by
  simp [Rules.parObjs, Rules.parObjsPar, RoundInput.parItems, Rules.cherries, I]

/-- The common hypotheses of the round-level statements hold. -/
example : I.Valid ∧ R0.Valid := ⟨I_valid, R0_valid⟩

/-- `RoundListsLawStatement`: a non-ultra hub with a live item, and an admissible sequence of
`k_0 = 1` disjoint `3`-subsets of `[4M]`. -/
example : (0 : ℕ) ∈ I.hubs ∧ ¬ I.ultra 0 ∧ 1 ≤ I.clive 0 ∧ I.kh 0 = 1 ∧
    ∃ A : ℕ → Finset ℕ,
      (∀ i < I.kh 0, A i ⊆ Finset.range (4 * I.M) ∧ (A i).card = 3) ∧
      (∀ i < I.kh 0, ∀ j < I.kh 0, i ≠ j → Disjoint (A i) (A j)) := by
  refine ⟨by simp [I], I_not_ultra, by rw [I_clive], I_kh, fun _ => {0, 1, 2}, ?_, ?_⟩
  · intro i _
    refine ⟨?_, rfl⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range, I]
    omega
  · intro i hi j hj hij
    rw [I_kh] at hi hj
    omega

/-- `RoundInjectionStatement`: the port `1`, with `E'(1) = ∅`; every map is an admissible
injection. -/
example : (1 : ℕ) ∈ I.ports ∧ R0.E' L0 1 = ∅ := by
  refine ⟨by simp [I], ?_⟩
  ext e
  simp only [Rules.E', parObjs_eq, Finset.biUnion_empty, Finset.empty_union, Finset.mem_image,
    Finset.mem_filter, Finset.notMem_empty, iff_false, not_exists, not_and]
  intro it hit _
  have h0 : it.1 = 0 := by
    have : it ∈ I.hubItems := by
      have h1 := hit.1
      simp only [Rules.colouredHub, Finset.mem_filter] at h1
      exact h1.1
    rw [I_hubItems] at this
    rw [Finset.mem_singleton.1 this]
  have hu := hit.2.2
  rw [h0] at hu
  exact I_not_ultra hu

/-- `CCPartnerStatement`, `CCMaxStatement`: a PAR colour `κ = 0 < 3M`, the pooled vertex `2`, and a
value pattern of the indicators whose atom has positive probability. -/
example : (0 : ℕ) < 3 * I.M ∧ (2 : ℕ) ∈ I.pool ∧
    0 < (ordersLaw I.G).prob (EG.Spec.ccAtom R0 L0 0 2 (fun _ _ => false)) := by
  refine ⟨by simp [I], ?_, ?_⟩
  · simp only [I, Finset.mem_Ico]
    exact ⟨le_rfl, two_lt_N⟩
  · have : EG.Spec.ccAtom R0 L0 0 2 (fun _ _ => false) = Set.univ := by
      ext O
      simp [EG.Spec.ccAtom, EG.Spec.parObjsOfColour, parObjs_eq]
    rw [this, FinDist.prob_univ]
    norm_num

end

end live

/-! ## A valid input with a live `J^par` item (fix round: non-trivial CC atom)

`ParLive.I` on `V = ℕ`: ports `0`, `1` of class `(1, [])`, `Pool_l = [2, N)`, `LJV` = the stars
`0–w`, `1–w` (`w ∈ [2, N)`), one live `J^par` item `01`, no hubs, no fresh centres, `M = 2^40`,
`λ = 64` (as `EGTest.Quot.Live`). For every valid rule and every value of the lists, the PAR object
`o` of `01` has an admissible colour `κ`, and the indicator pattern "the end `false` receives the
junction `2`, the end `true` does not" has an atom of positive probability with `S_2 = {o}` and a
nonempty partner set `(Cand \ Used) \ {2}` (`ccAtom_nontrivial`). -/

namespace ParLive

open EGTest.Quot.Live (N N_def Hval two_lt_N N_big)

noncomputable section

theorem three_lt_N : 3 < N := by rw [N_def]; norm_num

/-- The two stars `0–w`, `1–w` (`w ∈ [2, N)`). -/
def star : Finset (Sym2 ℕ) :=
  (Finset.Ico 2 N).image (fun w => s(0, w)) ∪ (Finset.Ico 2 N).image (fun w => s(1, w))

theorem mem_star {e : Sym2 ℕ} : e ∈ star ↔ ∃ u w, (u = 0 ∨ u = 1) ∧ 2 ≤ w ∧ w < N ∧ e = s(u, w) := by
  simp only [star, Finset.mem_union, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro (⟨w, ⟨h1, h2⟩, rfl⟩ | ⟨w, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨0, w, Or.inl rfl, h1, h2, rfl⟩
    · exact ⟨1, w, Or.inr rfl, h1, h2, rfl⟩
  · rintro ⟨u, w, hu | hu, h1, h2, rfl⟩ <;> subst hu
    · exact Or.inl ⟨w, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨w, ⟨h1, h2⟩, rfl⟩

theorem not_mem_star : s(0, 1) ∉ star := by
  rw [mem_star]
  rintro ⟨u, w, -, h1, -, h⟩
  rcases Sym2.eq_iff.1 h with ⟨h3, h2⟩ | ⟨h2, h3⟩ <;> omega

/-- The two stars plus the edge `01`, on `range N`. -/
def G : FGraph ℕ where
  verts := Finset.range N
  edges := insert s(0, 1) star
  edge_verts e he v hv := by
    have := two_lt_N
    rw [Finset.mem_insert, mem_star] at he
    simp only [Finset.mem_range]
    rcases he with rfl | ⟨u, w, hu, hw1, hw2, rfl⟩
    · rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
    · rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
  loopless e he := by
    rw [Finset.mem_insert, mem_star] at he
    rcases he with rfl | ⟨u, w, hu, hw1, hw2, rfl⟩
    · simp
    · simp only [Sym2.mk_isDiag_iff]; omega

/-- Ports `0`, `1` of class `(1, [])`, `Pool_l = [2, N)`, `LJV = ` both stars, `J^par = {01}`, no
hubs, no fresh centres. -/
def I : RoundInput ℕ where
  G := G
  l := 3
  M := 2 ^ 40
  lam := 64
  ancs := {(1, [])}
  ancVerts _ := Finset.range N
  ljv _ := star
  lendGood _ := True
  pool := Finset.Ico 2 N
  poolRound _ := 1
  hubs := ∅
  fresh := ∅
  ports := {0, 1}
  lost := ∅
  cls _ := (1, [])
  jvBad _ := False
  Jlost := ∅
  Jhub := ∅
  Jfr := ∅
  Jpar := {s(0, 1)}

theorem I_J : I.J = {s(0, 1)} := by
  simp [RoundInput.J, I]

theorem I_cand {u : ℕ} (hu : u = 0 ∨ u = 1) : I.cand u = Finset.Ico 2 N := by
  ext w
  rw [RoundInput.cand, Finset.mem_filter]
  change w ∈ Finset.Ico 2 N ∧ 1 = 1 ∧ s(u, w) ∈ star ↔ _
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, rfl, mem_star.2 ⟨u, w, hu, (Finset.mem_Ico.1 h).1, (Finset.mem_Ico.1 h).2, rfl⟩⟩

theorem I_Hcd : I.Hcd = Hval := by
  simp only [RoundInput.Hcd, HcdOf, I, Hval]; norm_num

theorem I_valid : I.Valid where
  M_ge := le_refl _
  Hcd_ge := by rw [I_Hcd, Hval]; simp only [I]; norm_num
  roles := by simp [I]
  hub_typed e he := by simp [I] at he
  fr_typed e he := by simp [I] at he
  par_typed e he := by
    simp only [I, Finset.mem_singleton] at he
    exact ⟨0, by simp [I], 1, by simp [I], he⟩
  lost_typed e he := by simp [I] at he
  J_sub := by rw [I_J]; simp [I, G]
  J1 h Y := by simp [I]
  J2 v _ := by
    rw [I_J]
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [I]
  J2tot := by
    rw [I_J]; simp only [I, G, FGraph.card, Finset.card_range, Finset.card_singleton]
    have := two_lt_N; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by norm_num))
  cls_anc u _ := by simp [I]
  cls_round u _ := by simp [I]
  cls_mem u hu := by
    simp only [I, Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hu ⊢
    have := two_lt_N; omega
  ljv_in Y _ e he := by
    have hN := two_lt_N
    change e ∈ star at he
    refine ⟨Finset.mem_insert_of_mem he, ?_⟩
    obtain ⟨u, w, hu, hw1, hw2, rfl⟩ := mem_star.1 he
    intro v hv
    change v ∈ Finset.range N
    rw [Finset.mem_range]
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
  ljv_disj Y hY Y' hY' hne := by simp [I] at hY hY'; exact absurd (hY.trans hY'.symm) hne
  ljv_J Y _ := by
    rw [I_J, Finset.disjoint_singleton_right]
    exact not_mem_star
  lendGood_ports _ _ := trivial
  good_cand u hu _ := by
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hu
    rw [I_cand hu, I_Hcd, Nat.card_Ico]; exact N_big
  pool_sub := by intro w hw; simp only [I, G, Finset.mem_Ico, Finset.mem_range] at hw ⊢; omega
  ports_sub := by
    intro w hw
    simp only [I, G, Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hw ⊢
    have := two_lt_N; omega

/-- The item `01` is live. -/
theorem I_live : I.live = {s(0, 1)} := by
  classical
  ext e
  simp only [RoundInput.live, RoundInput.paidPool, RoundInput.paidJVBad, RoundInput.items,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, I_J, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩; exact h
  · rintro rfl
    refine ⟨⟨rfl, by simp [I]⟩, ?_⟩
    simp [I]

theorem I_parItems : I.parItems = {s(0, 1)} := by
  ext e
  rw [RoundInput.mem_parItems, I_live]
  simp only [I, Finset.mem_singleton]
  tauto

theorem I_hubItems : I.hubItems = ∅ := by
  simp [RoundInput.hubItems, I]

/-! ### The one PAR object -/

/-- The PAR object of the item `01` (ends `Quot.out s(0,1)`, orientation unknown). -/
abbrev o : ParObj ℕ := ParObj.par (_root_.Quot.out s(0, 1)).1 (_root_.Quot.out s(0, 1)).2

theorem o_ends : ((_root_.Quot.out s(0, 1)).1 = 0 ∧ (_root_.Quot.out s(0, 1)).2 = 1) ∨
    ((_root_.Quot.out s(0, 1)).1 = 1 ∧ (_root_.Quot.out s(0, 1)).2 = 0) :=
  Sym2.eq_iff.1 (Quot.out_eq s(0, 1))

theorem endAt_mem (c : Bool) : o.endAt c = 0 ∨ o.endAt c = 1 := by
  rcases o_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases c <;> simp [ParObj.endAt, h1, h2]

theorem endAt_inj {c c' : Bool} (h : o.endAt c = o.endAt c') : c = c' := by
  rcases o_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases c <;> cases c' <;>
    simp [ParObj.endAt, h1, h2] at h ⊢

theorem endAt_verts (c : Bool) : o.endAt c ∈ I.G.verts := by
  have := two_lt_N
  change o.endAt c ∈ Finset.range N
  rw [Finset.mem_range]; rcases endAt_mem c with h | h <;> rw [h] <;> omega

section rules

variable (R : Rules I) (hR : R.Valid)
include hR

omit hR in
theorem parObjs_eq : R.parObjs = {o} := by
  unfold Rules.parObjs Rules.parObjsPar
  rw [I_parItems]
  simp [Rules.cherries, I]

omit hR in
theorem colouredHub_eq (L : Lists I.G I.M) : R.colouredHub L = ∅ := by
  simp [Rules.colouredHub, I_hubItems]

theorem used_eq (L : Lists I.G I.M) (u : ℕ) : R.used L u = ∅ := by
  have h := (hR.e1Order L).2
  have he : R.e1Items L = ∅ := by simp [Rules.e1Items, colouredHub_eq R]
  rw [he] at h
  have h0 : R.e1Order L = [] := by simpa using h
  simp [Rules.used, Rules.e1State, h0]

omit hR in
theorem E'_o (L : Lists I.G I.M) (c : Bool) : R.E' L (o.endAt c) = {REnd.par o c} := by
  rw [Rules.E', colouredHub_eq R, parObjs_eq R]
  simp only [Finset.filter_empty, Finset.image_empty, Finset.union_empty,
    Finset.singleton_biUnion]
  have h1 : (Finset.univ.filter (fun c' : Bool => o.endAt c' = o.endAt c)) = {c} := by
    ext c'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => endAt_inj h, fun h => h ▸ rfl⟩
  rw [h1]
  simp

theorem junction_o (L : Lists I.G I.M) (O : Orders I.G) (c : Bool) :
    R.junction (L, O) (.par o c) = (inOrder O (o.endAt c) (Finset.Ico 2 N))[0]? := by
  have he : R.e2Order L (o.endAt c) = [REnd.par o c] := by
    have h := (hR.e2Order L (o.endAt c))
    rw [E'_o R L c] at h
    have hperm : (R.e2Order L (o.endAt c)).Perm [REnd.par o c] :=
      (List.perm_ext_iff_of_nodup h.1 (List.nodup_singleton _)).2 (fun x => by
        rw [← List.mem_toFinset, h.2]; simp)
    exact List.perm_singleton.1 hperm
  simp only [Rules.junction, Rules.e2Junc, REnd.port, he, used_eq R hR, Finset.sdiff_empty,
    I_cand (endAt_mem c)]
  simp

end rules

/-! ### Orders with a prescribed first element -/

theorem card_pos : 0 < I.G.card := by
  have := two_lt_N
  change 0 < (Finset.range N).card
  rw [Finset.card_range]; omega

/-- A fixed rank function. -/
def e0 : ↥I.G.verts ≃ Fin I.G.card := Fintype.equivFinOfCardEq (card_verts_eq I.G)

/-- A rank function in which `v` comes first. -/
def ordFirst (v : ↥I.G.verts) : ↥I.G.verts ≃ Fin I.G.card :=
  (Equiv.swap v (e0.symm ⟨0, card_pos⟩)).trans e0

theorem ordFirst_symm_zero (v : ↥I.G.verts) : (ordFirst v).symm ⟨0, card_pos⟩ = v := by
  simp only [ordFirst, Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.swap_apply_right]

theorem filterMap_finRange_head {α : Type*} {n : ℕ} (f : Fin n → Option α) (h : 0 < n) {x : α}
    (hf : f ⟨0, h⟩ = some x) : ((List.finRange n).filterMap f)[0]? = some x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.finRange_succ, List.filterMap_cons]
  have h0 : f 0 = some x := hf
  simp [h0]

theorem inOrder_head (O : Orders I.G) {u : ℕ} (hu : u ∈ I.G.verts) (v : ↥I.G.verts)
    (hO : O ⟨u, hu⟩ = ordFirst v) {C : Finset ℕ} (hv : (v : ℕ) ∈ C) :
    (inOrder O u C)[0]? = some (v : ℕ) := by
  rw [inOrder, dif_pos hu, hO, sortByRank]
  apply filterMap_finRange_head _ card_pos
  rw [ordFirst_symm_zero]
  simp [hv]

/-- The vertex `k < N` of `G`. -/
def vx (k : ℕ) (hk : k < N) : ↥I.G.verts := ⟨k, by change k ∈ Finset.range N; simpa using hk⟩

/-- The orders: `≺_{o(false)}` starts with `2`, every other `≺_x` starts with `3`. -/
def O0 : Orders I.G := fun x =>
  if (x : ℕ) = o.endAt false then ordFirst (vx 2 two_lt_N) else ordFirst (vx 3 three_lt_N)

theorem O0_pos : 0 < (ordersLaw I.G).w O0 := by
  rw [ordersLaw, FinDist.pi_w]
  exact Finset.prod_pos (fun i _ => FinDist.uniform_w_pos _)

theorem junction_O0 (R : Rules I) (hR : R.Valid) (L : Lists I.G I.M) (c : Bool) :
    R.junction (L, O0) (.par o c) = some (if c then 3 else 2) := by
  rw [junction_o R hR]
  cases c
  · rw [inOrder_head O0 (endAt_verts false) (vx 2 two_lt_N) ?_ ?_]
    · simp [vx]
    · simp only [O0]; rw [if_pos trivial]
    · simp [vx]; exact two_lt_N
  · have hne : o.endAt true ≠ o.endAt false := fun h => by simpa using endAt_inj h
    rw [inOrder_head O0 (endAt_verts true) (vx 3 three_lt_N) ?_ ?_]
    · simp [vx]
    · simp only [O0]; rw [if_neg hne]
    · simp [vx]; exact three_lt_N

/-- The indicator pattern: the end `false` receives the junction `2`, the end `true` does not. -/
def b0 : ParObj ℕ → Bool → Bool := fun _ c => !c

/-- **A non-trivial atom of Lemma CC.** For every valid rule and every value of the lists: the PAR
object `o` has a colour `κ < 3M`, `2 ∈ Pool_l`, the atom of the pattern `b0` (the end `false`
receives the junction `2`, the end `true` does not) has positive probability, `S_2 = {o}`, and the
set `(Cand(v_o) \ Used(v_o)) \ {2}` of its partner end is nonempty. -/
theorem ccAtom_nontrivial (R : Rules I) (hR : R.Valid) (L : Lists I.G I.M) :
    ∃ κ, κ < 3 * I.M ∧ (2 : ℕ) ∈ I.pool ∧
      0 < (ordersLaw I.G).prob (EG.Spec.ccAtom R L κ 2 b0) ∧
      EG.Spec.ccS R κ b0 = {o} ∧
      ((I.cand (o.endAt (EG.Spec.ccPartner b0 o)) \
        R.used L (o.endAt (EG.Spec.ccPartner b0 o))).erase 2).Nonempty := by
  obtain ⟨κ, hκ, hcol⟩ := Rules.parColour_some I_valid hR (o := o) (by rw [parObjs_eq R]; simp)
  have hobj : EG.Spec.parObjsOfColour R κ = {o} := by
    simp [EG.Spec.parObjsOfColour, parObjs_eq R, hcol]
  refine ⟨κ, hκ, ?_, ?_, ?_, ?_⟩
  · simp only [I, Finset.mem_Ico]; exact ⟨le_rfl, two_lt_N⟩
  · rw [FinDist.prob_pos_iff]
    refine ⟨O0, ?_, O0_pos⟩
    intro o' ho' c
    rw [hobj, Finset.mem_singleton] at ho'
    subst ho'
    rw [junction_O0 R hR]
    cases c <;> simp [b0]
  · simp [EG.Spec.ccS, hobj, b0]
  · refine ⟨3, ?_⟩
    rw [used_eq R hR, Finset.sdiff_empty, I_cand (endAt_mem _)]
    simp only [Finset.mem_erase, Finset.mem_Ico]
    exact ⟨by norm_num, by norm_num, three_lt_N⟩

/-- `RoundInjectionStatement` at a port with `E'(u) ≠ ∅`: the port `o(c)` has `|E'| = 1` and
`|Cand \ Used| = N − 2 ≥ 1`, so the admissible injections exist and the uniform clause has content. -/
example (R : Rules I) (hR : R.Valid) (L : Lists I.G I.M) (c : Bool) :
    o.endAt c ∈ I.ports ∧ (R.E' L (o.endAt c)).card = 1 ∧
      (R.E' L (o.endAt c)).card ≤ (I.cand (o.endAt c) \ R.used L (o.endAt c)).card := by
  refine ⟨?_, ?_, ?_⟩
  · rcases endAt_mem c with h | h <;> rw [h] <;> simp [I]
  · rw [E'_o R L c]; rfl
  · rw [E'_o R L c, used_eq R hR, Finset.sdiff_empty, I_cand (endAt_mem c), Nat.card_Ico,
      Finset.card_singleton]
    have := three_lt_N; omega

/-- The hypotheses `I.Valid`, `R.Valid` hold for the chosen rules. -/
example : I.Valid ∧ I.chosenRules.Valid := ⟨I_valid, RoundInput.chosenRules_valid I_valid⟩

end

end ParLive

/-- The statements are propositions (parse checks). -/
example : List Prop :=
  [EG.Spec.PoolLawStatement, EG.Spec.CandCountStatement, EG.Spec.CandSubsetStatement,
    EG.Spec.RoundRulesExistStatement, EG.Spec.RoundListsLawStatement,
    EG.Spec.RoundInjectionStatement, EG.Spec.RoundMarkovStatement,
    EG.Spec.CCPartnerStatement, EG.Spec.CCMaxStatement, EG.Spec.CCCopiesStatement,
    EG.Spec.UltraIndepStatement, EG.Spec.UltraMaxStatement, EG.Spec.UltraCopiesStatement,
    EG.Spec.UltraSumStatement]

end EGTest.Spec_s7a
