module

public import EG.Defs.Quot.Round
public import EG.Lib.Quot.Cand
public import EG.Lib.Quot.Schedule
public import EG.Lib.Chain.JSet
public import EG.Lib.Found.FGraphFnum

/-!
# API for the round step (s7:consRound)

* the instantiation `RoundInput.ofPast` field by field (`rfl`), `ofPast_J` (the four classes of a
  set with `JPlusProps` recombine to it), `ofPast_cand` (the two candidate sets agree),
  `ofPast_multAt` (`multAt` is the run's `mult_r(w)`);
* membership lemmas for items, live items, hub items, fresh items;
* `pairUp` / `leftover`, the lists `listOf` of non-ultra hubs;
* the quotient: edges, vertices, looplessness;
* `Rules.xiChosen_spec` (the chosen `ξ_l` lies in the Markov event when the event has positive
  probability);
* **`Rules.exists_valid`**: fixed rules satisfying `Rules.Valid` exist whenever `Hcd > 0` (in
  particular for every `RoundInput.Valid` input). "Rules with these arguments exist, for instance
  lexicographically first choices for fixed orders of the finite sets involved"
  ([s7:consRound], *Fixed rules*).
* `RoundInput.chosenRules_valid`, `roundOut_eq`, `roundQuotient_eq`, `roundOut_roundQuotient`: the
  run-level J-consumer output and the quotient use one and the same valid rule and `ξ_l`
  (JV-SAME-Q).
* `Rules.one_le_rank`, `Rules.rank_head`: ranks start at `1` (fix round 2).

Design note: `formal/work/p2d/quot.md`.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain

variable {V : Type*} [DecidableEq V]

/-! ## `ofPast` -/

section ofPast

variable (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V)
  (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V))

@[simp] theorem ofPast_G : (RoundInput.ofPast run G δ S π l J).G = G := rfl
@[simp] theorem ofPast_l : (RoundInput.ofPast run G δ S π l J).l = l := rfl
@[simp] theorem ofPast_M : (RoundInput.ofPast run G δ S π l J).M = run.M G l := rfl
@[simp] theorem ofPast_lam : (RoundInput.ofPast run G δ S π l J).lam = run.lam G (l - 2) := rfl
@[simp] theorem ofPast_ancs : (RoundInput.ofPast run G δ S π l J).ancs = run.ancestors G := rfl
@[simp] theorem ofPast_hubs : (RoundInput.ofPast run G δ S π l J).hubs = run.D G l := rfl
@[simp] theorem ofPast_fresh :
    (RoundInput.ofPast run G δ S π l J).fresh = freshCentres run G l := rfl
@[simp] theorem ofPast_ports :
    (RoundInput.ofPast run G δ S π l J).ports = qsRound run G δ S l := rfl
@[simp] theorem ofPast_lost :
    (RoundInput.ofPast run G δ S π l J).lost = lostRound run G δ S l := rfl
@[simp] theorem ofPast_pool :
    (RoundInput.ofPast run G δ S π l J).pool = Stage1.poolL G π l := rfl

theorem ofPast_Hcd : (RoundInput.ofPast run G δ S π l J).Hcd = Hcd run G l := rfl

theorem ofPast_thult : (RoundInput.ofPast run G δ S π l J).thult = thult run G l := rfl

/-- The four classes of a set with `JPlusProps` recombine to it. -/
theorem ofPast_J {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J) :
    (RoundInput.ofPast run G δ S π l J).J = J :=
  hJ.union_types

/-- The candidate set of the round input equals `Cand_l(u)` of [s7:defCand] for a class of round
`r(u)` with `1 ≤ r(u)`, `r(u) + 2 ≤ l`. -/
theorem ofPast_cand {u : V} (h1 : 1 ≤ (δ l u).1) (h2 : (δ l u).1 + 2 ≤ l) :
    (RoundInput.ofPast run G δ S π l J).cand u = cand G δ S π l u := by
  ext w
  show w ∈ (Stage1.poolL G π l).filter _ ↔ _
  rw [Finset.mem_filter, mem_cand]
  constructor
  · rintro ⟨hw, hr, hl⟩
    refine ⟨?_, hl⟩
    have hr' : Stage1.poolRound π w = (δ l u).1 := hr
    rw [← hr']
    exact Stage1.mem_poolSet_poolRound hw
  · rintro ⟨hw, hl⟩
    refine ⟨Stage1.mem_poolL.2 ?_, Stage1.poolRound_eq hw, hl⟩
    exact ⟨(Stage1.mem_poolSet.1 hw).1, _, h1, h2, (Stage1.mem_poolSet.1 hw).2⟩

/-- The multiplicity read by the round step is `mult_r(w)` of the run ([s2:defAncestors]), for every
`r` (both count the round-`r` parts containing `w`; there are none outside `[1,R]`). Used by
Lemma [s7:lemUHsplit] (ii), whose junction-copy bound `4M Σ mult_{r(w)}(w)` is the `X_{V,l}` term. -/
theorem ofPast_multAt (r : ℕ) (w : V) :
    (RoundInput.ofPast run G δ S π l J).multAt r w = run.mult G r w := by
  have key : (run.ancestors G).filter (fun Y => Y.1 = r ∧ w ∈ run.ancVerts G Y) =
      ((run.prePartAddrs G r).filter (fun a => w ∈ run.partVerts G r a)).map
        ⟨fun a => (r, a), fun a b h => (Prod.ext_iff.1 h).2⟩ := by
    apply Finset.ext
    rintro ⟨r', a⟩
    rw [Finset.mem_filter, Finset.mem_map, Run.mem_ancestors]
    simp only [Run.ancVerts, Finset.mem_filter]
    constructor
    · rintro ⟨h1, rfl, h2⟩
      exact ⟨a, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨b, ⟨h1, h2⟩, hb⟩
      have hb' : (r, b) = (r', a) := hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb'
      exact ⟨h1, rfl, h2⟩
  change ((run.ancestors G).filter (fun Y => Y.1 = r ∧ w ∈ run.ancVerts G Y)).card = _
  rw [key, Finset.card_map]
  rfl

end ofPast

/-! ## Items -/

namespace RoundInput

variable (I : RoundInput V)

theorem mem_items {e : Sym2 V} : e ∈ I.items ↔ e ∈ I.J ∧ e ∉ I.Jlost := Finset.mem_sdiff

theorem live_subset_items : I.live ⊆ I.items := Finset.sdiff_subset

theorem mem_live {e : Sym2 V} :
    e ∈ I.live ↔ e ∈ I.items ∧ e ∉ I.paidPool ∧ e ∉ I.paidJVBad := by
  simp [live, not_or]

/-- (a2) "`Live ∩ Pool_l = ∅`". -/
theorem not_mem_pool_of_mem_live {e : Sym2 V} (he : e ∈ I.live) {v : V} (hv : v ∈ e) :
    v ∉ I.pool := by
  classical
  intro hp
  have h := (I.mem_live).1 he
  apply h.2.1
  simp only [paidPool, Finset.mem_filter]
  exact ⟨h.1, v, hv, hp⟩

theorem mem_hubItems {p : V × V} :
    p ∈ I.hubItems ↔ p.1 ∈ I.hubs ∧ p.2 ∈ I.ports ∧ s(p.1, p.2) ∈ I.live ∧
      s(p.1, p.2) ∈ I.Jhub := by
  simp [hubItems, and_assoc]

theorem mem_hubItemsAt {p : V × V} {u : V} :
    p ∈ I.hubItemsAt u ↔ p ∈ I.hubItems ∧ p.2 = u := Finset.mem_filter

theorem mem_frPorts {x u : V} :
    u ∈ I.frPorts x ↔ u ∈ I.ports ∧ s(x, u) ∈ I.live ∧ s(x, u) ∈ I.Jfr := Finset.mem_filter

theorem mem_parItems {e : Sym2 V} : e ∈ I.parItems ↔ e ∈ I.live ∧ e ∈ I.Jpar :=
  Finset.mem_filter

theorem ultra_iff (h : V) : I.ultra h ↔ I.thult < I.clive h := Iff.rfl

omit [DecidableEq V] in
theorem groupCap_pos (hH : 0 < I.Hcd) : 0 < I.groupCap :=
  Nat.ceil_pos.2 (by positivity)

/-- "`k_h ⌈Hcd_l/8⌉ ≥ c^live_h`" ([s7:consRound] (c): "This is possible because
`k_h⌈Hcd_l/8⌉ ≥ c^live_h`"). -/
theorem clive_le_kh_mul_groupCap (hH : 0 < I.Hcd) (h : V) :
    I.clive h ≤ I.kh h * I.groupCap := by
  have h1 : 8 * (I.clive h : ℝ) / I.Hcd ≤ I.kh h := Nat.le_ceil _
  have h2 : I.Hcd / 8 ≤ I.groupCap := Nat.le_ceil _
  have h3 : (I.clive h : ℝ) ≤ (I.kh h : ℝ) * I.groupCap := by
    calc (I.clive h : ℝ) = (8 * I.clive h / I.Hcd) * (I.Hcd / 8) := by field_simp
      _ ≤ I.kh h * I.groupCap :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
  exact_mod_cast h3

end RoundInput

/-! ## Pairing lists and HUB lists -/

theorem mem_of_mem_pairUp {α : Type*} {l : List α} {p : α × α} (hp : p ∈ pairUp l) :
    p.1 ∈ l ∧ p.2 ∈ l := by
  induction l using pairUp.induct with
  | case1 a b t ih =>
    simp only [pairUp, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hp).1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hp).2)⟩
  | case2 l h =>
    rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp [pairUp] at hp
    · simp [pairUp] at hp
    · exact absurd rfl (h a b t)

theorem mem_of_leftover {α : Type*} {l : List α} {a : α} (h : leftover l = some a) : a ∈ l := by
  induction l using leftover.induct with
  | case1 x y t ih => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))
  | case2 x => simp only [leftover, Option.some.injEq] at h; simp [h]
  | case3 => simp [leftover] at h

theorem lt_of_mem_listOf {K : ℕ} {η : Equiv.Perm (Fin K)} {i c : ℕ} (hc : c ∈ listOf η i) :
    c < K := by
  simp only [listOf, Finset.mem_image] at hc
  obtain ⟨a, -, rfl⟩ := hc
  exact a.2

/-- "The lists of the groups of `h` are pairwise disjoint". -/
theorem disjoint_listOf {K : ℕ} (η : Equiv.Perm (Fin K)) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (listOf η i) (listOf η j) := by
  rw [Finset.disjoint_left]
  intro c hi hj
  simp only [listOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hi
  obtain ⟨_, ⟨b, hb, rfl⟩, hab⟩ := hj
  have : b = a := η.injective (Fin.ext hab)
  subst this
  exact hij (ha.symm.trans hb)

/-- A group `i` with `3i + 3 ≤ K` receives a `3`-element list. -/
theorem card_listOf {K : ℕ} (η : Equiv.Perm (Fin K)) {i : ℕ} (hi : 3 * i + 3 ≤ K) :
    (listOf η i).card = 3 := by
  unfold listOf
  rw [Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ η.injective]
  have : (Finset.univ.filter (fun a : Fin K => a.val / 3 = i)) =
      (Finset.Ico (3 * i) (3 * i + 3)).attachFin (fun _ h => by
        simp only [Finset.mem_Ico] at h; omega) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
      Finset.mem_Ico]
    omega
  rw [this, Finset.card_attachFin]
  simp

/-! ## The quotient -/

namespace Rules

variable {I : RoundInput V} (R : Rules I)

theorem Q_edges (ξ : Xi I.G I.M) : (R.Q ξ).edges = R.qEdges ξ := rfl

theorem Q_verts (ξ : Xi I.G I.M) : (R.Q ξ).verts = (R.qEdges ξ).biUnion Sym2.toFinset := rfl

theorem mem_qEdges {ξ : Xi I.G I.M} {q : Sym2 (QVert V)} :
    q ∈ R.qEdges ξ ↔ ∃ e ∈ R.layerEdges ξ, R.qEdge ξ (R.rank ξ e) e = some q := by
  simp [qEdges]

/-- "`Q_l` … without isolated vertices": every vertex of `Q_l` is an end of an edge. -/
theorem Q_noIsolated (ξ : Xi I.G I.M) : ∀ v ∈ (R.Q ξ).verts, ∃ e ∈ (R.Q ξ).edges, v ∈ e := by
  intro v hv
  obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.1 hv
  exact ⟨e, he, Sym2.mem_toFinset.1 hv⟩

theorem copies_eq (ξ : Xi I.G I.M) : R.copies ξ = (R.Q ξ).verts.card := rfl

/-- The chosen `ξ_l` has positive weight and lies in the event of (f), provided such an outcome
exists (by Markov's inequality it does: a Spec obligation). -/
theorem xiChosen_spec (h : ∃ ξ, 0 < (roundLaw I.G I.M).w ξ ∧ R.MarkovEvent ξ) :
    0 < (roundLaw I.G I.M).w R.xiChosen ∧ R.MarkovEvent R.xiChosen := by
  unfold xiChosen
  rw [dif_pos h]
  exact Classical.choose_spec h

/-! ## Existence of valid fixed rules -/

variable (I) in
/-- The grouping rule of the existence proof: number the live items of `h` in a fixed order and
cut the numbering into blocks of `⌈Hcd/8⌉`. -/
noncomputable def groupStd (it : V × V) : ℕ :=
  ((I.hubItems.filter (fun p => p.1 = it.1)).toList.idxOf it) / I.groupCap

theorem groupStd_lt (hH : 0 < I.Hcd) {it : V × V} (hit : it ∈ I.hubItems) :
    groupStd I it < I.kh it.1 := by
  have hmem : it ∈ (I.hubItems.filter (fun p => p.1 = it.1)).toList := by
    simp [hit]
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [Finset.length_toList] at hlt
  unfold groupStd
  rw [Nat.div_lt_iff_lt_mul (I.groupCap_pos hH)]
  exact lt_of_lt_of_le hlt (I.clive_le_kh_mul_groupCap hH it.1)

theorem card_groupStd_le (hH : 0 < I.Hcd) (h : V) (i : ℕ) :
    (I.hubItems.filter (fun it => it.1 = h ∧ groupStd I it = i)).card ≤ I.groupCap := by
  set L := (I.hubItems.filter (fun p => p.1 = h)).toList
  have hgc := I.groupCap_pos hH
  calc (I.hubItems.filter (fun it => it.1 = h ∧ groupStd I it = i)).card
      ≤ (Finset.Ico (i * I.groupCap) (i * I.groupCap + I.groupCap)).card := by
        refine Finset.card_le_card_of_injOn (fun it => L.idxOf it) ?_ ?_
        · intro it hit
          rw [Finset.mem_coe, Finset.mem_filter] at hit
          obtain ⟨-, h1, h2⟩ := hit
          simp only [Finset.coe_Ico, Set.mem_Ico]
          have h2' : L.idxOf it / I.groupCap = i := by
            rw [← h2]; unfold groupStd; rw [h1]
          rw [← h2']
          exact ⟨Nat.div_mul_le_self _ _, by
            have := Nat.lt_div_mul_add (a := L.idxOf it) hgc
            linarith⟩
        · intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_filter] at ha hb
          have haL : a ∈ L := by simp [L, ha.1, ha.2.1]
          exact (List.idxOf_inj haL).1 hab
    _ = I.groupCap := by simp

variable (I) in
/-- The SDR rule of the existence proof: some SDR at the port, if one exists. -/
noncomputable def sdrFun (R : Rules I) (L : Lists I.G I.M) (u : V) : V × V → ℕ :=
  open Classical in
  if h : R.SDRExists L u then Classical.choose h else fun _ => 0

variable (I) in
/-- Stage 0 of the rules of the existence proof. -/
noncomputable def std0 : Rules I where
  pairing x := (I.frPorts x).toList
  parOrder := []
  group := groupStd I
  sdr _ _ := 0
  e1Order _ := []
  vertOrder _ := I.G.verts.toList
  e2Order _ _ := []
  rankOrder _ := []
  dec _ := []

variable (I) in
/-- The rules of the existence proof (lexicographically first choices in `Finset.toList` order,
with a choice of SDR and of an optimal decomposition). -/
noncomputable def std : Rules I :=
  let R1 : Rules I := { std0 I with parOrder := (std0 I).parObjs.toList }
  let R2 : Rules I := { R1 with sdr := fun L it => sdrFun I (std0 I) L it.2 it }
  let R3 : Rules I := { R2 with
    e1Order := fun L => (R2.e1Items L).toList
    e2Order := fun L u => (R2.E' L u).toList }
  let R4 : Rules I := { R3 with rankOrder := fun ξ => (R3.layerEdges ξ).toList }
  { R4 with dec := fun ξ => Classical.choose (FGraph.exists_isDecomp_edges (R4.Q ξ)) }

variable (I) in
/-- [s7:consRound] *Fixed rules*: "Rules with these arguments exist" (whenever `Hcd_l > 0`; in
particular for every valid round input, `RoundInput.Valid.Hcd_ge`). -/
theorem std_valid (hH : 0 < I.Hcd) : (std I).Valid where
  pairing x _ := ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩
  parOrder := ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩
  group h _ := ⟨fun it hit hh => hh ▸ groupStd_lt hH hit, card_groupStd_le hH h⟩
  sdr L u hL := by
    have hL' : (std0 I).SDRExists L u := hL
    have key : ∀ it ∈ I.hubItemsAt u, (std I).sdr L it = Classical.choose hL' it := by
      intro it hit
      have hu : it.2 = u := ((I.mem_hubItemsAt).1 hit).2
      change sdrFun I (std0 I) L it.2 it = _
      rw [hu]
      unfold sdrFun
      rw [dif_pos hL']
    refine ⟨fun it hit => ?_, fun a ha b hb hab => ?_⟩
    · rw [key it hit]
      exact (Classical.choose_spec hL').1 it hit
    · rw [key a ha, key b hb] at hab
      exact (Classical.choose_spec hL').2 ha hb hab
  e1Order _ := ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩
  vertOrder _ := ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩
  e2Order _ _ := ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩
  rankOrder _ := ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩
  dec ξ := Classical.choose_spec (FGraph.exists_isDecomp_edges _)

/-- [s7:consRound] *Fixed rules*: valid fixed rules exist for every valid round input. -/
theorem exists_valid (hI : I.Valid) : ∃ R : Rules I, R.Valid := by
  refine ⟨std I, std_valid I ?_⟩
  have hM : (0 : ℝ) < I.M := by exact_mod_cast lt_of_lt_of_le (by norm_num) hI.M_ge
  exact lt_of_lt_of_le (by positivity) hI.Hcd_ge

end Rules

/-! ## The chosen fixed rules (JV-SAME-Q) -/

namespace RoundInput

variable {I : RoundInput V}

/-- The chosen rules of a valid round input are valid. -/
theorem chosenRules_valid (hI : I.Valid) : I.chosenRules.Valid := by
  have h := Rules.exists_valid hI
  unfold chosenRules
  rw [dif_pos h]
  exact Classical.choose_spec h

end RoundInput

section consumer

variable (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V)
  (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (J : Finset (Sym2 V))

theorem roundOut_eq : roundOut run G δ S π l J =
    ((RoundInput.ofPast run G δ S π l J).chosenRules.objs
        (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen,
      (RoundInput.ofPast run G δ S π l J).chosenRules.lentJV
        (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen) := rfl

theorem roundQuotient_eq : roundQuotient run G δ S π l J =
    (RoundInput.ofPast run G δ S π l J).chosenRules.Q
      (RoundInput.ofPast run G δ S π l J).chosenRules.xiChosen := rfl

/-- The output and the quotient of a round come from the same rules and the same `ξ_l`. -/
theorem roundOut_roundQuotient :
    ∃ R : Rules (RoundInput.ofPast run G δ S π l J),
      (RoundInput.ofPast run G δ S π l J).Valid → R.Valid ∧
      roundOut run G δ S π l J = (R.objs R.xiChosen, R.lentJV R.xiChosen) ∧
      roundQuotient run G δ S π l J = R.Q R.xiChosen :=
  ⟨_, fun hI => ⟨RoundInput.chosenRules_valid hI, rfl, rfl⟩⟩

end consumer

/-! ## The rank (fix round 2, r2-1)

`Rules.rank` tests the prefix of the rank order with `decide (e' ≠ e)` (the decidable inequality of
`LayerEdge V`, lawful); ranks start at `1`. -/

namespace Rules

variable {I : RoundInput V} (R : Rules I)

theorem one_le_rank (ξ : Xi I.G I.M) (e : LayerEdge V) : 1 ≤ R.rank ξ e := by
  unfold rank; omega

/-- The rank of the first entry of the rank order is `1`. -/
theorem rank_head (ξ : Xi I.G I.M) (e : LayerEdge V) (l : List (LayerEdge V))
    (h : R.rankOrder ξ = e :: l) : R.rank ξ e = 1 := by
  simp [rank, h]

end Rules

end EG.Quot
