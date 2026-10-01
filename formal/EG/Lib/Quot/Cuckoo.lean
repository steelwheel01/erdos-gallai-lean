module

public import EG.Lib.Quot.Junction
public import EG.Lib.Prob.Uniform
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The Cuckoo SDR bound (manuscript s7:lemWellDef (iii)) — probe P-1, proof round 1

Unit P1, design note `formal/work/p2b/P1.md` §5. The probabilistic half of Lemma
[s7:lemWellDef] (iii); the series bound is the proved `EG.numWellDefSDRUse` (unit NUM).

Manuscript proof: "Fix `u` and let `(h_1,u),…,(h_m,u)` be its live hub items … the hubs are
distinct. … The list of `(h_i,u)` is a function of `η_{h_i}` if `h_i` is non-ultra, and equals
`ζ_{h_i,u}` if `h_i` is ultra. Since the `h_i` are distinct, the `m` lists are independent. Each
list is a uniformly random `3`-subset of `[K]` […]. By Hall's theorem […], an SDR fails to exist
only if some set of `s` items has at most `s−1` colours in the union of their lists. Since every
list has `3` elements, this forces `s ≥ 4`. The union is then contained in some `(s−1)`-subset of
`[K]`. The union bound over `s`, over the `s`-sets of items and over the `(s−1)`-subsets of `[K]`
gives `P(SDR failure at u | Past_l) ≤ ∑_{s=4}^m T_s`."

* `exists_bad_of_not_sdr`: the Hall step (pure combinatorics);
* `prob_listOf_subset`, `prob_subset3_subset`: a single list lies in a fixed `t`-set with
  probability `C(t,3)/C(K,3)`;
* `Rules.prob_lists_subset`: independence over the (distinct) hubs of the items at `u`;
* `Rules.prob_not_sdr_le`: the union bound, `≤ ∑_{s=4}^m C(m,s) C(K,s−1) (C(s−1,3)/C(K,3))^s`.
-/

public section

namespace EG.Quot

open Finset EG.FinDist

/-! ## Hall's theorem, in the form used -/

/-- [s7:lemWellDef] (iii) "By Hall's theorem …, an SDR fails to exist only if some set of `s`
items has at most `s−1` colours in the union of their lists. Since every list has `3` elements,
this forces `s ≥ 4`. The union is then contained in some `(s−1)`-subset of `[K]`." -/
theorem exists_bad_of_not_sdr {ι : Type*} [DecidableEq ι] (H : Finset ι) (t : ι → Finset ℕ)
    (K : ℕ) (ht3 : ∀ i ∈ H, (t i).card = 3) (htK : ∀ i ∈ H, t i ⊆ range K) (hHK : H.card ≤ K)
    (hno : ¬ ∃ f : ι → ℕ, (∀ i ∈ H, f i ∈ t i) ∧ Set.InjOn f (H : Set ι)) :
    ∃ S ∈ H.powerset.filter (fun S => 4 ≤ S.card),
      ∃ T ∈ (range K).powersetCard (S.card - 1), ∀ i ∈ S, t i ⊆ T := by
  by_contra hc
  apply hno
  have hall : ∀ s : Finset {x // x ∈ H}, s.card ≤ (s.biUnion (fun x => t x.1)).card := by
    intro s
    by_contra hlt
    push Not at hlt
    set S := s.map (Function.Embedding.subtype _) with hS
    have hSH : S ⊆ H := by
      intro i hi
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hi
      exact x.2
    have hScard : S.card = s.card := Finset.card_map _
    have hU : S.biUnion t = s.biUnion (fun x => t x.1) := by
      ext a
      simp only [hS, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨i, ⟨x, hx, rfl⟩, ha⟩; exact ⟨x, hx, ha⟩
      · rintro ⟨x, hx, ha⟩; exact ⟨x.1, ⟨x, hx, rfl⟩, ha⟩
    rw [← hU, ← hScard] at hlt
    have h4 : 4 ≤ S.card := by
      by_contra h4
      obtain ⟨i, hi⟩ : S.Nonempty := by
        rw [← Finset.card_pos]; omega
      have := Finset.card_le_card (Finset.subset_biUnion_of_mem t hi)
      rw [ht3 i (hSH hi)] at this
      omega
    have hUK : S.biUnion t ⊆ range K := by
      intro a ha
      obtain ⟨i, hi, ha⟩ := Finset.mem_biUnion.1 ha
      exact htK i (hSH hi) ha
    have hSK : S.card ≤ K := (Finset.card_le_card hSH).trans hHK
    obtain ⟨T, hUT, hTK, hTc⟩ := Finset.exists_subsuperset_card_eq hUK (n := S.card - 1)
      (by omega) (by rw [Finset.card_range]; omega)
    apply hc
    refine ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSH, h4⟩, T,
      Finset.mem_powersetCard.2 ⟨hTK, hTc⟩, fun i hi => ?_⟩
    exact (Finset.subset_biUnion_of_mem t hi).trans hUT
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).1 hall
  classical
  refine ⟨fun i => if h : i ∈ H then f ⟨i, h⟩ else 0, fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · simp only [dif_pos hi]; exact hft ⟨i, hi⟩
  · simp only [Finset.mem_coe] at hi hj
    simp only [dif_pos hi, dif_pos hj] at hij
    exact congrArg Subtype.val (hf hij)

/-! ## A single list -/

section single

variable {K : ℕ}

/-- The elements of `Fin K` whose value lies in `T`. -/
@[expose] def finOf (K : ℕ) (T : Finset ℕ) : Finset (Fin K) := univ.filter (fun a => a.val ∈ T)

theorem card_finOf {T : Finset ℕ} (hT : T ⊆ range K) : (finOf K T).card = T.card := by
  have h : (finOf K T).image Fin.val = T := by
    ext n
    simp only [finOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hn
      exact ⟨⟨n, Finset.mem_range.1 (hT hn)⟩, hn, rfl⟩
  conv_rhs => rw [← h]
  rw [Finset.card_image_of_injective _ Fin.val_injective]

theorem image_val_subset_iff {s : Finset (Fin K)} {T : Finset ℕ} :
    s.image Fin.val ⊆ T ↔ s ⊆ finOf K T := by
  simp [finOf, Finset.subset_iff]

/-- The `i`-th list of a uniform permutation lies in a fixed `t`-set with probability
`C(t,3)/C(K,3)` (for `3i + 3 ≤ K`). -/
theorem prob_listOf_subset {i : ℕ} (hi : 3 * i + 3 ≤ K) {T : Finset ℕ} (hT : T ⊆ range K) :
    (uniform (Equiv.Perm (Fin K))).prob {η | listOf η i ⊆ T} =
      (T.card.choose 3 : ℝ) / (K.choose 3 : ℝ) := by
  set A : Finset (Fin K) := univ.filter (fun a : Fin K => a.val / 3 = i) with hA
  have hA3 : A.card = 3 := by
    have := card_listOf (1 : Equiv.Perm (Fin K)) hi
    unfold listOf at this
    rwa [Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (Equiv.injective _)] at this
  have hset : {η : Equiv.Perm (Fin K) | listOf η i ⊆ T} =
      {η : Equiv.Perm (Fin K) | A.image ⇑η ⊆ finOf K T} := by
    ext η
    simp only [Set.mem_setOf_eq, listOf, ← hA]
    exact image_val_subset_iff
  rw [hset, prob_image_perm_subset A (finOf K T), hA3, card_finOf hT, Fintype.card_fin]

/-- A uniform `3`-subset lies in a fixed `t`-set with probability `C(t,3)/C(K,3)`. -/
theorem prob_subset3_subset (hK : 3 ≤ K) {T : Finset ℕ} (hT : T ⊆ range K) :
    (subset3Law K).prob {ζ | ζ.image Fin.val ⊆ T} = (T.card.choose 3 : ℝ) / (K.choose 3 : ℝ) := by
  have := nonempty_subset3 hK
  have hset : {ζ : Finset (Fin K) | ζ.image Fin.val ⊆ T} = {ζ | ζ ⊆ finOf K T} := by
    ext ζ
    exact image_val_subset_iff
  unfold subset3Law
  rw [dif_pos hK, hset, prob_uniformCard_subset 3 (finOf K T), card_finOf hT, Fintype.card_fin]

/-- On the support of `subset3Law K` (`K ≥ 3`) the sets have `3` elements. -/
theorem card_of_subset3Law_w (hK : 3 ≤ K) {ζ : Finset (Fin K)} (h : (subset3Law K).w ζ ≠ 0) :
    ζ.card = 3 := by
  have := nonempty_subset3 hK
  unfold subset3Law at h
  rw [dif_pos hK, map_w] at h
  by_contra hc
  apply h
  rw [prob_eq_zero_iff]
  intro x hx
  exact absurd (show x.1 = ζ from hx ▸ rfl) (fun e => hc (e ▸ x.2))

end single

variable {V : Type*} [DecidableEq V]

/-- On the support of the law of the lists, every `ζ_{h,u}` has `3` elements. -/
theorem card_zeta_of_w {G : FGraph V} {M : ℕ} (hK : 3 ≤ 4 * M) {L : Lists G M}
    (hL : 0 < (listsLaw G M).w L) (p : ↥G.verts × ↥G.verts) : (L.2 p).card = 3 := by
  unfold listsLaw at hL
  rw [prod_w'] at hL
  have h2 : (pi fun _ : ↥G.verts × ↥G.verts => subset3Law (4 * M)).w L.2 ≠ 0 := by
    intro h; rw [h, mul_zero] at hL; exact lt_irrefl _ hL
  have := (mem_supp_pi (μ := fun _ : ↥G.verts × ↥G.verts => subset3Law (4 * M))).1
    (mem_supp.2 h2) p
  exact card_of_subset3Law_w hK (mem_supp.1 this)

/-! ## The lists at a port -/

namespace Rules

variable {I : RoundInput V} {R : Rules I}

/-- The hubs and the port of a hub item are vertices of `G`. -/
theorem hubItems_verts (hI : I.Valid) {it : V × V} (hit : it ∈ I.hubItems) :
    it.1 ∈ I.G.verts ∧ it.2 ∈ I.G.verts := by
  have he := RoundInput.J_mem_edges hI (RoundInput.Jhub_sub_J (RoundInput.hubItems_Jhub hit))
  exact ⟨I.G.edge_verts _ he _ (Sym2.mem_mk_left _ _),
    I.G.edge_verts _ he _ (Sym2.mem_mk_right _ _)⟩

theorem hubList_ultra {L : Lists I.G I.M} {it : V × V} (hu : I.ultra it.1)
    (h1 : it.1 ∈ I.G.verts) (h2 : it.2 ∈ I.G.verts) :
    R.hubList L it = (L.2 (⟨it.1, h1⟩, ⟨it.2, h2⟩)).image Fin.val := by
  classical
  unfold hubList zetaAt
  rw [if_pos hu, dif_pos h1, dif_pos h2]

theorem hubList_nonultra {L : Lists I.G I.M} {it : V × V} (hu : ¬ I.ultra it.1)
    (h1 : it.1 ∈ I.G.verts) : R.hubList L it = listOf (L.1 ⟨it.1, h1⟩) (R.group it) := by
  classical
  unfold hubList etaAt
  rw [if_neg hu, dif_pos h1]

/-- On the support of the law of the lists, every list of a live hub item has `3` elements
(for non-ultra hubs this uses `3k_h ≤ 4M_l`, [s7:lemWellDef] (ii)). -/
theorem card_hubList (hI : I.Valid) (hR : R.Valid)
    (hk : ∀ h ∈ I.hubs, ¬ I.ultra h → 3 * I.kh h ≤ 4 * I.M) {L : Lists I.G I.M}
    (hL : 0 < (listsLaw I.G I.M).w L) {it : V × V} (hit : it ∈ I.hubItems) :
    (R.hubList L it).card = 3 := by
  obtain ⟨h1, h2⟩ := hubItems_verts hI hit
  have hK : 3 ≤ 4 * I.M := by have := hI.M_ge; omega
  by_cases hu : I.ultra it.1
  · rw [hubList_ultra hu h1 h2, Finset.card_image_of_injective _ Fin.val_injective]
    exact card_zeta_of_w hK hL _
  · rw [hubList_nonultra hu h1]
    have hg := (hR.group it.1 hu).1 it hit rfl
    have := hk it.1 (RoundInput.hubItems_hub hit) hu
    exact card_listOf _ (by omega)

/-- [s7:lemWellDef] (iii) "Since the `h_i` are distinct, the `m` lists are independent. Each list
is a uniformly random `3`-subset of `[K]`": for a set `S` of live hub items at `u` and a `t`-set
`T ⊆ [K]`, all lists of `S` lie in `T` with probability `(C(t,3)/C(K,3))^{|S|}`. -/
theorem prob_lists_subset (hI : I.Valid) (hR : R.Valid)
    (hk : ∀ h ∈ I.hubs, ¬ I.ultra h → 3 * I.kh h ≤ 4 * I.M) {u : V} (hu : u ∈ I.ports)
    {S : Finset (V × V)} (hS : S ⊆ I.hubItemsAt u) {T : Finset ℕ} (hT : T ⊆ range (4 * I.M)) :
    (listsLaw I.G I.M).prob {L | ∀ it ∈ S, R.hubList L it ⊆ T} =
      ((T.card.choose 3 : ℝ) / ((4 * I.M).choose 3 : ℝ)) ^ S.card := by
  classical
  set p : ℝ := (T.card.choose 3 : ℝ) / ((4 * I.M).choose 3 : ℝ) with hp
  have huG : u ∈ I.G.verts := hI.ports_sub hu
  set u' : ↥I.G.verts := ⟨u, huG⟩ with hu'
  have hSH : ∀ it ∈ S, it ∈ I.hubItems ∧ it.2 = u := fun it hit => (I.mem_hubItemsAt).1 (hS hit)
  have hSG : ∀ it ∈ S, it.1 ∈ I.G.verts := fun it hit => (hubItems_verts hI (hSH it hit).1).1
  set Sn := S.filter (fun it => ¬ I.ultra it.1) with hSn
  set Su := S.filter (fun it => I.ultra it.1) with hSu
  set Hn : Finset ↥I.G.verts := (Sn.image Prod.fst).subtype (· ∈ I.G.verts) with hHn
  set Hu0 : Finset ↥I.G.verts := (Su.image Prod.fst).subtype (· ∈ I.G.verts) with hHu0
  set Hu : Finset (↥I.G.verts × ↥I.G.verts) := Hu0.image (fun i => (i, u')) with hHu
  -- an item of `S` is determined by its hub
  have hitem : ∀ it ∈ S, it = (it.1, u) := fun it hit => Prod.ext rfl (hSH it hit).2
  have hK3 : 3 ≤ 4 * I.M := by have := hI.M_ge; omega
  -- the event is a product event
  have hset : {L : Lists I.G I.M | ∀ it ∈ S, R.hubList L it ⊆ T} =
      {F | ∀ i ∈ Hn, F i ∈ {η : Equiv.Perm (Fin (4 * I.M)) | listOf η (R.group (i.1, u)) ⊆ T}} ×ˢ
      {Z | ∀ j ∈ Hu, Z j ∈ {ζ : Finset (Fin (4 * I.M)) | ζ.image Fin.val ⊆ T}} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · rw [Finset.mem_subtype, Finset.mem_image] at hi
        obtain ⟨it, hit, hi1⟩ := hi
        have hit' := (Finset.mem_filter.1 hit)
        have h' := h it hit'.1
        rw [hubList_nonultra hit'.2 (hSG it hit'.1)] at h'
        have e1 : (⟨it.1, hSG it hit'.1⟩ : ↥I.G.verts) = i := Subtype.ext hi1
        have e2 : R.group it = R.group (i.1, u) := by
          rw [← hi1]; exact congrArg R.group (hitem it hit'.1)
        rw [e1, e2] at h'
        exact h'
      · rw [Finset.mem_image] at hj
        obtain ⟨i, hi, rfl⟩ := hj
        rw [Finset.mem_subtype, Finset.mem_image] at hi
        obtain ⟨it, hit, hi1⟩ := hi
        have hit' := (Finset.mem_filter.1 hit)
        have h' := h it hit'.1
        have h2 : it.2 ∈ I.G.verts := (hSH it hit'.1).2 ▸ huG
        rw [hubList_ultra hit'.2 (hSG it hit'.1) h2] at h'
        have e1 : (⟨it.1, hSG it hit'.1⟩ : ↥I.G.verts) = i := Subtype.ext hi1
        have e2 : (⟨it.2, h2⟩ : ↥I.G.verts) = u' := Subtype.ext (hSH it hit'.1).2
        rw [e1, e2] at h'
        exact h'
    · rintro ⟨h1, h2⟩ it hit
      by_cases hult : I.ultra it.1
      · have h2G : it.2 ∈ I.G.verts := (hSH it hit).2 ▸ huG
        rw [hubList_ultra hult (hSG it hit) h2G]
        have hj : ((⟨it.1, hSG it hit⟩ : ↥I.G.verts), u') ∈ Hu := by
          rw [Finset.mem_image]
          refine ⟨⟨it.1, hSG it hit⟩, ?_, rfl⟩
          rw [Finset.mem_subtype, Finset.mem_image]
          exact ⟨it, Finset.mem_filter.2 ⟨hit, hult⟩, rfl⟩
        have e2 : (⟨it.2, h2G⟩ : ↥I.G.verts) = u' := Subtype.ext (hSH it hit).2
        rw [e2]
        exact h2 _ hj
      · rw [hubList_nonultra hult (hSG it hit)]
        have hi : (⟨it.1, hSG it hit⟩ : ↥I.G.verts) ∈ Hn := by
          rw [Finset.mem_subtype, Finset.mem_image]
          exact ⟨it, Finset.mem_filter.2 ⟨hit, hult⟩, rfl⟩
        have := h1 _ hi
        have e : R.group (it.1, u) = R.group it := congrArg R.group (hitem it hit).symm
        rw [e] at this
        exact this
  -- cardinalities
  have hfst : ∀ X ⊆ S, (X.image Prod.fst).card = X.card := by
    intro X hX
    refine Finset.card_image_of_injOn (fun a ha b hb hab => ?_)
    exact Prod.ext hab ((hSH a (hX ha)).2.trans (hSH b (hX hb)).2.symm)
  have hsub : ∀ X ⊆ S, ((X.image Prod.fst).subtype (· ∈ I.G.verts)).card = X.card := by
    intro X hX
    rw [Finset.card_subtype, Finset.filter_true_of_mem, hfst X hX]
    intro a ha
    obtain ⟨it, hit, rfl⟩ := Finset.mem_image.1 ha
    exact hSG it (hX hit)
  have hcn : Hn.card = Sn.card := hsub Sn (Finset.filter_subset _ _)
  have hcu : Hu.card = Su.card := by
    rw [hHu, Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1)]
    exact hsub Su (Finset.filter_subset _ _)
  have hcs : Sn.card + Su.card = S.card := by
    rw [hSn, hSu, add_comm]
    exact Finset.card_filter_add_card_filter_not (fun it : V × V => I.ultra it.1)
  -- the probability
  unfold listsLaw
  rw [hset, prob_prod_set_prod, prob_pi_forall_mem, prob_pi_forall_mem]
  have e1 : ∏ i ∈ Hn, (uniform (Equiv.Perm (Fin (4 * I.M)))).prob
      {η | listOf η (R.group (i.1, u)) ⊆ T} = p ^ Hn.card := by
    rw [Finset.prod_eq_pow_card]
    intro i hi
    rw [Finset.mem_subtype, Finset.mem_image] at hi
    obtain ⟨it, hit, hi1⟩ := hi
    have hit' := Finset.mem_filter.1 hit
    have hH := (hSH it hit'.1).1
    have hg := (hR.group it.1 hit'.2).1 it hH rfl
    have := hk it.1 (RoundInput.hubItems_hub hH) hit'.2
    have heq : (i.1, u) = it := by rw [hitem it hit'.1, hi1]
    rw [heq]
    exact prob_listOf_subset (by omega) hT
  have e2 : ∏ j ∈ Hu, (subset3Law (4 * I.M)).prob {ζ | ζ.image Fin.val ⊆ T} = p ^ Hu.card := by
    rw [Finset.prod_eq_pow_card]
    intro j _
    exact prob_subset3_subset hK3 hT
  rw [e1, e2, ← pow_add, hcn, hcu, hcs]

/-- [s7:lemWellDef] (iii) "The union bound over `s`, over the `s`-sets of items and over the
`(s−1)`-subsets of `[K]` gives `P(SDR failure at u | Past_l) ≤ ∑_{s=4}^m T_s`,
`T_s := C(m,s) C(K,s−1) (C(s−1,3)/C(K,3))^s`" (with the lists law; `m = |hub items at u|`). -/
theorem prob_not_sdr_le (hI : I.Valid) (hR : R.Valid)
    (hk : ∀ h ∈ I.hubs, ¬ I.ultra h → 3 * I.kh h ≤ 4 * I.M) {u : V} (hu : u ∈ I.ports) :
    (listsLaw I.G I.M).prob {L | ¬ R.SDRExists L u} ≤
      ∑ s ∈ Icc 4 (I.hubItemsAt u).card, ((I.hubItemsAt u).card.choose s : ℝ) *
        ((4 * I.M).choose (s - 1) : ℝ) *
          (((s - 1).choose 3 : ℝ) / ((4 * I.M).choose 3 : ℝ)) ^ s := by
  classical
  set H := I.hubItemsAt u with hH
  set K := 4 * I.M with hK
  set m := H.card with hm
  set P4 := H.powerset.filter (fun S => 4 ≤ S.card) with hP4
  have hmK : m ≤ K := by
    have := RoundInput.card_hubItemsAt_le_M hI hu
    rw [← hH] at this
    omega
  have step1 : (listsLaw I.G I.M).prob {L | ¬ R.SDRExists L u} ≤
      (listsLaw I.G I.M).prob (⋃ S ∈ P4, ⋃ T ∈ (range K).powersetCard (S.card - 1),
        {L : Lists I.G I.M | ∀ it ∈ S, R.hubList L it ⊆ T}) := by
    apply prob_mono_ae
    intro L hL hns
    obtain ⟨S, hS, T, hT, hST⟩ := exists_bad_of_not_sdr H (R.hubList L) K
      (fun it hit => card_hubList hI hR hk hL ((I.mem_hubItemsAt).1 hit).1)
      (fun it _ c hc => Finset.mem_range.2 (hubList_lt L it hc)) hmK hns
    simp only [Set.mem_iUnion]
    exact ⟨S, hS, T, hT, hST⟩
  have step2 : ∀ S ∈ P4, (listsLaw I.G I.M).prob (⋃ T ∈ (range K).powersetCard (S.card - 1),
      {L : Lists I.G I.M | ∀ it ∈ S, R.hubList L it ⊆ T}) ≤
        (K.choose (S.card - 1) : ℝ) * (((S.card - 1).choose 3 : ℝ) / (K.choose 3 : ℝ)) ^ S.card := by
    intro S hS
    refine (prob_biUnion_le _ _ _).trans (le_of_eq ?_)
    have hSH : S ⊆ H := Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1
    rw [Finset.sum_congr rfl (fun T hT => prob_lists_subset hI hR hk hu hSH
      (Finset.mem_powersetCard.1 hT).1)]
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range, nsmul_eq_mul]
  refine step1.trans ((prob_biUnion_le _ _ _).trans ((Finset.sum_le_sum step2).trans (le_of_eq ?_)))
  rw [hP4, Finset.sum_filter]
  have hpow := Finset.sum_powerset_apply_card (x := H) (fun s => if 4 ≤ s then
    (K.choose (s - 1) : ℝ) * (((s - 1).choose 3 : ℝ) / (K.choose 3 : ℝ)) ^ s else 0)
  refine hpow.trans ?_
  rw [Finset.sum_congr rfl (fun s _ => by rw [nsmul_eq_mul, mul_ite, mul_zero]),
    ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  · intro s _
    ring

end Rules

end EG.Quot
