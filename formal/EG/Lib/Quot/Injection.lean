module

public import EG.Lib.Quot.E2
public import EG.Lib.Quot.Schedule
public import EG.Lib.Prob.RankOrder
public import EG.Lib.Prob.Indep

/-!
# The random injections of step (e2) (manuscript s7:consRound (e2))

"With `Past_l` and the lists fixed, the map `e_i ↦ w_i` is a uniformly random injection of `E'(u)`
into `Cand_l(u) \ Used(u)`, and these injections are independent over ports."

* `sortByRank_eq_map`: the order `≺_u` restricted to `C` is `EG.FinDist.rankList` of the rank
  function;
* `Rules.e2Junc_eq`: the junction of an end `e ∈ E'(u)` is the element of `C(u)` at the position of
  `e` in the order `e_1, …, e_q`;
* `Rules.e2_event_iff`: all ends of `E'(u)` receive the junctions `f(e)` iff the first `q` elements
  of `C(u)` in the order `≺_u` are `f(e_1), …, f(e_q)`;
* `Rules.prob_e2_eq`: this has probability `1/(|C(u)|)_q`;
* `Rules.iIndepFun_e2`: the junction maps of distinct ports are independent;
* `Rules.prob_e2Junc_eq`: a single junction is uniform on `C(u)` (for [s7:lemUltra] (i)).
-/

public section

namespace EG.Quot

open EG.FinDist

variable {V : Type*} [DecidableEq V]

/-- The order `≺` restricted to `C` is the rank list of `C ∩ V(G)`. -/
theorem sortByRank_eq_map {G : FGraph V} (o : ↥G.verts ≃ Fin G.card) (C : Finset V) :
    sortByRank o C = (rankList o (C.subtype (· ∈ G.verts))).map Subtype.val := by
  unfold sortByRank
  rw [rankList_def, List.map_filterMap]
  refine List.filterMap_congr fun i _ => ?_
  by_cases h : ((o.symm i : ↥G.verts) : V) ∈ C
  · have h' : o.symm i ∈ C.subtype (· ∈ G.verts) := Finset.mem_subtype.2 h
    simp [h, h']
  · have h' : o.symm i ∉ C.subtype (· ∈ G.verts) := fun h'' => h (Finset.mem_subtype.1 h'')
    simp [h, h']

theorem card_subtype_of_subset {G : FGraph V} {C : Finset V} (hC : C ⊆ G.verts) :
    (C.subtype (· ∈ G.verts)).card = C.card := by
  rw [Finset.card_subtype]
  congr 1
  exact Finset.filter_true_of_mem fun x hx => hC hx

variable {I : RoundInput V} {R : Rules I}

namespace Rules

/-- The junction of an end `e ∈ E'(u)` is the element of `C(u) = Cand_l(u) \ Used(u)` at the
position of `e` in the order `e_1, …, e_q` of `E'(u)`. -/
theorem e2Junc_eq (hR : R.Valid) (L : Lists I.G I.M) (O : Orders I.G) {u : V} {e : REnd V}
    (he : e ∈ R.E' L u) :
    R.e2Junc (L, O) e =
      (inOrder O u (I.cand u \ R.used L u))[(R.e2Order L u).idxOf e]? := by
  have hport := port_of_mem_E' he
  have hmem : e ∈ R.e2Order L u := by
    rw [← List.mem_toFinset, (hR.e2Order L u).2]; exact he
  unfold e2Junc
  simp only
  rw [hport]
  have hidx : (R.e2Order L u).idxOf? e = some ((R.e2Order L u).idxOf e) := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨List.idxOf_lt_length_of_mem hmem, List.getElem_idxOf _, fun j hj hje => ?_⟩
    have hj' : j < (R.e2Order L u).length := by
      have := List.idxOf_lt_length_of_mem hmem; omega
    have := (hR.e2Order L u).1.idxOf_getElem j hj'
    rw [hje] at this
    omega
  rw [hidx]

/-- "`e_i` receives the junction `w_i`" for all `i`: the event that every end `e ∈ E'(u)` receives
`f(e)` is the event that the first `q` elements of `C(u)` in the order `≺_u` are
`f(e_1), …, f(e_q)`. -/
theorem e2_event_iff (hR : R.Valid) (L : Lists I.G I.M) (O : Orders I.G) (u : V)
    (f : REnd V → V) :
    (∀ e ∈ R.E' L u, R.e2Junc (L, O) e = some (f e)) ↔
      (inOrder O u (I.cand u \ R.used L u)).take (R.e2Order L u).length =
        (R.e2Order L u).map f := by
  set σ := R.e2Order L u with hσ
  set Lst := inOrder O u (I.cand u \ R.used L u) with hLst
  have hnd := (hR.e2Order L u).1
  have hto := (hR.e2Order L u).2
  have hmemσ : ∀ e, e ∈ σ ↔ e ∈ R.E' L u := fun e => by rw [← List.mem_toFinset, hto]
  constructor
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take]
    by_cases hi : i < σ.length
    · rw [if_pos hi, List.getElem?_map, List.getElem?_eq_getElem hi]
      have he : σ[i] ∈ R.E' L u := (hmemσ _).1 (List.getElem_mem hi)
      have h1 := h _ he
      rw [e2Junc_eq hR L O he, ← hσ, hnd.idxOf_getElem i hi] at h1
      rw [h1]
      rfl
    · rw [if_neg hi, List.getElem?_eq_none (by simp; omega)]
  · intro h e he
    have hmem := (hmemσ e).2 he
    have hk := List.idxOf_lt_length_of_mem hmem
    rw [e2Junc_eq hR L O he, ← hσ]
    have h1 := congrArg (fun l => l[σ.idxOf e]?) h
    rw [List.getElem?_take, if_pos hk, List.getElem?_map, List.getElem?_eq_getElem hk,
      List.getElem_idxOf] at h1
    exact h1

variable (hI : I.Valid) (hR : R.Valid)
include hI

/-- `C(u) = Cand_l(u) \ Used(u) ⊆ V(G)`. -/
theorem sdiff_used_subset_verts (L : Lists I.G I.M) (u : V) :
    I.cand u \ R.used L u ⊆ I.G.verts := fun w hw =>
  hI.pool_sub (mem_cand (Finset.mem_sdiff.1 hw).1).1

/-- The order `≺_u` on `C(u)` as the rank list of the coordinate `O_u`. -/
theorem inOrder_eq_map (O : Orders I.G) {u : V} (hu : u ∈ I.ports) (C : Finset V) :
    inOrder O u C = (rankList (O ⟨u, hI.ports_sub hu⟩) (C.subtype (· ∈ I.G.verts))).map
      Subtype.val := by
  unfold inOrder
  rw [dif_pos (hI.ports_sub hu), sortByRank_eq_map]

include hR

/-- [s7:consRound] (e2) "the map `e_i ↦ w_i` is a uniformly random injection of `E'(u)` into
`Cand_l(u) \ Used(u)`": every injection `f` has probability `1/(|C(u)|)_{|E'(u)|}`. -/
theorem prob_e2_eq (L : Lists I.G I.M) {u : V} (hu : u ∈ I.ports) (f : REnd V → V)
    (hmaps : Set.MapsTo f (R.E' L u : Set (REnd V)) (I.cand u \ R.used L u : Set V))
    (hinj : Set.InjOn f (R.E' L u : Set (REnd V))) :
    (ordersLaw I.G).prob {O | ∀ e ∈ R.E' L u, R.e2Junc (L, O) e = some (f e)} =
      (((I.cand u \ R.used L u).card.descFactorial (R.E' L u).card : ℕ) : ℝ)⁻¹ := by
  classical
  have huv := hI.ports_sub hu
  set C := I.cand u \ R.used L u with hC
  have hCv : C ⊆ I.G.verts := sdiff_used_subset_verts hI L u
  set σ := R.e2Order L u with hσ
  have hnd := (hR.e2Order L u).1
  have hto := (hR.e2Order L u).2
  have hmemσ : ∀ e, e ∈ σ ↔ e ∈ R.E' L u := fun e => by rw [← List.mem_toFinset, hto]
  have hq : σ.length = (R.E' L u).card := by rw [← hto, List.toFinset_card_of_nodup hnd]
  have hmapsC : ∀ e ∈ R.E' L u, f e ∈ C := fun e he =>
    Finset.mem_sdiff.2 ⟨(hmaps (Finset.mem_coe.2 he)).1, (hmaps (Finset.mem_coe.2 he)).2⟩
  have hv : ∀ x ∈ σ.map f, x ∈ I.G.verts := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact hCv (hmapsC e ((hmemσ e).1 he))
  let cs : List ↥I.G.verts := (σ.map f).attach.map (fun x => ⟨x.1, hv x.1 x.2⟩)
  have hcs : cs.map Subtype.val = σ.map f := by
    simp only [cs, List.map_map]
    exact List.attach_map_subtype_val _
  have hcslen : cs.length = σ.length := by simp [cs]
  have hcsnd : cs.Nodup := by
    have h1 : (σ.map f).Nodup := hnd.map_on fun x hx y hy hxy =>
      hinj ((hmemσ x).1 hx) ((hmemσ y).1 hy) hxy
    exact List.Nodup.of_map Subtype.val (by rw [hcs]; exact h1)
  have hcsC : ∀ c ∈ cs, c ∈ C.subtype (· ∈ I.G.verts) := by
    intro c hc
    rw [Finset.mem_subtype]
    have : (c : V) ∈ σ.map f := by rw [← hcs]; exact List.mem_map_of_mem hc
    obtain ⟨e, he, hfe⟩ := List.mem_map.1 this
    rw [← hfe]
    exact hmapsC e ((hmemσ e).1 he)
  have hset : {O : Orders I.G | ∀ e ∈ R.E' L u, R.e2Junc (L, O) e = some (f e)} =
      {O | O ⟨u, huv⟩ ∈ {o | (rankList o (C.subtype (· ∈ I.G.verts))).take cs.length = cs}} := by
    ext O
    simp only [Set.mem_ofPred_eq]
    rw [e2_event_iff hR L O u f, ← hσ, inOrder_eq_map hI O hu, ← List.map_take, ← hcs, hcslen]
    exact (List.map_injective_iff.2 Subtype.val_injective).eq_iff
  rw [hset]
  unfold ordersLaw
  rw [prob_pi_eval, prob_rankList_take _ cs hcsnd hcsC, card_subtype_of_subset hCv, hcslen, hq,
    one_div]

/-- [s7:consRound] (e2) "these injections are independent over ports": the junction maps of the
ports are functions of distinct coordinates `≺_u` of the orders. -/
theorem iIndepFun_e2 (L : Lists I.G I.M) :
    (ordersLaw I.G).iIndepFun
      (fun (u : ↥I.ports) (O : Orders I.G) =>
        fun e : ↥(R.E' L (u : V)) => R.e2Junc (L, O) (e : REnd V)) := by
  classical
  unfold ordersLaw
  refine iIndepFun_pi_of_dependsOn _ (fun u => {⟨(u : V), hI.ports_sub u.2⟩}) ?_ _ ?_
  · intro u v huv
    rw [Set.disjoint_singleton]
    intro h
    exact huv (Subtype.ext (Subtype.mk.inj h))
  · intro u O O' h
    funext e
    have hO : O ⟨(u : V), hI.ports_sub u.2⟩ = O' ⟨(u : V), hI.ports_sub u.2⟩ :=
      h _ (Set.mem_singleton _)
    rw [e2Junc_eq hR L O e.2, e2Junc_eq hR L O' e.2, inOrder_eq_map hI O u.2,
      inOrder_eq_map hI O' u.2, hO]

/-- [s7:lemUltra] (i), [s7:lemCC] (i): the junction of one end `e ∈ E'(u)` is uniform on `C(u)`
(when `|E'(u)| ≤ |C(u)|`, which Lemma s7:lemWellDef (v) gives at a port carrying a live item). -/
theorem prob_e2Junc_eq (L : Lists I.G I.M) {u : V} (hu : u ∈ I.ports) {e : REnd V}
    (he : e ∈ R.E' L u) (hle : (R.E' L u).card ≤ (I.cand u \ R.used L u).card) {w : V}
    (hw : w ∈ I.cand u \ R.used L u) :
    (ordersLaw I.G).prob {O | R.e2Junc (L, O) e = some w} =
      1 / ((I.cand u \ R.used L u).card : ℝ) := by
  classical
  have huv := hI.ports_sub hu
  set C := I.cand u \ R.used L u with hC
  have hCv : C ⊆ I.G.verts := sdiff_used_subset_verts hI L u
  have hnd := (hR.e2Order L u).1
  have hto := (hR.e2Order L u).2
  have hmem : e ∈ R.e2Order L u := by rw [← List.mem_toFinset, hto]; exact he
  have hq : (R.e2Order L u).length = (R.E' L u).card := by
    rw [← hto, List.toFinset_card_of_nodup hnd]
  have hi : (R.e2Order L u).idxOf e < (C.subtype (· ∈ I.G.verts)).card := by
    rw [card_subtype_of_subset hCv]
    have := List.idxOf_lt_length_of_mem hmem
    omega
  have hset : {O : Orders I.G | R.e2Junc (L, O) e = some w} =
      {O | O ⟨u, huv⟩ ∈ {o | (rankList o (C.subtype (· ∈ I.G.verts)))[(R.e2Order L u).idxOf e]? =
        some ⟨w, hCv hw⟩}} := by
    ext O
    simp only [Set.mem_ofPred_eq]
    rw [e2Junc_eq hR L O he, inOrder_eq_map hI O hu, List.getElem?_map]
    constructor
    · intro h
      obtain ⟨x, hx, hxw⟩ := Option.map_eq_some_iff.1 h
      rw [hx]
      exact congrArg some (Subtype.ext hxw)
    · intro h
      rw [h]
      rfl
  rw [hset]
  unfold ordersLaw
  rw [prob_pi_eval, prob_rankList_getElem? _ hi (Finset.mem_subtype.2 hw),
    card_subtype_of_subset hCv]

omit hR in
/-- The junction of the end `e` at the port `x`, as a function of the order `≺_x` alone. -/
theorem e2Junc_eq_endJunc (hR : R.Valid) (L : Lists I.G I.M) (O : Orders I.G) {x : V}
    (hx : x ∈ I.ports) {e : REnd V} (he : e ∈ R.E' L x) :
    R.e2Junc (L, O) e =
      ((rankList (O ⟨x, hI.ports_sub hx⟩) ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
        Subtype.val)[(R.e2Order L x).idxOf e]? := by
  rw [e2Junc_eq hR L O he, inOrder_eq_map hI O hx]

/-- The single-junction law at the level of one coordinate `≺_x`. -/
theorem prob_endJunc (L : Lists I.G I.M) {x : V} (hx : x ∈ I.ports) {e : REnd V}
    (he : e ∈ R.E' L x) (hle : (R.E' L x).card ≤ (I.cand x \ R.used L x).card) {u : V}
    (hu : u ∈ I.cand x \ R.used L x) :
    (FinDist.uniform (↥I.G.verts ≃ Fin I.G.card)).prob {σ |
      ((rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
        Subtype.val)[(R.e2Order L x).idxOf e]? = some u} =
      1 / ((I.cand x \ R.used L x).card : ℝ) := by
  have h := prob_e2Junc_eq hI hR L hx he hle hu
  have hset : {O : Orders I.G | R.e2Junc (L, O) e = some u} =
      {O | O ⟨x, hI.ports_sub hx⟩ ∈ {σ |
        ((rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
          Subtype.val)[(R.e2Order L x).idxOf e]? = some u}} := by
    ext O
    simp only [Set.mem_ofPred_eq]
    rw [e2Junc_eq_endJunc hI hR L O hx he]
  rw [hset] at h
  unfold ordersLaw at h
  rw [prob_pi_eval] at h
  exact h

omit hR in
/-- The junction of the end `e` at `x` (with its position `< |C(x)|`) is always some element of
`C(x)`. -/
theorem endJunc_isSome (L : Lists I.G I.M) (x : V) (hCv : I.cand x \ R.used L x ⊆ I.G.verts)
    (σ : ↥I.G.verts ≃ Fin I.G.card) {i : ℕ} (hi : i < (I.cand x \ R.used L x).card) :
    ∃ u ∈ I.cand x \ R.used L x,
      ((rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
        Subtype.val)[i]? = some u := by
  have hlen : i < ((rankList σ ((I.cand x \ R.used L x).subtype (· ∈ I.G.verts))).map
      Subtype.val).length := by
    rw [List.length_map, length_rankList, card_subtype_of_subset hCv]; exact hi
  refine ⟨_, ?_, List.getElem?_eq_getElem hlen⟩
  rw [List.getElem_map]
  exact Finset.mem_subtype.1 ((mem_rankList _ _ _).1 (List.getElem_mem _))

end Rules

end EG.Quot
