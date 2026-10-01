module

public import EG.Proof.Chain.JSLCStep2Defs

/-!
# JS-LC Step 2: structure and parity of `R^0_Y`, `R_Y` (manuscript s6:lemJSLC, proof, Step 2)

Probe unit P2J (probe P-2, part 2), proof round 1. Under `Step2Hyp`:
* `R0_struct`: "Every edge of `R^0_Y` has exactly one end that is a class-`Y` port of some
  `Q*_Z`, its *port*; its other end is its *centre*. A centre lies in `Ret_Z` or is a port of
  `Q*_Z` of a class `≠ Y`. By Step 1, centres of class-`Y` edges lie outside `V(Y)`";
* `R0_disjoint`, `Jpar_disjoint_R0`: the `R^0_Y` are pairwise disjoint and disjoint from the
  PAR deletions;
* `even_degE_R0_of_mem_qs`: "A pseudo-hub `v ∈ Q*_Z` of class `b` lies in exactly one part (it
  is not in `D_l`). It is a centre of class-`Y` edges only through the edges of `E_{Yb}(Z)`
  assigned to `Y`, and it has even degree in those by Lemma s6:lemPAR";
* `mv_struct`: "Only centres in `Ret_Z` are ever odd", so a moved edge is `hu` with `h ∈ Ret_Z`;
* `even_degE_R`: "A moved edge `hu` changes the class-`Y` centre degree of `h` only: its other end
  `u` is a port, which carries no parity constraint. So after the moves every centre has even
  degree in every `R_Y`."
-/

public section

namespace EG.Chain.Step2

open EG.HB

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)}

namespace Step2Hyp

variable (H : Step2Hyp run G δ S l B)
include H

theorem mem_E {a : Addr} (ha : a ∈ run.Std G l) {e : Sym2 V} (he : e ∈ B a) :
    e ∈ run.E G l a :=
  (H.hB a ha).1 he

theorem part_eq {a b : Addr} (ha : a ∈ run.Std G l) (hb : b ∈ run.Std G l) {e : Sym2 V}
    (hea : e ∈ B a) (heb : e ∈ B b) : a = b :=
  eq_of_mem_E run G (H.mem_E ha hea) (H.mem_E hb heb)

omit H in
theorem not_isDiag_of_mem_E {a : Addr} {e : Sym2 V} (he : e ∈ run.E G l a) : ¬ e.IsDiag :=
  G.loopless e (E_subset_edges run G l a he)

theorem qs_classed {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) : u ∈ run.classed G l a :=
  qs_subset_classed run G δ S l a hu

theorem port_mem_ancVerts {a : Addr} (ha : a ∈ run.Std G l) {u : V}
    (hu : u ∈ qs run G δ S l a) : u ∈ run.ancVerts G (δ l u) :=
  H.hδ.mem_ancVerts H.l3 ha (H.qs_classed hu)

/-- A vertex of `Q*_Z` lies in `Z^0` and outside `D_l`. -/
theorem qs_Z0 {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) : u ∈ run.Z0 G l a :=
  classed_subset_Z0 run G l a (H.qs_classed hu)

theorem qs_notMem_D {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) : u ∉ run.D G l :=
  not_mem_D_of_mem_ports run G (classed_subset_ports run G l a (H.qs_classed hu))

/-- An edge of `E_l(Z')` at a vertex `u ∈ Q*_Z` lies in the same part: `Z' = Z`. -/
theorem part_eq_of_qs {a b : Addr} (ha : a ∈ run.Std G l) (hb : b ∈ run.Std G l) {u : V}
    (hu : u ∈ qs run G δ S l a) {e : Sym2 V} (he : e ∈ run.E G l b) (hue : u ∈ e) : b = a :=
  eq_of_mem_Z0_of_notMem_D run G (Std_subset_prePartAddrs run G l hb)
    (Std_subset_prePartAddrs run G l ha)
    (Run.partVerts_subset_Z0 run G l b (Run.mem_partVerts_of_mem_E run G he hue))
    (H.qs_Z0 hu) (H.qs_notMem_D hu)

/-- The hypotheses of the PAR specification hold for `E_p(a)` when `p` is the class pair of one
of its port–port edges. -/
theorem Epp_map {a : Addr} {p : Sym2 PartId} :
    ∀ e ∈ Epp run G δ S l B a p, e.map (δ l) = p :=
  fun _ he => (mem_Epp.1 he).2.2

theorem map_not_isDiag {a : Addr} (ha : a ∈ run.Std G l) {e : Sym2 V} (he : e ∈ B a)
    (hpp : IsPP run G δ S l a e) : ¬ (e.map (δ l)).IsDiag := by
  induction e using Sym2.ind with
  | _ x w =>
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    exact H.pp a ha x (H.qs_classed (hpp x (by simp))) w (H.qs_classed (hpp w (by simp)))
      (H.mem_E ha he)

theorem parAsg_mem {a : Addr} (ha : a ∈ run.Std G l) {e : Sym2 V} (he : e ∈ B a)
    (hpp : IsPP run G δ S l a e) :
    parAsg run G δ S l B a (e.map (δ l)) e ∈ e.map (δ l) :=
  ((parJ_spec run G δ S l B a (e.map (δ l))).2 H.Epp_map (H.map_not_isDiag ha he hpp)).2.1 e
    (mem_Epp.2 ⟨he, hpp, rfl⟩)

/-- [s6:lemJSLC] (proof, Step 2 (2b)) the structure of an edge of `R^0_Y`: it is `hu ∈ B_Z` with
port `u ∈ Q*_Z` of class `Y` and centre `h ∉ V(Y)`, and the centre lies in `Ret_Z` or is a port of
`Q*_Z` of a class `≠ Y`. -/
theorem R0_struct {Y : PartId} {e : Sym2 V} (he : e ∈ R0 run G δ S l B Y) :
    ∃ a ∈ run.Std G l, e ∈ B a ∧ ∃ h u, e = s(h, u) ∧ u ∈ qs run G δ S l a ∧ δ l u = Y ∧
      h ∉ run.ancVerts G Y ∧
      (h ∈ ret run G δ S l a ∨ (h ∈ qs run G δ S l a ∧ δ l h ≠ Y)) := by
  obtain ⟨a, ha, heB, hin⟩ := mem_R0.1 he
  refine ⟨a, ha, heB, ?_⟩
  have heE := H.mem_E ha heB
  rcases hin with ⟨hnpp, u, hu, hue, rfl⟩ | ⟨hpp, -, hasg⟩
  · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hue
    have hw : w ∉ qs run G δ S l a := by
      intro hw
      apply hnpp
      intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hu
      · exact hw
    have hwr : w ∈ ret run G δ S l a := by
      rcases H.ends a ha _ heE w (by simp) with h | h
      · exact h
      · exact absurd h hw
    have heE' : s(w, u) ∈ run.E G l a := by rw [Sym2.eq_swap]; exact heE
    exact ⟨w, u, Sym2.eq_swap, hu, rfl, H.el a ha u (H.qs_classed hu) w heE', Or.inl hwr⟩
  · have hmem := H.parAsg_mem ha heB hpp
    induction e using Sym2.ind with
    | _ x w =>
      have hx := hpp x (by simp)
      have hw := hpp w (by simp)
      have hne := H.pp a ha x (H.qs_classed hx) w (H.qs_classed hw) heE
      rw [hasg, Sym2.map_mk, Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · have heE' : s(w, x) ∈ run.E G l a := by rw [Sym2.eq_swap]; exact heE
        exact ⟨w, x, Sym2.eq_swap, hx, rfl, H.el a ha x (H.qs_classed hx) w heE',
          Or.inr ⟨hw, Ne.symm hne⟩⟩
      · exact ⟨x, w, rfl, hw, rfl, H.el a ha w (H.qs_classed hw) x heE, Or.inr ⟨hx, hne⟩⟩

/-- The port of an `R^0_Y`-edge lies in `V(Y)`, the centre outside: an edge of `R^0_Y` at a vertex
`h ∉ V(Y)` is `hu` with `u` its port. -/
theorem R0_at_centre {Y : PartId} {e : Sym2 V} (he : e ∈ R0 run G δ S l B Y) {h : V}
    (hh : h ∉ run.ancVerts G Y) (hhe : h ∈ e) :
    ∃ a ∈ run.Std G l, e ∈ B a ∧ ∃ u, e = s(h, u) ∧ u ∈ qs run G δ S l a ∧ δ l u = Y ∧
      (h ∈ ret run G δ S l a ∨ (h ∈ qs run G δ S l a ∧ δ l h ≠ Y)) := by
  obtain ⟨a, ha, heB, h', u, rfl, hu, hY, hh', hc⟩ := H.R0_struct he
  rcases Sym2.mem_iff.1 hhe with rfl | rfl
  · exact ⟨a, ha, heB, u, rfl, hu, hY, hc⟩
  · exact absurd (hY ▸ H.port_mem_ancVerts ha hu) hh

/-- The sets `R^0_Y` of distinct classes are disjoint. -/
theorem R0_disjoint {Y Y' : PartId} (hYY : Y ≠ Y') :
    Disjoint (R0 run G δ S l B Y) (R0 run G δ S l B Y') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, ha, heB, hin⟩ := mem_R0.1 he
  obtain ⟨a', ha', heB', hin'⟩ := mem_R0.1 he'
  obtain rfl := H.part_eq ha' ha heB' heB
  rcases hin with ⟨hnpp, u, hu, hue, rfl⟩ | ⟨hpp, -, hasg⟩ <;>
    rcases hin' with ⟨hnpp', u', hu', hue', rfl⟩ | ⟨hpp', -, hasg'⟩
  · apply hYY
    by_cases huu : u = u'
    · rw [huu]
    · exfalso
      apply hnpp
      rw [(Sym2.mem_and_mem_iff huu).1 ⟨hue, hue'⟩]
      intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hu
      · exact hu'
  · exact hnpp hpp'
  · exact hnpp' hpp
  · exact hYY (hasg.symm.trans hasg')

/-- The PAR deletions are not in any `R^0_Y`. -/
theorem Jpar_disjoint_R0 (Y : PartId) :
    Disjoint (Jpar run G δ S l B) (R0 run G δ S l B Y) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, ha, heB, hpp, hJ⟩ := mem_Jpar.1 he
  obtain ⟨a', ha', heB', hin⟩ := mem_R0.1 he'
  obtain rfl := H.part_eq ha' ha heB' heB
  rcases hin with ⟨hnpp, -⟩ | ⟨-, hnJ, -⟩
  · exact hnpp hpp
  · exact hnJ hJ

/-- [s6:lemJSLC] (proof, Step 2) "A pseudo-hub `v ∈ Q*_Z` of class `b` lies in exactly one part
(it is not in `D_l`). It is a centre of class-`Y` edges only through the edges of `E_{Yb}(Z)`
assigned to `Y`, and it has even degree in those by Lemma s6:lemPAR." -/
theorem even_degE_R0_of_mem_qs {a : Addr} (ha : a ∈ run.Std G l) {v : V}
    (hv : v ∈ qs run G δ S l a) {Y : PartId} (hvY : δ l v ≠ Y) :
    Even (degE (R0 run G δ S l B Y) v) := by
  set p0 : Sym2 PartId := s(δ l v, Y) with hp0
  have hset : edgesAt (R0 run G δ S l B Y) v =
      (Epp run G δ S l B a p0 \ parJ run G δ S l B a p0).filter
        (fun e => v ∈ e ∧ parAsg run G δ S l B a p0 e = Y) := by
    ext e
    rw [FGraph.mem_edgesAt, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨he, hve⟩
      obtain ⟨a', ha', heB, hin⟩ := mem_R0.1 he
      obtain rfl := H.part_eq_of_qs ha ha' hv (H.mem_E ha' heB) hve
      rcases hin with ⟨hnpp, u, hu, hue, hY⟩ | ⟨hpp, hnJ, hasg⟩
      · exfalso
        by_cases huv : u = v
        · exact hvY (huv ▸ hY)
        · apply hnpp
          rw [(Sym2.mem_and_mem_iff huv).1 ⟨hue, hve⟩]
          intro x hx
          rcases Sym2.mem_iff.1 hx with rfl | rfl
          · exact hu
          · exact hv
      · have hmap : e.map (δ l) = p0 := by
          have hmem := H.parAsg_mem ha heB hpp
          rw [hasg] at hmem
          obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve
          rw [Sym2.map_mk, Sym2.mem_iff] at hmem
          rw [Sym2.map_mk, hp0]
          rcases hmem with h | h
          · exact absurd h.symm hvY
          · rw [h]
        rw [hmap] at hnJ hasg
        exact ⟨⟨mem_Epp.2 ⟨heB, hpp, hmap⟩, hnJ⟩, hve, hasg⟩
    · rintro ⟨⟨he, hnJ⟩, hve, hasg⟩
      obtain ⟨heB, hpp, hmap⟩ := mem_Epp.1 he
      refine ⟨mem_R0.2 ⟨a, ha, heB, Or.inr ⟨hpp, ?_, ?_⟩⟩, hve⟩
      · rw [hmap]; exact hnJ
      · rw [hmap]; exact hasg
  unfold degE
  rw [hset]
  have hnd : ¬ p0.IsDiag := by rw [hp0, Sym2.mk_isDiag_iff]; exact hvY
  exact ((parJ_spec run G δ S l B a p0).2 H.Epp_map hnd).2.2 v Y hvY

/-- [s6:lemJSLC] (proof, Step 2) "Only centres in `Ret_Z` are ever odd": the moved edge at an odd
centre `h` of class `Y` is `hu ∈ B_Z` with `u ∈ Q*_Z` of class `Y` and `h ∈ Ret_Z`. -/
theorem mv_struct {Y : PartId} {h : V} (hh : h ∈ oddC run G δ S l B Y) :
    mv run G δ S l B Y h ∈ R0 run G δ S l B Y ∧
    ∃ a ∈ run.Std G l, mv run G δ S l B Y h ∈ B a ∧ ∃ u, mv run G δ S l B Y h = s(h, u) ∧
      u ∈ qs run G δ S l a ∧ δ l u = Y ∧ h ∈ ret run G δ S l a ∧ h ∉ run.ancVerts G Y := by
  obtain ⟨hmem, hhe⟩ := mv_spec (exists_mem_of_mem_oddC hh)
  obtain ⟨-, hhY, hodd⟩ := mem_oddC.1 hh
  obtain ⟨a, ha, heB, u, heq, hu, hY, hc⟩ := H.R0_at_centre hmem hhY hhe
  refine ⟨hmem, a, ha, heB, u, heq, hu, hY, ?_, hhY⟩
  rcases hc with hr | ⟨hq, hne⟩
  · exact hr
  · exact absurd (H.even_degE_R0_of_mem_qs ha hq hne) (Nat.not_even_iff_odd.2 hodd)

/-- The moved edges of class `Y` lie in `R^0_Y`. -/
theorem Moved_subset (Y : PartId) : Moved run G δ S l B Y ⊆ R0 run G δ S l B Y := by
  intro e he
  unfold Moved at he
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 he
  exact (H.mv_struct hh).1

/-- A moved edge of class `Y` containing a vertex `h ∉ V(Y)` is the moved edge at `h`. -/
theorem eq_of_mem_mv {Y : PartId} {h h' : V} (hh' : h' ∈ oddC run G δ S l B Y)
    (hh : h ∉ run.ancVerts G Y) (hmem : h ∈ mv run G δ S l B Y h') : h = h' := by
  obtain ⟨-, a, ha, -, u, heq, hu, hY, -, -⟩ := H.mv_struct hh'
  rw [heq] at hmem
  rcases Sym2.mem_iff.1 hmem with rfl | rfl
  · rfl
  · exact absurd (hY ▸ H.port_mem_ancVerts ha hu) hh

/-- The moved edges at `h`: `{mv Y h}` if `h` is an odd centre, none otherwise. -/
theorem edgesAt_Moved {Y : PartId} {h : V} (hh : h ∉ run.ancVerts G Y) :
    edgesAt (Moved run G δ S l B Y) h =
      if h ∈ oddC run G δ S l B Y then {mv run G δ S l B Y h} else ∅ := by
  ext e
  rw [FGraph.mem_edgesAt]
  unfold Moved
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨h', hh', rfl⟩, hmem⟩
    obtain rfl := H.eq_of_mem_mv hh' hh hmem
    rw [if_pos hh']
    exact Finset.mem_singleton_self _
  · intro he
    split_ifs at he with hodd
    · rw [Finset.mem_singleton.1 he]
      exact ⟨⟨h, hodd, rfl⟩, (mv_spec (exists_mem_of_mem_oddC hodd)).2⟩
    · exact absurd he (Finset.notMem_empty _)

/-- [s6:lemJSLC] (proof, Step 2) "So after the moves every centre has even degree in every
`R_Y`": every vertex outside `V(Y)` has even degree in `R_Y`. -/
theorem even_degE_R (Y : PartId) {h : V} (hh : h ∉ run.ancVerts G Y) :
    Even (degE (R run G δ S l B Y) h) := by
  have hsub : edgesAt (Moved run G δ S l B Y) h ⊆ edgesAt (R0 run G δ S l B Y) h :=
    FGraph.edgesAt_mono (H.Moved_subset Y) h
  have hRe : edgesAt (R run G δ S l B Y) h =
      edgesAt (R0 run G δ S l B Y) h \ edgesAt (Moved run G δ S l B Y) h := by
    ext e
    simp only [R, FGraph.mem_edgesAt, Finset.mem_sdiff]
    tauto
  have hcard : degE (R run G δ S l B Y) h + (edgesAt (Moved run G δ S l B Y) h).card =
      degE (R0 run G δ S l B Y) h := by
    unfold degE
    rw [hRe, Finset.card_sdiff_of_subset hsub, Nat.sub_add_cancel (Finset.card_le_card hsub)]
  rw [H.edgesAt_Moved hh] at hcard
  split_ifs at hcard with hodd
  · obtain ⟨-, -, hodd'⟩ := mem_oddC.1 hodd
    rw [Finset.card_singleton] at hcard
    rw [← hcard] at hodd'
    rcases hodd' with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rw [Finset.card_empty, add_zero] at hcard
    rw [hcard]
    by_cases hv : h ∈ edgeVerts (R0 run G δ S l B Y)
    · by_contra hne
      exact hodd (mem_oddC.2 ⟨hv, hh, Nat.not_even_iff_odd.1 hne⟩)
    · have : degE (R0 run G δ S l B Y) h = 0 := by
        unfold degE
        rw [Finset.card_eq_zero]
        ext e
        simp only [FGraph.mem_edgesAt, Finset.notMem_empty, iff_false, not_and]
        intro he hhe
        apply hv
        unfold edgeVerts
        exact Finset.mem_biUnion.2 ⟨e, he, Sym2.mem_toFinset.2 hhe⟩
      rw [this]; exact ⟨0, rfl⟩

/-- [s6:lemJSLC] (proof, Step 2) the moved edge at `(c, Y)` is the only edge of `J_l \ J^par`
of the form `cu` with `u ∈ Q*_Z` of class `Y` and `c ∉ Q*_Z` ("The moves are made once per pair
(centre, class)"). -/
theorem eq_mv_of_mem_Jmov {e : Sym2 V} (he : e ∈ Jmov run G δ S l B) {a : Addr}
    (ha : a ∈ run.Std G l) (heE : e ∈ run.E G l a) {c u : V} (heq : e = s(c, u))
    (hc : c ∉ qs run G δ S l a) (hu : u ∈ qs run G δ S l a) :
    c ∈ oddC run G δ S l B (δ l u) ∧ e = mv run G δ S l B (δ l u) c := by
  obtain ⟨Y, -, h, hh, rfl⟩ := mem_Jmov.1 he
  obtain ⟨-, a', ha', heB, u', heq', hu', hY, -, -⟩ := H.mv_struct hh
  obtain rfl := eq_of_mem_E run G (H.mem_E ha' heB) heE
  rw [heq'] at heq
  rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hY]; exact ⟨hh, rfl⟩
  · exact absurd hu' hc

omit H in
/-- A PAR deletion has both ends in `Q*_Z`. -/
theorem Jpar_struct {e : Sym2 V} (he : e ∈ Jpar run G δ S l B) :
    ∃ a ∈ run.Std G l, e ∈ B a ∧ IsPP run G δ S l a e :=
  let ⟨a, ha, heB, hpp, _⟩ := mem_Jpar.1 he
  ⟨a, ha, heB, hpp⟩

end Step2Hyp

end EG.Chain.Step2
