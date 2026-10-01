module

public import EG.Spec.Light.Parent
public import EG.Proof.Light.ParentEngine
public import EG.Proof.Light.ParentRun
public import EG.Proof.Light.ParentAvail
public import EG.Proof.Light.Setting
public import EG.Proof.Stage1.COLc
public import EG.Lib.Light.ParentData
public import EG.Proof.Light.ParentSum
public import Mathlib.Data.List.Flatten

/-!
# Proof of Lemma parent side (manuscript s5:lemParent), one round

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.lemParent`
(`LemParentStatement`, the s5 unit's Spec). For every phase `c`, the chaining engine
`EG.PEngine.engine` (`EG/Proof/Light/ParentEngine.lean`) is applied to the phase-`c` arcs of the
non-demoted light parts of round `l`, indexed by `(Z, j)` (Step 1, `EG.PData.arcIdx`), with the
parent map `par = parU`, the nodes `goodParents ω l`, the classes `LU_{Y,l,c,σ}` and the zones
`Zone_{Y,l,c,σ}`. The engine's hypotheses are Step 0 of the TeX proof:
* (F-a) `|Z| ≤ M_l` ([s2:lemCap] (ii), declared input `EG.capPrePart`), so an arc has at most
  `M_l − 1` edges and `Z` has at most `14(J̄_l+1)M_l` arcs;
* (F-c) light parts of one round are vertex-disjoint (`EG.structureLight`) and the sets `E_r(Y)`
  are disjoint (`EG.structureHY`, P2J, proved);
* (F-d) the child-side properties (`ArcHyp`);
* Step 5: every vertex is an end of at most `M_l − 1 < t_Y` arcs (`EG.bundleEndCount`, `EG.mlTy`);
* Step 4: `T^sl_Y ≥ (102 log₂λ_{l−2})^2` ([s5:eqLY], declared input `EG.eqLY`, and
  [s2:lemTower] (a), `EG.towerA`);
* Step 6: good parents are not parent-bad, so the classes are path connected through the zones.
The per-round count (ii) sums the engine's bounds over the four phases. Design note
`formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB EG.Stage1 EG.Light EG.MTrail

namespace ParentAux

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

theorem head?_eq_headD {l : List V} (h : l ≠ []) (d : V) : l.head? = some (l.headD d) := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h; rfl

theorem getLast?_eq_getLastD {l : List V} (h : l ≠ []) (d : V) :
    l.getLast? = some (l.getLastD d) := by
  rw [List.getLastD_eq_getLast?]
  cases hl : l.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hl) h
  | some x => rfl

/-- The classes `LU_{Y,l,c,σ}` of distinct pairs `(Y, σ)` (good parents of round `≤ l − 2`) are
edge-disjoint. -/
theorem disjoint_LU {Dstar : ℝ} (hV : run.Valid G Dstar) (ω : Outcome G run) {l : ℕ} {c : Fin 4}
    {Y Y' : PartId} (hY : Y ∈ goodParents ω l) (hY' : Y' ∈ goodParents ω l) {σ σ' : ℕ}
    (hne : (Y, σ) ≠ (Y', σ')) :
    Disjoint (LU G run Y (ω.colAt Y) l c σ).edges (LU G run Y' (ω.colAt Y') l c σ').edges := by
  have hHY := (structureHY _ G Dstar run hV).2.2.2
  have hYa := mem_ancestors_of_goodParent ((mem_goodParents ω).1 hY).1
  have hYa' := mem_ancestors_of_goodParent ((mem_goodParents ω).1 hY').1
  by_cases hYY : Y = Y'
  · subst hYY
    have hσ : σ ≠ σ' := fun h' => hne (by rw [h'])
    refine disjoint_lentClass G run Y (ω.colAt Y) ?_
    intro ht; injection ht with _ _ h3; exact hσ h3
  · refine Disjoint.mono (Lend_edges_subset G run Y _ |>.trans' (lentClass_edges_subset_Lend G run Y _ _))
      (Lend_edges_subset G run Y' _ |>.trans' (lentClass_edges_subset_Lend G run Y' _ _)) ?_
    exact hHY Y hYa Y' hYa' hYY

end ParentAux

universe u

/-- [s5:lemParent] for one round `l` and one phase `c`: the engine applied to the phase-`c` arcs. -/
theorem parent_phase {V : Type u} [DecidableEq V] {G : FGraph V} {N0 Dstar : ℝ} {run : Run V}
    (h : RunHyp N0 Dstar G run) (ω : Outcome G run) (hω : ω ∈ (Stage1.law G run).supp) {l : ℕ}
    (hl3 : 3 ≤ l) (hlR : l ≤ run.R)
    {H0 : PartId → Finset (Sym2 V)} {arcs : PartId → List (Arc V)} (hArc : ArcHyp ω l H0 arcs)
    (v0 : V) (c : Fin 4) :
    ∃ (LentU : Finset (Sym2 V)) (D : List (Obj V)) (extra : ℕ),
      Disjoint LentU (bundleEdges ω l arcs c) ∧
      IsDecomp ((bundleEdges ω l arcs c ∪ LentU : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      (∀ e ∈ LentU, ∃ Y ∈ goodParents ω l, ∃ σ < Tslot G run Y, ∃ p : List V,
        IsConnector ω l c Y σ p ∧ e ∈ walkEdges p) ∧
      D.length ≤ 14 * (Jbar G run l + 1) * run.M G l * ((goodParents ω l).card * run.M G l) +
        extra ∧
      (extra : ℝ) ≤ ((∑ Z ∈ childParts ω l, ((arcs Z).filter fun a => a.2 = c).length : ℕ) : ℝ) /
        (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 := by
  classical
  have hΓ := h.gamma1
  have hV := h.valid
  have hd1 := h.le_d_one
  have hSL := structureLight V G N0 Dstar run h
  have hHY := structureHY V G Dstar run hV
  -- the data of the engine
  set Zs := childParts ω l with hZs
  set L : PartId → List (List V) := fun Z => ((arcs Z).filter fun a => a.2 = c).map Prod.fst
    with hL
  set arcSet := PData.arcIdx Zs L with harcSet
  set arcPath := PData.arcAt L with harcPath
  set ends : PartId × ℕ → V × V := fun a => ((arcPath a).headD v0, (arcPath a).getLastD v0)
    with hends
  set par : V → PartId := fun v => (parU ω l v).getD (0, []) with hpar
  set Tmin : ℝ := (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 with hTmin
  -- basic facts on the arcs
  have hZmem : ∀ Z ∈ Zs, Z ∈ run.lightParts G ∧ Z.1 = l ∧ ¬ demoted ω Z := fun Z hZ =>
    (mem_childParts ω).1 hZ
  have harcOf : ∀ a ∈ arcSet, ∃ ar ∈ arcs a.1, ar.2 = c ∧ ar.1 = arcPath a := by
    intro a ha
    have hj := (PData.mem_arcIdx.1 ha).2
    have hm := PData.arcAt_mem hj
    simp only [hL, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨ar, ⟨har, hc⟩, he⟩ := hm
    exact ⟨ar, har, hc, he⟩
  have hsys : ∀ a ∈ arcSet, a.1 ∈ Zs ∧ ∃ ar ∈ arcs a.1, ar.2 = c ∧ ar.1 = arcPath a ∧
      IsPathIn (H0 a.1) ar.1 ∧ 1 ≤ pathLength ar.1 ∧
      (∀ x, (ar.1.head? = some x ∨ ar.1.getLast? = some x) → x ∈ Rt ω a.1) ∧
      ∀ x ∈ ar.1, ∀ (Y : PartId) (σ : ℕ), x ∉ Zone G run ω.zone Y (LentTag.U a.1.1 ar.2 σ) := by
    intro a ha
    have hZ := (PData.mem_arcIdx.1 ha).1
    obtain ⟨ar, har, hc, he⟩ := harcOf a ha
    exact ⟨hZ, ar, har, hc, he, ((hArc a.1 hZ).2.2.1 ar har)⟩
  have hverts : ∀ a ∈ arcSet, ∀ x ∈ arcPath a, x ∈ run.ancVerts G a.1 := by
    intro a ha x hx
    obtain ⟨hZ, ar, har, -, he, -⟩ := hsys a ha
    rw [← he] at hx
    exact ArcHyp.mem_verts hArc hZ har hx
  have hcardM : ∀ Z ∈ Zs, (run.ancVerts G Z).card ≤ run.M G l := by
    intro Z hZ
    obtain ⟨hZL, hZl, -⟩ := hZmem Z hZ
    obtain ⟨hZr, hZa, -⟩ := (mem_lightParts_iff G run Z).1 hZL
    have hcap := (capPrePart V G Dstar run h.gamma2a hV Z.1 hZr).2 Z.2 hZa
    rw [← hZl]
    exact (Finset.card_le_card (run.partVerts_subset_Z0 G Z.1 Z.2)).trans hcap.1
  have hne : ∀ a ∈ arcSet, arcPath a ≠ [] := by
    intro a ha he
    obtain ⟨-, ar, -, -, har, hp, -⟩ := hsys a ha
    rw [har] at hp; exact hp.1 he
  have hRtpar : ∀ Z ∈ Zs, ∀ x ∈ Rt ω Z, par x ∈ goodParents ω l ∧ x ∈ run.ancVerts G (par x) := by
    intro Z hZ x hx
    have hs := ((mem_Rt_iff_parU ω).1 hx).2
    rw [(hZmem Z hZ).2.1] at hs
    obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hs
    have hpx : par x = Y := by simp only [hpar, hY, Option.getD_some]
    obtain ⟨hg, hr, hv, -⟩ := parU_spec ω hY
    rw [hpx]
    exact ⟨(mem_goodParents ω).2 ⟨hg, hr⟩, hv⟩
  have hendsRt : ∀ a ∈ arcSet, (ends a).1 ∈ Rt ω a.1 ∧ (ends a).2 ∈ Rt ω a.1 := by
    intro a ha
    obtain ⟨-, ar, -, -, har, -, -, hRt, -⟩ := hsys a ha
    rw [har] at hRt
    exact ⟨hRt _ (Or.inl (ParentAux.head?_eq_headD (hne a ha) v0)),
      hRt _ (Or.inr (ParentAux.getLast?_eq_getLastD (hne a ha) v0))⟩
  have hgoodL : ∀ Y ∈ goodParents ω l, Y ∈ run.lightParts G ∧ Y.1 + 2 ≤ l ∧ ¬ parentBad ω Y := by
    intro Y hY
    obtain ⟨hg, hr⟩ := (mem_goodParents ω).1 hY
    exact ⟨hg.1, hr, hg.2.2⟩
  -- the hypotheses of the engine
  have hHyp : PEngine.Hyp arcSet arcPath ends Prod.snd (14 * (Jbar G run l + 1) * run.M G l) par
      (goodParents ω l) (Tslot G run) (fun Y => (tY G run Y : ℝ))
      (fun Y => (2 : ℝ) ^ 12 * run.LY G Y ^ 4) (fun Y σ => LU G run Y (ω.colAt Y) l c σ)
      (fun Y σ => Zone G run ω.zone Y (LentTag.U l c σ)) (fun Y => run.ancVerts G Y)
      (run.M G l - 1) Tmin := by
    have hlam := Standing.lam_ge hΓ hV (l := l - 2) ⟨by omega, by omega⟩
    have hlampos : 0 < run.lam G (l - 2) := lt_of_lt_of_le (by norm_num) hlam
    have hμ : (256 : ℝ) ≤ Real.logb 2 (run.lam G (l - 2)) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hlampos]
      calc (2 : ℝ) ^ (256 : ℝ) = 2 ^ (256 : ℕ) := by norm_num
        _ ≤ _ := hlam
    refine ⟨?hpath, ?hends, ?hcls, ?hvd, ?hed, ?hlen, ?hpar, ?hmult, ?htm, ?hTmin, ?hTsl, ?hLUv,
      ?hPC, ?hZdis, ?hZarc, ?hLUdis, ?hLUarc⟩
    case hpath =>
      intro a ha
      obtain ⟨-, ar, -, -, har, hp, hlen, -⟩ := hsys a ha
      rw [← har]
      exact ⟨hp.2.1, by unfold pathLength at hlen; omega⟩
    case hends =>
      intro a ha
      exact ⟨ParentAux.head?_eq_headD (hne a ha) v0, ParentAux.getLast?_eq_getLastD (hne a ha) v0⟩
    case hcls =>
      intro a ha
      obtain ⟨hZ, hj⟩ := PData.mem_arcIdx.1 ha
      obtain ⟨hZL, hZl, -⟩ := hZmem a.1 hZ
      have h1 : (L a.1).length ≤ (arcs a.1).length := by
        simp only [hL, List.length_map]; exact List.length_filter_le _ _
      have h2 := (hArc a.1 hZ).2.2.2.1
      have h3 : JY G run a.1 ≤ Jbar G run l := by
        unfold Jbar
        exact Finset.le_sup (f := JY G run) (Finset.mem_filter.2 ⟨hZL, hZl⟩)
      have h4 := hcardM a.1 hZ
      calc a.2 < (L a.1).length := hj
        _ ≤ 14 * (JY G run a.1 + 1) * (run.ancVerts G a.1).card := h1.trans h2
        _ ≤ 14 * (Jbar G run l + 1) * run.M G l := by gcongr
    case hvd =>
      intro a ha b hb hcl hab x hxa hxb
      have hZab : a.1 ≠ b.1 := fun he => hab (Prod.ext he hcl)
      have hZa := (PData.mem_arcIdx.1 ha).1
      have hZb := (PData.mem_arcIdx.1 hb).1
      exact Finset.disjoint_left.1 (hSL a.1 (hZmem a.1 hZa).1 b.1 (hZmem b.1 hZb).1
        ((hZmem a.1 hZa).2.1.trans (hZmem b.1 hZb).2.1.symm) hZab) (hverts a ha x hxa)
        (hverts b hb x hxb)
    case hed =>
      intro a ha b hb hab
      rw [List.disjoint_left]
      intro e hea heb
      by_cases hZ : a.1 = b.1
      · -- the same part: the arcs of `Z` are edge-disjoint
        obtain ⟨Z, i⟩ := a
        obtain ⟨Z', j⟩ := b
        simp only at hZ
        subst hZ
        have hj : i ≠ j := fun he => hab (by rw [he])
        obtain ⟨hZa, hja⟩ := PData.mem_arcIdx.1 ha
        obtain ⟨-, hjb⟩ := PData.mem_arcIdx.1 hb
        have hnd := (hArc Z hZa).2.1
        have hsub : List.Sublist ((L Z).flatMap walkEdges)
            ((arcs Z).flatMap fun ar => walkEdges ar.1) := by
          simp only [hL, List.flatMap_map]
          exact (List.filter_sublist).flatMap _
        have hpw := (List.nodup_flatMap.1 (hnd.sublist hsub)).2
        rw [List.pairwise_iff_getElem] at hpw
        have ea : arcPath (Z, i) = (L Z)[i] := PData.arcAt_eq hja
        have eb : arcPath (Z, j) = (L Z)[j] := PData.arcAt_eq hjb
        rw [ea] at hea
        rw [eb] at heb
        rcases Nat.lt_or_gt_of_ne hj with hlt | hlt
        · exact List.disjoint_left.1 (hpw i j hja hjb hlt) hea heb
        · exact List.disjoint_left.1 (hpw j i hjb hja hlt) heb hea
      · -- distinct parts are vertex-disjoint
        induction e using Sym2.ind with
        | h x y =>
          have hx1 := hverts a ha x (mem_of_mem_walkEdges hea (Sym2.mem_mk_left x y))
          have hx2 := hverts b hb x (mem_of_mem_walkEdges heb (Sym2.mem_mk_left x y))
          have hZa := (PData.mem_arcIdx.1 ha).1
          have hZb := (PData.mem_arcIdx.1 hb).1
          exact Finset.disjoint_left.1 (hSL a.1 (hZmem a.1 hZa).1 b.1 (hZmem b.1 hZb).1
            ((hZmem a.1 hZa).2.1.trans (hZmem b.1 hZb).2.1.symm) hZ) hx1 hx2
    case hlen =>
      intro a ha
      obtain ⟨hZ, -⟩ := PData.mem_arcIdx.1 ha
      obtain ⟨-, ar, -, -, har, hp, -⟩ := hsys a ha
      rw [length_walkEdges]
      unfold pathLength
      have h1 : (arcPath a).length ≤ (run.ancVerts G a.1).card := by
        rw [← List.toFinset_card_of_nodup (by rw [← har]; exact hp.2.1)]
        exact Finset.card_le_card fun x hx => hverts a ha x (List.mem_toFinset.1 hx)
      have h2 := hcardM a.1 hZ
      omega
    case hpar =>
      intro a ha
      have hZ := (PData.mem_arcIdx.1 ha).1
      obtain ⟨h1, h2⟩ := hendsRt a ha
      exact ⟨(hRtpar a.1 hZ _ h1).1, (hRtpar a.1 hZ _ h2).1, (hRtpar a.1 hZ _ h1).2,
        (hRtpar a.1 hZ _ h2).2⟩
    case hmult =>
      intro v
      have hcnt : (arcSet.filter fun a => (ends a).1 = v ∨ (ends a).2 = v).card =
          ∑ Z ∈ Zs, pathEndCount (L Z) v := by
        rw [Finset.filter_congr (q := fun a => (arcPath a).head? = some v ∨ (arcPath a).getLast? = some v)]
        · rw [PData.card_filter_arcIdx Zs L (fun p => p.head? = some v ∨ p.getLast? = some v)]
          rfl
        · intro a ha
          rw [ParentAux.head?_eq_headD (hne a ha) v0, ParentAux.getLast?_eq_getLastD (hne a ha) v0]
          simp only [Option.some.injEq, hends]
      rw [hcnt]
      have hB := bundleEndCount V G N0 Dstar run h ω hω l hl3 hlR H0 arcs hArc c v
      by_cases hv : ∃ a ∈ arcSet, (ends a).1 = v ∨ (ends a).2 = v
      · obtain ⟨a, ha, hav⟩ := hv
        have hZ := (PData.mem_arcIdx.1 ha).1
        have hRt : v ∈ Rt ω a.1 := by
          rcases hav with h' | h' <;> rw [← h']
          · exact (hendsRt a ha).1
          · exact (hendsRt a ha).2
        obtain ⟨hYg, -⟩ := hRtpar a.1 hZ v hRt
        obtain ⟨hYL, hYr, -⟩ := hgoodL _ hYg
        have hml := (mlTy V G N0 Dstar run h (par v) hYL l hYr hlR).2.2.2
        have : ∑ Z ∈ Zs, pathEndCount (L Z) v ≤ tY G run (par v) := by
          have := hB; simp only [hZs, hL] at this ⊢; omega
        exact_mod_cast this
      · push Not at hv
        have h0 : ∑ Z ∈ Zs, pathEndCount (L Z) v = 0 := by
          rw [← hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro a ha hav
          rcases hav with h' | h'
          · exact (hv a ha).1 h'
          · exact (hv a ha).2 h'
        rw [h0]; simp
    case htm => intro Y _; exact Nat.cast_nonneg _
    case hTmin =>
      rw [hTmin]
      have : (1 : ℝ) ≤ 102 * Real.logb 2 (run.lam G (l - 2)) := by linarith
      nlinarith
    case hTsl =>
      intro Y hY
      obtain ⟨hYL, hYr, -⟩ := hgoodL Y hY
      have hLY := eqLY V G N0 Dstar run h Y hYL
      have hY1 : 1 ≤ Y.1 := (Finset.mem_Icc.1 ((mem_lightParts_iff G run Y).1 hYL).1).1
      have hA := (towerA V G Dstar run hΓ.1 hV hd1).2.2.2.2 Y.1 l hY1 hYr (by omega)
      have hlog : Real.logb 2 (run.lam G (l - 2)) ≤ Real.logb 2 (run.lam G Y.1) :=
        Real.logb_le_logb_of_le (by norm_num) hlampos hA
      have h1 : 102 * Real.logb 2 (run.lam G (l - 2)) ≤ run.LY G Y := by
        linarith [hLY.2.2.1, hLY.2.2.2.1]
      have h0 : 0 ≤ 102 * Real.logb 2 (run.lam G (l - 2)) := by linarith
      rw [hTmin]
      calc (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 ≤ run.LY G Y ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ ≤ (Tslot G run Y : ℝ) := Nat.le_ceil _
    case hLUv =>
      intro Y hY σ _
      have hL' := isLight_of_mem_lightParts (hgoodL Y hY).1
      show (run.ancGraph G Y).verts = run.ancVerts G Y
      rw [ancGraph_eq_X_of_isLight hL', X_verts_of_isLight hL']
    case hPC =>
      intro Y hY σ hσ
      obtain ⟨hYL, hYr, hnb⟩ := hgoodL Y hY
      have hcol : COLc G run Y (ω.cOutAt Y) (fun i => Zone G run ω.zone Y i) := by
        unfold parentBad at hnb; exact not_not.1 hnb
      exact hcol (LentTag.U l c σ) (mem_IU.2 ⟨isLight_of_mem_lightParts hYL, l, c, σ, rfl,
        (mem_lateRounds run).2 ⟨hYr, hlR⟩, hσ⟩)
    case hZdis =>
      intro Y _ σ _ Y' _ σ' _ hne'
      refine disjoint_Zone ω.zone ?_
      intro he
      simp only [Prod.mk.injEq, LentTag.U.injEq] at he
      exact hne' (by rw [he.1, he.2.2.2])
    case hZarc =>
      intro a ha x hx Y _ σ _
      obtain ⟨hZ, ar, -, hc, har, -, -, -, hzone⟩ := hsys a ha
      rw [← har] at hx
      have := hzone x hx Y σ
      rwa [(hZmem a.1 hZ).2.1, hc] at this
    case hLUdis =>
      intro Y hY σ _ Y' hY' σ' _ hne'
      exact ParentAux.disjoint_LU hV ω hY hY' hne'
    case hLUarc =>
      intro a ha e he Y hY σ _ heY
      obtain ⟨hZ, ar, har0, -, har, hp, -⟩ := hsys a ha
      rw [← har] at he
      have heH0 := hp.2.2 e he
      have heE : e ∈ run.E G a.1.1 a.1.2 := ((hArc a.1 hZ).1).2 heH0
      obtain ⟨hYL, hYr, -⟩ := hgoodL Y hY
      have hYa := mem_ancestors_of_goodParent ((mem_goodParents ω).1 hY).1
      have hZa := COLcAux.mem_ancestors_of_mem_lightParts (hZmem a.1 hZ).1
      have heY' : e ∈ run.E G Y.1 Y.2 :=
        hHY.1 Y hYa (Lend_edges_subset G run Y _ (lentClass_edges_subset_Lend G run Y _ _ heY))
      have hne' : a.1 ≠ Y := by
        intro he'; have := (hZmem a.1 hZ).2.1; rw [he'] at this; omega
      exact Finset.disjoint_left.1 (hHY.2.2.1 a.1 hZa Y hYa hne') heE heY'
  obtain ⟨LentU, D, extra, hdisj, hdec, hconn, hlen, hext⟩ :=
    PEngine.engine arcSet arcPath ends Prod.snd _ par (goodParents ω l) (Tslot G run) _ _ _ _ _ _
      Tmin hHyp
  have hbund : PEngine.arcEdgeSet arcSet arcPath = bundleEdges ω l arcs c := by
    ext e
    rw [PEngine.mem_arcEdgeSet, mem_bundleEdges]
    constructor
    · rintro ⟨a, ha, he⟩
      obtain ⟨ar, har, hc, hare⟩ := harcOf a ha
      exact ⟨a.1, (PData.mem_arcIdx.1 ha).1, ar, har, hc, by rw [hare]; exact he⟩
    · rintro ⟨Z, hZ, ar, har, hc, he⟩
      have hmem : ar.1 ∈ L Z :=
        List.mem_map.2 ⟨ar, List.mem_filter.2 ⟨har, by simpa using hc⟩, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.1 hmem
      refine ⟨(Z, j), PData.mem_arcIdx.2 ⟨hZ, hj⟩, ?_⟩
      rw [show arcPath (Z, j) = (L Z)[j] from PData.arcAt_eq hj, hjeq]
      exact he
  rw [hbund] at hdisj hdec
  refine ⟨LentU, D, extra, hdisj, hdec, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨Y, hY, σ, hσ, p, hp1, hp2, hep⟩ := hconn e he
    exact ⟨Y, hY, σ, hσ, p, ⟨hp1, hp2⟩, hep⟩
  · have hM1 : 1 ≤ run.M G l := by
      have := ParentSumAux.M_ge G run l
      exact_mod_cast (show (1 : ℝ) ≤ run.M G l by linarith [show (1 : ℝ) ≤ 2 ^ 40 by norm_num])
    rw [Nat.sub_add_cancel hM1] at hlen
    exact hlen
  · rw [PData.card_arcIdx] at hext
    refine hext.trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun Z _ => ?_
    simp [hL]


/-- [s5:lemParent] Lemma parent side, for one round `3 ≤ l ≤ R` and any arc systems with the
child-side properties (the s5 unit's Spec `LemParentStatement`). -/
theorem lemParent : EG.Spec.LemParentStatement.{u} := by
  intro V _ G N0 Dstar run h ω hω l hl3 hlR H0 arcs hArc
  classical
  rcases isEmpty_or_nonempty V with hVe | hVn
  · -- no vertices: nothing to decompose
    refine ⟨fun _ => ∅, fun _ => [], 0, fun _ => Finset.disjoint_empty_left _,
      fun _ => ⟨by simp, by simp, fun e => ?_⟩, fun _ => Finset.empty_subset _,
      fun _ _ _ _ _ _ he => absurd he (Finset.notMem_empty _), by simp; positivity,
      by simp; positivity, fun _ _ _ => Finset.disjoint_empty_left _⟩
    induction e using Sym2.ind with
    | h x y => exact isEmptyElim x
  obtain ⟨v0⟩ := hVn
  choose LentU D extra hdisj hdec hconn hlen hext using
    fun c => parent_phase h ω hω hl3 hlR hArc v0 c
  -- the available sets
  have hsub : ∀ c, LentU c ⊆ lentUAvail ω l c := by
    intro c e he
    obtain ⟨Y, hY, σ, hσ, p, hp, hep⟩ := hconn c e he
    simp only [lentUAvail, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨Y, hY, σ, hσ, hp.1.2.2 e hep⟩
  have hlam := Standing.lam_ge h.gamma1 h.valid (l := l - 2) ⟨by omega, by omega⟩
  have hlampos : 0 < run.lam G (l - 2) := lt_of_lt_of_le (by norm_num) hlam
  have hμ : 0 < Real.logb 2 (run.lam G (l - 2)) :=
    Real.logb_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hlam)
  have hTmin : 0 < (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 := by positivity
  -- the arcs of all phases: at most `14(J̄_l+1)n`
  have hparts : ∑ Z ∈ childParts ω l, (run.ancVerts G Z).card ≤ G.card := by
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_card (Finset.biUnion_subset.2 fun Z _ =>
        Stage1.ancVerts_subset_verts G run Z)
    · intro Z hZ Z' hZ' hne
      obtain ⟨hZL, hZl, -⟩ := (mem_childParts ω).1 hZ
      obtain ⟨hZL', hZl', -⟩ := (mem_childParts ω).1 hZ'
      exact structureLight V G N0 Dstar run h Z hZL Z' hZL' (hZl.trans hZl'.symm) hne
  have harcs : ∑ c : Fin 4, ∑ Z ∈ childParts ω l, ((arcs Z).filter fun a => a.2 = c).length ≤
      14 * (Jbar G run l + 1) * G.card := by
    rw [Finset.sum_comm]
    have hZ1 : ∀ Z ∈ childParts ω l, ∑ c : Fin 4, ((arcs Z).filter fun a => a.2 = c).length =
        (arcs Z).length := by
      intro Z _
      have := MTrail.sum_countP_fiber (fun a : Arc V => a.2) Finset.univ (arcs Z) (by simp)
      rw [← this]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [List.countP_eq_length_filter]
    rw [Finset.sum_congr rfl hZ1]
    calc ∑ Z ∈ childParts ω l, (arcs Z).length
        ≤ ∑ Z ∈ childParts ω l, 14 * (Jbar G run l + 1) * (run.ancVerts G Z).card := by
          refine Finset.sum_le_sum fun Z hZ => (((hArc Z hZ).2.2.2.1)).trans ?_
          obtain ⟨hZL, hZl, -⟩ := (mem_childParts ω).1 hZ
          have : JY G run Z ≤ Jbar G run l := by
            unfold Jbar
            exact Finset.le_sup (f := JY G run) (Finset.mem_filter.2 ⟨hZL, hZl⟩)
          gcongr
      _ = 14 * (Jbar G run l + 1) * ∑ Z ∈ childParts ω l, (run.ancVerts G Z).card := by
          rw [Finset.mul_sum]
      _ ≤ 14 * (Jbar G run l + 1) * G.card := Nat.mul_le_mul_left _ hparts
  -- `|goodParents| ≤ ν_l`
  have hnu : (goodParents ω l).card ≤ run.nuAnc G l := by
    unfold Run.nuAnc
    refine Finset.card_le_card fun Y hY => ?_
    obtain ⟨hg, hr⟩ := (mem_goodParents ω).1 hY
    exact Finset.mem_filter.2 ⟨mem_ancestors_of_goodParent hg, hr⟩
  refine ⟨LentU, D, ∑ c, extra c, hdisj, hdec, hsub, ?_, ?_, ?_, ?_⟩
  · -- (i): every edge of `LentU ∩ LU_{Y,l,c,σ}` lies on a connector of `(Y, σ)`
    intro c Y hY σ hσ e he heY
    obtain ⟨Y', hY', σ', hσ', p, hp, hep⟩ := hconn c e he
    have heY' := hp.1.2.2 e hep
    by_cases hs : (Y, σ) = (Y', σ')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact ⟨p, hp, hep⟩
    · exact absurd heY' (Finset.disjoint_left.1 (ParentAux.disjoint_LU h.valid ω hY hY' hs) heY)
  · -- (ii): the visit-capping pieces
    push_cast
    calc ∑ c, (extra c : ℝ)
        ≤ ∑ c : Fin 4, ((∑ Z ∈ childParts ω l, ((arcs Z).filter fun a => a.2 = c).length : ℕ) : ℝ)
            / (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 := Finset.sum_le_sum fun c _ => hext c
      _ = ((∑ c : Fin 4, ∑ Z ∈ childParts ω l, ((arcs Z).filter fun a => a.2 = c).length : ℕ) : ℝ)
            / (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 := by
          rw [← Finset.sum_div, Nat.cast_sum]
      _ ≤ 14 * ((Jbar G run l : ℝ) + 1) * (G.card : ℝ) /
            (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 := by
          refine div_le_div_of_nonneg_right ?_ hTmin.le
          exact_mod_cast harcs
  · -- (ii): the number of objects
    have hD : ∑ c, (D c).length ≤ ∑ c : Fin 4,
        (14 * (Jbar G run l + 1) * run.M G l * ((goodParents ω l).card * run.M G l) + extra c) :=
      Finset.sum_le_sum fun c _ => hlen c
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hD
    have hD' : ((∑ c, (D c).length : ℕ) : ℝ) ≤
        4 * ((14 * (Jbar G run l + 1) * run.M G l * ((goodParents ω l).card * run.M G l) : ℕ) : ℝ)
          + ((∑ c, extra c : ℕ) : ℝ) := by exact_mod_cast hD
    refine hD'.trans ?_
    push_cast
    have hnu' : ((goodParents ω l).card : ℝ) ≤ (run.nuAnc G l : ℝ) := by exact_mod_cast hnu
    have hM0 : (0 : ℝ) ≤ run.M G l := Nat.cast_nonneg _
    have hJ0 : (0 : ℝ) ≤ (Jbar G run l : ℝ) + 1 := by positivity
    have key : ((goodParents ω l).card : ℝ) * (run.M G l : ℝ) ≤
        ((run.M G l : ℝ) + 1) * (run.nuAnc G l : ℝ) := by
      have h0 : (0 : ℝ) ≤ (goodParents ω l).card := Nat.cast_nonneg _
      nlinarith
    have : 4 * (14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) *
        (((goodParents ω l).card : ℝ) * (run.M G l : ℝ))) ≤
        4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
          (run.nuAnc G l : ℝ) := by
      have h1 : 0 ≤ 4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) := by positivity
      nlinarith
    linarith
  · -- the sets `LentU_{l,c}` are pairwise disjoint over `c`
    intro c c' hcc
    exact Disjoint.mono (hsub c) (hsub c')
      (lemParentAvailDisjoint V G N0 Dstar run h ω hω l l c c' (by simp [hcc]))


end EG
