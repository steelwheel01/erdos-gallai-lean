module

public import EG.Defs.Light.Stages
public import EG.Defs.Probe.S5.KRED
public import EG.Lib.Stage1.COL
public import EG.Lib.Found.Fnum
public import EG.Lib.Light.Stages

/-!
# Helpers for Lemma K-RED (s5:lemKRED)

Library of the P3-s5 unit (`formal/work/p3/s5.md`). Manuscript v6.1, `s5.tex`, proof of
[s5:lemKRED]. This file collects the edge-set facts of the proof that follow from the
definitions of the classes ([s3:defCOL]) and from the edge partition of s2:propStructure (iii)
(passed as hypotheses):
* "`Lent_ext(Y) ⊆ Lend_Y ⊆ E(H_Y) ⊆ E_{r(Y)}(Y)`";
* "The U-lent classes are disjoint from the JS- and JV-lent classes";
* "`LentU(Z) ∪ Lent_ext(Z) ⊆ Lend_Z`, which is disjoint from `Own_Z`; so `Own_Z ⊆ H_0(Z)`";
* the U-lent edges available at round `l` lie in the edge sets of the good parents of rounds
  `≤ l − 2` (Lemma s5:lemParent (i)), so they avoid the edge sets of all other light parts.
-/

public section

namespace EG.Light

open EG.HB EG.Stage1

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-! ### Classes of one part -/

theorem LU_edges_subset (Y : PartId) (c : Colouring G run Y) (l : ℕ) (ph : Fin 4) (σ : ℕ) :
    (LU G run Y c l ph σ).edges ⊆ (run.ancGraph G Y).edges :=
  (lentClass_edges_subset_Lend G run Y c _).trans (Lend_edges_subset G run Y c)

theorem lentJSJV_subset_Lend (ω : Outcome G run) (Y : PartId) :
    lentJSJV ω Y ⊆ (Lend G run Y (ω.colAt Y)).edges := by
  intro e he
  simp only [lentJSJV, Finset.mem_union, Finset.mem_biUnion] at he
  rcases he with ⟨l, -, j, -, he⟩ | ⟨l, -, he⟩
  · exact lentClass_edges_subset_Lend G run Y _ _ he
  · exact lentClass_edges_subset_Lend G run Y _ _ he

theorem lentJSJV_subset_ancGraph (ω : Outcome G run) (Y : PartId) :
    lentJSJV ω Y ⊆ (run.ancGraph G Y).edges :=
  (lentJSJV_subset_Lend ω Y).trans (Lend_edges_subset G run Y _)

theorem disjoint_Own_lentJSJV (ω : Outcome G run) (Y : PartId) :
    Disjoint (Own G run Y (ω.colAt Y)).edges (lentJSJV ω Y) :=
  (disjoint_Own_Lend G run Y _).mono_right (lentJSJV_subset_Lend ω Y)

theorem disjoint_Own_LU (Y : PartId) (c : Colouring G run Y) (l : ℕ) (ph : Fin 4) (σ : ℕ) :
    Disjoint (Own G run Y c).edges (LU G run Y c l ph σ).edges :=
  (disjoint_Own_Lend G run Y c).mono_right (lentClass_edges_subset_Lend G run Y c _)

theorem disjoint_LU_lentJSJV (ω : Outcome G run) (Y : PartId) (l : ℕ) (ph : Fin 4) (σ : ℕ) :
    Disjoint (LU G run Y (ω.colAt Y) l ph σ).edges (lentJSJV ω Y) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [lentJSJV, Finset.mem_union, Finset.mem_biUnion] at he'
  rcases he' with ⟨l', -, j, -, he'⟩ | ⟨l', -, he'⟩
  · exact Finset.disjoint_left.1 (disjoint_lentClass G run Y _ (by simp)) he he'
  · exact Finset.disjoint_left.1 (disjoint_lentClass G run Y _ (by simp)) he he'

/-! ### Arcs -/

/-- The arcs of one part are pairwise edge-disjoint, so arcs of distinct phases have disjoint
edge sets. -/
theorem disjoint_arcEdges_filter {as : List (Arc V)}
    (h : (as.flatMap fun a => walkEdges a.1).Nodup) {c c' : Fin 4} (hc : c ≠ c') :
    Disjoint (arcEdges (as.filter fun a => a.2 = c)) (arcEdges (as.filter fun a => a.2 = c')) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_arcEdges] at he he'
  obtain ⟨a, ha, hea⟩ := he
  obtain ⟨b, hb, heb⟩ := he'
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  have hab : a ≠ b := by
    rintro rfl
    exact hc (ha.2.symm.trans hb.2)
  have hpw : as.Pairwise (fun a b => List.Disjoint (walkEdges a.1) (walkEdges b.1)) :=
    (List.nodup_flatMap.1 h).2
  have : Std.Symm (fun a b : Arc V => List.Disjoint (walkEdges a.1) (walkEdges b.1)) :=
    ⟨fun _ _ h => List.disjoint_comm.1 h⟩
  have := hpw.forall ha.1 hb.1 hab
  exact this hea heb

/-! ### The hypotheses of the construction -/

/-- The bound of Lemma s5:lemParent (ii) for round `l`, with `cap_l` replaced by its bound:
`4·14(J̄_l+1)M_l(M_l+1)ν_l + 14(J̄_l+1)n/(102 log₂λ_{l−2})^2`. -/
@[expose] noncomputable def pbound (G : FGraph V) (run : Run V) (l : ℕ) : ℝ :=
  4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
      (run.nuAnc G l : ℝ) +
    14 * ((Jbar G run l : ℝ) + 1) * (G.card : ℝ) / (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2

theorem pbound_eq (G : FGraph V) (run : Run V) (l : ℕ) : pbound G run l =
    4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
        (run.nuAnc G l : ℝ) +
      14 * ((Jbar G run l : ℝ) + 1) * (G.card : ℝ) / (102 * Real.logb 2 (run.lam G (l - 2))) ^ 2 :=
  rfl

/-- The facts used by the K-RED construction (for one stage-1 outcome `ω` and one family
`Lent_ext`): the edge-set facts of s2:propStructure (iii), the hypothesis on `Lent_ext`, the
disjointness of the available U-lent sets (Lemma s5:lemParent), and the three lemmas
s5:lemChild, s5:lemDemoted, s5:lemParent in the form used. -/
structure KHyp (ω : Outcome G run) (Lext : PartId → Finset (Sym2 V)) : Prop where
  round : ∀ Y ∈ run.lightParts G, 1 ≤ Y.1 ∧ Y.1 ≤ run.R
  ancE : ∀ Y ∈ run.lightParts G, (run.ancGraph G Y).edges ⊆ run.E G Y.1 Y.2
  ancX : ∀ Y ∈ run.lightParts G, (run.X G Y.1 Y.2).edges ⊆ run.E G Y.1 Y.2
  disjE : ∀ Y ∈ run.lightParts G, ∀ Y' ∈ run.lightParts G, Y ≠ Y' →
    Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2)
  lext : LentExtHyp ω Lext
  avail : ∀ (l l' : ℕ) (c c' : Fin 4), (l, c) ≠ (l', c') →
    Disjoint (lentUAvail ω l c) (lentUAvail ω l' c')
  child : ∀ Z ∈ run.lightParts G, ¬ demoted ω Z → ∀ H0 : Finset (Sym2 V), H0Adm ω Z H0 →
    ∃ (Hobj : Finset (Sym2 V)) (Dobj : List (Obj V)) (as : List (Arc V)),
      Disjoint Hobj (arcEdges as) ∧ Hobj ∪ arcEdges as = H0 ∧
      IsDecomp (Hobj : Set (Sym2 V)) Dobj ∧ Dobj.length ≤ 369 * (Pl ω Z).card ∧
      ArcSys ω Z H0 as
  demot : ∀ Y ∈ run.lightParts G, demoted ω Y →
    ∀ E : Finset (Sym2 V), (run.X G Y.1 Y.2).edges ⊆ E → E ⊆ run.E G Y.1 Y.2 →
      ∃ D : List (Obj V), IsDecomp (E : Set (Sym2 V)) D ∧ D.length ≤ 80 * (run.ancVerts G Y).card
  parent : ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
    ∀ (H0 : PartId → Finset (Sym2 V)) (arcs : PartId → List (Arc V)), ArcHyp ω l H0 arcs →
      ∃ (LentU : Fin 4 → Finset (Sym2 V)) (D : Fin 4 → List (Obj V)),
        (∀ c, Disjoint (LentU c) (bundleEdges ω l arcs c)) ∧
        (∀ c, IsDecomp ((bundleEdges ω l arcs c ∪ LentU c : Finset (Sym2 V)) : Set (Sym2 V))
          (D c)) ∧
        (∀ c, LentU c ⊆ lentUAvail ω l c) ∧
        ((∑ c, (D c).length : ℕ) : ℝ) ≤ pbound G run l ∧
        (∀ c c', c ≠ c' → Disjoint (LentU c) (LentU c'))

/-- An available U-lent edge of round `l` is an edge of a U-lent class of a good parent of round
`≤ l − 2`, hence an edge of that parent's edge set. -/
theorem exists_of_mem_lentUAvail {ω : Outcome G run} {l : ℕ} {c : Fin 4} {e : Sym2 V} (he : e ∈ lentUAvail ω l c) :
    ∃ Y ∈ goodParents ω l, ∃ σ, e ∈ (LU G run Y (ω.colAt Y) l c σ).edges := by
  simp only [lentUAvail, Finset.mem_biUnion, Finset.mem_range] at he
  obtain ⟨Y, hY, σ, -, he⟩ := he
  exact ⟨Y, hY, σ, he⟩

theorem goodParents_sub {ω : Outcome G run} {l : ℕ} {Y : PartId} (hY : Y ∈ goodParents ω l) :
    Y ∈ run.lightParts G ∧ ¬ demoted ω Y ∧ Y.1 + 2 ≤ l := by
  obtain ⟨⟨h1, h2, -⟩, h3⟩ := (mem_goodParents ω).1 hY
  exact ⟨h1, h2, h3⟩

namespace KHyp

variable {ω : Outcome G run} {Lext : PartId → Finset (Sym2 V)} (h : KHyp ω Lext)
include h

theorem Lext_subset {Y : PartId} (hY : Y ∈ run.lightParts G) : Lext Y ⊆ run.E G Y.1 Y.2 :=
  ((h.lext Y hY).1.trans (lentJSJV_subset_ancGraph ω Y)).trans (h.ancE Y hY)

/-- The available U-lent edges of round `l` avoid the edge set of every light part that is not a
good parent of round `≤ l − 2`. -/
theorem disjoint_lentUAvail_E {l : ℕ} {c : Fin 4} {Z : PartId} (hZ : Z ∈ run.lightParts G)
    (hZg : Z ∉ goodParents ω l) : Disjoint (lentUAvail ω l c) (run.E G Z.1 Z.2) := by
  rw [Finset.disjoint_left]
  intro e he heZ
  obtain ⟨Y, hY, σ, heY⟩ := exists_of_mem_lentUAvail he
  have hYl := (goodParents_sub hY).1
  have heY' : e ∈ run.E G Y.1 Y.2 := h.ancE Y hYl (LU_edges_subset Y _ l c σ heY)
  by_cases hYZ : Y = Z
  · exact hZg (hYZ ▸ hY)
  · exact Finset.disjoint_left.1 (h.disjE Y hYl Z hZ hYZ) heY' heZ

theorem disjoint_lentUAvail_E_of_lt {l : ℕ} {c : Fin 4} {Z : PartId} (hZ : Z ∈ run.lightParts G)
    (hlt : l < Z.1 + 2) : Disjoint (lentUAvail ω l c) (run.E G Z.1 Z.2) :=
  h.disjoint_lentUAvail_E hZ fun hg => by have := (goodParents_sub hg).2.2; omega

theorem disjoint_lentUAvail_E_of_demoted {l : ℕ} {c : Fin 4} {Z : PartId}
    (hZ : Z ∈ run.lightParts G) (hd : demoted ω Z) :
    Disjoint (lentUAvail ω l c) (run.E G Z.1 Z.2) :=
  h.disjoint_lentUAvail_E hZ fun hg => (goodParents_sub hg).2.1 hd

/-- The available U-lent edges avoid `Own_Z` for every light part `Z`. -/
theorem disjoint_lentUAvail_Own {l : ℕ} {c : Fin 4} {Z : PartId} (hZ : Z ∈ run.lightParts G) :
    Disjoint (lentUAvail ω l c) (Own G run Z (ω.colAt Z)).edges := by
  rw [Finset.disjoint_left]
  intro e he heZ
  obtain ⟨Y, hY, σ, heY⟩ := exists_of_mem_lentUAvail he
  have hYl := (goodParents_sub hY).1
  have heY' : e ∈ run.E G Y.1 Y.2 := h.ancE Y hYl (LU_edges_subset Y _ l c σ heY)
  have heZ' : e ∈ run.E G Z.1 Z.2 := h.ancE Z hZ (Own_edges_subset G run Z _ heZ)
  by_cases hYZ : Y = Z
  · subst hYZ
    exact Finset.disjoint_left.1 (disjoint_Own_LU Y _ l c σ) heZ heY
  · exact Finset.disjoint_left.1 (h.disjE Y hYl Z hZ hYZ) heY' heZ'

/-- The available U-lent edges avoid every `Lent_ext(Y)`. -/
theorem disjoint_lentUAvail_Lext {l : ℕ} {c : Fin 4} {Z : PartId} (hZ : Z ∈ run.lightParts G) :
    Disjoint (lentUAvail ω l c) (Lext Z) := by
  rw [Finset.disjoint_left]
  intro e he heZ
  obtain ⟨Y, hY, σ, heY⟩ := exists_of_mem_lentUAvail he
  have hYl := (goodParents_sub hY).1
  have heY' : e ∈ run.E G Y.1 Y.2 := h.ancE Y hYl (LU_edges_subset Y _ l c σ heY)
  have heZ' : e ∈ run.E G Z.1 Z.2 := h.Lext_subset hZ heZ
  by_cases hYZ : Y = Z
  · subst hYZ
    exact Finset.disjoint_left.1 (disjoint_LU_lentJSJV ω Y l c σ) heY ((h.lext Y hZ).1 heZ)
  · exact Finset.disjoint_left.1 (h.disjE Y hYl Z hZ hYZ) heY' heZ'

/-- An available U-lent edge lies in `E_{r(Y)}(Y) \ Lent_ext(Y)` for a light part `Y`. -/
theorem mem_E_sdiff_of_mem_lentUAvail {l : ℕ} {c : Fin 4} {e : Sym2 V}
    (he : e ∈ lentUAvail ω l c) :
    ∃ Y ∈ run.lightParts G, e ∈ run.E G Y.1 Y.2 \ Lext Y := by
  obtain ⟨Y, hY, σ, heY⟩ := exists_of_mem_lentUAvail he
  have hYl := (goodParents_sub hY).1
  refine ⟨Y, hYl, Finset.mem_sdiff.2 ⟨h.ancE Y hYl (LU_edges_subset Y _ l c σ heY), ?_⟩⟩
  exact Finset.disjoint_left.1 (h.disjoint_lentUAvail_Lext hYl) he

end KHyp

/-! ### The long cycles -/

/-- The long cycles of a round `l ≤ R` of a valid run decompose `E(Cyc_l)` ((R1): well-formed
cycles with pairwise disjoint, duplicate-free edge lists). -/
theorem isDecomp_cycEdges {Dstar : ℝ} (hv : run.Valid G Dstar) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 run.R) :
    IsDecomp ((run.cycEdges l : Finset (Sym2 V)) : Set (Sym2 V)) ((run.cycles l).map Obj.cycle) := by
  have hR : run.IsRound l := Finset.mem_Icc.1 hl
  have hV := (hv.round run G hR).1
  have hc : run.cycles l = (run.choice l).cycles := by simp [Run.cycles, hR]
  have hfl : ((run.cycles l).map Obj.cycle).flatMap Obj.edges = (run.cycles l).flatMap cycleEdges := by
    rw [List.flatMap_map]; rfl
  refine ⟨?_, ?_, fun e => ?_⟩
  · intro o ho
    obtain ⟨cyc, hcyc, rfl⟩ := List.mem_map.1 ho
    rw [hc] at hcyc
    exact (hV.1 cyc hcyc).1
  · rw [hfl, hc]; exact hV.2.1
  · rw [hfl, Run.cycEdges, Finset.mem_coe, List.mem_toFinset]

end EG.Light
