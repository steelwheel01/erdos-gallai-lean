module

public import EG.Lib.HB.StructureAux
public import EG.Lib.HB.OVRound

/-!
# Helpers for Proposition s2:propParentless (i) (manuscript s2:propParentless)

Helper lemmas for `EG.Todo.Fresh` (unit P3-s2):
* `Run.home_mem_partVerts`: "If `x` lies in a round-`r` pre-part, then `H := home_r(x)` is an
  ancestor of round `r` containing `x`";
* `Run.j0_le`, `Run.exists_j0`: `j_0(x)` is at most every round in which `x` lies in a pre-part,
  and is attained;
* `Run.anc_eq_empty_iff`: "for `Z ∈ Std_l` and `x ∈ U_Z`, `x ∈ F_Z` iff `j_0(x) ≥ l - 1`".
-/

public section

namespace EG.HB

variable {V : Type*} [DecidableEq V]

namespace Run

variable {run : Run V} {G : FGraph V}

theorem home_mem_partVerts {Dstar : ℝ} (hv : run.Valid G Dstar) {r : ℕ} (hr : run.IsRound r)
    {x : V} (hx : ∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a) :
    ∃ a : Addr, run.home G r x = some a ∧ a ∈ run.prePartAddrs G r ∧
      x ∈ run.partVerts G r a ∧ (run.isLight G r a → x ∈ run.Z0 G r a \ run.guests G r a) ∧
      (¬ run.isLight G r a → x ∈ run.Z0 G r a) := by
  classical
  have hval : Round.Valid (run.graph G r) (run.choice r) := (hv.1 r (Finset.mem_Icc.2 hr)).2
  rw [prePartAddrs_of_isRound run G hr] at hx ⊢
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb⟩ := Round.home_isSome _ _ hval ha hxa
  obtain ⟨hbP, hxb⟩ := Round.home_spec _ _ hb
  have hnotS : x ∉ run.guests G r b := by
    intro hS
    unfold guests Round.guests at hS
    rw [Finset.mem_filter] at hS
    exact hS.2 hb
  refine ⟨b, hb, hbP, ?_, fun _ => Finset.mem_sdiff.2 ⟨hxb, hnotS⟩, fun _ => hxb⟩
  change x ∈ Round.partVerts _ _ b
  unfold Round.partVerts
  split_ifs
  · exact Finset.mem_sdiff.2 ⟨hxb, hnotS⟩
  · exact hxb

theorem j0_le {r : ℕ} (hr : run.IsRound r) {a : Addr} (ha : a ∈ run.prePartAddrs G r) {x : V}
    (hx : x ∈ run.Z0 G r a) : run.j0 G x ≤ (r : WithTop ℕ) := by
  unfold j0
  exact Finset.min_le (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hr, a, ha, hx⟩)

theorem exists_j0 {x : V} (hx : ∃ r, ∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a) :
    ∃ m : ℕ, run.j0 G x = (m : WithTop ℕ) ∧ run.IsRound m ∧
      ∃ a ∈ run.prePartAddrs G m, x ∈ run.Z0 G m a := by
  obtain ⟨r, a, ha, hxa⟩ := hx
  have hr := isRound_of_mem_prePartAddrs ha
  obtain ⟨m, hm⟩ := Finset.min_of_mem
    (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hr, a, ha, hxa⟩ :
      r ∈ (Finset.Icc 1 run.R).filter (fun r => ∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a))
  have hmem := Finset.mem_of_min hm
  rw [Finset.mem_filter] at hmem
  exact ⟨m, hm, Finset.mem_Icc.1 hmem.1, hmem.2⟩

theorem anc_eq_empty_iff {Dstar : ℝ} (hv : run.Valid G Dstar) {l : ℕ} {a : Addr}
    (ha : a ∈ run.prePartAddrs G l) {x : V} (hx : x ∈ run.Z0 G l a) :
    run.anc G l x = ∅ ↔ (l : WithTop ℕ) ≤ run.j0 G x + 1 := by
  obtain ⟨m, hm, hmr, hmx⟩ := exists_j0 (run := run) (G := G) ⟨l, a, ha, hx⟩
  have key : ((l : WithTop ℕ) ≤ (m : WithTop ℕ) + 1) ↔ l ≤ m + 1 := by norm_cast
  rw [hm, key]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨a0, -, ha0, hx0, -, -⟩ := home_mem_partVerts hv hmr hmx
    have hmem : (m, a0) ∈ run.anc G l x :=
      (mem_anc run G).2 ⟨(mem_ancestors run G).2 ha0, by simp only; omega, hx0⟩
    rw [h] at hmem
    simp at hmem
  · intro hle
    rw [Finset.eq_empty_iff_forall_notMem]
    intro Y hY
    obtain ⟨hYa, hYl, hxY⟩ := (mem_anc run G).1 hY
    have hYp := (mem_ancestors run G).1 hYa
    have hYr := isRound_of_mem_prePartAddrs hYp
    have hxZ : x ∈ run.Z0 G Y.1 Y.2 := partVerts_subset_Z0 run G Y.1 Y.2 hxY
    have := j0_le hYr hYp hxZ
    rw [hm] at this
    have : m ≤ Y.1 := by exact_mod_cast this
    omega

open Classical in
theorem j1_le {r : ℕ} (hr : run.IsRound r) {a : Addr} (ha : a ∈ run.prePartAddrs G r)
    (hl : run.isLight G r a) {x : V} (hx : x ∈ run.partVerts G r a) :
    run.j1 G x ≤ (r : WithTop ℕ) := by
  unfold j1
  exact Finset.min_le (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hr, a, ha, hl, hx⟩)

open Classical in
theorem exists_j1 {x : V}
    (hx : ∃ r, ∃ a ∈ run.prePartAddrs G r, run.isLight G r a ∧ x ∈ run.partVerts G r a) :
    ∃ m : ℕ, run.j1 G x = (m : WithTop ℕ) ∧ run.IsRound m ∧
      ∃ a ∈ run.prePartAddrs G m, run.isLight G m a ∧ x ∈ run.partVerts G m a := by
  obtain ⟨r, a, ha, hl, hxa⟩ := hx
  have hr := isRound_of_mem_prePartAddrs ha
  obtain ⟨m, hm⟩ := Finset.min_of_mem
    (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hr, a, ha, hl, hxa⟩ :
      r ∈ (Finset.Icc 1 run.R).filter
        (fun r => ∃ a ∈ run.prePartAddrs G r, run.isLight G r a ∧ x ∈ run.partVerts G r a))
  have hmem := Finset.mem_of_min hm
  rw [Finset.mem_filter] at hmem
  exact ⟨m, hm, Finset.mem_Icc.1 hmem.1, hmem.2⟩

end Run

end EG.HB
