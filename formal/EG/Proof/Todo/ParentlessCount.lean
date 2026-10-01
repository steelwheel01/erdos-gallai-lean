module

public import EG.Spec.HB.Parentless
public import EG.Lib.HB.Fresh
public import EG.Proof.HB.Structure

/-!
# P3 stub: `EG.Spec.ParentlessCountStatement` (s2:propParentless)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.ParentlessCount`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propParentless] see `EG.Spec.ParentlessCountStatement`. -/
theorem ParentlessCount : EG.Spec.ParentlessCountStatement := by
  classical
  intro V _ G Dstar run hv Bad
  have hLP : ∀ Z ∈ run.lightParts G, Z.2 ∈ run.prePartAddrs G Z.1 ∧ run.isLight G Z.1 Z.2 ∧
      run.IsRound Z.1 := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := (EG.HB.Run.mem_lightParts run G).1 hZ
    exact ⟨h1, h2, EG.HB.Run.isRound_of_mem_prePartAddrs h1⟩
  -- a vertex lies in at most one light part per round
  have huniq : ∀ v : V, ∀ Z ∈ run.lightParts G, ∀ Z' ∈ run.lightParts G,
      v ∈ run.ancVerts G Z → v ∈ run.ancVerts G Z' → Z.1 = Z'.1 → Z = Z' := by
    intro v Z hZ Z' hZ' hvZ hvZ' h1
    obtain ⟨hZp, hZl, hZr⟩ := hLP Z hZ
    obtain ⟨hZ'p, hZ'l, -⟩ := hLP Z' hZ'
    have hc := (EG.structureVertex V G Dstar run hv Z.1 (Finset.mem_Icc.2 hZr)).2.2.2.2.2 v
    rw [h1] at hc
    have h2 : Z.2 = Z'.2 := by
      have hvZ2 : v ∈ run.partVerts G Z'.1 Z.2 := h1 ▸ hvZ
      rw [h1] at hZp hZl
      exact Finset.card_le_one.1 hc Z.2 (Finset.mem_filter.2 ⟨hZp, hZl, hvZ2⟩) Z'.2
        (Finset.mem_filter.2 ⟨hZ'p, hZ'l, hvZ'⟩)
    exact Prod.ext h1 h2
  -- the characterization of parentless pairs
  have hchar : ∀ Z ∈ run.lightParts G, ∀ v ∈ run.ancVerts G Z,
      (¬ ∃ Y ∈ run.lightParts G, Y ∉ Bad ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y) →
      ∃ m : ℕ, run.j1 G v = (m : WithTop ℕ) ∧ m ≤ Z.1 ∧
        (Z.1 = m ∨ Z.1 = m + 1 ∨
          (m + 2 ≤ Z.1 ∧ ∃ Y ∈ Bad, Y ∈ run.lightParts G ∧ Y.1 = m ∧ v ∈ run.ancVerts G Y)) := by
    intro Z hZ v hvZ hpl
    obtain ⟨hZp, hZl, hZr⟩ := hLP Z hZ
    obtain ⟨m, hm, -, a1, ha1, hl1, hv1⟩ := EG.HB.Run.exists_j1 (run := run) (G := G)
      ⟨Z.1, Z.2, hZp, hZl, hvZ⟩
    have hle := EG.HB.Run.j1_le hZr hZp hZl hvZ
    rw [hm] at hle
    have hmZ : m ≤ Z.1 := by exact_mod_cast hle
    refine ⟨m, hm, hmZ, ?_⟩
    by_cases h2 : m + 2 ≤ Z.1
    · right; right
      refine ⟨h2, (m, a1), ?_, (EG.HB.Run.mem_lightParts run G).2 ⟨ha1, hl1⟩, rfl, hv1⟩
      by_contra hnot
      exact hpl ⟨(m, a1), (EG.HB.Run.mem_lightParts run G).2 ⟨ha1, hl1⟩, hnot, h2, hv1⟩
    · omega
  refine ⟨?_, fun Z hZ v hvZ hpl => ?_⟩
  swap
  · obtain ⟨m, hm, -, h⟩ := hchar Z hZ v hvZ hpl
    rw [hm]
    rcases h with h | h | ⟨h2, Y, hY, hYl, hYm, hvY⟩
    · left; rw [h]
    · right; left; rw [h]; push_cast; rfl
    · right; right
      refine ⟨by exact_mod_cast h2, Y, hY, hYl, by rw [hYm], hvY⟩
  -- the count
  have hAV : ∀ Z, run.ancVerts G Z ⊆ G.verts := fun Z =>
    (EG.HB.Run.partVerts_subset_Z0 run G Z.1 Z.2).trans (EG.HB.Run.Z0_subset_verts run G Z.1 Z.2)
  set PL : EG.HB.PartId → V → Prop := fun Z v =>
    ¬ ∃ Y ∈ run.lightParts G, Y ∉ Bad ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y with hPL
  have hdc : ∑ Z ∈ run.lightParts G, ((run.ancVerts G Z).filter (fun v => PL Z v)).card =
      ∑ v ∈ G.verts, ((run.lightParts G).filter
        (fun Z => v ∈ run.ancVerts G Z ∧ PL Z v)).card := by
    have h1 : ∀ Z ∈ run.lightParts G, ((run.ancVerts G Z).filter (fun v => PL Z v)).card =
        ∑ v ∈ G.verts, if v ∈ run.ancVerts G Z ∧ PL Z v then 1 else 0 := by
      intro Z _
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨hAV Z h1, h1, h2⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_boole]; simp
  have hpv : ∀ v ∈ G.verts, ((run.lightParts G).filter (fun Z => v ∈ run.ancVerts G Z ∧ PL Z v)).card
      ≤ 2 + ∑ Y ∈ Bad.filter (fun Y => v ∈ run.ancVerts G Y), (run.R - Y.1) := by
    intro v _
    set S := (run.lightParts G).filter (fun Z => v ∈ run.ancVerts G Z ∧ PL Z v) with hS
    by_cases hne : S.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
    obtain ⟨Z0, hZ0⟩ := hne
    rw [Finset.mem_filter] at hZ0
    obtain ⟨m, hm, -, -⟩ := hchar Z0 hZ0.1 v hZ0.2.1 hZ0.2.2
    have hinj : Set.InjOn (fun Z : EG.HB.PartId => Z.1) (S : Set EG.HB.PartId) := by
      intro Z hZ Z' hZ' h
      rw [Finset.mem_coe, Finset.mem_filter] at hZ hZ'
      exact huniq v Z hZ.1 Z' hZ'.1 hZ.2.1 hZ'.2.1 h
    have hround : ∀ Z ∈ S, m ≤ Z.1 ∧ Z.1 ≤ run.R ∧ (Z.1 = m ∨ Z.1 = m + 1 ∨
        (m + 2 ≤ Z.1 ∧ ∃ Y ∈ Bad, Y ∈ run.lightParts G ∧ Y.1 = m ∧ v ∈ run.ancVerts G Y)) := by
      intro Z hZ
      rw [Finset.mem_filter] at hZ
      obtain ⟨m', hm', hle, h⟩ := hchar Z hZ.1 v hZ.2.1 hZ.2.2
      rw [hm] at hm'
      have hmm : m = m' := by exact_mod_cast hm'
      subst hmm
      exact ⟨hle, (hLP Z hZ.1).2.2.2, h⟩
    by_cases hbad : ∃ Y ∈ Bad, Y ∈ run.lightParts G ∧ Y.1 = m ∧ v ∈ run.ancVerts G Y
    · obtain ⟨Y, hY, hYl, hYm, hvY⟩ := hbad
      have h1 : S.card ≤ (Finset.Icc m run.R).card := by
        refine Finset.card_le_card_of_injOn (fun Z : EG.HB.PartId => Z.1) (fun Z hZ => ?_) hinj
        obtain ⟨h1, h2, -⟩ := hround Z hZ
        exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨h1, h2⟩)
      have h2 : run.R - Y.1 ≤ ∑ Y ∈ Bad.filter (fun Y => v ∈ run.ancVerts G Y), (run.R - Y.1) :=
        Finset.single_le_sum (f := fun Y : EG.HB.PartId => run.R - Y.1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.2 ⟨hY, hvY⟩)
      rw [Nat.card_Icc] at h1
      omega
    · have h1 : S.card ≤ ({m, m + 1} : Finset ℕ).card := by
        refine Finset.card_le_card_of_injOn (fun Z : EG.HB.PartId => Z.1) (fun Z hZ => ?_) hinj
        obtain ⟨-, -, h⟩ := hround Z hZ
        rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
        rcases h with h | h | ⟨-, h⟩
        · left; exact h
        · right; exact h
        · exact absurd h hbad
      have := Finset.card_le_two (a := m) (b := m + 1)
      omega
  rw [hdc]
  calc ∑ v ∈ G.verts, ((run.lightParts G).filter (fun Z => v ∈ run.ancVerts G Z ∧ PL Z v)).card
      ≤ ∑ v ∈ G.verts, (2 + ∑ Y ∈ Bad.filter (fun Y => v ∈ run.ancVerts G Y), (run.R - Y.1)) :=
        Finset.sum_le_sum hpv
    _ = 2 * G.card + ∑ v ∈ G.verts, ∑ Y ∈ Bad.filter (fun Y => v ∈ run.ancVerts G Y),
          (run.R - Y.1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, EG.FGraph.card_def]
    _ = 2 * G.card + ∑ Y ∈ Bad, (run.ancVerts G Y).card * (run.R - Y.1) := by
        congr 1
        rw [Finset.sum_comm' (t' := Bad) (s' := fun Y => (run.ancVerts G Y))]
        · apply Finset.sum_congr rfl
          intro Y _
          rw [Finset.sum_const, smul_eq_mul]
        · intro v Y
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨-, hY, hvY⟩; exact ⟨hvY, hY⟩
          · rintro ⟨hvY, hY⟩; exact ⟨hAV Y hvY, hY, hvY⟩

end EG.Todo
