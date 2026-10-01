module

public import EG.Spec.HB.Parentless
public import EG.Lib.HB.Fresh
public import EG.Proof.HB.Structure

/-!
# P3 stub: `EG.Spec.FreshStatement` (s2:propParentless)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.Fresh`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propParentless] see `EG.Spec.FreshStatement`. -/
theorem Fresh : EG.Spec.FreshStatement := by
  classical
  intro V _ G Dstar run hv
  have hStdP : ∀ l a, a ∈ run.Std G l → a ∈ run.prePartAddrs G l :=
    fun l a ha => ((EG.HB.Run.mem_Std_iff run G).1 ha).1
  have hportsZ : ∀ l a x, x ∈ run.ports G l a → x ∈ run.Z0 G l a :=
    fun l a x hx => (Finset.mem_sdiff.1 hx).1
  have hfreshP : ∀ l a x, x ∈ run.fresh G l a → x ∈ run.ports G l a :=
    fun l a x hx => (Finset.mem_filter.1 hx).1
  -- (i), first sentence
  have hA : ∀ r ∈ Finset.Icc 1 run.R, ∀ x : V,
      (∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a) →
      ∃ a : EG.HB.Addr, run.home G r x = some a ∧ a ∈ run.prePartAddrs G r ∧
        (r, a) ∈ run.ancestors G ∧ x ∈ run.ancVerts G (r, a) ∧
        (run.isLight G r a → x ∈ run.Z0 G r a \ run.guests G r a) ∧
        (¬ run.isLight G r a → x ∈ run.Z0 G r a) := by
    intro r hr x hx
    obtain ⟨a, h1, h2, h3, h4, h5⟩ := EG.HB.Run.home_mem_partVerts hv (Finset.mem_Icc.1 hr) hx
    exact ⟨a, h1, h2, (EG.HB.Run.mem_ancestors run G).2 h2, h3, h4, h5⟩
  -- fresh ports
  have hB : ∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.Std G l, ∀ x ∈ run.ports G l a,
      (x ∈ run.fresh G l a ↔ (l : WithTop ℕ) ≤ run.j0 G x + 1) := by
    intro l _ a ha x hx
    unfold EG.HB.Run.fresh
    rw [Finset.mem_filter]
    rw [← EG.HB.Run.anc_eq_empty_iff hv (hStdP l a ha) (hportsZ l a x hx)]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hC : ∀ l ∈ Finset.Icc 1 run.R, ∀ x : V,
      ((run.Std G l).filter (fun a => x ∈ run.ports G l a)).card ≤ 1 := by
    intro l hl x
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hne
    exact Finset.disjoint_left.1 ((EG.structureVertex V G Dstar run hv l hl).2.2.2.1 a ha.1 b hb.1
      hne) ha.2 hb.2
  have hD : ∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.Std G l, ∀ x ∈ run.fresh G l a,
      run.j0 G x = (l : WithTop ℕ) ∨ run.j0 G x + 1 = (l : WithTop ℕ) := by
    intro l hl a ha x hx
    have hxp := hfreshP l a x hx
    have hle := (hB l hl a ha x hxp).1 hx
    have hj := EG.HB.Run.j0_le (Finset.mem_Icc.1 hl) (hStdP l a ha) (hportsZ l a x hxp)
    obtain ⟨m, hm, -, -⟩ := EG.HB.Run.exists_j0 (run := run) (G := G)
      ⟨l, a, hStdP l a ha, hportsZ l a x hxp⟩
    rw [hm] at hle hj ⊢
    have h1 : m ≤ l := by exact_mod_cast hj
    have h2 : l ≤ m + 1 := by exact_mod_cast hle
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · left; rw [h]
    · right; have : m + 1 = l := by omega
      rw [← this]; push_cast; rfl
  refine ⟨hA, hB, hC, hD, ?_⟩
  -- (K4)
  have hfV : ∀ l a, run.fresh G l a ⊆ G.verts := fun l a x hx =>
    EG.HB.Run.Z0_subset_verts run G l a (hportsZ l a x (hfreshP l a x hx))
  have hsum : ∀ l, ∑ a ∈ run.Std G l, (run.fresh G l a).card =
      ∑ x ∈ G.verts, ((run.Std G l).filter (fun a => x ∈ run.fresh G l a)).card := by
    intro l
    rw [← EG.HB.sum_card_inter_eq]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.inter_eq_left.2 (hfV l a)]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  calc ∑ x ∈ G.verts, ∑ l ∈ Finset.Icc 1 run.R,
        ((run.Std G l).filter (fun a => x ∈ run.fresh G l a)).card
      ≤ ∑ _x ∈ G.verts, 2 := by
        apply Finset.sum_le_sum
        intro x _
        set f : ℕ → ℕ := fun l => ((run.Std G l).filter (fun a => x ∈ run.fresh G l a)).card
        have hf1 : ∀ l ∈ Finset.Icc 1 run.R, f l ≤ 1 := by
          intro l hl
          refine le_trans (Finset.card_le_card ?_) (hC l hl x)
          intro a ha
          rw [Finset.mem_filter] at ha ⊢
          exact ⟨ha.1, hfreshP l a x ha.2⟩
        rw [← Finset.sum_filter_ne_zero]
        calc ∑ l ∈ (Finset.Icc 1 run.R).filter (fun l => f l ≠ 0), f l
            ≤ ∑ _l ∈ (Finset.Icc 1 run.R).filter (fun l => f l ≠ 0), 1 :=
              Finset.sum_le_sum (fun l hl => hf1 l (Finset.mem_filter.1 hl).1)
          _ = ((Finset.Icc 1 run.R).filter (fun l => f l ≠ 0)).card := by simp
          _ ≤ 2 := by
            by_cases hx : ∃ r, ∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a
            · obtain ⟨m, hm, -, -⟩ := EG.HB.Run.exists_j0 hx
              have hsub : (Finset.Icc 1 run.R).filter (fun l => f l ≠ 0) ⊆ {m, m + 1} := by
                intro l hl
                rw [Finset.mem_filter] at hl
                obtain ⟨a, ha⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hl.2)
                rw [Finset.mem_filter] at ha
                have := hD l hl.1 a ha.1 x ha.2
                rw [hm] at this
                rw [Finset.mem_insert, Finset.mem_singleton]
                rcases this with h | h
                · left; exact_mod_cast h.symm
                · right; have : m + 1 = l := by exact_mod_cast h
                  exact this.symm
              exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
            · have hemp : (Finset.Icc 1 run.R).filter (fun l => f l ≠ 0) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro l _ hl
                obtain ⟨a, ha⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hl)
                rw [Finset.mem_filter] at ha
                exact hx ⟨l, a, hStdP l a ha.1, hportsZ l a x (hfreshP l a x ha.2)⟩
              rw [hemp]; simp
    _ = 2 * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm, EG.FGraph.card_def]

end EG.Todo
