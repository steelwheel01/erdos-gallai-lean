module

public import EG.Spec.HB.Exists
public import EG.Lib.HB.Exists
public import EG.Proof.Todo.RoundTauTerm

/-!
# P3 stub: `EG.Spec.RoundExistsStatement` (s2:propExists)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundExists`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propExists] see `EG.Spec.RoundExistsStatement`. -/
theorem RoundExists : EG.Spec.RoundExistsStatement := by
  classical
  intro V _ H Dstar hD hdD
  -- (R1): a maximal family of long cycles
  obtain ⟨cyc, hcyc⟩ := EG.HB.Round.exists_cyclesValid H
  -- witness rules
  have hwit : ∀ (s : ℝ) (K : FGraph V), ¬ K.IsExpander EG.epsC s →
      ∃ p : Finset V × Finset (Sym2 V), EG.HB.IsWitness K EG.epsC s p.1 p.2 := by
    intro s K hK
    obtain ⟨U, F, hw⟩ := (EG.HB.not_isExpander_iff_exists_isWitness K EG.epsC s).1 hK
    exact ⟨(U, F), hw⟩
  let Wr : ℝ → EG.HB.Addr → FGraph V → Finset V × Finset (Sym2 V) := fun s _ K =>
    if h : ¬ K.IsExpander EG.epsC s then Classical.choose (hwit s K h) else (∅, ∅)
  have hWr : ∀ (s : ℝ) (a : EG.HB.Addr) (K : FGraph V), ¬ K.IsExpander EG.epsC s →
      EG.HB.IsWitness K EG.epsC s (Wr s a K).1 (Wr s a K).2 := by
    intro s a K hK
    simp only [Wr, dif_pos hK]
    exact Classical.choose_spec (hwit s K hK)
  -- (R3), first level
  let c0 : EG.HB.RoundChoice V := ⟨cyc, .nil, fun _ => .nil, []⟩
  let G' := EG.HB.Round.graph' H c0
  let tree := EG.HB.STree.s0Build EG.epsC (Wr 0) G'.card [] G'
  obtain ⟨hS0, hstop, -⟩ := EG.HB.STree.s0Build_spec (Wr 0) (fun a K hK => by
    have := hWr 0 a K hK; simpa using this) G'.card [] G' le_rfl
  let c1 : EG.HB.RoundChoice V := ⟨cyc, tree, fun _ => .nil, []⟩
  have hcyc1 : EG.HB.Round.CyclesValid H c1 := hcyc
  -- (R3), second level: the `τ`-runs of the big pieces
  have htau := fun q (hq : q ∈ EG.HB.Round.bigPieceAddrs H c1) =>
    (EG.Todo.RoundTauTerm V H c1 Dstar hD hdD hcyc1 hS0 hstop q hq).2.2.2
      (Wr (EG.HB.sOf (EG.HB.Round.d H))) (fun a K hK => hWr _ a K hK)
  let tr : EG.HB.Addr → EG.HB.STree V := fun q =>
    if hq : q ∈ EG.HB.Round.bigPieceAddrs H c1 then Classical.choose (htau q hq) else .nil
  let c2 : EG.HB.RoundChoice V := ⟨cyc, tree, tr, []⟩
  let c : EG.HB.RoundChoice V := ⟨cyc, tree, tr, (EG.HB.Round.prePartAddrs H c2).toList⟩
  refine ⟨c, hcyc, hS0, hstop, ?_, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  intro a ha hP
  have hq : a ∈ EG.HB.Round.bigPieceAddrs H c1 := Finset.mem_filter.2 ⟨ha, hP⟩
  have e : c.tauRun a = Classical.choose (htau a hq) := by
    show tr a = _
    simp only [tr, dif_pos hq]
  rw [e]
  exact (Classical.choose_spec (htau a hq)).1

end EG.Todo
