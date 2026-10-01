module

public import EG.Lib.Vortex.TPVStep
public import EG.Lib.Vortex.PVAux
public import EG.Proof.Vortex.PVCore
public import EG.Defs.Probe.P4A.PVHyp

/-!
# One step of the PV run (manuscript s4:lemPV, proof, "The process", "Step `j`" (i)–(vi), "The
invariants persist", "Cost of step `j`")

Unit P3-s4. The deterministic part of the proof of Lemma PV for fixed labels in the good event
`𝒢_PV` (the properties (G2), (G4) and the multiplicity bound of the sets `A(w)` are the
hypotheses `EG.PVRun.Good`). The run sets are those of the TPV run with `P := Pl`:

* `U_j = Rt ∪ {v ∈ Pl : lev(v) ≥ j}` is `EG.TPVRun.U Z Pl lev j` (inside `Z = Rt ⊔ Pl`),
* `W_j = {v ∈ Pl : lev(v) = j}` is `EG.TPVRun.Wt Pl lev j`,
* `Z_j = {u ∈ U_{j+1} : κ(u) = 0}` (`EG.PVRun.Zr`),
* `V_{j,c} = {u ∈ U_{j+1} : κ(u) = c}` (`EG.PVRun.Vc`; phases `c : Fin 4` ↔ `κ = c.succ`,
  `κ : Fin 5`).

The state before step `j` is the set `S` of used edges; `H_j = H_0 \ S`. The invariants
(Inv1)–(Inv3) are `EG.PVRun.Inv`.

The phases of one step are handled by P4A's engine `EG.pvStepPhase` (steps (iv), (v), the arcs
of (vi) and the cost analysis; `EG/Proof/Vortex/PVCore.lean`), the closing of the non-arc paths
by `EG.TPVRun.close_class` ((G2) and observation (C)).

Main result: `EG.PVRun.step` (one step: the edges used, split into the objects part, decomposed
into at most `28|Pl ∩ U_j|` objects, and the arcs, at most `4N` of them, and the invariants for
`j + 1`).
-/

public section

namespace EG

namespace PVRun

open List

variable {V : Type*} [DecidableEq V]

section Sets

variable (Z Pl : Finset V) (lev : V → ℕ) (kap : V → Fin 5)

/-- `Z_j := {u ∈ U_{j+1} : κ(u) = 0}`. -/
@[expose] def Zr (j : ℕ) : Finset V := (TPVRun.U Z Pl lev (j + 1)).filter fun v => kap v = 0

/-- `V_{j,c} := {u ∈ U_{j+1} : κ(u) = c}` (phase `c : Fin 4` is the label `c.succ`). -/
@[expose] def Vc (j : ℕ) (c : Fin 4) : Finset V :=
  (TPVRun.U Z Pl lev (j + 1)).filter fun v => kap v = c.succ

end Sets

/-- `C_w := {wu : u ∈ A(w), wu ∈ E(M), ext(u) = *}`, by its far ends `u`. -/
@[expose] def Cw (D : Vortex.PVData V) (w : V) : Finset V :=
  (D.A w).filter fun u => s(w, u) ∈ D.M.edges ∧ D.ext u = none

/-- The hypotheses of the deterministic run: the hypotheses of Lemma PV and labels in the good
event ((G2), (G4)) with the multiplicity bound `b + 2 ≤ t` of the sets `A(w)`. -/
structure Good (D : Vortex.PVData V) (lev : V → ℕ) (kap : V → Fin 5) (ℓ t : ℝ) : Prop where
  hyp : Vortex.PVHyp D
  G2 : ∀ i : Fin (Vortex.pvJ D.Z.card) × Fin 4,
    (D.R i).IsPathConnected ℓ t (Vc D.Z D.Pl lev kap i.1 i.2)
  G4 : ∀ j < Vortex.pvJ D.Z.card, ∀ w ∈ D.Pl,
    8 ≤ ((Cw D w).filter fun u => u ∈ Zr D.Z D.Pl lev kap j).card
  mult : ∀ v : V, ((D.Z.filter fun w => v ∈ D.A w).card : ℝ) + 2 ≤ t

/-- The invariants (Inv1)–(Inv3) before step `j`, for the set `S` of used edges. -/
@[expose] def Inv (D : Vortex.PVData V) (lev : V → ℕ) (H0 : Finset (Sym2 V)) (j : ℕ)
    (S : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ H0, e ∉ S → ∀ v ∈ e, v ∈ TPVRun.U D.Z D.Pl lev j) ∧
  (∀ i : Fin (Vortex.pvJ D.Z.card) × Fin 4, j ≤ (i.1 : ℕ) → ∀ e ∈ (D.R i).edges,
    (∀ v ∈ e, v ∈ TPVRun.U D.Z D.Pl lev ((i.1 : ℕ) + 1)) → e ∉ S) ∧
  (∀ j', j ≤ j' → j' < Vortex.pvJ D.Z.card → ∀ w ∈ TPVRun.Wt D.Pl lev j',
    ∀ u ∈ TPVRun.U D.Z D.Pl lev (j' + 1), s(w, u) ∈ D.M.edges → s(w, u) ∉ S)

/-- The arc conditions of Lemma PV (b): both ends in `Rt`, and `ext ≠ c` on every vertex of a
phase-`c` arc. -/
@[expose] def ArcOK (D : Vortex.PVData V) (a : List V × Fin 4) : Prop :=
  (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ D.Rt) ∧ ∀ x ∈ a.1, D.ext x ≠ some a.2

/-- The invariants hold before step `0` with nothing used. -/
theorem inv_zero {D : Vortex.PVData V} {lev : V → ℕ} {H0 : Finset (Sym2 V)}
    (hH : Vortex.PVAdm D H0) : Inv D lev H0 0 ∅ :=
  ⟨fun e he _ v hv => TPVRun.mem_U.2 ⟨hH.2.1 e he v hv, Or.inr (Nat.zero_le _)⟩,
    fun _ _ _ _ _ h => Finset.notMem_empty _ h,
    fun _ _ _ _ _ _ _ _ h => Finset.notMem_empty _ h⟩

set_option maxHeartbeats 1000000 in
-- the proof assembles the four phases of a step; it is long but elementary
/-- [s4:lemPV] proof, "Step `j`" (i)–(vi), "The invariants persist", "Cost of step `j`" and the
step part of (c) ("At step `j`, each arc of phase `c` comes from a distinct path of
`Paths_{j,c}`, so there are at most `N` of them"). -/
theorem step {D : Vortex.PVData V} {lev : V → ℕ} {kap : V → Fin 5} {ℓ t : ℝ}
    (hg : Good D lev kap ℓ t) {H0 : Finset (Sym2 V)} (hH : Vortex.PVAdm D H0) {j : ℕ}
    (hj : j < Vortex.pvJ D.Z.card) {S : Finset (Sym2 V)} (hinv : Inv D lev H0 j S) :
    ∃ (Tobj Tarc : Finset (Sym2 V)) (Dl : List (Obj V)) (arcs : List (List V × Fin 4)),
      Disjoint Tobj Tarc ∧ Disjoint (Tobj ∪ Tarc) S ∧ Tobj ∪ Tarc ⊆ H0 ∧
      IsDecomp (Tobj : Set (Sym2 V)) Dl ∧
      Dl.length ≤ 28 * (D.Pl.filter fun v => j ≤ lev v).card ∧
      IsPathDecomp (Tarc : Set (Sym2 V)) (arcs.map Prod.fst) ∧ (∀ a ∈ arcs, ArcOK D a) ∧
      arcs.length ≤ 4 * D.Z.card ∧
      Inv D lev H0 (j + 1) (S ∪ (Tobj ∪ Tarc)) := by
  classical
  obtain ⟨hyp, hG2, hG4, hmult⟩ := hg
  obtain ⟨_, _, _, _, _, hRexp, hMZ, _, _, hRd, hRM, hRtPl, hZ, _⟩ := hyp
  obtain ⟨hHl, _, hMH, hRH⟩ := hH
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  -- notation
  set W := TPVRun.Wt D.Pl lev j with hWdef
  set Up := D.Pl.filter fun v => j + 1 ≤ lev v with hUpdef
  set Uc := TPVRun.U D.Z D.Pl lev (j + 1) with hUcdef
  set Pj := D.Pl.filter fun v => j ≤ lev v with hPjdef
  set ij : Fin (Vortex.pvJ D.Z.card) := ⟨j, hj⟩ with hijdef
  have hPlZ : D.Pl ⊆ D.Z := hZ ▸ Finset.subset_union_right
  have hRtZ : D.Rt ⊆ D.Z := hZ ▸ Finset.subset_union_left
  have hWPl : ∀ w ∈ W, w ∈ D.Pl := fun w hw => (TPVRun.mem_Wt.1 hw).1
  have hWUc : ∀ x ∈ Uc, x ∉ W := fun x hx => TPVRun.notWt_of_U hx
  have hmemUc : ∀ v, v ∈ Uc ↔ v ∈ D.Rt ∨ v ∈ Up := by
    intro v
    rw [hUcdef, TPVRun.mem_U, hUpdef, Finset.mem_filter]
    constructor
    · rintro ⟨hvZ, h | h⟩
      · left
        rw [← hZ] at hvZ
        rcases Finset.mem_union.1 hvZ with h' | h'
        · exact h'
        · exact absurd h' h
      · by_cases hv : v ∈ D.Pl
        · exact Or.inr ⟨hv, h⟩
        · left
          rw [← hZ] at hvZ
          rcases Finset.mem_union.1 hvZ with h' | h'
          · exact h'
          · exact absurd h' hv
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨hRtZ h, Or.inl (Finset.disjoint_left.1 hRtPl h)⟩
      · exact ⟨hPlZ h1, Or.inr h2⟩
  have hRtW : Disjoint D.Rt W := by
    rw [Finset.disjoint_left]
    intro x hx hxW
    exact Finset.disjoint_left.1 hRtPl hx (hWPl x hxW)
  have hRtUp : Disjoint D.Rt Up := by
    rw [Finset.disjoint_left]
    intro x hx hxU
    exact Finset.disjoint_left.1 hRtPl hx (Finset.mem_filter.1 hxU).1
  have hWUp : Disjoint W Up := by
    rw [Finset.disjoint_left]
    intro x hxW hxU
    exact hWUc x ((hmemUc x).2 (Or.inr hxU)) hxW
  have hWPj : W ⊆ Pj := by
    intro w hw
    rw [TPVRun.mem_Wt] at hw
    exact Finset.mem_filter.2 ⟨hw.1, hw.2.ge⟩
  have hUpPj : Up ⊆ Pj := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact Finset.mem_filter.2 ⟨hv.1, by omega⟩
  -- (i) Reserve: far ends
  let Cj : V → Finset V := fun w => (Cw D w).filter fun u => u ∈ Zr D.Z D.Pl lev kap j
  have hsel : ∀ w, ∃ f : Fin 4 → Fin 2 → V, w ∈ W → (∀ c i, f c i ∈ Cj w) ∧
      ∀ c i c' i', f c i = f c' i' → c = c' ∧ i = i' := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨f, h1, h2⟩ := exists_eight (hG4 j hj w (hWPl w hw))
      exact ⟨f, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => w, fun h => absurd h hw⟩
  choose fe hfe using hsel
  have hfC : ∀ w ∈ W, ∀ c i, s(w, fe w c i) ∈ D.M.edges ∧ fe w c i ∈ D.A w ∧
      D.ext (fe w c i) = none ∧ fe w c i ∈ Uc ∧ kap (fe w c i) = 0 := by
    intro w hw c i
    have h := ((hfe w hw).1 c i)
    simp only [Cj, Cw, Finset.mem_filter, Zr] at h
    exact ⟨h.1.2.1, h.1.1, h.1.2.2, h.2.1, h.2.2⟩
  have hfinj : ∀ w ∈ W, ∀ c i c' i', fe w c i = fe w c' i' → c = c' ∧ i = i' :=
    fun w hw => (hfe w hw).2
  have hfW : ∀ w ∈ W, ∀ c i, fe w c i ∉ W := fun w hw c i => hWUc _ (hfC w hw c i).2.2.2.1
  have hfne : ∀ w ∈ W, ∀ c, fe w c 0 ≠ fe w c 1 := by
    intro w hw c h
    have := (hfinj w hw c 0 c 1 h).2
    exact absurd this (by decide)
  -- reserved edges
  let Res : Fin 4 → Finset (Sym2 V) := fun c =>
    W.biUnion fun w => {s(w, fe w c 0), s(w, fe w c 1)}
  have hmemRes : ∀ c e, e ∈ Res c ↔ ∃ w ∈ W, e = s(w, fe w c 0) ∨ e = s(w, fe w c 1) := by
    intro c e
    simp [Res]
  let ResAll : Finset (Sym2 V) := Finset.univ.biUnion Res
  have hmemResAll : ∀ e, e ∈ ResAll ↔ ∃ c, e ∈ Res c := by intro e; simp [ResAll]
  have hsym : ∀ {w w' x x' : V}, w ∈ W → x ∉ W → x' ∉ W → s(w, x) = s(w', x') →
      w = w' ∧ x = x' := by
    intro w w' x x' hw hx hx' h
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · subst h1; exact absurd hw hx'
  have hResM : ∀ c, ∀ e ∈ Res c, e ∈ D.M.edges := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he
    · exact (hfC w hw c 0).1
    · exact (hfC w hw c 1).1
  have hResW : ∀ c, ∀ e ∈ Res c, ∃ w ∈ W, w ∈ e := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he <;> exact ⟨w, hw, Sym2.mem_mk_left _ _⟩
  -- (ii) Phases
  have hcls : ∀ e : Sym2 V, ∃ c : Fin 4, (∃ w ∈ W, w ∈ e) →
      ∀ y ∈ e, D.ext y ≠ some c ∧ (y ∉ W → kap y ≠ c.succ) := by
    intro e
    by_cases he : ∃ w ∈ W, w ∈ e
    · obtain ⟨c, hc⟩ := exists_step_phase W kap D.ext he
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose cls hclsP using hcls
  let F : Finset (Sym2 V) := (H0.filter fun e => e ∉ S).filter fun e => ∃ w ∈ W, w ∈ e
  have hmemF : ∀ e, e ∈ F ↔ e ∈ H0 ∧ e ∉ S ∧ ∃ w ∈ W, w ∈ e := by
    intro e; simp [F, and_assoc]
  let Fc : Fin 4 → Finset (Sym2 V) := fun c => (F.filter fun e => e ∉ ResAll).filter
    fun e => cls e = c
  have hmemFc : ∀ c e, e ∈ Fc c ↔ e ∈ F ∧ e ∉ ResAll ∧ cls e = c := by
    intro c e; simp [Fc, and_assoc]
  have hFcH : ∀ c, ∀ e ∈ Fc c, e ∈ H0 := fun c e he => ((hmemF e).1 ((hmemFc c e).1 he).1).1
  have hFcW : ∀ c, ∀ e ∈ Fc c, ∃ w ∈ W, w ∈ e := fun c e he =>
    ((hmemF e).1 ((hmemFc c e).1 he).1).2.2
  have hFcU : ∀ c, ∀ e ∈ Fc c, ∀ v ∈ e, v ∈ TPVRun.U D.Z D.Pl lev j := by
    intro c e he v hv
    have hF := (hmemF e).1 ((hmemFc c e).1 he).1
    exact hI1 e hF.1 hF.2.1 v hv
  have hFcZ : ∀ c, ∀ e ∈ Fc c, ∀ v ∈ e, v ∈ D.Z := fun c e he v hv =>
    (TPVRun.mem_U.1 (hFcU c e he v hv)).1
  have hFcends : ∀ c, ∀ e ∈ Fc c, ∀ v ∈ e, v ∈ D.Rt ∪ W ∪ Up := by
    intro c e he v hv
    obtain ⟨hvZ, hv'⟩ := TPVRun.mem_U.1 (hFcU c e he v hv)
    by_cases hvPl : v ∈ D.Pl
    · rcases hv' with h | h
      · exact absurd hvPl h
      · rcases Nat.lt_or_ge j (lev v) with h' | h'
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hvPl, h'⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (TPVRun.mem_Wt.2 ⟨hvPl, le_antisymm h' h⟩))
    · rw [← hZ] at hvZ
      rcases Finset.mem_union.1 hvZ with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact absurd h hvPl
  have hFcph : ∀ c, ∀ e ∈ Fc c, ∀ y ∈ e, D.ext y ≠ some c ∧ (y ∉ W → kap y ≠ c.succ) := by
    intro c e he y hy
    have h := (hmemFc c e).1 he
    rw [← h.2.2]
    exact hclsP e (hFcW c e he) y hy
  -- (iii) Paths: Corollary-22 decompositions
  have hcor : ∀ c, ∃ Pc : List (List V),
      IsPathDecomp ((Fc c : Finset (Sym2 V)) : Set (Sym2 V)) Pc ∧
      ∀ v, pathEndCount Pc v ≤ 2 := fun c =>
    EG.cor22 V (Fc c) fun e he => hHl e (hFcH c e he)
  choose Pc hPc using hcor
  -- (iv)–(vi): the engine, one phase at a time
  have hph : ∀ c, ∃ (Dp : List (Obj V)) (Ap Qp : List (List V)),
      (∀ o ∈ Dp, o.WF) ∧
      (Dp.flatMap Obj.edges ++ Ap.flatMap walkEdges ++ Qp.flatMap walkEdges).Nodup ∧
      (∀ e, e ∈ Dp.flatMap Obj.edges ++ Ap.flatMap walkEdges ++ Qp.flatMap walkEdges ↔
        e ∈ Fc c ∨ ∃ w ∈ W, e = s(w, fe w c 0) ∨ e = s(w, fe w c 1)) ∧
      (∀ a ∈ Ap, a.Nodup ∧ 2 ≤ a.length ∧ (∃ x ∈ D.Rt, a.head? = some x) ∧
        (∃ y ∈ D.Rt, a.getLast? = some y) ∧
        ∀ x ∈ a, (∃ e ∈ Fc c, x ∈ e) ∨ ∃ w ∈ W, x = fe w c 0 ∨ x = fe w c 1) ∧
      Ap.length ≤ (Pc c).length ∧
      (∀ q ∈ Qp, q.Nodup ∧ 2 ≤ pathLength q ∧ (∃ x ∈ D.Rt ∪ Up, q.head? = some x) ∧
        (∃ y ∈ D.Rt ∪ Up, q.getLast? = some y) ∧
        ∀ x ∈ q, (∃ e ∈ Fc c, x ∈ e) ∨ x ∈ W ∨ ∃ w ∈ W, x = fe w c 0 ∨ x = fe w c 1) ∧
      (∀ v : V, pathEndCount Qp v ≤
        2 + (W.filter fun w => v = fe w c 0 ∨ v = fe w c 1).card) ∧
      Dp.length + Qp.length ≤ W.card + 3 * (2 * W.card + 2 * Up.card) := by
    intro c
    refine EG.pvStepPhase V D.Rt W Up (Fc c) (Pc c) (fun w => fe w c 0) (fun w => fe w c 1)
      hRtW hRtUp hWUp (fun e he => hHl e (hFcH c e he)) (hFcends c) (hFcW c) (hPc c).1
      (hPc c).2 ?_
    intro w hw
    refine ⟨hfne w hw c, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_union.2 ((hmemUc _).1 (hfC w hw c 0).2.2.2.1)
    · exact Finset.mem_union.2 ((hmemUc _).1 (hfC w hw c 1).2.2.2.1)
    · intro hf
      exact ((hmemFc c _).1 hf).2.1 ((hmemResAll _).2 ⟨c, (hmemRes c _).2 ⟨w, hw, Or.inl rfl⟩⟩)
    · intro hf
      exact ((hmemFc c _).1 hf).2.1 ((hmemResAll _).2 ⟨c, (hmemRes c _).2 ⟨w, hw, Or.inr rfl⟩⟩)
  choose Dp Ap Qp hDp using hph
  -- the object edges `X c` and the arc edges `Y c` of phase `c`
  let X : Fin 4 → Finset (Sym2 V) := fun c =>
    ((Dp c).flatMap Obj.edges ++ (Qp c).flatMap walkEdges).toFinset
  let Y : Fin 4 → Finset (Sym2 V) := fun c => ((Ap c).flatMap walkEdges).toFinset
  have hmemX : ∀ c e, e ∈ X c ↔ e ∈ (Dp c).flatMap Obj.edges ++ (Qp c).flatMap walkEdges :=
    fun c e => List.mem_toFinset
  have hmemY : ∀ c e, e ∈ Y c ↔ e ∈ (Ap c).flatMap walkEdges := fun c e => List.mem_toFinset
  have hXYph : ∀ c e, e ∈ X c ∨ e ∈ Y c ↔ e ∈ Fc c ∨ e ∈ Res c := by
    intro c e
    rw [hmemX, hmemY, hmemRes, ← (hDp c).2.2.1 e]
    simp only [List.mem_append]
    tauto
  have hXph : ∀ c e, e ∈ X c → e ∈ Fc c ∨ e ∈ Res c := fun c e he =>
    (hXYph c e).1 (Or.inl he)
  have hYph : ∀ c e, e ∈ Y c → e ∈ Fc c ∨ e ∈ Res c := fun c e he =>
    (hXYph c e).1 (Or.inr he)
  have hXY : ∀ c, Disjoint (X c) (Y c) := by
    intro c
    rw [Finset.disjoint_left]
    intro e hx hy
    have hnd := (hDp c).2.1
    rw [List.nodup_append] at hnd
    rw [hmemX, List.mem_append] at hx
    rw [hmemY] at hy
    rcases hx with hx | hx
    · exact List.disjoint_of_nodup_append hnd.1 hx hy
    · exact hnd.2.2 e (List.mem_append_right _ hy) e hx rfl
  have hphW : ∀ c e, e ∈ Fc c ∨ e ∈ Res c → ∃ w ∈ W, w ∈ e := by
    rintro c e (he | he)
    · exact hFcW c e he
    · exact hResW c e he
  -- (vi): closing the non-arc paths
  have hcl : ∀ c, ∃ (Conn : Finset (Sym2 V)) (Dc : List (Obj V)),
      IsDecomp ((X c ∪ Conn : Finset (Sym2 V)) : Set (Sym2 V)) Dc ∧
      Disjoint (X c) Conn ∧ Conn ⊆ (D.R (ij, c)).edges ∧
      (∀ e ∈ Conn, ∀ v ∈ e, v ∈ Uc) ∧ Dc.length = (Dp c).length + (Qp c).length ∧
      Dc.countP Obj.isEdge = (Dp c).countP Obj.isEdge := by
    intro c
    obtain ⟨hwf, hnd, _, _, _, hQ, hpec, _⟩ := hDp c
    have hnd' : ((Dp c).flatMap Obj.edges ++ (Qp c).flatMap walkEdges).Nodup :=
      hnd.sublist ((List.sublist_append_left _ _).append (List.Sublist.refl _))
    refine TPVRun.close_class (hG2 (ij, c)) hwf hnd' (X := X c) (fun e => (hmemX c e).symm)
      ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨h1, h2, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, h5⟩ := hQ q hq
      refine ⟨h1, h2, ⟨x, ?_, hx'⟩, ⟨y, ?_, hy'⟩, fun z hz hzV => ?_⟩
      · rw [hmemUc]; exact Finset.mem_union.1 hx
      · rw [hmemUc]; exact Finset.mem_union.1 hy
      · simp only [Vc, Finset.mem_filter] at hzV
        have hzW : z ∉ W := hWUc z hzV.1
        rcases h5 z hz with ⟨e, he, hze⟩ | hzW' | ⟨w, hw, hz' | hz'⟩
        · exact (hFcph c e he z hze).2 hzW hzV.2
        · exact hzW hzW'
        · rw [hz', (hfC w hw c 0).2.2.2.2] at hzV
          exact absurd hzV.2 (Fin.succ_ne_zero c).symm
        · rw [hz', (hfC w hw c 1).2.2.2.2] at hzV
          exact absurd hzV.2 (Fin.succ_ne_zero c).symm
    · intro x hx
      rw [(hRexp (ij, c)).1]
      exact (TPVRun.mem_U.1 hx).1
    · intro x hx
      exact (Finset.mem_filter.1 hx).1
    · intro v
      refine le_trans (Nat.cast_le.2 (hpec v)) ?_
      refine le_trans ?_ (hmult v)
      rw [Nat.cast_add, add_comm]
      push_cast
      refine add_le_add_left (Nat.cast_le.2 (Finset.card_le_card fun w hw => ?_)) _
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨hPlZ (hWPl w hw.1), ?_⟩
      rcases hw.2 with h | h <;> rw [h]
      · exact (hfC w hw.1 c 0).2.1
      · exact (hfC w hw.1 c 1).2.1
    · intro e he
      obtain ⟨w, hw, hwe⟩ := hphW c e (hXph c e he)
      exact ⟨w, hwe, fun hwU => hWUc w hwU hw⟩
  choose Conn Dc hDc using hcl
  -- properties of connectors
  have hConnR : ∀ c, ∀ e ∈ Conn c, e ∈ (D.R (ij, c)).edges := fun c e he => (hDc c).2.2.1 he
  have hConnUc : ∀ c, ∀ e ∈ Conn c, ∀ v ∈ e, v ∈ Uc := fun c => (hDc c).2.2.2.1
  have hConnNotW : ∀ c, ∀ e ∈ Conn c, ∀ w ∈ W, w ∉ e := fun c e he w hw hwe =>
    hWUc w (hConnUc c e he w hwe) hw
  -- the phase sets are pairwise disjoint
  have hFcdisj : ∀ c c', c ≠ c' → Disjoint (Fc c) (Fc c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    exact hcc' (((hmemFc c e).1 he).2.2.symm.trans ((hmemFc c' e).1 he').2.2)
  have hFcRes : ∀ c c', Disjoint (Fc c) (Res c') := by
    intro c c'
    rw [Finset.disjoint_left]
    intro e he he'
    exact ((hmemFc c e).1 he).2.1 ((hmemResAll e).2 ⟨c', he'⟩)
  have hResdisj : ∀ c c', c ≠ c' → Disjoint (Res c) (Res c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨w, hw, h1⟩ := (hmemRes c e).1 he
    obtain ⟨w', hw', h2⟩ := (hmemRes c' e).1 he'
    have key : ∀ i i' : Fin 2, s(w, fe w c i) = s(w', fe w' c' i') → False := by
      intro i i' h
      obtain ⟨rfl, h'⟩ := hsym hw (hfW w hw c i) (hfW w' hw' c' i') h
      exact hcc' (hfinj w hw c i c' i' h').1
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
    · exact key 0 0 h2
    · exact key 0 1 h2
    · exact key 1 0 h2
    · exact key 1 1 h2
  have hConndisj : ∀ c c', c ≠ c' → Disjoint (Conn c) (Conn c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    have hd := hRd (ij, c) (ij, c') (by simp [hcc'])
    exact Finset.disjoint_left.1 hd (hConnR c e he) (hConnR c' e he')
  -- membership in a phase set
  let Ph : Fin 4 → Finset (Sym2 V) := fun c => Fc c ∪ Res c ∪ Conn c
  have hPhdisj : ∀ c c', c ≠ c' → Disjoint (Ph c) (Ph c') := by
    intro c c' hcc'
    simp only [Ph]
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_union] at he he'
    rcases he with (he | he) | he <;> rcases he' with (he' | he') | he'
    · exact Finset.disjoint_left.1 (hFcdisj c c' hcc') he he'
    · exact Finset.disjoint_left.1 (hFcRes c c') he he'
    · obtain ⟨w, hw, hwe⟩ := hFcW c e he
      exact hConnNotW c' e he' w hw hwe
    · exact Finset.disjoint_left.1 (hFcRes c' c) he' he
    · exact Finset.disjoint_left.1 (hResdisj c c' hcc') he he'
    · obtain ⟨w, hw, hwe⟩ := hResW c e he
      exact hConnNotW c' e he' w hw hwe
    · obtain ⟨w, hw, hwe⟩ := hFcW c' e he'
      exact hConnNotW c e he w hw hwe
    · obtain ⟨w, hw, hwe⟩ := hResW c' e he'
      exact hConnNotW c e he w hw hwe
    · exact Finset.disjoint_left.1 (hConndisj c c' hcc') he he'
  have hXPh : ∀ c e, e ∈ X c ∪ Conn c → e ∈ Ph c := by
    intro c e he
    simp only [Ph, Finset.mem_union]
    rcases Finset.mem_union.1 he with he | he
    · rcases hXph c e he with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
    · exact Or.inr he
  have hYPh : ∀ c e, e ∈ Y c → e ∈ Ph c := by
    intro c e he
    simp only [Ph, Finset.mem_union]
    rcases hYph c e he with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  have hYConn : ∀ c, Disjoint (Y c) (Conn c) := by
    intro c
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨w, hw, hwe⟩ := hphW c e (hYph c e he)
    exact hConnNotW c e he' w hw hwe
  -- the step's edges
  let Tobj : Finset (Sym2 V) := Finset.univ.biUnion fun c => X c ∪ Conn c
  let Tarc : Finset (Sym2 V) := Finset.univ.biUnion Y
  have hmemTobj : ∀ e, e ∈ Tobj ↔ ∃ c, e ∈ X c ∪ Conn c := by intro e; simp [Tobj]
  have hmemTarc : ∀ e, e ∈ Tarc ↔ ∃ c, e ∈ Y c := by intro e; simp [Tarc]
  have hmemT : ∀ e, e ∈ Tobj ∪ Tarc → ∃ c, e ∈ Fc c ∨ e ∈ Res c ∨ e ∈ Conn c := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨c, hc⟩ := (hmemTobj e).1 he
      rcases Finset.mem_union.1 hc with hc | hc
      · rcases hXph c e hc with h | h
        · exact ⟨c, Or.inl h⟩
        · exact ⟨c, Or.inr (Or.inl h)⟩
      · exact ⟨c, Or.inr (Or.inr hc)⟩
    · obtain ⟨c, hc⟩ := (hmemTarc e).1 he
      rcases hYph c e hc with h | h
      · exact ⟨c, Or.inl h⟩
      · exact ⟨c, Or.inr (Or.inl h)⟩
  have hphT : ∀ c e, e ∈ Fc c ∨ e ∈ Res c → e ∈ Tobj ∪ Tarc := by
    intro c e he
    rcases (hXYph c e).2 he with h | h
    · exact Finset.mem_union_left _ ((hmemTobj e).2 ⟨c, Finset.mem_union_left _ h⟩)
    · exact Finset.mem_union_right _ ((hmemTarc e).2 ⟨c, h⟩)
  have hFT : ∀ e ∈ H0, e ∉ S → (∃ w ∈ W, w ∈ e) → e ∈ Tobj ∪ Tarc := by
    intro e he heS heW
    by_cases hr : e ∈ ResAll
    · obtain ⟨c, hc⟩ := (hmemResAll e).1 hr
      exact hphT c e (Or.inr hc)
    · exact hphT (cls e) e (Or.inl ((hmemFc _ e).2 ⟨(hmemF e).2 ⟨he, heS, heW⟩, hr, rfl⟩))
  -- decompositions
  have hTobjdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
      fun c => X c ∪ Conn c := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.1 (hPhdisj c c' hcc') (hXPh c e he) (hXPh c' e he')
  have hTobjdec : IsDecomp ((Tobj : Finset (Sym2 V)) : Set (Sym2 V))
      ((Finset.univ : Finset (Fin 4)).toList.flatMap Dc) :=
    isDecomp_finset_biUnion Finset.univ (Ds := Dc) hTobjdisj fun c _ => (hDc c).1
  have hTarcdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint Y := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.1 (hPhdisj c c' hcc') (hYPh c e he) (hYPh c' e he')
  have hYdec : ∀ c ∈ (Finset.univ : Finset (Fin 4)),
      IsPathDecomp ((Y c : Finset (Sym2 V)) : Set (Sym2 V)) (Ap c) := by
    intro c _
    refine ⟨fun a ha => ⟨((hDp c).2.2.2.1 a ha).2.1, ((hDp c).2.2.2.1 a ha).1⟩, ?_,
      fun e => ?_⟩
    · have hnd := (hDp c).2.1
      exact hnd.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
    · rw [Finset.mem_coe, hmemY]
  have hTarcdec := isPathDecomp_biUnion Finset.univ hTarcdisj hYdec
  -- the arcs with their phases
  let arcs : List (List V × Fin 4) :=
    (Finset.univ : Finset (Fin 4)).toList.flatMap fun c => (Ap c).map fun a => (a, c)
  have harcs_fst : arcs.map Prod.fst = (Finset.univ : Finset (Fin 4)).toList.flatMap Ap := by
    simp only [arcs, List.map_flatMap, List.map_map]
    have e : (fun c => List.map (Prod.fst ∘ fun a => (a, c)) (Ap c)) = Ap := by
      funext c
      simp [Function.comp_def]
    rw [e]
  -- membership facts
  have hResS : ∀ c, ∀ e ∈ Res c, e ∉ S := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he
    · exact hI3 j le_rfl hj w hw _ (hfC w hw c 0).2.2.2.1 (hfC w hw c 0).1
    · exact hI3 j le_rfl hj w hw _ (hfC w hw c 1).2.2.2.1 (hfC w hw c 1).1
  have hConnS : ∀ c, ∀ e ∈ Conn c, e ∉ S := fun c e he =>
    hI2 (ij, c) le_rfl e (hConnR c e he) (hConnUc c e he)
  refine ⟨Tobj, Tarc, (Finset.univ : Finset (Fin 4)).toList.flatMap Dc, arcs, ?_, ?_, ?_,
    hTobjdec, ?_, ?_, ?_, ?_, ?_⟩
  · -- Disjoint Tobj Tarc
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨c, hc⟩ := (hmemTobj e).1 he
    obtain ⟨c', hc'⟩ := (hmemTarc e).1 he'
    by_cases hcc : c = c'
    · subst hcc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact Finset.disjoint_left.1 (hXY c) hc hc'
      · exact Finset.disjoint_left.1 (hYConn c) hc' hc
    · exact Finset.disjoint_left.1 (hPhdisj c c' hcc) (hXPh c e hc) (hYPh c' e hc')
  · -- Disjoint T S
    rw [Finset.disjoint_left]
    intro e he heS
    obtain ⟨c, hc | hc | hc⟩ := hmemT e he
    · exact ((hmemF e).1 ((hmemFc c e).1 hc).1).2.1 heS
    · exact hResS c e hc heS
    · exact hConnS c e hc heS
  · -- T ⊆ H0
    intro e he
    obtain ⟨c, hc | hc | hc⟩ := hmemT e he
    · exact hFcH c e hc
    · exact hMH (hResM c e hc)
    · exact hRH (ij, c) (hConnR c e hc)
  · -- cost
    rw [length_flatMap_toList]
    have hc : ∀ c ∈ (Finset.univ : Finset (Fin 4)),
        (Dc c).length ≤ W.card + 3 * (2 * W.card + 2 * Up.card) := by
      intro c _
      rw [(hDc c).2.2.2.2.1]
      exact (hDp c).2.2.2.2.2.2.2
    have h1 := Finset.sum_le_sum hc
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : W.card + Up.card ≤ Pj.card := by
      rw [← Finset.card_union_of_disjoint hWUp]
      exact Finset.card_le_card (Finset.union_subset hWPj hUpPj)
    omega
  · rw [harcs_fst]
    exact hTarcdec
  · -- the arc conditions
    intro a ha
    obtain ⟨c, -, ha⟩ := List.mem_flatMap.1 ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    obtain ⟨_, _, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, hv⟩ := (hDp c).2.2.2.1 a' ha'
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rcases hz with hz | hz
      · rw [hx'] at hz; rw [← Option.some.inj hz]; exact hx
      · rw [hy'] at hz; rw [← Option.some.inj hz]; exact hy
    · rcases hv z hz with ⟨e, he, hze⟩ | ⟨w, hw, hz' | hz'⟩
      · exact (hFcph c e he z hze).1
      · rw [hz', (hfC w hw c 0).2.2.1]; simp
      · rw [hz', (hfC w hw c 1).2.2.1]; simp
  · -- the number of arcs
    have e1 : arcs.length = ∑ c ∈ (Finset.univ : Finset (Fin 4)), (Ap c).length := by
      simp only [arcs, List.length_flatMap, List.length_map]
      rw [Finset.sum_map_toList]
    rw [e1]
    have hc : ∀ c ∈ (Finset.univ : Finset (Fin 4)), (Ap c).length ≤ D.Z.card := by
      intro c _
      exact ((hDp c).2.2.2.2.1).trans ((hPc c).1.length_le_card (hPc c).2 (hFcZ c))
    have := Finset.sum_le_sum hc
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact this
  · -- the invariants persist
    refine ⟨?_, ?_, ?_⟩
    · intro e he heST v hv
      have heS : e ∉ S := fun h => heST (Finset.mem_union_left _ h)
      have heT : e ∉ Tobj ∪ Tarc := fun h => heST (Finset.mem_union_right _ h)
      obtain ⟨hvZ, h1⟩ := TPVRun.mem_U.1 (hI1 e he heS v hv)
      refine TPVRun.mem_U.2 ⟨hvZ, ?_⟩
      by_cases hvPl : v ∈ D.Pl
      · rcases h1 with h1 | h1
        · exact absurd hvPl h1
        · rcases Nat.lt_or_ge j (lev v) with h | h
          · exact Or.inr h
          · exfalso
            exact heT (hFT e he heS ⟨v, TPVRun.mem_Wt.2 ⟨hvPl, le_antisymm h h1⟩, hv⟩)
      · exact Or.inl hvPl
    · intro i hi e he hU' heST
      have hjj' : ij ≠ i.1 := by
        intro h
        have h' : (ij : ℕ) = (i.1 : ℕ) := congrArg Fin.val h
        simp only [hijdef] at h'
        omega
      have hUj : ∀ v ∈ e, v ∈ Uc := fun v hv =>
        TPVRun.U_anti (by omega) (hU' v hv)
      rcases Finset.mem_union.1 heST with heS | heT
      · exact hI2 i (by omega) e he hU' heS
      · obtain ⟨c, hc | hc | hc⟩ := hmemT e heT
        · obtain ⟨w, hw, hwe⟩ := hFcW c e hc
          exact hWUc w (hUj w hwe) hw
        · exact Finset.disjoint_left.1 (hRM i) he (hResM c e hc)
        · have hne : (ij, c) ≠ i := fun h => hjj' (congrArg Prod.fst h)
          exact Finset.disjoint_left.1 (hRd (ij, c) i hne) (hConnR c e hc) he
    · intro j' hj' hj'J w hw u hu hM heST
      have hjj' : j ≠ j' := by omega
      rcases Finset.mem_union.1 heST with heS | heT
      · exact hI3 j' (by omega) hj'J w hw u hu hM heS
      · have hwW : w ∉ W := TPVRun.Wt_ne hjj' hw
        have huW : u ∉ W := hWUc u (TPVRun.U_anti (by omega) hu)
        have hnot : ∀ x ∈ W, x ∉ s(w, u) := by
          intro x hx hxe
          rcases Sym2.mem_iff.1 hxe with rfl | rfl
          · exact hwW hx
          · exact huW hx
        obtain ⟨c, hc | hc | hc⟩ := hmemT _ heT
        · obtain ⟨x, hx, hxe⟩ := hFcW c _ hc
          exact hnot x hx hxe
        · obtain ⟨x, hx, hxe⟩ := hResW c _ hc
          exact hnot x hx hxe
        · exact Finset.disjoint_left.1 (hRM (ij, c)) (hConnR c _ hc) hM

end PVRun

end EG
