module

public import EG.Lib.Vortex.TPVClose
public import EG.Proof.Ext.Cor22
public import EG.Defs.Probe.S4.TPV

/-!
# One step of the TPV run (manuscript s4:lemTPV, proof, "The process", "Step `j`", "The
invariants persist", "Cost of step `j`")

Unit P3-s4. The deterministic part of the proof of Lemma TPV, for fixed labels in the good event
(the good-event properties (G2), (G4) and the multiplicity bound of the sets `A(w)` are the
hypotheses `EG.TPVRun.Good`). The run sets are

* `U j = Q ∪ {v ∈ P : lev(v) ≥ j}` (`EG.TPVRun.U`, as a subset of `Z`),
* `W_j = {v ∈ P : lev(v) = j}` (`EG.TPVRun.Wt`),
* `Z_j = {u ∈ U_{j+1} : κ(u) = 0}` (`EG.TPVRun.Zr`),
* `V_{j,c} = {u ∈ U_{j+1} : κ(u) = c}` (`EG.TPVRun.Vc`, classes `c : Fin 3` ↔ `κ = c.succ`).

The state before step `j` is the set `S` of used edges; `H_j = H_0 \ S` with
`H_0 = {e ∈ E : both ends in P}`. The invariants (Inv1)–(Inv3) are `EG.TPVRun.Inv`.

Main result: `EG.TPVRun.step` (one step: the edges used, their decomposition into at most
`12|P ∩ U_j|` objects, and the invariants for `j + 1`).
-/

public section

namespace EG

namespace TPVRun

open List

variable {V : Type*} [DecidableEq V]

section Sets

variable (Z P : Finset V) (lev : V → ℕ) (kap : V → Fin 4)

/-- `U_j := Q ∪ {v ∈ P : lev(v) ≥ j}` (inside `Z`). -/
@[expose] def U (j : ℕ) : Finset V := Z.filter fun v => v ∉ P ∨ j ≤ lev v

/-- `W_j := {v ∈ P : lev(v) = j}`. -/
@[expose] def Wt (j : ℕ) : Finset V := P.filter fun v => lev v = j

/-- `Z_j := {u ∈ U_{j+1} : κ(u) = 0}`. -/
@[expose] def Zr (j : ℕ) : Finset V := (U Z P lev (j + 1)).filter fun v => kap v = 0

/-- `V_{j,c} := {u ∈ U_{j+1} : κ(u) = c}` (class `c : Fin 3` is the label `c.succ`). -/
@[expose] def Vc (j : ℕ) (c : Fin 3) : Finset V :=
  (U Z P lev (j + 1)).filter fun v => kap v = c.succ

end Sets

/-- `H_0 := {e ∈ E : e has both ends in P}`. -/
@[expose] def H0 (P : Finset V) (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e => e ∈ P.sym2

variable {Z P : Finset V} {lev : V → ℕ} {kap : V → Fin 4}

theorem mem_U {j : ℕ} {v : V} : v ∈ U Z P lev j ↔ v ∈ Z ∧ (v ∉ P ∨ j ≤ lev v) := Finset.mem_filter

omit [DecidableEq V] in
theorem mem_Wt {j : ℕ} {v : V} : v ∈ Wt P lev j ↔ v ∈ P ∧ lev v = j := Finset.mem_filter

theorem mem_H0 {E : Finset (Sym2 V)} {e : Sym2 V} : e ∈ H0 P E ↔ e ∈ E ∧ ∀ v ∈ e, v ∈ P := by
  rw [H0, Finset.mem_filter, Finset.mem_sym2_iff]

theorem notWt_of_U {j : ℕ} {v : V} (hv : v ∈ U Z P lev (j + 1)) : v ∉ Wt P lev j := by
  intro hw
  rw [mem_Wt] at hw
  rw [mem_U] at hv
  rcases hv.2 with h | h
  · exact h hw.1
  · omega

theorem U_anti {j j' : ℕ} (h : j ≤ j') {v : V} (hv : v ∈ U Z P lev j') : v ∈ U Z P lev j := by
  rw [mem_U] at hv ⊢
  exact ⟨hv.1, hv.2.imp_right fun h' => le_trans h h'⟩

omit [DecidableEq V] in
theorem Wt_ne {j j' : ℕ} (h : j ≠ j') {v : V} (hv : v ∈ Wt P lev j') : v ∉ Wt P lev j := by
  rw [mem_Wt] at hv ⊢
  intro h'
  exact h (h'.2.symm.trans hv.2)

/-- The hypotheses of the deterministic run: the labels lie in the good event. -/
structure Good (Z P : Finset V) (O : FGraph V) (J : ℕ) (R : ℕ → Fin 3 → Finset (Sym2 V))
    (M : Finset (Sym2 V)) (lev : V → ℕ) (kap : V → Fin 4) (A : V → Finset V) (ℓ t : ℝ) :
    Prop where
  PZ : P ⊆ Z
  OZ : O.verts = Z
  MO : M ⊆ O.edges
  Rdisj : ∀ j < J, ∀ j' < J, ∀ c c' : Fin 3, (j, c) ≠ (j', c') → Disjoint (R j c) (R j' c')
  RM : ∀ j < J, ∀ c, Disjoint (R j c) M
  G2 : ∀ j < J, ∀ c, (O.restrictEdges (R j c)).IsPathConnected ℓ t (Vc Z P lev kap j c)
  G4 : ∀ j < J, ∀ w ∈ P, 6 ≤ ((A w).filter fun u => s(w, u) ∈ M ∧ u ∈ Zr Z P lev kap j).card
  mult : ∀ v : V, ((Z.filter fun w => v ∈ A w).card : ℝ) + 2 ≤ t

/-- The invariants (Inv1)–(Inv3) before step `j`, for the set `S` of used edges. -/
@[expose] def Inv (Z P : Finset V) (J : ℕ) (R : ℕ → Fin 3 → Finset (Sym2 V))
    (M : Finset (Sym2 V)) (lev : V → ℕ) (E : Finset (Sym2 V)) (j : ℕ) (S : Finset (Sym2 V)) :
    Prop :=
  (∀ e ∈ H0 P E, e ∉ S → ∀ v ∈ e, j ≤ lev v) ∧
  (∀ j', j ≤ j' → j' < J → ∀ c, ∀ e ∈ R j' c, (∀ v ∈ e, v ∈ U Z P lev (j' + 1)) → e ∉ S) ∧
  (∀ j', j ≤ j' → j' < J → ∀ w ∈ Wt P lev j', ∀ u ∈ U Z P lev (j' + 1), s(w, u) ∈ M →
    s(w, u) ∉ S)

omit [DecidableEq V] in
/-- An edge meeting `W` has a class avoiding the label of its other end. -/
theorem exists_class (W : Finset V) (kap : V → Fin 4) {e : Sym2 V} (he : ∃ w ∈ W, w ∈ e) :
    ∃ c : Fin 3, ∀ x ∈ e, x ∉ W → kap x ≠ c.succ := by
  have key : ∀ k : Fin 4, ∃ c : Fin 3, k ≠ c.succ := by decide
  obtain ⟨w, hw, hwe⟩ := he
  induction e using Sym2.ind with
  | _ a b =>
    rcases Sym2.mem_iff.1 hwe with rfl | rfl
    · obtain ⟨c, hc⟩ := key (kap b)
      refine ⟨c, fun x hx hxW => ?_⟩
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact absurd hw hxW
      · exact hc
    · obtain ⟨c, hc⟩ := key (kap a)
      refine ⟨c, fun x hx hxW => ?_⟩
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hc
      · exact absurd hw hxW

omit [DecidableEq V] in
/-- Six distinct elements of a set with at least six elements, indexed by `Fin 3 × Fin 2`. -/
theorem exists_six {s : Finset V} (h : 6 ≤ s.card) :
    ∃ f : Fin 3 → Fin 2 → V, (∀ c i, f c i ∈ s) ∧
      ∀ c i c' i', f c i = f c' i' → c = c' ∧ i = i' := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h
  let g : Fin 6 → V := fun k => (t.equivFin.symm (Fin.cast htc.symm k)).1
  have hg : Function.Injective g := by
    intro a b hab
    have := Subtype.ext hab
    have := t.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  refine ⟨fun c i => g (finProdFinEquiv (c, i)), fun c i => hts ?_, fun c i c' i' h' => ?_⟩
  · exact (t.equivFin.symm _).2
  · have := finProdFinEquiv.injective (hg h')
    simp only [Prod.mk.injEq] at this
    exact this

end TPVRun

end EG
