module

public import EG.Lib.Vortex.VXStep

/-!
# One step of the VX⁺ run: the assembly (manuscript s4:thmVXp, proof, "Step `j`" (a)–(f), the
invariants, "Cost")

Unit P3-s4. `EG.VXRun.step`: the run sets are those of `EG/Lib/Vortex/TPVStep.lean` with `P = Z`.
For labels in the good event ((G2), (G4) with nine edges, the multiplicity bound of the sets
`A(w)`) and a set `S` of used edges satisfying (Inv1)–(Inv3) before step `j < J`, step `j` uses a
set `T` of edges (all of `F_j` and the connectors), decomposes it into at most
`4|W_j| + 9|U_j| ≤ 13|U_j|` objects of which at most `|W_j|` are single edges (the parity edges),
and (Inv1)–(Inv3) hold before step `j + 1`. (The manuscript's count is `19|U_j|`.)
-/

public section

namespace EG

namespace VXRun

open TPVRun List

variable {V : Type*} [DecidableEq V]

variable {Z : Finset V} {lev : V → ℕ} {kap : V → Fin 4}

set_option maxHeartbeats 1000000 in
-- the proof assembles the parity, reserved and flexible edges and the three classes of a step
/-- [s4:thmVXp] proof, "Step `j`" (a)–(f), the invariants, and "Cost". -/
theorem step {O : FGraph V} {J : ℕ} {R : ℕ → Fin 3 → Finset (Sym2 V)} {M : Finset (Sym2 V)}
    {A : V → Finset V} {ℓ t : ℝ} (hg : Good Z Z O J R M lev kap A ℓ t)
    (hG9 : ∀ j < J, ∀ w ∈ Z,
      9 ≤ ((A w).filter fun u => s(w, u) ∈ M ∧ u ∈ Zr Z Z lev kap j).card)
    {E : Finset (Sym2 V)} (hE : Vortex.TPVAdm Z O E) {j : ℕ} (hj : j < J)
    {S : Finset (Sym2 V)} (hinv : Inv Z Z J R M lev E j S) :
    ∃ (T : Finset (Sym2 V)) (D : List (Obj V)),
      Disjoint T S ∧ T ⊆ E ∧
      (∀ e ∈ H0 Z E, e ∉ S → (∃ w ∈ Wt Z lev j, w ∈ e) → e ∈ T) ∧
      IsDecomp (T : Set (Sym2 V)) D ∧
      D.length ≤ 13 * (Z.filter fun v => j ≤ lev v).card ∧
      D.countP Obj.isEdge ≤ (Wt Z lev j).card ∧
      Inv Z Z J R M lev E (j + 1) (S ∪ T) := by
  classical
  obtain ⟨_, hOZ, hMO, hRd, hRM, hG2, _, hmult⟩ := hg
  obtain ⟨hEl, hEZ, hOE⟩ := hE
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  -- notation
  set W := Wt Z lev j with hWdef
  set Up := U Z Z lev (j + 1) with hUpdef
  set Pj := Z.filter fun v => j ≤ lev v with hPjdef
  have hWP : W ⊆ Pj := by
    intro w hw
    rw [mem_Wt] at hw
    exact Finset.mem_filter.2 ⟨hw.1, hw.2.ge⟩
  have hWUp : ∀ x ∈ Up, x ∉ W := fun x hx => notWt_of_U hx
  have hWZ : ∀ w ∈ W, w ∈ Z := fun w hw => (mem_Wt.1 hw).1
  -- the nine far ends
  let Cw : V → Finset V := fun w => (A w).filter fun u => s(w, u) ∈ M ∧ u ∈ Zr Z Z lev kap j
  have hsel : ∀ w, ∃ f : Fin 9 → V, w ∈ W → (∀ k, f k ∈ Cw w) ∧ Function.Injective f := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨f, h1, h2⟩ := exists_nine (hG9 j hj w (hWZ w hw))
      exact ⟨f, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => w, fun h => absurd h hw⟩
  choose fe hfe using hsel
  have hfC : ∀ w ∈ W, ∀ k, s(w, fe w k) ∈ M ∧ fe w k ∈ A w ∧ fe w k ∈ Up ∧
      kap (fe w k) = 0 := by
    intro w hw k
    have h := (hfe w hw).1 k
    simp only [Cw, Finset.mem_filter, Zr] at h
    exact ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩
  have hfW : ∀ w ∈ W, ∀ k, fe w k ∉ W := fun w hw k => hWUp _ (hfC w hw k).2.2.1
  -- an edge `s(w, x)` with `w ∈ W`, `x ∉ W` determines `w` and `x`
  have hsym : ∀ {w w' x x' : V}, w ∈ W → x ∉ W → x' ∉ W → s(w, x) = s(w', x') →
      w = w' ∧ x = x' := by
    intro w w' x x' hw hx hx' h
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · subst h1; exact absurd hw hx'
  have hchinj : ∀ w ∈ W, ∀ w' ∈ W, ∀ k k', s(w, fe w k) = s(w', fe w' k') → w = w' ∧ k = k' := by
    intro w hw w' hw' k k' h
    obtain ⟨rfl, h2⟩ := hsym hw (hfW w hw k) (hfW w' hw' k') h
    exact ⟨rfl, (hfe w hw).2 h2⟩
  have hchmem : ∀ w' ∈ W, ∀ k, ∀ x ∈ W, x ∈ s(w', fe w' k) → x = w' := by
    intro w' hw' k x hx hxe
    rcases Sym2.mem_iff.1 hxe with h | h
    · exact h
    · exact absurd (h ▸ hx) (hfW w' hw' k)
  -- the edges `F_j`
  let F : Finset (Sym2 V) := ((H0 Z E).filter fun e => e ∉ S).filter fun e => ∃ w ∈ W, w ∈ e
  have hmemF : ∀ e, e ∈ F ↔ e ∈ H0 Z E ∧ e ∉ S ∧ ∃ w ∈ W, w ∈ e := by
    intro e; simp [F, and_assoc]
  have hchF : ∀ w ∈ W, ∀ k, s(w, fe w k) ∈ F := by
    intro w hw k
    refine (hmemF _).2 ⟨mem_H0.2 ⟨hOE (hMO (hfC w hw k).1), fun v hv => ?_⟩,
      hI3 j le_rfl hj w hw _ (hfC w hw k).2.2.1 (hfC w hw k).1, w, hw, Sym2.mem_mk_left _ _⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hWZ _ hw
    · exact (mem_U.1 (hfC w hw k).2.2.1).1
  have hFE : ∀ e ∈ F, e ∈ E := fun e he => (mem_H0.1 ((hmemF e).1 he).1).1
  have hFW : ∀ e ∈ F, ∃ w ∈ W, w ∈ e := fun e he => ((hmemF e).1 he).2.2
  have hFPj : ∀ e ∈ F, ∀ v ∈ e, v ∈ Pj := by
    intro e he v hv
    have hF := (hmemF e).1 he
    exact Finset.mem_filter.2 ⟨(mem_H0.1 hF.1).2 v hv, hI1 e hF.1 hF.2.1 v hv⟩
  have hFends : ∀ e ∈ F, ∀ v ∈ e, v ∈ W ∨ v ∈ Up := by
    intro e he v hv
    have hvP := hFPj e he v hv
    rw [Finset.mem_filter] at hvP
    rcases Nat.lt_or_ge j (lev v) with h | h
    · right
      exact mem_U.2 ⟨hvP.1, Or.inr h⟩
    · left
      exact mem_Wt.2 ⟨hvP.1, le_antisymm h hvP.2⟩
  -- (a), (b): the chosen edges
  let oddW : V → Prop := fun w => degE F w % 2 = 1
  let CK : V → Fin 9 → Prop := fun w k => (k : ℕ) < 8 ∨ oddW w
  let Chosen : Finset (Sym2 V) :=
    W.biUnion fun w => (Finset.univ.filter (CK w)).image fun k => s(w, fe w k)
  have hmemCh : ∀ e, e ∈ Chosen ↔ ∃ w ∈ W, ∃ k, CK w k ∧ s(w, fe w k) = e := by
    intro e; simp [Chosen]
  have hChF : ∀ e ∈ Chosen, e ∈ F := by
    intro e he
    obtain ⟨w, hw, k, _, rfl⟩ := (hmemCh e).1 he
    exact hchF w hw k
  let NR : Finset (Sym2 V) := F \ Chosen
  -- degrees at `w ∈ W`
  have hdegF : ∀ w ∈ W, degE F w = degE NR w + (Finset.univ.filter (CK w)).card := by
    intro w hw
    have hsplit : edgesAt F w = edgesAt NR w ∪ (Finset.univ.filter (CK w)).image
        (fun k => s(w, fe w k)) := by
      ext e
      simp only [edgesAt, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and, NR, Finset.mem_sdiff]
      constructor
      · rintro ⟨heF, hwe⟩
        by_cases hc : e ∈ Chosen
        · right
          obtain ⟨w', hw', k, hk, rfl⟩ := (hmemCh e).1 hc
          obtain rfl := hchmem w' hw' k w hw hwe
          exact ⟨k, hk, rfl⟩
        · left; exact ⟨⟨heF, hc⟩, hwe⟩
      · rintro (⟨⟨heF, _⟩, hwe⟩ | ⟨k, hk, rfl⟩)
        · exact ⟨heF, hwe⟩
        · exact ⟨hchF w hw k, Sym2.mem_mk_left _ _⟩
    have hdisj : Disjoint (edgesAt NR w) ((Finset.univ.filter (CK w)).image
        (fun k => s(w, fe w k))) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he'
      simp only [edgesAt, Finset.mem_filter, NR, Finset.mem_sdiff] at he
      exact he.1.2 ((hmemCh _).2 ⟨w, hw, k, (Finset.mem_filter.1 hk).2, rfl⟩)
    have hinj : Set.InjOn (fun k => s(w, fe w k)) ↑(Finset.univ.filter (CK w)) :=
      fun k _ k' _ h => (hchinj w hw w hw k k' h).2
    have hc : (edgesAt F w).card = (edgesAt NR w).card +
        ((Finset.univ.filter (CK w)).image fun k => s(w, fe w k)).card := by
      rw [hsplit]; exact Finset.card_union_of_disjoint hdisj
    calc degE F w = (edgesAt F w).card := rfl
      _ = (edgesAt NR w).card + ((Finset.univ.filter (CK w)).image
            fun k => s(w, fe w k)).card := hc
      _ = degE NR w + (Finset.univ.filter (CK w)).card := by
        rw [Finset.card_image_of_injOn hinj]; rfl
  have hdegNR : ∀ w ∈ W, degE NR w % 2 = 0 := by
    intro w hw
    have h := hdegF w hw
    rw [card_chosen] at h
    by_cases ho : oddW w
    · rw [if_pos ho] at h
      have : degE F w % 2 = 1 := ho
      omega
    · rw [if_neg ho] at h
      have : degE F w % 2 = 0 := by simp only [oddW] at ho; omega
      omega
  -- (c): classes
  have hcls : ∀ e : Sym2 V, ∃ c : Fin 3, (∃ w ∈ W, w ∈ e) → ∀ x ∈ e, x ∉ W → kap x ≠ c.succ := by
    intro e
    by_cases he : ∃ w ∈ W, w ∈ e
    · obtain ⟨c, hc⟩ := exists_class W kap he
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose cls hclsP using hcls
  let dc : V → Fin 3 → ℕ := fun w c => degE (NR.filter fun e => cls e = c) w
  have hdcsum : ∀ w, dc w 0 + dc w 1 + dc w 2 = degE NR w := by
    intro w
    have hfib : ∀ c, dc w c = ((edgesAt NR w).filter fun e => cls e = c).card := by
      intro c
      simp only [dc, degE, edgesAt, Finset.filter_filter]
      congr 1
      ext e
      simp [and_comm]
    have h := Finset.card_eq_sum_card_fiberwise (s := edgesAt NR w) (t := Finset.univ)
      (f := cls) (fun _ _ => Finset.mem_univ _)
    rw [Fin.sum_univ_three] at h
    rw [hfib 0, hfib 1, hfib 2, degE, h]
  let fa : V → Fin 3 := fun w => flA (dc w)
  let fb : V → Fin 3 := fun w => flB (dc w)
  -- the class edge sets `F_{j,c}` (classed and flexible)
  let Fc : Fin 3 → Finset (Sym2 V) := fun c => NR.filter (fun e => cls e = c) ∪
    W.biUnion fun w => (Finset.univ.filter fun k : Fin 9 => ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧
      chc (fa w) (fb w) k = c).image fun k => s(w, fe w k)
  have hmemFc : ∀ c e, e ∈ Fc c ↔ (e ∈ NR ∧ cls e = c) ∨ ∃ w ∈ W, ∃ k : Fin 9,
      ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧ chc (fa w) (fb w) k = c ∧ s(w, fe w k) = e := by
    intro c e
    simp [Fc, and_assoc]
  have hFcF : ∀ c, ∀ e ∈ Fc c, e ∈ F := by
    intro c e he
    rcases (hmemFc c e).1 he with ⟨h, _⟩ | ⟨w, hw, k, _, _, rfl⟩
    · exact (Finset.mem_sdiff.1 h).1
    · exact hchF w hw k
  have hdegFc : ∀ w ∈ W, ∀ c, degE (Fc c) w % 2 = 0 := by
    intro w hw c
    have hsplit : edgesAt (Fc c) w = edgesAt (NR.filter fun e => cls e = c) w ∪
        (Finset.univ.filter fun k : Fin 9 => ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧
          chc (fa w) (fb w) k = c).image fun k => s(w, fe w k) := by
      ext e
      simp only [edgesAt, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and]
      rw [hmemFc]
      constructor
      · rintro ⟨⟨h, hc⟩ | ⟨w', hw', k, hk, hc, rfl⟩, hwe⟩
        · exact Or.inl ⟨⟨h, hc⟩, hwe⟩
        · obtain rfl := hchmem w' hw' k w hw hwe
          exact Or.inr ⟨k, ⟨hk, hc⟩, rfl⟩
      · rintro (⟨⟨h, hc⟩, hwe⟩ | ⟨k, ⟨hk, hc⟩, rfl⟩)
        · exact ⟨Or.inl ⟨h, hc⟩, hwe⟩
        · exact ⟨Or.inr ⟨w, hw, k, hk, hc, rfl⟩, Sym2.mem_mk_left _ _⟩
    have hdisj : Disjoint (edgesAt (NR.filter fun e => cls e = c) w)
        ((Finset.univ.filter fun k : Fin 9 => ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧
          chc (fa w) (fb w) k = c).image fun k => s(w, fe w k)) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he'
      simp only [edgesAt, Finset.mem_filter, NR, Finset.mem_sdiff] at he hk
      refine he.1.1.2 ((hmemCh _).2 ⟨w, hw, k, Or.inl ?_, rfl⟩)
      rcases hk.2.1 with h | h <;> omega
    have hinj : Set.InjOn (fun k => s(w, fe w k)) ↑(Finset.univ.filter fun k : Fin 9 =>
        ((k : ℕ) = 6 ∨ (k : ℕ) = 7) ∧ chc (fa w) (fb w) k = c) :=
      fun k _ k' _ h => (hchinj w hw w hw k k' h).2
    unfold degE
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
      card_flex]
    have := flex_parity (dc w) (by rw [hdcsum]; exact hdegNR w hw) c
    simp only [dc, degE, fa, fb] at this ⊢
    omega
  have hFckap : ∀ c, ∀ e ∈ Fc c, ∀ x ∈ e, x ∉ W → kap x ≠ c.succ := by
    intro c e he x hx hxW
    rcases (hmemFc c e).1 he with ⟨h, hc⟩ | ⟨w, hw, k, _, _, rfl⟩
    · rw [← hc]
      exact hclsP e (hFW e (Finset.mem_sdiff.1 h).1) x hx hxW
    · rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact absurd hw hxW
      · rw [(hfC w hw k).2.2.2]; exact (Fin.succ_ne_zero c).symm
  -- reserved edges
  let Res : Fin 3 → Finset (Sym2 V) := fun c =>
    W.biUnion fun w => {s(w, fe w (idx c 0)), s(w, fe w (idx c 1))}
  have hmemRes : ∀ c e, e ∈ Res c ↔ ∃ w ∈ W, e = s(w, fe w (idx c 0)) ∨
      e = s(w, fe w (idx c 1)) := by
    intro c e; simp [Res]
  have hResF : ∀ c, ∀ e ∈ Res c, e ∈ F := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he <;> exact hchF w hw _
  -- (d): Corollary-22 decompositions
  have hcor : ∀ c, ∃ Pc : List (List V),
      IsPathDecomp ((Fc c : Finset (Sym2 V)) : Set (Sym2 V)) Pc ∧
      ∀ v, pathEndCount Pc v ≤ 2 := fun c =>
    EG.cor22 V (Fc c) fun e he => hEl e (hFE e (hFcF c e he))
  choose Pc hPc using hcor
  have hHyp : ∀ c, PVStep.Hyp ∅ W Up (Fc c) (Pc c) (fun w => fe w (idx c 0))
      (fun w => fe w (idx c 1)) := by
    intro c
    refine ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, ?_, fun e he =>
      hEl e (hFE e (hFcF c e he)), ?_, fun e he => hFW e (hFcF c e he), (hPc c).1, (hPc c).2,
      ?_⟩
    · rw [Finset.disjoint_left]
      intro x hxW hxU
      exact hWUp x hxU hxW
    · intro e he v hv
      rcases hFends e (hFcF c e he) v hv with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
    · intro w hw
      refine ⟨fun h => idx_ne c ((hfe w hw).2 h), Finset.mem_union_right _
        (hfC w hw _).2.2.1, Finset.mem_union_right _ (hfC w hw _).2.2.1, ?_, ?_⟩ <;>
      · intro hf
        rcases (hmemFc c _).1 hf with ⟨h, _⟩ | ⟨w', hw', k, hk, _, he⟩
        · exact (Finset.mem_sdiff.1 h).2 ((hmemCh _).2 ⟨w, hw, _, Or.inl (by
            have := idx_lt c 0; have := idx_lt c 1; omega), rfl⟩)
        · obtain ⟨_, rfl⟩ := hchinj w' hw' w hw k _ he
          have := idx_lt c 0
          have := idx_lt c 1
          rcases hk with h | h <;> omega
  have hpec1 : ∀ c, ∀ w ∈ W, pathEndCount (Pc c) w ≠ 1 := by
    intro c w hw h
    have := (hPc c).1.pathEndCount_mod_two w
    rw [h, hdegFc w hw c] at this
    exact absurd this (by norm_num)
  -- (e): the output of each class
  have hph := fun c => (hHyp c).exists_output_noRoot_even (hpec1 c)
  choose Dp Qp hDp using hph
  -- (f): closing
  have hcl : ∀ c, ∃ (Conn : Finset (Sym2 V)) (Dc : List (Obj V)),
      IsDecomp ((Fc c ∪ Res c ∪ Conn : Finset (Sym2 V)) : Set (Sym2 V)) Dc ∧
      Disjoint (Fc c ∪ Res c) Conn ∧ Conn ⊆ (O.restrictEdges (R j c)).edges ∧
      (∀ e ∈ Conn, ∀ v ∈ e, v ∈ Up) ∧ Dc.length = (Dp c).length + (Qp c).length ∧
      Dc.countP Obj.isEdge = (Dp c).countP Obj.isEdge := by
    intro c
    obtain ⟨hwf, hnd, hmem, hQ, hpec, _⟩ := hDp c
    refine TPVRun.close_class (hG2 j hj c) hwf hnd (X := Fc c ∪ Res c) ?_ ?_ ?_ ?_ ?_ ?_
    · intro e
      rw [hmem e]
      exact ⟨fun h => h.elim (Finset.mem_union_left _)
        (fun h => Finset.mem_union_right _ ((hmemRes c e).2 h)),
        fun h => (Finset.mem_union.1 h).imp id ((hmemRes c e).1)⟩
    · intro q hq
      obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
      refine ⟨h1, h2, h3, h4, fun x hx hxV => ?_⟩
      simp only [Vc, Finset.mem_filter] at hxV
      have hxW : x ∉ W := hWUp x hxV.1
      rcases h5 x hx with ⟨e, he, hxe⟩ | hxW' | ⟨w, hw, hx' | hx'⟩
      · exact hFckap c e he x hxe hxW hxV.2
      · exact hxW hxW'
      · rw [hx', (hfC w hw _).2.2.2] at hxV
        exact absurd hxV.2 (Fin.succ_ne_zero c).symm
      · rw [hx', (hfC w hw _).2.2.2] at hxV
        exact absurd hxV.2 (Fin.succ_ne_zero c).symm
    · intro x hx
      rw [FGraph.restrictEdges_verts, hOZ]
      exact (mem_U.1 hx).1
    · intro x hx
      exact (Finset.mem_filter.1 hx).1
    · intro v
      refine le_trans (Nat.cast_le.2 (hpec v)) ?_
      refine le_trans ?_ (hmult v)
      rw [Nat.cast_add, add_comm]
      push_cast
      refine add_le_add_left (Nat.cast_le.2 (Finset.card_le_card fun w hw => ?_)) _
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨hWZ w hw.1, ?_⟩
      rcases hw.2 with h | h <;> rw [h]
      · exact (hfC w hw.1 _).2.1
      · exact (hfC w hw.1 _).2.1
    · intro e he
      obtain ⟨w, hw, hwe⟩ := hFW e (by
        rcases Finset.mem_union.1 he with he | he
        · exact hFcF c e he
        · exact hResF c e he)
      exact ⟨w, hwe, fun hwU => hWUp w hwU hw⟩
  choose Conn Dc hDc using hcl
  have hConnR : ∀ c, ∀ e ∈ Conn c, e ∈ O.edges ∧ e ∈ R j c := fun c e he =>
    FGraph.mem_restrictEdges_edges.1 ((hDc c).2.2.1 he)
  have hConnUp : ∀ c, ∀ e ∈ Conn c, ∀ v ∈ e, v ∈ Up := fun c => (hDc c).2.2.2.1
  have hConnNotW : ∀ c, ∀ e ∈ Conn c, ∀ w ∈ W, w ∉ e := fun c e he w hw hwe =>
    hWUp w (hConnUp c e he w hwe) hw
  -- the parity edges
  let Par : Finset (Sym2 V) := (W.filter oddW).image fun w => s(w, fe w 8)
  have hParF : ∀ e ∈ Par, e ∈ F := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
    exact hchF w (Finset.mem_filter.1 hw).1 8
  -- the class sets and their disjointness
  have hmemX : ∀ c, ∀ e ∈ Fc c ∪ Res c, (e ∈ NR ∧ cls e = c) ∨ ∃ w ∈ W, ∃ k : Fin 9,
      (k : ℕ) < 8 ∧ chc (fa w) (fb w) k = c ∧ s(w, fe w k) = e := by
    intro c e he
    rcases Finset.mem_union.1 he with he | he
    · rcases (hmemFc c e).1 he with h | ⟨w, hw, k, hk, hc, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, k, by omega, hc, rfl⟩
    · obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he
      · exact Or.inr ⟨w, hw, idx c 0, by have := idx_lt c 0; omega, chc_idx _ _ c 0, rfl⟩
      · exact Or.inr ⟨w, hw, idx c 1, by have := idx_lt c 1; omega, chc_idx _ _ c 1, rfl⟩
  have hXdisj : ∀ c c', c ≠ c' → Disjoint (Fc c ∪ Res c) (Fc c' ∪ Res c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    rcases hmemX c e he with ⟨h1, hc1⟩ | ⟨w, hw, k, hk, hc, rfl⟩ <;>
      rcases hmemX c' _ he' with ⟨h2, hc2⟩ | ⟨w', hw', k', hk', hc', he2⟩
    · exact hcc' (hc1.symm.trans hc2)
    · rw [← he2] at h1
      exact (Finset.mem_sdiff.1 h1).2 ((hmemCh _).2 ⟨w', hw', k', Or.inl hk', rfl⟩)
    · exact (Finset.mem_sdiff.1 h2).2 ((hmemCh _).2 ⟨w, hw, k, Or.inl hk, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := hchinj w' hw' w hw k' k he2
      exact hcc' (hc.symm.trans hc')
  have hXConn : ∀ c c', Disjoint (Fc c ∪ Res c) (Conn c') := by
    intro c c'
    rw [Finset.disjoint_left]
    intro e he he'
    have heF : e ∈ F := by
      rcases Finset.mem_union.1 he with h | h
      · exact hFcF c e h
      · exact hResF c e h
    obtain ⟨w, hw, hwe⟩ := hFW e heF
    exact hConnNotW c' e he' w hw hwe
  have hConndisj : ∀ c c', c ≠ c' → Disjoint (Conn c) (Conn c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    have hd := hRd j hj j hj c c' (by simp [hcc'])
    exact Finset.disjoint_left.1 hd (hConnR c e he).2 (hConnR c' e he').2
  let Yc : Fin 3 → Finset (Sym2 V) := fun c => Fc c ∪ Res c ∪ Conn c
  have hYdisj : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint Yc := by
    intro c _ c' _ hcc'
    simp only [Function.onFun, Yc]
    rw [Finset.disjoint_left]
    intro e he he'
    rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
    · exact Finset.disjoint_left.1 (hXdisj c c' hcc') he he'
    · exact Finset.disjoint_left.1 (hXConn c c') he he'
    · exact Finset.disjoint_left.1 (hXConn c' c) he' he
    · exact Finset.disjoint_left.1 (hConndisj c c' hcc') he he'
  have hYdec : IsDecomp (((Finset.univ : Finset (Fin 3)).biUnion Yc : Finset (Sym2 V)) :
      Set (Sym2 V)) ((Finset.univ : Finset (Fin 3)).toList.flatMap Dc) :=
    isDecomp_finset_biUnion Finset.univ (Ds := Dc) hYdisj fun c _ => (hDc c).1
  have hParY : Disjoint Par ((Finset.univ : Finset (Fin 3)).biUnion Yc) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
    have hw' := (Finset.mem_filter.1 hw).1
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.1 he'
    rcases Finset.mem_union.1 hc with hc | hc
    · rcases hmemX c _ hc with ⟨h, _⟩ | ⟨w'', hw'', k, hk, _, he2⟩
      · exact (Finset.mem_sdiff.1 h).2 ((hmemCh _).2 ⟨w, hw', 8,
          Or.inr (Finset.mem_filter.1 hw).2, rfl⟩)
      · obtain ⟨_, rfl⟩ := hchinj w'' hw'' w hw' k 8 he2
        simp at hk
    · exact hConnNotW c _ hc w hw' (Sym2.mem_mk_left _ _)
  have hParDec : IsDecomp ((Par : Finset (Sym2 V)) : Set (Sym2 V)) (Par.toList.map Obj.edge) :=
    isDecomp_singletons Par fun e he => hEl e (hFE e (hParF e he))
  let T : Finset (Sym2 V) := Par ∪ (Finset.univ : Finset (Fin 3)).biUnion Yc
  have hTdec : IsDecomp ((T : Finset (Sym2 V)) : Set (Sym2 V))
      (Par.toList.map Obj.edge ++ (Finset.univ : Finset (Fin 3)).toList.flatMap Dc) := by
    rw [Finset.coe_union]
    exact hParDec.append hYdec (Finset.disjoint_coe.2 hParY)
  -- every edge of `T` is an edge of `F_j` or a connector
  have hTFC : ∀ e ∈ T, e ∈ F ∨ ∃ c, e ∈ Conn c := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact Or.inl (hParF e h)
    · obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.1 h
      rcases Finset.mem_union.1 hc with hc | hc
      · rcases Finset.mem_union.1 hc with hc | hc
        · exact Or.inl (hFcF c e hc)
        · exact Or.inl (hResF c e hc)
      · exact Or.inr ⟨c, hc⟩
  have hFT : ∀ e ∈ F, e ∈ T := by
    intro e he
    by_cases hch : e ∈ Chosen
    · obtain ⟨w, hw, k, hk, rfl⟩ := (hmemCh e).1 hch
      by_cases h8 : (k : ℕ) < 8
      · by_cases h6 : (k : ℕ) < 6
        · -- reserved
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨⟨k / 2, by omega⟩,
            Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_union_right _ ?_)⟩)
          rw [hmemRes]
          refine ⟨w, hw, ?_⟩
          rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
          · left
            congr 2
            ext; simp [idx]; omega
          · right
            congr 2
            ext; simp [idx]; omega
        · -- flexible
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨chc (fa w) (fb w) k,
            Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_union_left _ ?_)⟩)
          rw [hmemFc]
          exact Or.inr ⟨w, hw, k, by omega, rfl, rfl⟩
      · -- parity
        have hodd : oddW w := by
          rcases hk with hk | hk
          · exact absurd hk h8
          · exact hk
        have hk8 : k = 8 := by ext; simp; omega
        subst hk8
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, hodd⟩, rfl⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨cls e, Finset.mem_univ _,
        Finset.mem_union_left _ (Finset.mem_union_left _ ?_)⟩)
      rw [hmemFc]
      exact Or.inl ⟨Finset.mem_sdiff.2 ⟨he, hch⟩, rfl⟩
  have hConnS : ∀ c, ∀ e ∈ Conn c, e ∉ S := fun c e he =>
    hI2 j le_rfl hj c e (hConnR c e he).2 (hConnUp c e he)
  refine ⟨T, Par.toList.map Obj.edge ++ (Finset.univ : Finset (Fin 3)).toList.flatMap Dc,
    ?_, ?_, ?_, hTdec, ?_, ?_, ?_⟩
  · -- Disjoint T S
    rw [Finset.disjoint_left]
    intro e he heS
    rcases hTFC e he with h | ⟨c, hc⟩
    · exact ((hmemF e).1 h).2.1 heS
    · exact hConnS c e hc heS
  · -- T ⊆ E
    intro e he
    rcases hTFC e he with h | ⟨c, hc⟩
    · exact hFE e h
    · exact hOE (hConnR c e hc).1
  · -- F ⊆ T
    intro e he heS heW
    exact hFT e ((hmemF e).2 ⟨he, heS, heW⟩)
  · -- cost
    rw [List.length_append, List.length_map, Finset.length_toList, length_flatMap_toList]
    have hc : ∀ c ∈ (Finset.univ : Finset (Fin 3)), (Dc c).length ≤ 3 * Pj.card + W.card := by
      intro c _
      rw [(hDc c).2.2.2.2.1]
      have h1 := (hDp c).2.2.2.2.2.1
      have h2 : (Pc c).length ≤ Pj.card :=
        (hPc c).1.length_le_card (hPc c).2 fun e he => hFPj e (hFcF c e he)
      omega
    have := Finset.sum_le_sum hc
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    have hPar : Par.card ≤ W.card :=
      (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    have h3 : W.card ≤ Pj.card := Finset.card_le_card hWP
    omega
  · -- single edges
    rw [countP_isEdge_append, countP_isEdge_map_edge, Finset.length_toList,
      countP_isEdge_flatMap_toList]
    have h0 : ∀ c ∈ (Finset.univ : Finset (Fin 3)), (Dc c).countP Obj.isEdge = 0 := by
      intro c _
      rw [(hDc c).2.2.2.2.2]
      exact (hDp c).2.2.2.2.2.2
    rw [Finset.sum_eq_zero h0, add_zero]
    exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  · -- the invariants persist
    refine ⟨?_, ?_, ?_⟩
    · intro e he heST v hv
      have heS : e ∉ S := fun h => heST (Finset.mem_union_left _ h)
      have heT : e ∉ T := fun h => heST (Finset.mem_union_right _ h)
      have h1 := hI1 e he heS v hv
      rcases Nat.lt_or_ge j (lev v) with h | h
      · exact h
      · exfalso
        have hvW : v ∈ W := mem_Wt.2 ⟨(mem_H0.1 he).2 v hv, le_antisymm h h1⟩
        exact heT (hFT e ((hmemF e).2 ⟨he, heS, v, hvW, hv⟩))
    · intro j' hj' hj'J c' e he hU' heST
      have hjj' : j ≠ j' := by omega
      have hUj : ∀ v ∈ e, v ∈ Up := fun v hv => U_anti (by omega) (hU' v hv)
      rcases Finset.mem_union.1 heST with heS | heT
      · exact hI2 j' (by omega) hj'J c' e he hU' heS
      · rcases hTFC e heT with h | ⟨c, hc⟩
        · obtain ⟨w, hw, hwe⟩ := hFW e h
          exact hWUp w (hUj w hwe) hw
        · have hd := hRd j hj j' hj'J c c' (by simp [hjj'])
          exact Finset.disjoint_left.1 hd (hConnR c e hc).2 he
    · intro j' hj' hj'J w hw u hu hM heST
      have hjj' : j ≠ j' := by omega
      rcases Finset.mem_union.1 heST with heS | heT
      · exact hI3 j' (by omega) hj'J w hw u hu hM heS
      · have hwW : w ∉ W := Wt_ne hjj' hw
        have huW : u ∉ W := hWUp u (U_anti (by omega) hu)
        rcases hTFC _ heT with h | ⟨c, hc⟩
        · obtain ⟨x, hx, hxe⟩ := hFW _ h
          rcases Sym2.mem_iff.1 hxe with rfl | rfl
          · exact hwW hx
          · exact huW hx
        · exact Finset.disjoint_left.1 (hRM j hj c) (hConnR c _ hc).2 hM

end VXRun

end EG
