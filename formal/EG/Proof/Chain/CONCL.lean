module

public import EG.Spec.Chain.CONCL
public import EG.Proof.Chain.CONC
public import EG.Lib.Found.Gamma

/-!
# Proof of Theorem CONC-L (i)–(iii), the bound `α_{Y,l} < θ^GC_r(Y^0)` and the per-ancestor bound
(manuscript s6:thmCONCL)

Unit P3B (probe P-3, part 2), proof round 1. Statements: `EG/Spec/Chain/CONCL.lean`. Design note
`formal/work/p2b/P3B.md` (the per-ancestor bound is the named refutation target of probe P-3).

* (i), (ii): ORIGIN^τ (a), (b) (`EG.originTypes`, `EG.originThin`): an edge `hu`, `u ∈ Y \ Dup*_r`,
  is (β) (then `h ∉ Y^0`, counted by the thin cut) or (α) (then `h ∈ S_Y` and `hu ∈ E(X^0_Y)`).
  "No such `u` if `h ∈ Y`" follows from the exclusivity of the two types (no appeal to Lemma EL).
* (iii): the port-counting form of `d_{Y,l}(h)`; ports in `Dup*_r` are counted by `d^*`, the
  others by (i) if `h ∉ S_Y`, by the definition of `α_{Y,l}` if `h ∈ S_Y`.
* `alphaY_le_thetaGC_sub_one`: `α_{Y,l} ≤ θ^GC_r(Y^0) - 1` for every valid run (by (ii) and rule
  (GC)); with `θ^GC ≥ 1` under Γ1 this is (iv), first sentence.
* the per-ancestor bound: (iii) and the previous item for light `Y`, Theorem CONC (ii) for
  standalone `Y`, and `m_{Y,l} = 0` for `l ≤ r(Y)`.
-/

public section

namespace EG

open EG.HB EG.Chain

namespace Chain

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}

/-- For a light pre-part, `V(Y) = Y^0 \ S_Y`. -/
theorem ancVerts_of_isLight {r : ℕ} {a : Addr} (hl : run.isLight G r a) :
    run.ancVerts G (r, a) = run.Z0 G r a \ run.guests G r a := by
  classical
  show Round.partVerts _ _ a = _
  unfold Round.partVerts
  rw [if_pos (show Round.isLight _ _ a from hl)]
  rfl

end Chain

open Classical in
/-- [s6:thmCONCL] (i) "If `h ∉ S_Y`: `#{u ∈ Y \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r - 1`, and there are
no such `u` if `h ∈ Y`." -/
theorem concLI : EG.Spec.ConcLIStatement := by
  intro V _ G Dstar run hv r a ha hl l hrl h hh
  have hR := Run.isRound_of_mem_prePartAddrs ha
  have hr : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  -- every counted `u` gives a (β)-edge `hu`
  have hβ : ∀ u ∈ ((run.Z0 G r a \ run.guests G r a) \ run.DupStar G r).filter
      (fun u => s(h, u) ∈ (run.graph G l).edges), run.OriginBeta G r a u h := by
    intro u hu
    obtain ⟨hu1, he⟩ := Finset.mem_filter.1 hu
    obtain ⟨hu2, hD⟩ := Finset.mem_sdiff.1 hu1
    have hu3 : u ∈ run.Z0 G r a \ run.DupStar G r :=
      Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hu2).1, hD⟩
    obtain ⟨-, -, -, -, hcl, -⟩ := originTypes V G Dstar run hv r hr a ha u hu3
    have he' : s(u, h) ∈ (run.graph G l).edges := by rw [Sym2.eq_swap]; exact he
    rcases hcl l (by omega) h he' with ⟨hb, -, -⟩ | ⟨hα, -, -⟩
    · exact hb
    · exact absurd hα.2.1 hh
  refine ⟨?_, fun hY => ?_⟩
  · refine le_trans (Finset.card_le_card ?_) (originThin V G Dstar run hv r hr a ha h l (by omega))
    intro u hu
    obtain ⟨hu1, he⟩ := Finset.mem_filter.1 hu
    obtain ⟨hu2, hD⟩ := Finset.mem_sdiff.1 hu1
    exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hu2).1, hD⟩, he, hβ u hu⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro u hu
    exact (hβ u hu).1 (Finset.mem_sdiff.1 hY).1

open Classical in
/-- [s6:thmCONCL] (ii) "If `h ∈ S_Y`: every such `hu` is an edge of `X^0_Y`, and their number is
at most `e_{X^0_Y}(h, Y)`." -/
theorem concLII : EG.Spec.ConcLIIStatement := by
  intro V _ G Dstar run hv r a ha hl l hrl h hh
  have hR := Run.isRound_of_mem_prePartAddrs ha
  have hr : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  have hX : ∀ u ∈ (run.Z0 G r a \ run.guests G r a) \ run.DupStar G r,
      s(h, u) ∈ (run.graph G l).edges → s(h, u) ∈ (run.X0 G r a).edges := by
    intro u hu he
    obtain ⟨hu2, hD⟩ := Finset.mem_sdiff.1 hu
    have hu3 : u ∈ run.Z0 G r a \ run.DupStar G r :=
      Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hu2).1, hD⟩
    obtain ⟨-, -, -, -, hcl, -⟩ := originTypes V G Dstar run hv r hr a ha u hu3
    have he' : s(u, h) ∈ (run.graph G l).edges := by rw [Sym2.eq_swap]; exact he
    rcases hcl l (by omega) h he' with ⟨hb, -, -⟩ | ⟨hα, -, -⟩
    · exact absurd (HB.Run.guests_subset_Z0 r a hh) hb.1
    · rw [Sym2.eq_swap]; exact hα.2.2
  refine ⟨hX, ?_⟩
  rw [← FGraph.card_nbrs_inter_eq_eBetween]
  refine Finset.card_le_card (fun u hu => ?_)
  obtain ⟨hu1, he⟩ := Finset.mem_filter.1 hu
  exact Finset.mem_inter.2 ⟨FGraph.mem_nbrs.2 (hX u hu1 he), (Finset.mem_sdiff.1 hu1).1⟩

namespace Chain

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}

/-- `α_{Y,l} ≤ θ^GC_r(Y^0) - 1` for a light part of every valid run and every `l ≥ r + 1`
(proof of s6:thmCONCL (iv): the counted edges are distinct `X^0_Y`-edges from `x` into `Y`, by
(ii), and rule (GC) bounds them). No hypothesis on `D_*`. -/
theorem alphaY_le_thetaGC_sub_one {Dstar : ℝ} (hv : run.Valid G Dstar) {r : ℕ} {a : Addr}
    (ha : a ∈ run.prePartAddrs G r) (hl : run.isLight G r a) {l : ℕ} (hrl : r + 1 ≤ l) :
    alphaY run G δ (r, a) l ≤ run.thetaGC G r a - 1 := by
  classical
  unfold alphaY
  refine Finset.sup_le (fun x hx => ?_)
  have hgc := (Run.isGC_iff_eBetween run G r a).1 hl.2.2 x hx
  have hII := (concLII _ G Dstar run hv r a ha hl l hrl x hx).1
  have hle : ((run.ancVerts G (r, a) \ run.DupStar G r).filter (fun u =>
      ∃ a' ∈ run.Std G l, u ∈ run.classed G l a' ∧ δ l u = (r, a) ∧ s(x, u) ∈ run.E G l a')).card
      ≤ (run.X0 G r a).eBetween {x} (run.Z0 G r a \ run.guests G r a) := by
    rw [← FGraph.card_nbrs_inter_eq_eBetween]
    refine Finset.card_le_card (fun u hu => ?_)
    obtain ⟨hu1, a', -, -, -, he⟩ := Finset.mem_filter.1 hu
    rw [ancVerts_of_isLight hl] at hu1
    exact Finset.mem_inter.2 ⟨FGraph.mem_nbrs.2 (hII u hu1 (E_subset_graph_edges l a' he)),
      (Finset.mem_sdiff.1 hu1).1⟩
  simp only at hle ⊢
  omega

/-- Under Γ1, `θ^GC_r(Y^0) ≥ 1` for every pre-part of a round (`λ_r > 0`, `|Y^0| ≥ P_r ≥ 1`). -/
theorem one_le_thetaGC {Dstar : ℝ} (hΓ : Gamma1core Dstar) (hv : run.Valid G Dstar) {r : ℕ}
    {a : Addr} (ha : a ∈ run.prePartAddrs G r) : 1 ≤ run.thetaGC G r a := by
  have hR := Run.isRound_of_mem_prePartAddrs ha
  have hd : Dstar ≤ run.d G r := Run.Valid.dstar_le run G hv hR
  have hlam : 1 < lamOf (run.d G r) := by
    unfold lamOf
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith [hΓ.two_lt])]
    norm_num; linarith [hΓ.two_lt]
  have hP : POf (run.d G r) ≤ (run.Z0 G r a).card := by
    rw [Run.prePartAddrs_of_isRound run G hR] at ha
    exact (Finset.mem_filter.1 ha).2
  have hP1 : 1 ≤ POf (run.d G r) := by
    unfold POf
    rw [Nat.one_le_ceil_iff]
    positivity
  have hz : (1 : ℝ) ≤ ((run.Z0 G r a).card : ℝ) := by exact_mod_cast hP1.trans hP
  rw [Run.thetaGC_eq]
  unfold HB.thetaGC
  rw [Nat.one_le_ceil_iff]
  have : 0 < lamOf (run.d G r) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  positivity

end Chain

open Chain in
/-- [s6:thmCONCL] (iii) "For every designation, `m_{Y,l} ≤ max(τ_r - 1, α_{Y,l}) + d^*_{Y,l}`." -/
theorem concLIII : EG.Spec.ConcLIIIStatement := by
  classical
  intro V _ G Dstar run hv δ hδ r a ha hl l hrl
  unfold mY
  refine Finset.sup_le (fun h _ => ?_)
  refine classDeg_le_dStar_add (r, a) l h _ ?_
  -- the ports outside `Dup*_r` lie in `Y \ Dup*_r` and have `hu ∈ E(G_l)`
  have hmem : ∀ u ∈ ((classedPorts run G l).filter (fun u => δ l u = (r, a) ∧
      ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ s(h, u) ∈ run.E G l a)).filter
        (fun u => u ∉ run.DupStar G (r, a).1),
      u ∈ (run.Z0 G r a \ run.guests G r a) \ run.DupStar G r ∧
        s(h, u) ∈ (run.graph G l).edges ∧
        ∃ a' ∈ run.Std G l, u ∈ run.classed G l a' ∧ δ l u = (r, a) ∧ s(h, u) ∈ run.E G l a' := by
    intro u hu
    obtain ⟨hu1, hD⟩ := Finset.mem_filter.1 hu
    obtain ⟨-, hY, a', ha', hua', he⟩ := Finset.mem_filter.1 hu1
    obtain ⟨-, hV, -, -, hG⟩ := classPort_facts hδ ha' hua' he
    rw [hY, ancVerts_of_isLight hl] at hV
    exact ⟨Finset.mem_sdiff.2 ⟨hV, hD⟩, hG, a', ha', hua', hY, he⟩
  by_cases hh : h ∈ run.guests G r a
  · refine le_trans ?_ (le_max_right _ _)
    unfold alphaY
    refine le_trans ?_ (Finset.le_sup (f := fun x =>
      ((run.ancVerts G (r, a) \ run.DupStar G (r, a).1).filter (fun u =>
        ∃ a' ∈ run.Std G l, u ∈ run.classed G l a' ∧ δ l u = (r, a) ∧
          s(x, u) ∈ run.E G l a')).card) hh)
    refine Finset.card_le_card (fun u hu => ?_)
    obtain ⟨h1, -, h3⟩ := hmem u hu
    rw [ancVerts_of_isLight hl]
    exact Finset.mem_filter.2 ⟨h1, h3⟩
  · refine le_trans ?_ (le_max_left _ _)
    refine le_trans (Finset.card_le_card ?_) (concLI V G Dstar run hv r a ha hl l hrl h hh).1
    intro u hu
    obtain ⟨h1, h2, -⟩ := hmem u hu
    exact Finset.mem_filter.2 ⟨h1, h2⟩

open Chain in
/-- [s6:thmCONCL] (iv), first sentence, "`α_{Y,l} < θ^GC_r(Y^0)`." -/
theorem concLAlpha : EG.Spec.ConcLAlphaStatement := by
  intro V _ G Dstar run hΓ hv δ _ r a ha hl l hrl
  have h1 := alphaY_le_thetaGC_sub_one (δ := δ) hv ha hl hrl
  have h2 := one_le_thetaGC hΓ hv ha
  omega

open Chain in
/-- [s6:thmCONCL] (proof of (iv)) "`m_{Y,l} ≤ (τ_r - 1) + (θ^GC_r(Y^0) - 1) + d^*_{Y,l}` (`Y`
light), `m_{Y,l} ≤ τ_r - 1 + d^*_{Y,l}` (`Y` standalone), the latter by Theorem
[s6:thmCONC](ii); GC-parts are standalone": the per-ancestor bound. -/
theorem concLPerAncestor : EG.Spec.ConcLPerAncestorStatement := by
  classical
  intro V _ G Dstar run hv δ hδ Y hY l
  obtain ⟨r, a⟩ := Y
  have ha : a ∈ run.prePartAddrs G r := (Run.mem_ancestors run G).1 hY
  refine ⟨fun hl => ?_, fun hnl => ?_⟩
  · by_cases hrl : r + 1 ≤ l
    · have h3 := concLIII V G Dstar run hv δ hδ r a ha hl l hrl
      have h4 := alphaY_le_thetaGC_sub_one (δ := δ) hv ha hl hrl
      simp only at h3 h4 ⊢
      have : max (run.tau G r - 1) (alphaY run G δ (r, a) l) ≤
          (run.tau G r - 1) + (run.thetaGC G r a - 1) :=
        max_le (Nat.le_add_right _ _) (h4.trans (Nat.le_add_left _ _))
      omega
    · rw [mY_eq_zero_of_not_anc run G δ hδ (fun h => hrl (by simp only at h; omega))]
      exact Nat.zero_le _
  · exact concII V G Dstar run hv δ hδ r a ((Run.mem_Std_iff run G).2 ⟨ha, hnl⟩) l

end EG
