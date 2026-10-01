module

public import EG.Spec.Light.Zones
public import EG.Proof.Todo.EqZp
public import EG.Proof.Light.Setting
public import EG.Lib.Stage1.Zones
public import EG.Lib.Stage1.Law

/-!
# [s5:lemZones] (formerly a declared input of probe P4B; proved in P3)

Upstream s5 lemma; used by s5:lemE1 (c) (`EG.Spec.ParentBadProbStatement`). Design note
`formal/work/p2b/P4B.md`.

Proof (P3), as in `s5.tex`: (i) is (s5:eqZp) (`EG.Todo.EqZp`, `zp_Y = L_Y^{-2}`); in particular
the guard `Σ_{Y ∈ A(v)} zp_Y ≤ 1` of the zone-label law holds at every vertex. (ii) the zone is a
`ρ_Y`-random subset under the zone law (`EG.Stage1.isRSubset_Zone`), transported to the joint
stage-1 law by `EG.Stage1.map_zone`; `ρ_Y ≥ 1/(12L_Y^5)` from `R − r − 1 ≤ L_Y/102`
((s5:eqLY), `EG.eqLY`) and `T^sl_Y = ⌈L_Y^2⌉ ≤ 2L_Y^2`. (iii) every vertex has one label
(`EG.Stage1.disjoint_Zone`). (iv) the zones are functions of component (1b), which is independent
of (1a), (1c) (`EG.Stage1.indepFun_colJS_zone`).
-/

public section

namespace EG

open EG.HB EG.Stage1 Real

/-- Proved in P3. [s5:lemZones] Lemma zones (i)–(iv). -/
theorem lemZones : EG.Spec.LemZonesStatement := by
  classical
  intro V _ G N0 Dstar run hR
  have hZp := EG.Todo.EqZp V G N0 Dstar run hR
  have hLY := EG.eqLY V G N0 Dstar run hR
  -- (i)
  have hi : ∀ v : V, ∑ Y ∈ (run.lightParts G).filter (fun Y => v ∈ run.ancVerts G Y),
      zp G run Y ≤ 1 / 2 := fun v => (hZp v).le
  -- the guard of the zone-label law
  have hg : ∀ v : V, zpSum G run v ≤ 1 := by
    intro v
    have hsub : availParts G run v ⊆
        (run.lightParts G).filter (fun Y => v ∈ run.ancVerts G Y) := by
      intro Y hY
      simp only [availParts, Finset.mem_filter] at hY ⊢
      exact ⟨hY.1, hY.2.1⟩
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun Y => zp G run Y) (fun Y _ _ => zp_nonneg G run Y)
    unfold zpSum
    linarith [hi v]
  refine ⟨hi, ?_, ?_, ?_⟩
  · -- (ii)
    intro Y hY hYR
    refine ⟨fun i hiU => ?_, ?_⟩
    · have h := isRSubset_Zone G run hY hYR (fun v _ => hg v) hiU
      rw [← map_zone G run, FinDist.isRSubset_map_iff] at h
      exact h
    · obtain ⟨-, -, h3, h4, -, h6, h7⟩ := hLY Y hY
      set L := run.LY G Y with hL
      set lam := run.lam G Y.1
      have hlog : (2 : ℝ) ≤ logb 2 lam := by
        have : (0 : ℝ) ≤ (logStar (run.d G Y.1) : ℝ) := Nat.cast_nonneg _
        linarith
      have hL1 : (1 : ℝ) ≤ L := by linarith
      have hLpos : (0 : ℝ) < L := by linarith
      have hk1 : (1 : ℝ) ≤ (run.R : ℝ) - (Y.1 : ℝ) - 1 := by
        have : ((Y.1 + 2 : ℕ) : ℝ) ≤ (run.R : ℝ) := by exact_mod_cast hYR
        push_cast at this
        linarith
      have hk2 : (run.R : ℝ) - (Y.1 : ℝ) - 1 ≤ L / 102 := by linarith
      have hT1 : (1 : ℝ) ≤ (Tslot G run Y : ℝ) := by
        have : 1 ≤ Tslot G run Y := Nat.one_le_ceil_iff.2 (by positivity)
        exact_mod_cast this
      have hT2 : (Tslot G run Y : ℝ) ≤ 2 * L ^ 2 := by
        have : (Tslot G run Y : ℝ) ≤ L ^ 2 + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
        nlinarith
      have hDpos : 0 < ((run.R : ℝ) - (Y.1 : ℝ) - 1) * 4 * (Tslot G run Y : ℝ) := by
        positivity
      have hD : ((run.R : ℝ) - (Y.1 : ℝ) - 1) * 4 * (Tslot G run Y : ℝ) ≤ 12 * L ^ 3 := by
        have hk0 : (0 : ℝ) ≤ (run.R : ℝ) - (Y.1 : ℝ) - 1 := by linarith
        have := mul_le_mul hk2 hT2 (by positivity) (by positivity)
        nlinarith
      unfold rhoY zp
      rw [← hL, zpow_neg, zpow_ofNat, div_le_div_iff₀ (by positivity) hDpos]
      have e : (L ^ 2)⁻¹ * (12 * L ^ 5) = 12 * L ^ 3 := by
        field_simp
      rw [e]
      linarith
  · -- (iii)
    intro ζ Y _ Y' _ i _ i' _ hne
    exact disjoint_Zone ζ hne
  · -- (iv)
    exact (indepFun_colJS_zone G run).comp id (fun ζ (p : ZIdx) => Zone G run ζ p.1 p.2)

end EG
