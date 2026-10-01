module

public import EG.Spec.HB.Structure
public import EG.Lib.HB.StructureAux
public import EG.Lib.HB.TowerRun

/-!
# Proposition s2:propStructure (iv) (formerly a declared input of probe P4B; proved in P3, unit P3-s2)

Stub of a declared input of probe unit P4B (probe P-4, part 2), placed at the natural path of the
future proof (P4A pattern). The Spec `EG.Spec.StructureVertexStatement` is the s2 unit's
(`EG/Spec/HB/Structure.lean`, `formal/work/p2s/s2b.md`); the s2 unit owns this file and replaces
the stub by its proof. P4B uses only the first clause ("light parts of one round are pairwise
vertex-disjoint"), through `EG.structureLight` (`EG/Proof/HB/StructureLight.lean`), which is
derived from this stub (fix round of `formal/work/p2b/P4B.md`). It is not proved by the probe.
-/

public section

namespace EG

/-- Proved in P3. [s2:propStructure] (iv) "light parts of one round are pairwise
vertex-disjoint, and `|Y| ≥ |Y^0|/2 ≥ P_r/2` for every light part `Y` of round `r`; every vertex
outside `D_l` lies in at most one round-`l` pre-part; the port sets `U_Z` of distinct `Z ∈ Std_l`
are pairwise disjoint; and each vertex lies in at most one light part per round, namely in the
light part of `home_l(v)` if that pre-part is light". -/
theorem structureVertex : EG.Spec.StructureVertexStatement := by
  classical
  intro V _ G Dstar run hv l hl
  have hr : run.IsRound l := Finset.mem_Icc.1 hl
  have hval : EG.HB.Round.Valid (run.graph G l) (run.choice l) := (hv.1 l hl).2
  have hP : run.prePartAddrs G l =
      EG.HB.Round.prePartAddrs (run.graph G l) (run.choice l) :=
    EG.HB.Run.prePartAddrs_of_isRound run G hr
  have hD : run.D G l = EG.HB.Round.D (run.graph G l) (run.choice l) := if_pos hr
  have hhome : ∀ a ∈ run.prePartAddrs G l, run.isLight G l a → ∀ v ∈ run.partVerts G l a,
      run.home G l v = some a := by
    intro a ha hla v hv'
    rw [hP] at ha
    exact EG.HB.Round.home_eq_of_mem_partVerts _ _ hval ha hla hv'
  have hone : ∀ v : V, v ∉ run.D G l →
      ((run.prePartAddrs G l).filter (fun a => v ∈ run.Z0 G l a)).card ≤ 1 := by
    intro v hvD
    rw [hD] at hvD
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, hP] at ha hb
    exact EG.HB.Round.eq_of_notMem_D _ _ hvD ha.1 hb.1 ha.2 hb.2
  refine ⟨?_, ?_, hone, ?_, hhome, ?_⟩
  · intro a ha b hb hab hla hlb
    rw [Finset.disjoint_left]
    intro v hva hvb
    have h1 := hhome a ha hla v hva
    have h2 := hhome b hb hlb v hvb
    rw [h1] at h2
    exact hab (Option.some_injective _ h2)
  · intro a ha hla
    have hL1 := hla.1
    change 2 * (run.guests G l a).card ≤ (run.Z0 G l a).card at hL1
    have hpv : run.partVerts G l a = run.Z0 G l a \ run.guests G l a := by
      change EG.HB.Round.partVerts _ _ a = _
      unfold EG.HB.Round.partVerts; exact if_pos hla
    have hsub : run.guests G l a ⊆ run.Z0 G l a := EG.HB.Round.guests_subset _ _ a
    have hc : (run.partVerts G l a).card = (run.Z0 G l a).card - (run.guests G l a).card := by
      rw [hpv, Finset.card_sdiff_of_subset hsub]
    have hPZ := EG.HB.Run.P_le_card_Z0 ha
    refine ⟨?_, ?_⟩
    · have : (run.Z0 G l a).card ≤ 2 * (run.partVerts G l a).card := by omega
      have : ((run.Z0 G l a).card : ℝ) ≤ 2 * ((run.partVerts G l a).card : ℝ) := by
        exact_mod_cast this
      linarith
    · have : (run.P G l : ℝ) ≤ (run.Z0 G l a).card := by exact_mod_cast hPZ
      linarith
  · intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro v hva hvb
    unfold EG.HB.Run.ports at hva hvb
    rw [Finset.mem_sdiff] at hva hvb
    have ha' : a ∈ run.prePartAddrs G l := (EG.HB.Run.mem_Std_iff run G).1 ha |>.1
    have hb' : b ∈ run.prePartAddrs G l := (EG.HB.Run.mem_Std_iff run G).1 hb |>.1
    exact hab (Finset.card_le_one.1 (hone v hva.2) a (Finset.mem_filter.2 ⟨ha', hva.1⟩) b
      (Finset.mem_filter.2 ⟨hb', hvb.1⟩))
  · intro v
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have h1 := hhome a ha.1 ha.2.1 v ha.2.2
    have h2 := hhome b hb.1 hb.2.1 v hb.2.2
    rw [h1] at h2
    exact Option.some_injective _ h2

end EG
