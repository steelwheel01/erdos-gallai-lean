module

public import EG.Spec.Light.ParentRun
public import EG.Spec.Light.Zones
public import EG.Proof.Stage1.COLc
public import EG.Proof.Light.Zones
public import EG.Lib.Stage1.Law

/-!
# Proof of the parent-bad probability (manuscript s5:lemE1 (c), proof, first step)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.parentBadProb`
(`ParentBadProbStatement`): "By Lemma s5:lemZones(ii),(iv), for every sublabel `(l,c,σ)` of `Y`
the set `V_{l,c,σ} := Zone_{Y,l,c,σ} ⊆ V(Y)` contains each vertex of `Y` independently with
probability `ρ_Y ≥ 1/(12L_Y^5)`, independently of the colouring of `Y`. (The zones of `Y` are
dependent across indices, since they are disjoint; Lemma s3:lemCOL(c) allows this.) So Lemma
s3:lemCOL(c), applied with this family, gives `P(Y parent-bad) ≤ |Y|^{-2}/2`."

Inputs: `EG.colc` (proved, `EG/Proof/Stage1/COLc.lean`), the declared input `EG.lemZones`
([s5:lemZones] (ii)), and the independence of the zones from the lending data of `Y` in the
stage-1 law (`EG.Stage1.indepFun_cOutAt_zone`, Lib). Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemE1] (c), proof: `P(Y parent-bad) ≤ |Y|^{-2}/2`, by Lemma COL (c) applied to the zones
of `Y`. -/
theorem parentBadProb : EG.Spec.ParentBadProbStatement.{u} := by
  intro V _ G N0 Dstar run h Y hY
  have hZ := lemZones V G N0 Dstar run h
  obtain ⟨hΓ, -, -, -, hd1, hV⟩ := h
  have hanc : Y ∈ run.ancestors G := COLcAux.mem_ancestors_of_mem_lightParts hY
  have hind : (law G run).IndepFun (fun ω => ω.cOutAt Y)
      (fun ω (i : LentTag) => Zone G run ω.zone Y i) :=
    (indepFun_cOutAt_zone G run Y).comp id fun ζ i => Zone G run ζ Y i
  refine colc V G Dstar run hΓ hV hd1 Y hY (Outcome G run) (law G run) (fun ω => ω.cOutAt Y)
    (fun ω i => Zone G run ω.zone Y i) (fun _ => rhoY G run Y) (map_cOutAt G run hanc) ?_ hind
  intro i hi
  obtain ⟨-, l, c, σ, -, hl, -⟩ := mem_IU.1 hi
  have hR : Y.1 + 2 ≤ run.R := by have := (mem_lateRounds run).1 hl; omega
  exact ⟨(hZ.2.1 Y hY hR).1 i hi, (hZ.2.1 Y hY hR).2⟩

end EG
