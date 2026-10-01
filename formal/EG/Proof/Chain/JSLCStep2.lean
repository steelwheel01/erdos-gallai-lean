module

public import EG.Proof.Chain.JSLCStep2Count
public import EG.Proof.HB.CapPrePart

/-!
# Proof of Step 2 of Lemma JS-LC: the set `J_l`, the realized beads, (J1) aggregated
(manuscript s6:lemJSLC, proof, Steps 2–3; s6:lemJplus)

Probe unit P2J (probe P-2, part 2), proof round 1. `EG.jslcStep2 : EG.Spec.JslcStep2Statement`.
The construction is in `EG.Proof.Chain.JSLCStep2Defs` (PAR per part and pair of classes, then one
move per (centre, class) with odd degree in `R^0_Y`, the degree aggregated over all parts of round
`l`), the facts in `…Facts` (structure and parity), `…JPlus` (partition, `R_Y ⊆ Bead`, Lemma J⁺)
and `…Count` ((s6:eqJbound)).

**Refutation target of probe P-2** ("two `J^hub` edges of one class at one hub in one round"):
the conjunct `∀ h ∈ D_l, ∀ Y, #{e ∈ J_l : e is a J^hub-edge of class Y at h} ≤ 1` is proved
(`Step2Hyp.jPlusProps`, field `J1hub`, via `Step2Hyp.card_filter_le_one`): a `J^hub`-edge `hu` of
class `Y` is not a PAR deletion (those are port–port, and a hub is not a port), so it is a moved
edge; a moved edge `cu` with `u ∈ Q*_Z` of class `Y` and `c ∉ Q*_Z` is `mv Y c`, the unique edge
moved at the pair `(c, Y)` (`Step2Hyp.eq_mv_of_mem_Jmov`); the degree deciding the move is
`degE (R^0_Y) c`, which counts the class-`Y` edges at `c` over **all** parts of round `l`.

Declared input used: `EG.capPrePart` (s2:lemCap (ii), per-part degree `≤ M_l − 1`). Lemma EL
enters through `EG.jslcTypes` (proved). Lemma PAR: `EG.par`, `EG.parExists` (proved).
-/

public section

namespace EG

open EG.HB EG.Chain EG.Chain.Step2

/-- The Step 2 hypotheses from the hypotheses of JS-LC (Step 1 facts by `EG.jslcTypes`, Lemma
s2:lemCap(ii) by `EG.capPrePart`). -/
theorem step2Hyp_of {V : Type*} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}
    {δ : Designation V} {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)}
    (hΓ : Gamma2a Dstar) (hrun : run.Valid G Dstar) (hδ : IsDesignation run G δ) (hl : 3 ≤ l)
    (hlR : l ≤ run.R)
    (hB : ∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ qs run G δ S l a, u ∈ e) :
    Step2Hyp run G δ S l B where
  l3 := hl
  hδ := hδ
  hB := hB
  ends a ha := (EG.jslcTypes V G Dstar run δ S l a hrun hδ hl ha).2.1
  el a ha u hu h he := ((EG.jslcTypes V G Dstar run δ S l a hrun hδ hl ha).2.2.1 u hu h he).1
  pp a ha := (EG.jslcTypes V G Dstar run δ S l a hrun hδ hl ha).2.2.2
  cap a ha v := ((EG.capPrePart V G Dstar run hΓ hrun l (Finset.mem_Icc.2 ⟨by omega, hlR⟩)).2 a
    (Std_subset_prePartAddrs run G l ha)).2 v

/-- [s6:lemJSLC:proof-step-2] Step 2 of the proof of Lemma JS-LC and the first paragraph of
Step 3, with Lemma J⁺ for `J_l`: "(2a) … Apply Lemma s6:lemPAR … (2b) … For each `Y` and each
vertex `h` that is the centre of an odd number of edges of `R^0_Y`, move one such edge (any one)
into `J_l`. Let `R_Y` be the rest: the realized class-`Y` beads. Finally, `J_l` consists of all
edges `J'_ab(Z)` and all moved edges. … So after the moves every centre has even degree in every
`R_Y`. … This proves (s6:eqJbound)." -/
theorem jslcStep2 : EG.Spec.JslcStep2Statement := by
  intro V _ G Dstar run δ S l B hΓ hrun hδ hl hlR hB
  have H : Step2Hyp run G δ S l B := step2Hyp_of hΓ hrun hδ hl hlR hB
  have hJP := H.jPlusProps
  exact ⟨J run G δ S l B, R run G δ S l B, H.J_subset, fun Y => Step2Hyp.R_subset Y, H.cover,
    H.disjoint_J_R, fun Y Y' h => H.R_disjoint h, H.R_struct, fun Y h hh => H.even_degE_R Y hh,
    H.R_subset_Bead, hJP.J1hub, H.card_J_le_jBound, hJP⟩

end EG
