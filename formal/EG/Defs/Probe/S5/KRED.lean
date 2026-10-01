module

public import EG.Defs.Light.Stages

/-!
# The standalone edge set `K_std` and the hypothesis on `Lent_ext` of Lemma K-RED (s5:lemKRED)

NEW DEFS FILE of the P2 s5 Spec unit (`formal/work/p2s/s5.md`). Blueprint s5 (lemKRED,
`defs_needed`): "Defs `Kstd`, `LentExtHyp`"; no locked Defs file provides them. The s6b
blueprint (s6:lemLent (iv), `lentext_KREDhyp`) consumes the hypothesis by name.

Manuscript v6.1, `s5.tex` (before Lemma [s5:lemKRED]): "Put
`K_std := ⊔_l ⊔_{Z ∈ Std_l} E_l(Z)`. Here `Std_l` is the deterministic family of Definition
[s2:defHBtp] … so `K_std` is a function of the run alone". Lemma [s5:lemKRED]: "Let
`(Lent_ext(Y))_Y` be *any* family, indexed by the light parts `Y`, such that for every light part
`Y`, `Lent_ext(Y) ⊆ (⋃_{l,j} LJS_{Y,l,j}) ∪ (⋃_l LJV_{Y,l})`, and `Lent_ext(Y) = ∅` if `Y` is
demoted."

Formal reading.
* `Kstd G run`: the union over the rounds `1 ≤ l ≤ R` and the addresses `a ∈ Std_l` of `E_l(a)`
  (`run.Std G l` and `run.E G l a` are empty outside `[1, R]`).
* The JS-lent classes `LJS_{Y,l,j}` exist for the indices `(l, j) ∈ I^JS(Y)`
  (`r + 2 ≤ l ≤ R`, `0 ≤ j < K^JS_l`) and the JV-lent classes `LJV_{Y,l}` for `l ∈ I^JV(Y)`
  (`r + 2 ≤ l ≤ R`) ([s3:defCOL] (ii)); the unions range over exactly these indices. The classes
  are those of the colouring of `Y` in the stage-1 outcome `ω` (`ω.colAt Y`).
* The family is `Lext : PartId → Finset (Sym2 V)`, read only at light parts.
-/

@[expose] public section

namespace EG.Light

open EG.HB EG.Stage1

variable {V : Type*} [DecidableEq V]

/-- [s5:lemKRED] (preamble) "Put `K_std := ⊔_l ⊔_{Z ∈ Std_l} E_l(Z)`" (a function of the run
alone). -/
noncomputable def Kstd (G : FGraph V) (run : Run V) : Finset (Sym2 V) :=
  (Finset.Icc 1 run.R).biUnion fun l => (run.Std G l).biUnion fun a => run.E G l a

variable {G : FGraph V} {run : Run V}

/-- The JS- and JV-lent edges of `Y` in the outcome `ω`:
"`(⋃_{l,j} LJS_{Y,l,j}) ∪ (⋃_l LJV_{Y,l})`" ([s5:lemKRED]; indices as in [s3:defCOL] (ii)). -/
noncomputable def lentJSJV (ω : Outcome G run) (Y : PartId) : Finset (Sym2 V) :=
  ((lateRounds run Y.1).biUnion fun l =>
      (Finset.range (KJS G run l)).biUnion fun j => (LJS G run Y (ω.colAt Y) l j).edges) ∪
    (lateRounds run Y.1).biUnion fun l => (LJV G run Y (ω.colAt Y) l).edges

/-- [s5:lemKRED] the hypothesis on the family `Lent_ext`: "for every light part `Y`,
`Lent_ext(Y) ⊆ (⋃_{l,j} LJS_{Y,l,j}) ∪ (⋃_l LJV_{Y,l})`, and `Lent_ext(Y) = ∅` if `Y` is
demoted". -/
def LentExtHyp (ω : Outcome G run) (Lext : PartId → Finset (Sym2 V)) : Prop :=
  ∀ Y ∈ run.lightParts G, Lext Y ⊆ lentJSJV ω Y ∧ (demoted ω Y → Lext Y = ∅)

end EG.Light
