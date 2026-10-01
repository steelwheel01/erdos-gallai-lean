module

public import EG.Defs.Gamma.Full
public import EG.Defs.Stage1.Law

/-!
# Statement of Lemma zones (manuscript s5:lemZones)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemZones.

Manuscript v6.1, `s5.tex`, Lemma [s5:lemZones]:
"(i) For every vertex `v`, `∑_Y zp_Y ≤ 1/2`, the sum over all light parts `Y ∋ v`.
(ii) For every light part `Y` of round `r ≤ R−2` and every sublabel `(l,c,σ)` of `Y`, the set
`Zone_{Y,l,c,σ}` is exactly a `ρ_Y`-random subset of `Y` (each vertex of `Y` independently,
product measure), where `ρ_Y := zp_Y/((R−r−1)·4·T^sl_Y) ≥ 1/(12L_Y^5)`.
(iii) All zones `Zone_{Y,l,c,σ}`, over all light parts `Y` and all sublabels `(l,c,σ)` of `Y`,
are pairwise disjoint.
(iv) The family of all zones is independent of the colourings (i)–(iii) and of the JS labels (iv)
of Definition s3:defCOL."

Formal reading (Defs `EG/Defs/Stage1/Zones.lean`, `EG/Defs/Stage1/Law.lean`; TRIAGE §2.7).
* Setting: `EG.RunHyp N0 Dstar G run`. The stage-1 randomness is the joint law
  `EG.Stage1.law G run` (the zone labels are its field `ω.zone`); (ii) and (iv) are stated on the
  joint law, the form in which s5:lemE1 (c) feeds them to s3:lemCOL (c) (TRIAGE §2.7: "s3 lemCOL
  Specs are in the 'any μ with μ.map D = colLaw Y' form (and joint IndepFun for (c))"). On the
  zone marginal `EG.Stage1.zoneLaw` the statement (ii) is the same (the law of `ω.zone` is
  `zoneLaw`).
* The sublabels `(l,c,σ)` of `Y` are the tags `i ∈ I^U(Y)` (`EG.Stage1.IU`; [s5:defZones] "The
  sublabels available to `Y` are exactly the indices of the family `I^U` of `Y`"); the zone of
  `(Y, i)` is `EG.Stage1.Zone G run ω.zone Y i`.
* "exactly a `ρ_Y`-random subset of `Y`": `EG.FinDist.IsRSubset` with `S = V(Y)` and
  `ρ = EG.Stage1.rhoY G run Y` (real `R − r − 1`).
* (iii) holds for every assignment `ζ` of zone labels (one label per vertex); it is stated for
  every `ζ`, over pairs of light parts and sublabels.
* (iv) "the family of all zones": the map `(Y, i) ↦ Zone_{Y,i}` (all `PartId × LentTag`);
  "the colourings and the JS labels": the fields `ω.col`, `ω.js`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1

universe u

open Classical in
/-- [s5:lemZones] Lemma zones, (i)–(iv) (module docstring), in the setting of Section s5
(`RunHyp`), over the stage-1 law `EG.Stage1.law G run`. -/
def LemZonesStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    -- (i)
    (∀ v : V, ∑ Y ∈ (run.lightParts G).filter (fun Y => v ∈ run.ancVerts G Y), zp G run Y ≤ 1 / 2) ∧
    -- (ii)
    (∀ Y ∈ run.lightParts G, Y.1 + 2 ≤ run.R →
      (∀ i ∈ IU G run Y,
        FinDist.IsRSubset (law G run) (fun ω => Zone G run ω.zone Y i) (run.ancVerts G Y)
          (rhoY G run Y)) ∧
      1 / (12 * run.LY G Y ^ 5) ≤ rhoY G run Y) ∧
    -- (iii)
    (∀ ζ : ↥G.verts → Option ZIdx, ∀ Y ∈ run.lightParts G, ∀ Y' ∈ run.lightParts G,
      ∀ i ∈ IU G run Y, ∀ i' ∈ IU G run Y', (Y, i) ≠ (Y', i') →
        Disjoint (Zone G run ζ Y i) (Zone G run ζ Y' i')) ∧
    -- (iv)
    FinDist.IndepFun (law G run) (fun ω => (ω.col, ω.js))
      (fun ω (p : ZIdx) => Zone G run ω.zone p.1 p.2)

end EG.Spec
