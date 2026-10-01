module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma-25 size cap, part (ii) (manuscript s2:lemCap (ii)) — declared input of unit P2J

Statement file (`EG/Spec/**`), unit P2J (probe P-2, part 2). This statement is a DECLARED INPUT
of the probe: the proof of Lemma JS-LC [s6:lemJSLC] (its "two facts": "Every vertex has degree at
most `M_l − 1` in every `E_l(Z)` (Lemma s2:lemCap(ii))", and Steps 2, 3, 8) and of Lemma J⁺
[s6:lemJplus] ((J2): "By Lemma s2:lemCap(ii), every vertex has at most `M_l − 1` edges of `E_l(Z)`
for each `Z`") cite it, and the probe does not prove it; the stub is `EG.capPrePart` in
`EG/Proof/HB/CapPrePart.lean`. Justification: design note `formal/work/p2b/P2J.md`, "Declared
inputs". Part (i) is `EG.Spec.CapStatement` (`EG/Spec/HB/Cap.lean`, proved); the graph-level step
of the proof of (ii) is `EG.Spec.CapGraphStatement`. The full Spec of (ii) (s2 structure unit,
blueprint s2b, STR-II-DUPLICATE) must imply this statement.

Manuscript v6.1, `s2.tex`, Lemma [s2:lemCap] (ii):
"In every round `l ≤ R` of a valid `HB^tp` run, every `s = 0` piece `𝒫` satisfies `|𝒫| ≤ M_l`.
Hence every round-`l` pre-part has `|Z^0| ≤ M_l`; for every round-`l` part `Z` (light or
standalone) every vertex is incident with at most `M_l − 1` edges of `E_l(Z)`; and
`τ_l ≥ 128 s_l log²|𝒫|`, so Lemma s2:lem14tau applies to the `τ`-run of every piece with
`|𝒫| ≥ P_l`."

Formal reading.
* Hypotheses: `run.Valid G Dstar` and `Gamma2a Dstar` (`D_* ≥ 2^{117}`): the proof uses
  "By Γ2(a) (Condition s1:condG2), `d_l ≥ D_* ≥ 2^{117}`" (blueprint s2b CAP-GAMMA-EXPLICIT: the
  manuscript's "valid run" hides this standing assumption). Rounds `l ∈ [1, R]`.
* "every `s = 0` piece `𝒫`": the leaves `q ∈ run.pieceAddrs l` of the `s = 0` recursion, with
  `|𝒫| = (run.piece G l q).card` (number of vertices).
* "every round-`l` pre-part": `a ∈ run.prePartAddrs G l`, `|Z^0| = (run.Z0 G l a).card`.
* "for every round-`l` part `Z` (light or standalone)": the part of the pre-part `a` (its light
  part if light, itself if standalone); `E_l(Z) = run.E G l a`; "incident with at most `M_l − 1`
  edges" is `degE (run.E G l a) v ≤ M_l − 1` for every vertex `v` (`M_l = run.M G l ∈ ℕ`,
  `M_l ≥ 2^{40}`, so the `ℕ`-subtraction is the real one).
* The last clause (`τ_l ≥ 128 s_l log²|𝒫|`) is not used by the probe and is not stated here.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemCap] (ii) "In every round `l ≤ R` of a valid `HB^tp` run, every `s = 0` piece `𝒫`
satisfies `|𝒫| ≤ M_l`. Hence every round-`l` pre-part has `|Z^0| ≤ M_l`; for every round-`l` part
`Z` (light or standalone) every vertex is incident with at most `M_l − 1` edges of `E_l(Z)`"
(under `Γ2(a)`; the clause on `τ_l` is omitted, see the module docstring). -/
def CapPrePartStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    ∀ l ∈ Finset.Icc 1 run.R,
      (∀ q ∈ run.pieceAddrs l, (run.piece G l q).card ≤ run.M G l) ∧
      ∀ a ∈ run.prePartAddrs G l,
        (run.Z0 G l a).card ≤ run.M G l ∧ ∀ v : V, degE (run.E G l a) v ≤ run.M G l - 1

end EG.Spec
