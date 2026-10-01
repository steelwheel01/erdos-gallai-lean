module

public import EG.Defs.Vortex
public import EG.Defs.Expander
public import EG.Defs.Objects
public import EG.Defs.Fnum

/-!
# Statement of Theorem VX⁺, vortex absorption with arbitrary extra edges, deterministic form
(manuscript s4:thmVXp)

Statement file (`EG/Spec/**`) of the P2 s4 Spec unit (`formal/work/p2s/s4.md`); blueprint s4,
node s4:thmVXp.

Manuscript v6.1, `s4.tex`, Theorem [s4:thmVXp] (Theorem VX⁺ (sharpened vortex absorption with
arbitrary extra edges)):
"Let `Z` be a set of `N ≥ N_0` vertices, `L := log₂N`, and let `O` be a spanning
`(ε_O,s)`-expander on `Z`, where either
`ε_O = 2^{-5}` and `s ≥ 2^{146}L^{38} log₂L`, or `ε_O = 2^{-6}` and `s ≥ 2^{151}L^{38} log₂L`.
Put `J := ⌊log₂(L/6)⌋`, `k := 3J+1`, `m := ⌈L^3⌉`, `b := ⌈2mL^2/ε_O⌉` (that is, `⌈64L^2m⌉`,
resp. `⌈128L^2m⌉`) and `t := 2^8L^5`, resp. `t := 2^9L^5`. The labels of the run are independent:
a uniform colouring of `E(O)` with the `k` colours `R_{j,c}` (`0 ≤ j < J`, `c ∈ [3]`) and `M`; for
every `v ∈ Z` a level `lev(v) ∈ {0,1,…,J}` with `P(lev(v) ≥ j) = 2^{-j}` for `0 ≤ j ≤ J` (…); for
every `v ∈ Z` a label `κ(v) ∈ {0,1,2,3}` with `P(κ(v) = 0) = 1/2` and `P(κ(v) = c) = 1/6`
(`c ∈ [3]`). There is an event `𝒢_VX`, determined by `O` and the labels only, with
(s4:eqVXprob) `P(𝒢_VX) ≥ 1 − η_VX(N) ≥ 1/2`, where
`η_VX(N) := 2LN^{-5} + 2^{95}L^{28}N^{-3} + NL e^{-3L^2/(32 log₂L)} + L e^{-N/(5000L)}`,
such that on `𝒢_VX` the following holds simultaneously for *every* graph `G` with `V(G) = Z` and
`E(O) ⊆ E(G)` (the edges of `E(G) \ E(O)` are arbitrary): `E(G)` decomposes into at most
`38.4N + 13N ≤ 52N ≤ 80N` objects, all of which are cycles except at most `N + 13N/L = N + o(N)`
single edges. In particular `f(G) ≤ 80N`."

Formal reading (TRIAGE §2.8 and §2.12, decision VX-DET-SPEC "TPV, PV and VX⁺ are deterministic";
blueprint s4 thmVXp).
* **Deterministic form.** The conclusion does not mention the labels, and
  `P(𝒢_VX) ≥ 1/2 > 0` forces `𝒢_VX ≠ ∅`; so the theorem implies "for every such `G` there is a
  decomposition with the stated counts". Conversely that statement gives the theorem with
  `𝒢_VX` := the whole label space (probability `1 ≥ 1 − η_VX(N)`; `η_VX(N) ≥ 0` since `L ≥ 0`, and
  `η_VX(N) ≤ 1/100 ≤ 1/2` is size condition (iv), part of `VXSize`). The only consumer
  (s5:lemDemoted, `EG.Spec.LemDemotedStatement`, which is itself stated deterministically) uses
  only non-emptiness. Parameters, labels, `𝒢_VX` and its probability are proof internals (Lib);
  the meta-claim "determined by `O` and the labels only" is not stated.
* "`N ≥ N_0`": `EG.Vortex.VXSize Z.card` (the size conditions (i), (ii), (iv) of the proof;
  TRIAGE §2.4, as for Lemmas TPV and PV). `L = EG.Vortex.L Z.card`, `log₂L = logb 2 L`.
* "spanning `(ε_O,s)`-expander on `Z`": `O.verts = Z ∧ O.IsExpander εO s`; the two admissible
  parameter pairs are a disjunction.
* "every graph `G` with `V(G) = Z` and `E(O) ⊆ E(G)`": `G : FGraph V` (simple: loopless, edges
  inside `G.verts`), `G.verts = Z`, `O.edges ⊆ G.edges`.
* "decomposes into at most `38.4N + 13N` objects": the strongest bound in the displayed chain
  (the TeX writes `38.4N + 13N ≤ 52N ≤ 80N`; the Spec keeps `38.4N + 13N`, a real inequality),
  "all of which are cycles except at most `N + 13N/L` single edges": the number of single-edge
  objects `D.countP Obj.isEdge` is at most `N + 13N/L` (real); both for the same decomposition `D`.
* "In particular `f(G) ≤ 80N`": `fnum G.edges ≤ 80 * N` (implied by the first two conjuncts; kept
  because the TeX states it).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s4:thmVXp] Theorem VX⁺ (sharpened vortex absorption with arbitrary extra edges),
deterministic form: if `Z` has `N ≥ N_0` vertices (`VXSize`) and `O` is a spanning
`(ε_O,s)`-expander on `Z` with `ε_O = 2^{-5}`, `s ≥ 2^{146}L^{38}log₂L` or `ε_O = 2^{-6}`,
`s ≥ 2^{151}L^{38}log₂L`, then every graph `G` with `V(G) = Z` and `E(O) ⊆ E(G)` has a
decomposition of `E(G)` into at most `38.4N + 13N` objects, at most `N + 13N/L` of which are single
edges; in particular `f(G) ≤ 80N`. -/
def VXStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (Z : Finset V) (O : FGraph V) (εO s : ℝ),
    Vortex.VXSize Z.card →
    O.verts = Z → O.IsExpander εO s →
    ((εO = (2 : ℝ) ^ (-5 : ℤ) ∧
        (2 : ℝ) ^ 146 * Vortex.L Z.card ^ 38 * Real.logb 2 (Vortex.L Z.card) ≤ s) ∨
     (εO = (2 : ℝ) ^ (-6 : ℤ) ∧
        (2 : ℝ) ^ 151 * Vortex.L Z.card ^ 38 * Real.logb 2 (Vortex.L Z.card) ≤ s)) →
    ∀ G : FGraph V, G.verts = Z → O.edges ⊆ G.edges →
      (∃ D : List (Obj V), IsDecomp (G.edges : Set (Sym2 V)) D ∧
        (D.length : ℝ) ≤ 38.4 * (Z.card : ℝ) + 13 * (Z.card : ℝ) ∧
        (D.countP Obj.isEdge : ℝ) ≤ (Z.card : ℝ) + 13 * (Z.card : ℝ) / Vortex.L Z.card) ∧
      fnum G.edges ≤ 80 * Z.card

end EG.Spec
