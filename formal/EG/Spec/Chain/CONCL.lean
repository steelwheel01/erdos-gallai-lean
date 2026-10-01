module

public import EG.Defs.Chain.Design
public import EG.Defs.Chain.Constants
public import EG.Defs.Gamma.Core
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Statement of Theorem CONC-L (manuscript s6:thmCONCL), including the per-ancestor bound and the
`θ^GC`-sum of the proof of (iv)

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). Design note
`formal/work/p2b/P3B.md`. Definitions: `EG/Defs/HB/Run.lean`, `EG/Defs/Chain/Design.lean`,
`EG/Defs/Chain/Constants.lean` (`epsCONC`), `EG/Defs/Gamma/Core.lean` (all locked).

Manuscript v6.1, `s6.tex`, Theorem [s6:thmCONCL] (Theorem CONC-L):
"Let `Y` be a light part of round `r` of a valid `HB*^{τ+}` run, let `l ≥ r+1`, and let `h` be a
vertex.
(i) If `h ∉ S_Y`: `#{u ∈ Y \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r - 1`, and there are no such `u` if
`h ∈ Y`.
(ii) If `h ∈ S_Y`: every such `hu` is an edge of `X^0_Y`, and their number is at most
`e_{X^0_Y}(h, Y)`.
(iii) For every designation, `m_{Y,l} ≤ max(τ_r - 1, α_{Y,l}) + d^*_{Y,l}`.
(iv) `α_{Y,l} < θ^GC_r(Y^0)`. For every valid run and every designation, summing over *all*
ancestors (light and standalone, GC-parts included),
`Σ_{(Y,l)} m_{Y,l} ≤ ε_CONC(D_*) n`, where
`ε_CONC(D_*) := 2^{σ+15} log* D_*/log D_* + 200 ε log* D_*/(C' log log D_*)
+ 4(2 log* D_* + 2)/(log D_*)^{1/2}`.
`ε_CONC` depends only on `D_*` (and on `σ, C', ε`), and `ε_CONC(D_*) → 0` as `D_* → ∞`."
From the proof of (iv):
"Hence `α_{Y,l} < θ^GC_r(Y^0)`, and by (iii),
`m_{Y,l} ≤ (τ_r - 1) + (θ^GC_r(Y^0) - 1) + d^*_{Y,l}` (`Y` light),
`m_{Y,l} ≤ τ_r - 1 + d^*_{Y,l}` (`Y` standalone), the latter by Theorem [s6:thmCONC](ii); GC-parts
are standalone (Lemma [s2:lemGC](iii))." (the per-ancestor bound: the named refutation target of
probe P-3, TRIAGE §4) and
"*`θ^GC`-terms.* … `Σ_{(Y,l), Y light} θ^GC_r(Y^0) ≤ 1.38 n Σ_{r ≤ R} 𝖼(d_r) ≤ 2.76 n 𝖼(d_R)
≤ 2.76 n (2k_*+3)/(log D_*)^{1/2} ≤ 4n(2 log* D_* + 2)/(log D_*)^{1/2}`."

Formal reading.
* "a light part of round `r`": an address `a ∈ run.prePartAddrs G r` with `run.isLight G r a`
  (the part `Y = (r, a) : PartId`). "Recall `Y^0 = Y ⊔ S_Y` and `V(Y) = Y`": the vertex set `Y` of
  the light part is written `run.Z0 G r a \ run.guests G r a` (it is `run.ancVerts G (r, a)` for a
  light pre-part). `S_Y = run.guests G r a`, `X^0_Y = run.X0 G r a`,
  `e_{X^0_Y}(h, Y) = (run.X0 G r a).eBetween {h} Y` (disjoint sets, as `h ∈ S_Y`),
  `θ^GC_r(Y^0) = run.thetaGC G r a`, `α_{Y,l} = EG.Chain.alphaY`, `m`, `d^*` as in CONC.
* "`l ≥ r+1`": every natural number `l ≥ r + 1`. (i)–(iii) need no hypothesis on `D_*`.
  (iii) and (iv) read the designation: `∀ δ, IsDesignation run G δ → …`.
* (iv), first sentence, `α_{Y,l} < θ^GC_r(Y^0)`: carries `Gamma1core Dstar` (the standing
  assumption). Without it the claim can fail: when `S_Y = ∅` the claim is `0 < θ^GC_r(Y^0)`, and
  `θ^GC = 0` when `λ_r = 0` (e.g. `d_r = 1`, since Lean's `0^{-1/2} = 0`; no valid run with
  `d_r = 1` and a light part with `S_Y = ∅` is exhibited); under Γ1, `λ_r > 0` and `θ^GC ≥ 1`
  (T0; design note).
* The per-ancestor bound (`ConcLPerAncestorStatement`) is stated for every ancestor
  `Y ∈ run.ancestors G` and every natural number `l`, with no hypothesis on `D_*`: its light case
  follows from (iii) and `α ≤ θ^GC - 1`, which holds for every valid run (each guest has fewer than
  `θ^GC` core edges by [s2:lemGC](ii), and `α = 0` if `S_Y = ∅`). `θ^GC - 1`, `τ - 1` are
  `ℕ`-subtractions.
* The sum `Σ_{(Y,l)}` over all ancestors is `Σ_{l ∈ [1,R]} Σ_{Y ∈ run.ancestors G}` (design note
  `work/p2d/design.md`, "Notes for Spec authors"; `m_{Y,l} = 0` for `l ∉ [1,R]`); `n = G.card`;
  `ε_CONC = EG.Chain.epsCONC` (locked Def, the displayed formula). It carries `Gamma1core Dstar`
  (blueprint CONCL-HYPS; `d_1 ≥ D_*` follows from `Valid` when `R ≥ 1`, and the sum is empty when
  `R = 0`; no `n ≥ N_0`).
* The `θ^GC`-sum (`ConcLGCSumStatement`) ranges over the light parts `Y ∈ run.lightParts G` and
  the rounds `l` with `r(Y) + 2 ≤ l ≤ R` (the pairs with possibly `m_{Y,l} ≠ 0`; "Each `Y` occurs
  for at most `R-r-1` values of `l`"). Only its final bound is stated.
* "`ε_CONC` depends only on `D_*`" is definitional (`epsCONC : ℝ → ℝ`); "`ε_CONC(D_*) → 0` as
  `D_* → ∞`" is `EpsCONCTendstoStatement` (`Filter.Tendsto epsCONC atTop (nhds 0)`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

/-- [s6:thmCONCL] (i) "If `h ∉ S_Y`: `#{u ∈ Y \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r - 1`, and there are
no such `u` if `h ∈ Y`." (`Y` a light part of round `r` of a valid run, `l ≥ r+1`, `h` a
vertex.) -/
def ConcLIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r : ℕ, ∀ a ∈ run.prePartAddrs G r, run.isLight G r a →
    ∀ l : ℕ, r + 1 ≤ l → ∀ h : V, h ∉ run.guests G r a →
      (((run.Z0 G r a \ run.guests G r a) \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges)).card ≤ run.tau G r - 1 ∧
      (h ∈ run.Z0 G r a \ run.guests G r a →
        ((run.Z0 G r a \ run.guests G r a) \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges) = ∅)

/-- [s6:thmCONCL] (ii) "If `h ∈ S_Y`: every such `hu` is an edge of `X^0_Y`, and their number is
at most `e_{X^0_Y}(h, Y)`." ("such": `u ∈ Y \ Dup*_r` with `hu ∈ E(G_l)`; `Y` a light part of
round `r` of a valid run, `l ≥ r+1`.) -/
def ConcLIIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r : ℕ, ∀ a ∈ run.prePartAddrs G r, run.isLight G r a →
    ∀ l : ℕ, r + 1 ≤ l → ∀ h ∈ run.guests G r a,
      (∀ u ∈ (run.Z0 G r a \ run.guests G r a) \ run.DupStar G r,
        s(h, u) ∈ (run.graph G l).edges → s(h, u) ∈ (run.X0 G r a).edges) ∧
      (((run.Z0 G r a \ run.guests G r a) \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges)).card ≤
        (run.X0 G r a).eBetween {h} (run.Z0 G r a \ run.guests G r a)

/-- [s6:thmCONCL] (iii) "For every designation, `m_{Y,l} ≤ max(τ_r - 1, α_{Y,l}) + d^*_{Y,l}`."
(`Y` a light part of round `r` of a valid run, `l ≥ r+1`.) -/
def ConcLIIIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
    ∀ r : ℕ, ∀ a ∈ run.prePartAddrs G r, run.isLight G r a → ∀ l : ℕ, r + 1 ≤ l →
      mY run G δ (r, a) l ≤ max (run.tau G r - 1) (alphaY run G δ (r, a) l) + dStar run G δ (r, a) l

/-- [s6:thmCONCL] (iv), first sentence, "`α_{Y,l} < θ^GC_r(Y^0)`." (`Y` a light part of round `r`
of a valid run, `l ≥ r+1`, every designation; under the standing assumption Γ1 on `D_*`, see
the module docstring.) -/
def ConcLAlphaStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
    ∀ r : ℕ, ∀ a ∈ run.prePartAddrs G r, run.isLight G r a → ∀ l : ℕ, r + 1 ≤ l →
      alphaY run G δ (r, a) l < run.thetaGC G r a

/-- [s6:thmCONCL] (proof of (iv)) "`m_{Y,l} ≤ (τ_r - 1) + (θ^GC_r(Y^0) - 1) + d^*_{Y,l}` (`Y`
light), `m_{Y,l} ≤ τ_r - 1 + d^*_{Y,l}` (`Y` standalone) … GC-parts are standalone": the
per-ancestor bound, for every ancestor `Y = (r, a)` of a valid run, every round `l` and every
designation. (The named refutation target of probe P-3, TRIAGE §4.) -/
def ConcLPerAncestorStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
    ∀ Y ∈ run.ancestors G, ∀ l : ℕ,
      (run.isLight G Y.1 Y.2 →
        mY run G δ Y l ≤ (run.tau G Y.1 - 1) + (run.thetaGC G Y.1 Y.2 - 1) + dStar run G δ Y l) ∧
      (¬ run.isLight G Y.1 Y.2 → mY run G δ Y l ≤ run.tau G Y.1 - 1 + dStar run G δ Y l)

/-- [s6:thmCONCL] (proof of (iv), "*`θ^GC`-terms.*") "`Σ_{(Y,l), Y light} θ^GC_r(Y^0) ≤ … ≤
4n(2 log* D_* + 2)/(log D_*)^{1/2}`": the sum of `θ^GC_{r(Y)}(Y^0)` over the light parts `Y` and
the rounds `l` with `r(Y) + 2 ≤ l ≤ R`. (For every valid run, under Γ1.) -/
def ConcLGCSumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
      (∑ Y ∈ run.lightParts G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R,
          (run.thetaGC G Y.1 Y.2 : ℝ)) ≤
        4 * (G.card : ℝ) * (2 * (logStar Dstar : ℝ) + 2) / Real.logb 2 Dstar ^ ((1 : ℝ) / 2)

/-- [s6:thmCONCL] (iv) "For every valid run and every designation, summing over *all* ancestors
(light and standalone, GC-parts included), `Σ_{(Y,l)} m_{Y,l} ≤ ε_CONC(D_*) n`." (Under the
standing assumption Γ1 on `D_*`.) -/
def ConcLSumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
      (∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ)) ≤
        epsCONC Dstar * (G.card : ℝ)

/-- [s6:thmCONCL] (iv) "`ε_CONC(D_*) → 0` as `D_* → ∞`." -/
def EpsCONCTendstoStatement : Prop :=
  Filter.Tendsto epsCONC Filter.atTop (nhds 0)

end EG.Spec
