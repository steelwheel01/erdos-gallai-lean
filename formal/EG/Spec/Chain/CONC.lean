module

public import EG.Defs.Chain.Design
public import EG.Defs.Gamma.Core
public import EG.Defs.Log

/-!
# Statement of Theorem CONC (manuscript s6:thmCONC) and of the two shared sums of its proof

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). Design note
`formal/work/p2b/P3B.md`. Definitions: `EG/Defs/HB/Run.lean`, `EG/Defs/Chain/Design.lean`,
`EG/Defs/Constants.lean`, `EG/Defs/Log.lean`, `EG/Defs/Gamma/Core.lean` (all locked).

Manuscript v6.1, `s6.tex`, Theorem [s6:thmCONC] (Theorem CONC, standalone ancestors):
"For every valid `HB*^{τ+}` run and every designation `δ`:
(i) for every `Y ∈ Std_r`, every `l ≥ r+1` and every vertex `h`:
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r - 1`;
(ii) `m_{Y,l} ≤ τ_r - 1 + d^*_{Y,l}` for every `Y ∈ Std_r` and every `l`;
(iii) `Σ_{(Y,l): Y standalone} m_{Y,l} ≤ 2^{σ+14} n log* D_*/log D_*
+ 100 ε n log* D_*/(C' log log D_*)`;
(iv) (i)–(iii) hold for every designation, including designations that mix light and standalone
classes: (i) bounds, for every vertex `h`, the number of `G_l`-edges from `h` into `Y^0 \ Dup*_r`,
whatever the classes of the ports involved."
From the proof of (iii) (the two sums; the proof of [s6:thmCONCL] (iv) reuses them "verbatim" for
all ancestors):
"*The `τ`-term.* … `Σ_{(Y,l), Y ∈ Std} (τ_r - 1) ≤ … ≤ 2^{σ+14} n log* D_*/log D_*`."
"*The `d^*`-term.* … `Σ_{(Y,l)} d^*_{Y,l} ≤ … ≤ 80 ε n log* D_*/(C' log log D_*)`." and
([s6:thmCONCL] (iv)) "*`τ`-terms.* The number of ancestors of round `r` (light and standalone) is
at most `1.37 n/P_r` ([s2:propOV](K1)). The computation in the proof of Theorem [s6:thmCONC](iii)
applies verbatim and gives at most `2^{σ+14} n log* D_*/log D_*`. *`d^*`-terms.* … it applies to
all ancestors together and gives at most `80 ε n log* D_*/(C' log log D_*)`."

Formal reading.
* "valid run": `run.Valid G Dstar`. (i), (ii) need no hypothesis on `D_*` (their proof is
  [s2:propOrigin] (a), (b) and the definitions). (iii) and the two sums use the standing
  assumption through [s2:lemTower] (a), (c), [s2:propOV] (K1), (K3) and the tower facts; they carry
  `Gamma1core Dstar` (blueprint s6a CONC-IMPLICIT-HYPS; TRIAGE §2.6: s6a CONC takes only the items
  it uses). `d_1 ≥ D_*` is not a hypothesis: if `R ≥ 1` it follows from `Valid`, and if `R = 0`
  the sums are empty. No `n ≥ N_0` (TRIAGE §2.6).
* "designation": `δ : EG.Chain.Designation V` with `EG.Chain.IsDesignation run G δ`; (iv) is a
  meta-statement and is automatic, since (ii), (iii) quantify over every designation (blueprint
  CONC-IV-META); (i) does not mention `δ` and is stated without it.
* `Y ∈ Std_r` is an address `a ∈ run.Std G r` (the round `r` is any natural number: `Std_r = ∅`
  outside `[1,R]`); as an ancestor it is `(r, a) : PartId`. `Y^0 = run.Z0 G r a`,
  `Dup*_r = run.DupStar G r`, `G_l = run.graph G l`, `τ_r = run.tau G r`,
  `m_{Y,l} = EG.Chain.mY`, `d^*_{Y,l} = EG.Chain.dStar`. `τ_r - 1` is `ℕ`-subtraction (`τ_r ≥ 1`
  for every `d`, so exact; blueprint CONC-NAT-SUB).
* (i): "every `l ≥ r+1`" is every natural number `l ≥ r + 1` (`G_l` is stationary for
  `l ≥ R + 1`; blueprint CONC-ROUND-RANGE). (ii): "every `l`" is every natural number `l`.
* (iii): the sum over the pairs `(Y,l)` with `Y` standalone is
  `Σ_{l ∈ [1,R]} Σ_{Y ∈ run.stdParts G}` (TRIAGE / design note: "Sums over `(Y,l)` …
  `Σ_{l∈[1,R]} Σ_{Y ∈ ancestors}`"; `m_{Y,l} = 0` for `l ∉ [1,R]`, since `Std_l = ∅` there, so no
  pair with `m_{Y,l} ≠ 0` is lost). `n = G.card`, `σ = EG.sigmaC`, `ε = EG.epsC`, `C' = EG.Cp`,
  `log = Real.logb 2`, `log* = EG.logStar`.
* The two shared sums are stated over **all** ancestors, the form in which [s6:thmCONCL] (iv)
  uses them; the standalone sums of the proof of (iii) are sub-sums (all terms are `≥ 0`):
  - `ConcTauSumStatement`: `Σ_{(Y,l)} (τ_{r(Y)} - 1)` over the ancestors `Y` and the rounds `l`
    with `r(Y) + 2 ≤ l ≤ R` (exactly the pairs with possibly `m_{Y,l} ≠ 0`: `m_{Y,l} = 0` unless
    `r(Y) + 2 ≤ l ≤ R`, [s6:thmCONC] (iii) proof "`m_{Y,l} = 0` unless `3 ≤ l` and
    `r+2 ≤ l ≤ R`");
  - `ConcDStarSumStatement`: `Σ_{l ∈ [1,R]} Σ_{Y ancestor} d^*_{Y,l}` for every designation.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

/-- [s6:thmCONC] (i) "for every `Y ∈ Std_r`, every `l ≥ r+1` and every vertex `h`:
`#{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r - 1`." (For every valid run.) -/
def ConcIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r : ℕ, ∀ a ∈ run.Std G r, ∀ l : ℕ, r + 1 ≤ l → ∀ h : V,
      ((run.Z0 G r a \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges)).card ≤ run.tau G r - 1

/-- [s6:thmCONC] (ii) "`m_{Y,l} ≤ τ_r - 1 + d^*_{Y,l}` for every `Y ∈ Std_r` and every `l`." (For
every valid run and every designation.) -/
def ConcIIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
    ∀ r : ℕ, ∀ a ∈ run.Std G r, ∀ l : ℕ,
      mY run G δ (r, a) l ≤ run.tau G r - 1 + dStar run G δ (r, a) l

/-- [s6:thmCONC] (iii) "`Σ_{(Y,l): Y standalone} m_{Y,l} ≤ 2^{σ+14} n log* D_*/log D_*
+ 100 ε n log* D_*/(C' log log D_*)`." (For every valid run and every designation, under the
standing assumption Γ1 on `D_*`.) -/
def ConcIIIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
      (∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.stdParts G, (mY run G δ Y l : ℝ)) ≤
        (2 : ℝ) ^ (sigmaC + 14) * (G.card : ℝ) * (logStar Dstar : ℝ) / Real.logb 2 Dstar +
          100 * epsC * (G.card : ℝ) * (logStar Dstar : ℝ) /
            ((Cp : ℝ) * Real.logb 2 (Real.logb 2 Dstar))

/-- [s6:thmCONC] (proof of (iii), "*The `τ`-term.*") and [s6:thmCONCL] (proof of (iv),
"*`τ`-terms.* … The computation in the proof of Theorem [s6:thmCONC](iii) applies verbatim and
gives at most `2^{σ+14} n log* D_*/log D_*`"): the sum of `τ_{r(Y)} - 1` over all ancestors `Y`
(light and standalone) and all rounds `l` with `r(Y) + 2 ≤ l ≤ R` is at most
`2^{σ+14} n log* D_*/log D_*`. (For every valid run, under Γ1.) -/
def ConcTauSumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
      (∑ Y ∈ run.ancestors G, ∑ _l ∈ Finset.Icc (Y.1 + 2) run.R,
          ((run.tau G Y.1 - 1 : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (sigmaC + 14) * (G.card : ℝ) * (logStar Dstar : ℝ) / Real.logb 2 Dstar

/-- [s6:thmCONC] (proof of (iii), "*The `d^*`-term.*" "`Σ_{(Y,l)} d^*_{Y,l} ≤ … ≤
80 ε n log* D_*/(C' log log D_*)`") and [s6:thmCONCL] (proof of (iv), "*`d^*`-terms.* … it
applies to all ancestors together and gives at most `80 ε n log* D_*/(C' log log D_*)`"). (For
every valid run and every designation, under Γ1.) -/
def ConcDStarSumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ δ : Designation V, IsDesignation run G δ →
      (∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (dStar run G δ Y l : ℝ)) ≤
        80 * epsC * (G.card : ℝ) * (logStar Dstar : ℝ) /
          ((Cp : ℝ) * Real.logb 2 (Real.logb 2 Dstar))

end EG.Spec
