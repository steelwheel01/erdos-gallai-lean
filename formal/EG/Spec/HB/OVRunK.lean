module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Proposition OV on runs, items (K1) and (K3) (manuscript s2:propOV) — declared
input of unit P3B

Statement file (`EG/Spec/**`), unit P3B (probe P-3, part 2). These statements are DECLARED INPUTS
of the probe: Theorems [s6:thmCONC] (iii) and [s6:thmCONCL] (iv) use (K1) and (K3), and
[s2:propOrigin] (c) is (K3); the probe does not prove them. Stubs `EG.ovK1`, `EG.ovK3` in
`EG/Proof/HB/OVRunK.lean`. Justification: design note `formal/work/p2b/P3B.md`, "Declared inputs".
The full Spec of [s2:propOV] (blueprint s2b `OVRunStatement`: leaf masses, (K1)–(K3), (F11)) is not
written yet; its (K1) and (K3) must be these statements (import this file, do not restate them).

Manuscript v6.1, `s2.tex`, Proposition [s2:propOV] (overlap constants on `HB*^{τ+}`):
"Fix a valid `HB*^{τ+}` run and a round `r ≤ R`. … Then … and:
(K1) `Σ|Z^0| ≤ 1.37 n`, the sum over the round-`r` pre-parts; `|Std_r| ≤ 1.37 n/P_r`; the number
of ancestors of round `r` is at most `1.37 n/P_r` (each ancestor corresponds to a distinct pre-part
`Y^0 ⊇ V(Y)`); hence the number `ν_l` of ancestors of rounds at most `l-2` satisfies
`ν_l ≤ 1.37 n Σ_{r ≤ l-2} P_r^{-1}`;
…
(K3) the total size `Σ|Z^0|` of the round-`r` pre-parts failing (L1) is at most
`30.4 ε n / log P_r`, and `Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n / log P_r`, the sum over all round-`r`
pre-parts `Y`."

Formal reading.
* Hypothesis `Gamma2a Dstar` (`D_* ≥ 2^{117}`): implicit in the manuscript; the proof applies
  Lemma 14^τ (b) to every `τ`-run through [s2:lemCap] (ii) (blueprint s2b OV-IMPLICIT-DSTAR). No
  `n ≥ N_0` (TRIAGE §2.6: s2 Specs take only the items they use; propStructure drops `n ≥ N_0`).
* `n = G.card`, `ε = EG.epsC`, `P_r = run.P G r`, `log = Real.logb 2`; pre-parts are addresses
  `a ∈ run.prePartAddrs G r` with `Z^0 = run.Z0 G r a`; "failing (L1)" is `¬ run.isL1 G r a`;
  `Dup*_r = run.DupStar G r`.
* "the number of ancestors of round `r`": `#{Y ∈ run.ancestors G : Y.1 = r}` (ancestors are
  `PartId = (round, pre-part address)`, one per pre-part).
* `ν_l = run.nuAnc G l` for every `l : ℕ`; "`Σ_{r ≤ l-2}`" ranges over the rounds `r ∈ [1,R]` with
  `r + 2 ≤ l` (the ancestors of round `r` exist only for `r ≤ R`; blueprint OV-NU-DEF). The
  `ν_l` clause does not depend on the round `r` fixed in the statement and is stated once.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propOV] (K1) "`Σ|Z^0| ≤ 1.37 n`, the sum over the round-`r` pre-parts;
`|Std_r| ≤ 1.37 n/P_r`; the number of ancestors of round `r` is at most `1.37 n/P_r` …; hence the
number `ν_l` of ancestors of rounds at most `l-2` satisfies `ν_l ≤ 1.37 n Σ_{r ≤ l-2} P_r^{-1}`."
(For every valid run and round `r ≤ R`, with `D_* ≥ 2^{117}`; module docstring.) -/
def OVK1Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    (∀ r ∈ Finset.Icc 1 run.R,
      ((∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a).card : ℕ) : ℝ) ≤ 1.37 * (G.card : ℝ) ∧
      ((run.Std G r).card : ℝ) ≤ 1.37 * (G.card : ℝ) / (run.P G r : ℝ) ∧
      (((run.ancestors G).filter (fun Y => Y.1 = r)).card : ℝ) ≤
        1.37 * (G.card : ℝ) / (run.P G r : ℝ)) ∧
    ∀ l : ℕ, (run.nuAnc G l : ℝ) ≤
      1.37 * (G.card : ℝ) *
        ∑ r ∈ (Finset.Icc 1 run.R).filter (fun r => r + 2 ≤ l), 1 / (run.P G r : ℝ)

open Classical in
/-- [s2:propOV] (K3) "the total size `Σ|Z^0|` of the round-`r` pre-parts failing (L1) is at most
`30.4 ε n / log P_r`, and `Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n / log P_r`, the sum over all round-`r`
pre-parts `Y`." (For every valid run and round `r ≤ R`, with `D_* ≥ 2^{117}`.) -/
def OVK3Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R,
      ((∑ a ∈ (run.prePartAddrs G r).filter (fun a => ¬ run.isL1 G r a),
          (run.Z0 G r a).card : ℕ) : ℝ) ≤
        30.4 * epsC * (G.card : ℝ) / Real.logb 2 (run.P G r : ℝ) ∧
      ((∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a ∩ run.DupStar G r).card : ℕ) : ℝ) ≤
        16 * epsC * (G.card : ℝ) / Real.logb 2 (run.P G r : ℝ)

end EG.Spec
