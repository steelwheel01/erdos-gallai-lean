module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Probe.S4.TPV
public import EG.Defs.Chain.JConsumer
public import EG.Defs.Chain.Constants
public import EG.Defs.Gamma.Full

/-!
# Statement of Theorem MIX-C, the assembly with `𝒱 = ∅`, deterministic form (manuscript s6:thmMIXC)

Statement file (`EG/Spec/**`) of the P2 Spec unit s6b (`formal/work/p2s/s6b.md`); blueprint s6b,
node `s6:thmMIXC`.

Manuscript v6.1, `s6.tex`, Theorem [s6:thmMIXC] (Theorem MIX-C: the assembly with `𝒱 = ∅`,
deterministic form):
"Fix the following data:
* a valid `HB*^{τ+}` run on `G` with `n ≥ N_0` and `d_1 ≥ D_*`, and a designation `δ`;
* *any* stage-1 outcome;
* stage-3 outcomes in the good events of Lemma s4:lemTPV (every `Z ∈ Std`), of Lemma s4:lemPV
  through Lemma s5:lemChild (every non-demoted light part), and of Theorem s4:thmVXp through Lemma
  s5:lemDemoted (every demoted light part);
* *any* J-consumer.
Run Construction s6:consOrder. Then:
(a) (Order.) At step (1) of round `l`, `Lent(Z)` is final for every `Z ∈ Std_l`. JS-LC at round `l`
uses only classes `LJS_{Y,l,·}`, and the J-consumer only classes `LJV_{Y,l}`, of ancestors `Y` of
rounds `≤ l − 2`, which are processed later. The hypotheses of Lemma s6:lemJSLC hold at every round
`l ≥ 3`, and every device is applied within its hypotheses.
(b) (Coverage.) The output is a decomposition of `E(G)`: every edge of `G` lies in exactly one
output object. In detail: [five items about `LentU`, `LentJS`, `LentJV`, `H_0`, `Lent(Z)`, `E^V(Z)`,
`E^Q(Z)`, `J_l`, returned lent edges and (s6:eqJbound)].
(c) (Cost.) The number of output objects is at most
`(D_*/2 + c_KRED + c_Fresh) n + ε_M(D_*) n + [80 dem + 369 lp + 169 Σ_l |Lost_l|]
+ 1.5 Σ_{(Y,l)} m_{Y,l} + Σ_l |Obj_l|`,
where `ε_M(D_*) := ε_K(D_*) + 169 ε_A + 252/D_*`, with `ε_A = 31ε/(C' log log D_*)` as defined in
Lemma s2:lemTower(e). Thus `ε_M` is a function of `D_*` alone; it depends neither on the run nor on
`n`. Moreover `1.5 Σ_{(Y,l)} m_{Y,l} ≤ 1.5 ε_CONC(D_*) n` by Theorem s6:thmCONCL(iv)."
(followed by the itemization of (c), whose TPV bullet names `c_Fresh = 169 · 2`, and, in the proof
of (a), the bullet "Lemma TPV at step (1)": "`|Z^0| ≥ P_l ≥ N_0` by (s1:condG3). If `Z` is
lend-good, then `O_Z = Own_Z`. By Lemma s3:lemCOL(a) it is a spanning `(2^{-5}, s_l/4)`-expander
on `Z^0`, and by Lemma s3:lemCOL(e) we have `s_l/4 ≥ 2^{150} L_Z^{42}`. If `Z` is lend-bad,
`O_Z = X^0_Z` is a spanning `(2^{-5}, s_l)`-expander on `Z^0` (Proposition s2:propStructure(i)), and
`s_l ≥ s_l/4 ≥ 2^{150} L_Z^{42}` … `E = Erem(Z) ⊇ E(O_Z)` …, and all its edges lie inside `Z^0`.")

Formal reading (TRIAGE §2.8, §2.9 "MIX-C = Option B′", §2.12; blueprint s6b MIXC-*).
* **Setting.** `EG.RunHyp N0 Dstar G run` (TRIAGE §2.6; it contains Γ1, Γ3, `N0Cond`, `n ≥ N_0`,
  `d_1 ≥ D_*` and the valid run; Γ4 is not needed, blueprint MIXC-HYPS), a designation `δ` with
  `IsDesignation run G δ`.
* **"*any* stage-1 outcome"**: every `ω ∈ (Stage1.law G run).supp` (T0, TRIAGE §2.7 OO-SUPP:
  statements about a fixed stage-1 outcome quantify the outcomes of positive weight), with its
  stage-2 data `S := EG.Quot.stageOf ω` (the instantiation D-DES-1 / TRIAGE §3 item 20; the
  record read by s7:propCost). `dem = Light.dem ω`, `lp = Light.lp ω` (the fields of `stageOf ω`;
  the form of the K-RED Spec), `|Lost_l| = (lostRound run G δ S l).card`.
* **Stage-3 outcomes** are not data: TPV, PV (through lemChild) and VX⁺ (through lemDemoted) are
  deterministic Specs (TRIAGE §2.8, TPV-DET-SPEC; "K-RED is pure existence for any admissible
  family"). "In the good events" is discharged inside the proof by those Specs; the hypotheses of
  Lemma TPV at `(Z^0, O_Z, Ret_Z)` are the separate statement `MixCTPVApplicableStatement` (TRIAGE
  §2.8: "MIX-C applies the deterministic TPV Spec, plus `MixCTPVApplicable` for its hypotheses").
* **"*any* J-consumer"**: every `C : EG.Chain.JConsumer run G δ S` (obligations (JC1), (JC2)
  required on sets with `JPlusProps` at rounds `3 ≤ l ≤ R`, s6:defJconsumer). T0: this is a
  subclass of the TeX's rules. The locked Def makes a consumer a function of `(l, J_l)` in the fixed
  context `(run, δ, stageOf ω)`, while the TeX rule may also depend on everything constructed at
  rounds `> l` and on fresh randomness. So the Spec, universally quantified over consumers, is
  weaker than the TeX. It covers the only consumer used, s7's `EG.Quot.roundOut` (through
  `EG.Quot.pastOf`, a function of `(ω, l, J)`).
* **Option B′ (TRIAGE §2.9, binding).** Construction s6:consOrder and the Lent sets are
  proof-internal, so `Σ_l |Obj_l|` (the consumer's outputs on the chain's sets `J_l`) cannot be
  named in the Spec. It is stated through an arbitrary per-round bound
  `b : ℕ → Finset (Sym2 V) → ℝ` on the consumer, `|(C.out l J).1| ≤ b l J` for every `3 ≤ l ≤ R`
  and every `J` with `JPlusProps`, and the conclusion exposes the chain's sets:
  `∃ Js, (∀ l ∈ [3, R], JPlusProps … l (Js l)) ∧ ∃ D, IsDecomp E(G) D ∧ |D| ≤ … + Σ_{l=3}^{R} b l (Js l)`.
  The TeX statement implies this form: take the chain's `J_l` (the consumer acts at rounds
  `3 ≤ l ≤ R` only, and `|Obj_l| ≤ b l J_l` there). The converse fails. The `Js` are existential
  and constrained only by `JPlusProps` (`∅` qualifies), so they need not be the chain's sets, and a
  prover may pick them to make `Σ b l (Js l)` large. So the Lean form is strictly weaker than the
  TeX, even with `b l J := |(C.out l J).1|`. Design obligation: every downstream bound on
  `Σ_l b(l, J_l)` (or on quantities read at the returned `Js`) must hold uniformly over all sets
  with `JPlusProps`, not only at the chain's sets. s7:propCost (`EG/Spec/Quot/Cost.lean`) has the
  same existential shape (it reads the `Js` for its quotients), so the chain of Specs stays
  consistent.
* **(b)** "The output is a decomposition of `E(G)`": `IsDecomp (G.edges : Set (Sym2 V)) D`
  (objects well formed, edge lists pairwise disjoint, union exactly `E(G)`). The itemized details
  of (b) and all of (a) except the TPV bullet are statements about objects internal to the
  construction (`Lent`, `Erem`, `H_0`, `E^V`, `E^Q`, `J_l`); they are proof obligations, not Spec
  conjuncts (T0, blueprint MIXC-DETAILS-INTERNAL; no consumer reads them).
* **(c)** `c_KRED = 745`, `c_Fresh = 169 · 2 = 338` (numerals), `ε_M = EG.Chain.epsM` (locked
  formula; "`ε_M` is a function of `D_*` alone" is definitional), `n = G.card`. `Σ_l |Lost_l|` over
  `l ∈ [1, R]` (`Lost_l = ∅` for `l ≤ 2`); `Σ_{(Y,l)} m_{Y,l}` over `l ∈ [1, R]` and all ancestors
  `Y ∈ run.ancestors G` (the index convention of `EG.Spec.ConcLSumStatement`, blueprint
  CONCL-SUM-RANGE; `m_{Y,l} = 0` off the pairs with `r(Y) + 2 ≤ l`). The last sentence of (c)
  ("Moreover `1.5 Σ m ≤ 1.5 ε_CONC(D_*) n`") is `MixCConcStatement`.
* **TPV bullet of (a)** (`MixCTPVApplicableStatement`): for every `Z ∈ Std_l` (address `a`),
  `EG.Vortex.TPVHyp (Z^0) (O_Z) (Ret_Z) εO s` with `εO = 2^{-5}` and `s = s_l/4` if `Z` is lend-good,
  `s = s_l` if `Z` is lend-bad (as displayed). `TPVHyp` contains `TPVSize |Z^0|`, the consumer form
  of `|Z^0| ≥ N_0` read by `TPVStatement`. T0: `N0Cond N0 → N0 ≤ N → TPVSize N`, so the TeX's
  `|Z^0| ≥ P_l ≥ N_0` implies it, but the literal `N_0 ≤ |Z^0|` cannot be recovered from it; no
  consumer needs the literal inequality. `TPVHyp` also contains "spanning … on `Z^0`"
  (`O.verts = Z^0`), the bounds on `εO`, `2^{150}L^{42} ≤ s`
  with `L = log₂|Z^0|`, and `Ret_Z ⊆ Z^0` (the partition `Z^0 = Ret_Z ⊔ Q*_Z` of s6:defLending, with
  `P = Ret_Z`, `Q = Q*_Z = Z^0 \ Ret_Z`). The clause "`E = Erem(Z) ⊇ E(O_Z)`, all its edges inside
  `Z^0`" concerns the internal set `Erem(Z)` and is a proof obligation (s6:lemLent (iii)).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s6:thmMIXC] (b), (c), Option B′: for every stage-1 outcome (of positive weight), every
J-consumer `C` and every per-round bound `b` on `C` over the sets with `JPlusProps`, there are
sets `J_l` (`3 ≤ l ≤ R`) with the properties of Lemma J⁺ and a decomposition `D` of `E(G)` with
"`|D| ≤ (D_*/2 + c_KRED + c_Fresh) n + ε_M(D_*) n + [80 dem + 369 lp + 169 Σ_l |Lost_l|]
+ 1.5 Σ_{(Y,l)} m_{Y,l} + Σ_l |Obj_l|`" (`c_KRED = 745`, `c_Fresh = 338`, `|Obj_l| ≤ b l J_l`).
(Setting `RunHyp`; module docstring.) -/
def MixCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp,
    ∀ (C : JConsumer run G δ (stageOf ω)) (b : ℕ → Finset (Sym2 V) → ℝ),
    (∀ l J, 3 ≤ l → l ≤ run.R → JPlusProps run G δ (stageOf ω) l J →
      ((C.out l J).1.length : ℝ) ≤ b l J) →
    ∃ Js : ℕ → Finset (Sym2 V),
      (∀ l ∈ Finset.Icc 3 run.R, JPlusProps run G δ (stageOf ω) l (Js l)) ∧
      ∃ D : List (Obj V), IsDecomp (G.edges : Set (Sym2 V)) D ∧
        (D.length : ℝ) ≤ (Dstar / 2 + 745 + 338) * (G.card : ℝ) + epsM Dstar * (G.card : ℝ) +
          (80 * (Light.dem ω : ℝ) + 369 * (Light.lp ω : ℝ) +
            169 * ∑ l ∈ Finset.Icc 1 run.R, ((lostRound run G δ (stageOf ω) l).card : ℝ)) +
          1.5 * ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) +
          ∑ l ∈ Finset.Icc 3 run.R, b l (Js l)

/-- [s6:thmMIXC] (c), last sentence: "Moreover `1.5 Σ_{(Y,l)} m_{Y,l} ≤ 1.5 ε_CONC(D_*) n` by
Theorem s6:thmCONCL(iv)." (Setting `RunHyp` of the theorem, every designation; the sum as in
`MixCStatement`.) -/
def MixCConcStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
      1.5 * ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) ≤
        1.5 * epsCONC Dstar * (G.card : ℝ)

/-- [s6:thmMIXC] (a), bullet "Lemma TPV at step (1)" (`MixCTPVApplicable`, TRIAGE §2.8): for every
stage-1 outcome (of positive weight) and every `Z ∈ Std_l`, the data `(Z^0, O_Z, Ret_Z)` satisfy
the hypotheses of Lemma s4:lemTPV: "`|Z^0| ≥ P_l ≥ N_0` … If `Z` is lend-good, then `O_Z = Own_Z`
… is a spanning `(2^{-5}, s_l/4)`-expander on `Z^0`, and … `s_l/4 ≥ 2^{150} L_Z^{42}`. If `Z` is
lend-bad, `O_Z = X^0_Z` is a spanning `(2^{-5}, s_l)`-expander on `Z^0` …, and
`s_l ≥ s_l/4 ≥ 2^{150} L_Z^{42}`" (with the partition `Z^0 = Ret_Z ⊔ Q*_Z`). -/
def MixCTPVApplicableStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ l : ℕ, ∀ a ∈ run.Std G l,
      (¬ lendBad run G (stageOf ω) (l, a) →
        Vortex.TPVHyp (run.Z0 G l a) (OZ run G (stageOf ω) l a) (ret run G δ (stageOf ω) l a)
          ((2 : ℝ) ^ (-5 : ℤ)) ((run.s G l : ℝ) / 4)) ∧
      (lendBad run G (stageOf ω) (l, a) →
        Vortex.TPVHyp (run.Z0 G l a) (OZ run G (stageOf ω) l a) (ret run G δ (stageOf ω) l a)
          ((2 : ℝ) ^ (-5 : ℤ)) (run.s G l : ℝ))

end EG.Spec
