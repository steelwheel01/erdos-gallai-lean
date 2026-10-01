module

public import EG.Defs.Main.GammaCond
public import EG.Defs.Chain.Design
public import EG.Defs.Fnum

/-!
# Statement of Theorem JV⁺* (manuscript s7:thmJVps)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:thmJVps`. Consumer: s7:thmMainProof, through the hypothesis `EG.Spec.HIHyp` of
Theorem HI″ (`EG/Spec/Quot/HI.lean`).

Manuscript v6.1, `s7.tex`, Theorem [s7:thmJVps] (Theorem JV⁺*):
"Assume that `D_*` satisfies Γ1–Γ4. Let `G` be a graph with `n ≥ N_0` vertices and `d_1 ≥ D_*`.
Take any valid `HB^{τ+}` run on `G` (Proposition s2:propExists), any designation `δ`, and no
VX-parts (`𝒱 = ∅`). Then there are simple graphs `Q_3, …, Q_R` without isolated vertices such that
(1) `f(G) ≤ C_0 n + 2 Σ_{l=3}^{R} f(Q_l)`, where `C_0 := D_*/2 + 1085 + ε_1(D_*)`;
(2) `Σ_{l=3}^{R} |V(Q_l)| ≤ θ_Q n`, where `θ_Q = ε_2(D_*) ≤ 1/4`.
Here `ε_1` and `ε_2` are the explicit functions of `D_*` defined in Proposition s7:propCost and
Lemma s7:lemUHsplit. Items at ultra hubs cost no collision payments. They pay only the standard
costs (pooled vertices, JV-bad ports, SDR failures), and they add quotient vertices only through
Lemma s7:lemUHsplit."

Formal reading (blueprint s7b JV-*).
* "`D_*` satisfies Γ1–Γ4" with "`N_0` as in Definition s1:defConstants": `EG.N0Cond N0` and
  `EG.GammaCond N0 Dstar` (`Γ1 ∧ Γ2(a) ∧ Γ3 ∧ Γ4`; Γ2(b),(c) are consequences of Γ1, never
  hypotheses). `n = G.card`, `d_1 = run.d G 1`; "any valid run": `run.Valid G Dstar`; "any
  designation": `δ` with `IsDesignation run G δ`. "No VX-parts" has no Lean content (VX-parts
  are not defined in the formalization; blueprint JV-HYPS).
* "simple graphs `Q_3, …, Q_R`": graphs `Q l : FGraph (W l)` on vertex types `W l` (an `FGraph`
  is simple: finite vertex set, loopless, no parallel edges), read for `3 ≤ l ≤ R` (the values at
  other `l` are ignored; none if `R < 3`); "without isolated vertices":
  `∀ v ∈ (Q l).verts, ∃ e ∈ (Q l).edges, v ∈ e`. The same family is used in (1) and (2)
  (JV-SAME-Q). The vertex types live in the universe of `V` (the proof takes
  `W l = EG.Quot.QVert V`), so that the consumer `HIHyp` (universe 0) can use the statement.
* `f = EG.fnum`, `C_0 = EG.Quot.C0`, `θ_Q = EG.Quot.thetaQ` (`= ε_2 = EG.Quot.eps2`). "`θ_Q ≤ 1/4`"
  in (2) is the hypothesis Γ4 (inside `GammaCond`) and is not restated.
* The last two sentences (ultra hubs) are commentary (Lemma s7:lemPay (e) with Lemma s7:lemUltra);
  they are not part of the statement (blueprint JV-ULTRA-PROSE).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s7:thmJVps] Theorem JV⁺*: "Assume that `D_*` satisfies Γ1–Γ4. Let `G` be a graph with
`n ≥ N_0` vertices and `d_1 ≥ D_*`. Take any valid `HB^{τ+}` run on `G`, any designation `δ`, and
no VX-parts. Then there are simple graphs `Q_3, …, Q_R` without isolated vertices such that
(1) `f(G) ≤ C_0 n + 2 Σ_{l=3}^{R} f(Q_l)`, where `C_0 := D_*/2 + 1085 + ε_1(D_*)`;
(2) `Σ_{l=3}^{R} |V(Q_l)| ≤ θ_Q n`, where `θ_Q = ε_2(D_*) ≤ 1/4`." -/
def JVpsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    N0Cond N0 → GammaCond N0 Dstar → N0 ≤ (G.card : ℝ) → Dstar ≤ run.d G 1 →
    run.Valid G Dstar → IsDesignation run G δ →
    ∃ (W : ℕ → Type u) (Q : (l : ℕ) → FGraph (W l)),
      (∀ l ∈ Finset.Icc 3 run.R, ∀ v ∈ (Q l).verts, ∃ e ∈ (Q l).edges, v ∈ e) ∧
      (fnum G.edges : ℝ) ≤
        C0 Dstar * (G.card : ℝ) + 2 * ∑ l ∈ Finset.Icc 3 run.R, (fnum (Q l).edges : ℝ) ∧
      ∑ l ∈ Finset.Icc 3 run.R, ((Q l).card : ℝ) ≤ thetaQ Dstar * (G.card : ℝ)

end EG.Spec
