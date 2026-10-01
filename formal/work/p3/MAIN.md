# P3 MAIN: assembly of `EG.Proof.mainInternal` (s7:thmMainProof, s1:thmMain)

Status (2026-09-30): `EG.Proof.mainInternal : EG.Spec.MainInternal` is proved in place in
`EG/Proof/Main.lean` (name and statement unchanged; `sorry` removed). Compiles
(`scripts/check.sh EG/Proof/Main.lean`: rc=0, 0 errors, 0 sorry warnings; `lake build EG.Proof.Main`
succeeds); lint 0 findings. The Specs compose as the TeX proof says: no missing hypothesis, no form
or quantifier-order mismatch, no parameter condition left unestablished.

## Assembly (follows s7:thmMainProof)

1. `N_0`, `D_*`: `EG.exists_gammaCond : Spec.GammaCondExistsStatement` (s7:lemGammaSat,
   `EG/Proof/Gamma/Sat.lean`, fully proved) gives `N0Cond N0 ∧ GammaCond N0 D`.
2. Constants of HI″ with `C := C_0 D`, `ϑ := θ_Q D` ("`C_0 ≥ D_*/2` since `ε_1 ≥ 0`;
   `0 ≤ θ_Q ≤ 1/4 < 1/2`"): `D ≥ 4` from Γ1 via `Gamma1core.gamma2a` (Γ2(a) derived from Γ1,
   per the watch item, not assumed); `EG.MainConst.half_le_C0`, `thetaQ_nonneg` (all terms of
   `ε_1`, `ε_2` are ≥ 0 for `D ≥ 4`), `thetaQ_lt_half` (Γ4 `ε_2 ≤ 1/4`). New helper file
   `EG/Lib/Main/Constants.lean` (namespace `EG.MainConst`, to avoid clashing with the same facts
   in the s7 unit's `EG/Lib/Quot/ConstNonneg.lean`, namespace `EG.Quot`).
3. `EG.Proof.hiHyp_of_gammaCond : N0Cond N0 → GammaCond N0 D → Spec.HIHyp D N0 (C0 D) (thetaQ D)`:
   for `G : FGraph V` (`V : Type`) without isolated vertices, `N0 ≤ |G|`, `D ≤ 2|E|/|G|`:
   * a valid run: `EG.Todo.ExistsRun` (s2:propExists) with `Gamma1core D` (from Γ1);
   * a designation: `EG.Chain.exists_isDesignation` (s6:defDesign, Lib, proved);
   * `d_1 = run.d G 1 = 2|E(G)|/|G|` by `Run.graph_one` (definitional unfolding of `Round.d`);
   * `EG.Todo.JVps` (s7:thmJVps) gives `W, Q` with (1), (2) over `l ∈ Icc 3 R`;
   * reindex `Q_3..Q_R` as `Fin (R+1-3)` (`EG.Proof.sum_Icc_three_eq_sum_fin`).
   The "no isolated vertices" hypothesis of HIHyp is not needed by JVps (JVps is stronger);
   the "no isolated vertices" conclusion of JVps for the `Q_l` is not needed by HIHyp.
4. `EG.mainInternal_of_hiHyp` (`EG/Proof/Quot/HIMain.lean`, from the proved `EG.hi`, s7:thmHI)
   gives `Spec.MainInternal` with `c = ⌈c_EG⌉₊`.

Universe: `JVpsStatement.{u}` and `ExistsRunStatement.{u}` are used at `u = 0`, matching
`HIHyp` (`V : Type`). No universe transport needed.

## Theorems used (direct)
- `EG.exists_gammaCond` (s7:lemGammaSat; proved, no stub)
- `EG.Todo.ExistsRun` (s2:propExists; [DECLARED INPUT] stub)
- `EG.Todo.JVps` (s7:thmJVps; proved by the s7 unit this round from further stubs)
- `EG.Chain.exists_isDesignation` (s6:defDesign; Lib)
- `EG.mainInternal_of_hiHyp` / `EG.hi` (s7:thmHI; proved)
- `EG.Gamma1core.gamma2a`, `EG.GammaCond.gamma1core`, `EG.HB.Run.graph_one` (Lib)
- `EG.MainConst.*` (this unit, `EG/Lib/Main/Constants.lean`)

Not used: `EG.Todo.GammaCondExists` (redundant with the proved `EG.exists_gammaCond`),
`EG.Todo.CorJVpsEG` (the explicit form; the same assembly proves it at universe 0).

## Axiom scan
`lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Main`:
"inspected 3545 constants under [EG]; 10 use sorryAx; 0 meta-scan hits; 0 violations".
sorryAx users: `EG.Proof.hiHyp_of_gammaCond`, `EG.Proof.mainInternal`, `EG.Todo.JVps`,
`EG.Todo.UHsplitSum`, `EG.Todo.UHsplitTheta` (proved, depend on stubs), and the remaining
[DECLARED INPUT] leaves that `mainInternal` depends on:
- `EG.Todo.ExistsRun` (s2:propExists)
- `EG.Todo.Cost` (s7:propCost; bundles the MIX-C decomposition)
- `EG.Todo.EXprime` (s7:lemEXprime)
- `EG.Todo.UHsplitDet` (s7:lemUHsplit)
- `EG.Todo.UHsplitRound` (s7:lemUHsplit)
(As of this scan; the s7 unit is proving stubs concurrently, so the leaf set may shrink.)
Only `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` occur.

## Findings
None blocking. Observation for P3 review: the Main chain's declared inputs are only five
stubs because `CostStatement` states the existence of the decomposition of `E(G)` itself
(MIX-C, lift, simplicity are inside the Cost stub's future proof, not separate leaves of Main).
