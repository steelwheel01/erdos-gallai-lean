module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core
public import EG.Spec.HB.OVRunK

/-!
# Statements of Proposition "overlap constants on `HB*^{τ+}`" (manuscript s2:propOV), round level
and the run-level clauses not in `OVRunK.lean`

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:propOV. Definitions: `EG/Defs/HB/SplitTree.lean`, `Round.lean`, `Run.lean`,
`EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Proposition [s2:propOV] (overlap constants on `HB*^{τ+}`):
"Fix a valid `HB*^{τ+}` run and a round `r ≤ R`. Let `S_r` be the total size of the leaves of the
two-level recursion of round `r`, and `S^𝒫_r` the total size of the `s = 0` pieces. Then
`S^𝒫_r ≤ 1.12 n` and `S_r ≤ 1.21 n`, and:
(K1) `Σ|Z^0| ≤ 1.37 n`, the sum over the round-`r` pre-parts; `|Std_r| ≤ 1.37 n/P_r`; the number
of ancestors of round `r` is at most `1.37 n/P_r` (each ancestor corresponds to a distinct pre-part
`Y^0 ⊇ V(Y)`); hence the number `ν_l` of ancestors of rounds at most `l-2` satisfies
`ν_l ≤ 1.37 n Σ_{r≤l-2} P_r^{-1}`;
(K2) `|D_r| ≤ dup_r ≤ 7.6 ε n/log P_r`, and
`Σ_{Z∈Std_r}|A_Z| ≤ Σ|Z^0 ∩ D_r| ≤ 2dup_r ≤ 15.2 ε n/log P_r`, the middle sum over all round-`r`
pre-parts;
(K3) the total size `Σ|Z^0|` of the round-`r` pre-parts failing (L1) is at most
`30.4 ε n/log P_r`, and `Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n/log P_r`, the sum over all round-`r`
pre-parts `Y`;
(F11) `Σ_w mult_r(w) = Σ_Y |V(Y)| ≤ 1.37 n`, the second sum over the ancestors `Y` of round `r`,
and `mult_r(w) ≤ μ_r(w)` for every vertex `w`."
and, in the proof, (s2:eqDupComposite): "for `M ≥ 2`,
`Δ_{≥M} ≤ 5.46 ε S_r/log M ≤ 6.61 ε n/log M`" (a displayed, labelled equation that
[s2:propDegRec] and the (K2), (K3) bounds use; stated here as a conjunct).

Where each part is stated.
* Run level, (K1) and (K3): the declared inputs `EG.Spec.OVK1Statement`, `EG.Spec.OVK3Statement`
  (`EG/Spec/HB/OVRunK.lean`, unit P3B; not restated). Run level, the rest (leaf masses,
  (eqDupComposite), (K2), (F11)): `OVRunStatement` (this file). [s2:propOV] at run level is
  `OVK1Statement ∧ OVK3Statement ∧ OVRunStatement`.
* Round level, all clauses except the `ν_l` bound (which involves several rounds):
  `OVRoundStatement` (this file). TRIAGE §2.2 (decision DR-ROUND-LOCAL): s2:propExists applies
  propOV "to every round `l` with `d_l ≥ D_*` of any (possibly unfinished) execution", i.e. to one
  round `(H = G_l, c)` with `Round.Valid H c` and `D_* ≤ d(H)`, not to a valid run.

Formal reading.
* Hypothesis `Γ2(a)` (`D_* ≥ 2^{117}`, `Gamma2a`): implicit in the manuscript; the proof applies
  Lemma 14^τ (b) to every `τ`-run through Lemma [s2:lemCap] (ii) (blueprint OV-IMPLICIT-DSTAR),
  exactly as in `OVK1Statement`, `OVK3Statement`. At round level: `D_* ≤ d(H)` (the round is run,
  (R0)) and `Round.Valid H c`.
* `n = |V(G)|`: at run level `G.card`; at round level `H.card` (every `G_l`, `G'_l` has vertex set
  `V(G)`, `EG.HB.Run.graph_verts`). `ε = EG.epsC`, `log = Real.logb 2`,
  `P_r = POf d_r` (`run.P G r`).
* `S^𝒫_r` is the leaf mass of the `s = 0` tree `tree0` rooted at `G'_r`; `S_r` the leaf mass of the
  two-level recursion `twoLevel` rooted at `G'_r` (`STree.leafMass`, leaves counted by address).
  `Δ_{≥M}` is `STree.DeltaGe` of the two-level recursion, for every real `M ≥ 2`.
* (K1) "the number of ancestors of round `r`": at round level, the number of pre-part addresses
  (one ancestor per pre-part, [s2:defAncestors]).
* (K2) `dup_r = Σ_{w∈V(G)} (μ_r(w) - 1)^+` (`run.dup G r`; at round level the same sum with
  `Round.mu`, truncated subtraction in `ℕ`); `A_Z = Z^0 ∩ D_r` (`run.hubs G r a`); the chain is
  split into its links; `2 dup_r ≤ 15.2 ε n/log P_r` is the last link.
* (K3) "failing (L1)" is `¬ isL1`; `Dup*_r = DupStar`.
* (F11) "`Σ_w mult_r(w) = Σ_Y |V(Y)|`": the sum over `w ∈ V(G)` of `run.mult G r w` equals the sum
  of `|V(Y)|` over the ancestors of round `r` (`Y ∈ run.ancestors G`, `Y.1 = r`,
  `V(Y) = run.ancVerts G Y`); at round level `mult_r(w)` is written out as the number of pre-parts
  `a` with `w ∈ V(part of a)` (`Round.partVerts`), which is `Run.mult`'s definition.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

open Classical in
/-- [s2:propOV], round level: "`S^𝒫_r ≤ 1.12 n` and `S_r ≤ 1.21 n`", (s2:eqDupComposite)
"`Δ_{≥M} ≤ 5.46 ε S_r/log M ≤ 6.61 ε n/log M`" (`M ≥ 2`), (K1) without the `ν_l` clause, (K2),
(K3), (F11) (quoted in the module docstring), for one round with input graph `H = G_r` and
choices `c`: `Round.Valid H c`, `D_* ≤ d(H)`, `Γ2(a)`. -/
def OVRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V) (Dstar : ℝ),
    Gamma2a Dstar → Dstar ≤ Round.d H → Round.Valid H c →
    ((c.tree0.leafMass (Round.graph' H c) : ℕ) : ℝ) ≤ 1.12 * (H.card : ℝ) ∧
    (((Round.twoLevel H c).leafMass (Round.graph' H c) : ℕ) : ℝ) ≤ 1.21 * (H.card : ℝ) ∧
    (∀ M : ℝ, 2 ≤ M →
      (((Round.twoLevel H c).DeltaGe (Round.graph' H c) M : ℕ) : ℝ) ≤
          5.46 * epsC * (((Round.twoLevel H c).leafMass (Round.graph' H c) : ℕ) : ℝ) /
            Real.logb 2 M ∧
        5.46 * epsC * (((Round.twoLevel H c).leafMass (Round.graph' H c) : ℕ) : ℝ) /
            Real.logb 2 M ≤
          6.61 * epsC * (H.card : ℝ) / Real.logb 2 M) ∧
    -- (K1)
    ((∑ a ∈ Round.prePartAddrs H c, (Round.Z0 H c a).card : ℕ) : ℝ) ≤ 1.37 * (H.card : ℝ) ∧
    ((Round.Std H c).card : ℝ) ≤ 1.37 * (H.card : ℝ) / (POf (Round.d H) : ℝ) ∧
    ((Round.prePartAddrs H c).card : ℝ) ≤ 1.37 * (H.card : ℝ) / (POf (Round.d H) : ℝ) ∧
    -- (K2)
    (Round.D H c).card ≤ ∑ w ∈ H.verts, (Round.mu H c w - 1) ∧
    ((∑ w ∈ H.verts, (Round.mu H c w - 1) : ℕ) : ℝ) ≤
      7.6 * epsC * (H.card : ℝ) / Real.logb 2 (POf (Round.d H) : ℝ) ∧
    ∑ a ∈ Round.Std H c, (Round.Z0 H c a ∩ Round.D H c).card ≤
      ∑ a ∈ Round.prePartAddrs H c, (Round.Z0 H c a ∩ Round.D H c).card ∧
    ∑ a ∈ Round.prePartAddrs H c, (Round.Z0 H c a ∩ Round.D H c).card ≤
      2 * ∑ w ∈ H.verts, (Round.mu H c w - 1) ∧
    ((2 * ∑ w ∈ H.verts, (Round.mu H c w - 1) : ℕ) : ℝ) ≤
      15.2 * epsC * (H.card : ℝ) / Real.logb 2 (POf (Round.d H) : ℝ) ∧
    -- (K3)
    ((∑ a ∈ (Round.prePartAddrs H c).filter (fun a => ¬ Round.isL1 H c a),
        (Round.Z0 H c a).card : ℕ) : ℝ) ≤
      30.4 * epsC * (H.card : ℝ) / Real.logb 2 (POf (Round.d H) : ℝ) ∧
    ((∑ a ∈ Round.prePartAddrs H c, (Round.Z0 H c a ∩ Round.DupStar H c).card : ℕ) : ℝ) ≤
      16 * epsC * (H.card : ℝ) / Real.logb 2 (POf (Round.d H) : ℝ) ∧
    -- (F11)
    ∑ w ∈ H.verts, ((Round.prePartAddrs H c).filter (fun a => w ∈ Round.partVerts H c a)).card =
      ∑ a ∈ Round.prePartAddrs H c, (Round.partVerts H c a).card ∧
    ((∑ a ∈ Round.prePartAddrs H c, (Round.partVerts H c a).card : ℕ) : ℝ) ≤
      1.37 * (H.card : ℝ) ∧
    ∀ w : V, ((Round.prePartAddrs H c).filter (fun a => w ∈ Round.partVerts H c a)).card ≤
      Round.mu H c w

/-- [s2:propOV], run level, the clauses not stated by `OVK1Statement`, `OVK3Statement`:
"`S^𝒫_r ≤ 1.12 n` and `S_r ≤ 1.21 n`", (s2:eqDupComposite) "`Δ_{≥M} ≤ 5.46 ε S_r/log M ≤
6.61 ε n/log M`" (`M ≥ 2`), "(K2) `|D_r| ≤ dup_r ≤ 7.6 ε n/log P_r`, and
`Σ_{Z∈Std_r}|A_Z| ≤ Σ|Z^0 ∩ D_r| ≤ 2dup_r ≤ 15.2 ε n/log P_r`, the middle sum over all round-`r`
pre-parts" and "(F11) `Σ_w mult_r(w) = Σ_Y |V(Y)| ≤ 1.37 n`, the second sum over the ancestors `Y`
of round `r`, and `mult_r(w) ≤ μ_r(w)` for every vertex `w`" (for every valid run and round
`r ≤ R`, under `Γ2(a)`). -/
def OVRunStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R,
      (((run.tree0 r).leafMass (run.graph' G r) : ℕ) : ℝ) ≤ 1.12 * (G.card : ℝ) ∧
      (((run.twoLevel G r).leafMass (run.graph' G r) : ℕ) : ℝ) ≤ 1.21 * (G.card : ℝ) ∧
      (∀ M : ℝ, 2 ≤ M →
        (((run.twoLevel G r).DeltaGe (run.graph' G r) M : ℕ) : ℝ) ≤
            5.46 * epsC * (((run.twoLevel G r).leafMass (run.graph' G r) : ℕ) : ℝ) /
              Real.logb 2 M ∧
          5.46 * epsC * (((run.twoLevel G r).leafMass (run.graph' G r) : ℕ) : ℝ) /
              Real.logb 2 M ≤
            6.61 * epsC * (G.card : ℝ) / Real.logb 2 M) ∧
      -- (K2)
      (run.D G r).card ≤ run.dup G r ∧
      (run.dup G r : ℝ) ≤ 7.6 * epsC * (G.card : ℝ) / Real.logb 2 (run.P G r : ℝ) ∧
      ∑ a ∈ run.Std G r, (run.hubs G r a).card ≤
        ∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a ∩ run.D G r).card ∧
      ∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a ∩ run.D G r).card ≤ 2 * run.dup G r ∧
      ((2 * run.dup G r : ℕ) : ℝ) ≤ 15.2 * epsC * (G.card : ℝ) / Real.logb 2 (run.P G r : ℝ) ∧
      -- (F11)
      ∑ w ∈ G.verts, run.mult G r w =
        ∑ Y ∈ (run.ancestors G).filter (fun Y => Y.1 = r), (run.ancVerts G Y).card ∧
      ((∑ Y ∈ (run.ancestors G).filter (fun Y => Y.1 = r), (run.ancVerts G Y).card : ℕ) : ℝ) ≤
        1.37 * (G.card : ℝ) ∧
      ∀ w : V, run.mult G r w ≤ run.mu G r w

end EG.Spec
