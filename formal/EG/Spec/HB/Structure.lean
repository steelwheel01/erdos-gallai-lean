module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core
public import EG.Spec.HB.StructureHY
public import EG.Spec.HB.StructureLight
public import EG.Spec.HB.CapPrePart
public import EG.Spec.HB.CapRound

/-!
# Statements of Proposition "structure of a valid run" (manuscript s2:propStructure), parts (i),
(iii) and (iv)

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:propStructure. Definitions: `EG/Defs/HB/Round.lean`, `EG/Defs/HB/Run.lean`,
`EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Proposition [s2:propStructure]:
"For every valid `HB^tp` run on a graph `G` with `n ≥ N_0` and `d_1 ≥ D_*`:
(i) each `X^0_Z` is a `(2^{-5},s_l)`-expander on `Z^0`; each light `X_Z` is a
`(2^{-6},s_l/2)`-expander on the light part `Z`; every `H_Y` has minimum degree greater than
`s_Y`; and `s_r ≥ λ_r^{100}` for every `r ≤ R`;
(ii) the conclusions of Lemma s2:lemCap(ii) hold;
(iii) `E(G_{l+1}) ⊆ E(G'_l) ⊆ E(G_l)` for every `l ≤ R`, so `d_{l+1} ≤ d_l`; and
`E(G) = ⨆_{l≤R} E(Cyc_l) ⊔ E_0 ⊔ ⨆_{Y light} E_{r(Y)}(Y) ⊔ ⨆_{l≤R} ⨆_{Z∈Std_l} E_l(Z)`
(disjoint unions); `E(H_Y) ⊆ E_{r(Y)}(Y)` for every ancestor `Y`; every edge of `E_{r(Y)}(Y)` has
both ends in `V(Y)`; the graphs `H_Y` of all ancestors `Y` of all rounds are pairwise
edge-disjoint, and the graphs `X^0_Z` of the pre-parts of one round are pairwise edge-disjoint;
`Σ_{l≤R}|Cyc_l| ≤ n` (the number of long cycles); and `|E_0| < D_* n/2`;
(iv) light parts of one round are pairwise vertex-disjoint, and `|Y| ≥ |Y^0|/2 ≥ P_r/2` for every
light part `Y` of round `r`; every vertex outside `D_l` lies in at most one round-`l` pre-part;
the port sets `U_Z` of distinct `Z ∈ Std_l` are pairwise disjoint; and each vertex lies in at most
one light part per round, namely in the light part of `home_l(v)` if that pre-part is light."

Where each part is stated.
* (i): `StructureExpStatement` (this file).
* (ii): not restated. It is Lemma [s2:lemCap] (ii): `EG.Spec.CapPrePartStatement` (run level, first
  three clauses), `EG.Spec.CapRunTauStatement` (run level, last clause) and
  `EG.Spec.CapRoundStatement` (round level, all clauses) (blueprint STR-II-DUPLICATE).
* (iii): `EG.Spec.StructureHYStatement` (unit P2J: `E(H_Y) ⊆ E_{r(Y)}(Y)`, ends in `V(Y)`, the
  `H_Y` pairwise edge-disjoint, the assigned sets pairwise disjoint) and
  `StructurePartitionStatement` (this file: the edge inclusions, the displayed partition, the
  `X^0_Z` of one round, the cycle count, `|E_0|`). The conjunction of the two is (iii).
* (iv): `StructureVertexStatement` (this file; all clauses). Its first clause, under the stronger
  hypothesis `RunHyp`, is the declared input `EG.Spec.StructureLightStatement` (unit P4B), which
  `StructureVertexStatement` implies (`RunHyp` contains `run.Valid`).

Formal reading.
* Hypotheses. The manuscript's `n ≥ N_0` is dropped (TRIAGE §2.12 "propStructure drops
  `n ≥ N_0`", blueprint STR-N0; `N0Cond` belongs to a later layer); dropping it strengthens the
  statements. `d_1 ≥ D_*` is also dropped: it is used only for `n > 0`, which (iii) needs for
  `|E_0| < D_* n/2` (for `n = 0` the claim reads `0 < 0`) and which (iii) carries as `0 < G.card`.
  The standing condition on `D_*` enters only through `Γ2(a)` (`D_* ≥ 2^{117}`, `Gamma2a`): the
  proof uses `P_l ≥ 11`, `D_* ≥ 8`, `λ_l ≥ 1` and Lemma s2:lemCap(ii) (blueprint STR-GAMMA-MIN);
  (i) and (iii) carry `Gamma2a Dstar`; (iv) needs no condition on `D_*`.
* Rounds are 1-indexed (`l ∈ Finset.Icc 1 run.R`); pre-parts are addresses
  `a ∈ run.prePartAddrs G l`; `X^0_Z = run.X0 G l a`, `Z^0 = run.Z0 G l a`,
  `S_Z = run.guests G l a`, `X_Z = run.X G l a`, `s_l = run.s G l` (a natural number; `s_l/2`
  is the real quotient), `λ_r = run.lam G r`, `P_r = run.P G r`, `D_l = run.D G l`,
  `home_l = run.home G l`, `Std_l = run.Std G l`, `U_Z = run.ports G l a`.
* (i) "`(2^{-5}, s_l)`-expander on `Z^0`": `(run.X0 G l a).verts = run.Z0 G l a` (definitional)
  and `IsExpander (2^{-5}) s_l`; "on the light part `Z`" is the vertex set `Z^0 \ S_Z`. The
  literals `2^{-5}`, `2^{-6}` are `(2 : ℝ) ^ (-5 : ℤ)` (as in `Run.ancEps`; `epsC` is the same
  number by definition).
* (i) "every `H_Y` has minimum degree greater than `s_Y`": for every ancestor `Y`
  (`Y ∈ run.ancestors G`, `H_Y = run.ancGraph G Y`, `s_Y = run.ancS G Y`), `V(H_Y)` is nonempty
  and every vertex of `H_Y` has degree `> s_Y` (pointwise, not through `FGraph.minDeg`, which is
  `0` on the empty graph; nonemptiness is stated explicitly, as the manuscript's `δ(H_Y) > s_Y`
  presupposes it: blueprint STR-MINDEG).
* (i) "`s_r ≥ λ_r^{100}`": conjunct `λ_r^{100} ≤ s_r`. The inequality `λ_r ≤ Λ_r`
  (`Λ_r = run.Lam G r = log M_r`) proved on the way ("so `Λ_r ≥ λ_r` and
  `s_r ≥ Λ_r^{100} ≥ λ_r^{100}`") is added as a conjunct, because [s2:lemTower] (b) cites it from
  "the proof of" (i) (blueprint STR-LAMBDA-LE-LAMBDA). This strengthens the statement.
* (iii) The displayed partition is written as: `E(G)` is the union of the four families
  (`E(Cyc_l) = run.cycEdges l` for `l ∈ [1,R]`; `E_0 = run.E0 G`; `E_{r(Y)}(Y) = run.E G Y.1 Y.2`
  for `Y` in the light parts `run.lightParts G`; `E_l(Z)` for `Z ∈ Std_l`, i.e. `(l, a)` in
  `run.stdParts G`), and any two distinct members of the families are disjoint. The light parts
  and the standalone pre-parts are both indexed by `PartId = (round, address)` and form two
  disjoint sets, so the last two families are written as one family over
  `run.lightParts G ∪ run.stdParts G`. `E(Cyc_l)` is one member per round (as displayed:
  `⨆_{l≤R} E(Cyc_l)`); the edge-disjointness of the cycles within a round is a field of
  `Round.Valid` (`CyclesValid`) and not restated.
* (iii) "`Σ_{l≤R}|Cyc_l| ≤ n` (the number of long cycles)": `|Cyc_l|` is the number of cycles,
  `(run.cycles l).length`.
* (iv) "`|Y| ≥ |Y^0|/2 ≥ P_r/2`": `|Y^0|/2 ≤ |Y|` and `P_r/2 ≤ |Y^0|/2` in `ℝ`, with
  `|Y| = |run.partVerts G l a|` (`Z^0 \ S_Z` for a light pre-part). "each vertex lies in at most one
  light part per round, namely in the light part of `home_l(v)`": every vertex of the light part of
  a light pre-part `a` has `home_l(v) = a`, and at most one light pre-part of round `l` has `v` in
  its light part.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propStructure] (i) "each `X^0_Z` is a `(2^{-5},s_l)`-expander on `Z^0`; each light `X_Z`
is a `(2^{-6},s_l/2)`-expander on the light part `Z`; every `H_Y` has minimum degree greater than
`s_Y`; and `s_r ≥ λ_r^{100}` for every `r ≤ R`" (for every valid run, under `Γ2(a)`; with the
inequality `λ_r ≤ Λ_r` from the proof, module docstring). -/
def StructureExpStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l,
      (run.X0 G l a).verts = run.Z0 G l a ∧
      (run.X0 G l a).IsExpander ((2 : ℝ) ^ (-5 : ℤ)) (run.s G l : ℝ)) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
      (run.X G l a).verts = run.Z0 G l a \ run.guests G l a ∧
      (run.X G l a).IsExpander ((2 : ℝ) ^ (-6 : ℤ)) ((run.s G l : ℝ) / 2)) ∧
    (∀ Y ∈ run.ancestors G, (run.ancGraph G Y).verts.Nonempty ∧
      ∀ v ∈ (run.ancGraph G Y).verts, run.ancS G Y < ((run.ancGraph G Y).deg v : ℝ)) ∧
    (∀ r ∈ Finset.Icc 1 run.R,
      run.lam G r ≤ run.Lam G r ∧ run.lam G r ^ 100 ≤ (run.s G r : ℝ))

/-- [s2:propStructure] (iii), the clauses not in `StructureHYStatement`: "`E(G_{l+1}) ⊆ E(G'_l) ⊆
E(G_l)` for every `l ≤ R`, so `d_{l+1} ≤ d_l`; and
`E(G) = ⨆_{l≤R} E(Cyc_l) ⊔ E_0 ⊔ ⨆_{Y light} E_{r(Y)}(Y) ⊔ ⨆_{l≤R} ⨆_{Z∈Std_l} E_l(Z)`
(disjoint unions); … the graphs `X^0_Z` of the pre-parts of one round are pairwise
edge-disjoint; `Σ_{l≤R}|Cyc_l| ≤ n` (the number of long cycles); and `|E_0| < D_* n/2`" (for every
valid run on a graph with `n ≥ 1`, under `Γ2(a)`; module docstring). -/
def StructurePartitionStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → 0 < G.card → run.Valid G Dstar →
    (∀ l ∈ Finset.Icc 1 run.R,
      (run.graph G (l + 1)).edges ⊆ (run.graph' G l).edges ∧
      (run.graph' G l).edges ⊆ (run.graph G l).edges ∧
      run.d G (l + 1) ≤ run.d G l) ∧
    G.edges = ((Finset.Icc 1 run.R).biUnion run.cycEdges ∪ run.E0 G) ∪
      (run.lightParts G ∪ run.stdParts G).biUnion (fun Y => run.E G Y.1 Y.2) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ l' ∈ Finset.Icc 1 run.R, l ≠ l' →
      Disjoint (run.cycEdges l) (run.cycEdges l')) ∧
    (∀ l ∈ Finset.Icc 1 run.R, Disjoint (run.cycEdges l) (run.E0 G)) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ Y ∈ run.lightParts G ∪ run.stdParts G,
      Disjoint (run.cycEdges l) (run.E G Y.1 Y.2)) ∧
    (∀ Y ∈ run.lightParts G ∪ run.stdParts G, Disjoint (run.E G Y.1 Y.2) (run.E0 G)) ∧
    (∀ Y ∈ run.lightParts G ∪ run.stdParts G, ∀ Y' ∈ run.lightParts G ∪ run.stdParts G,
      Y ≠ Y' → Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2)) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l, ∀ b ∈ run.prePartAddrs G l, a ≠ b →
      Disjoint (run.X0 G l a).edges (run.X0 G l b).edges) ∧
    (∑ l ∈ Finset.Icc 1 run.R, (run.cycles l).length) ≤ G.card ∧
    ((run.E0 G).card : ℝ) < Dstar * (G.card : ℝ) / 2

open Classical in
/-- [s2:propStructure] (iv) "light parts of one round are pairwise vertex-disjoint, and
`|Y| ≥ |Y^0|/2 ≥ P_r/2` for every light part `Y` of round `r`; every vertex outside `D_l` lies in
at most one round-`l` pre-part; the port sets `U_Z` of distinct `Z ∈ Std_l` are pairwise disjoint;
and each vertex lies in at most one light part per round, namely in the light part of `home_l(v)`
if that pre-part is light" (for every valid run; no condition on `D_*`; module docstring). -/
def StructureVertexStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    run.Valid G Dstar → ∀ l ∈ Finset.Icc 1 run.R,
    (∀ a ∈ run.prePartAddrs G l, ∀ b ∈ run.prePartAddrs G l, a ≠ b →
      run.isLight G l a → run.isLight G l b →
      Disjoint (run.partVerts G l a) (run.partVerts G l b)) ∧
    (∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
      ((run.Z0 G l a).card : ℝ) / 2 ≤ ((run.partVerts G l a).card : ℝ) ∧
      (run.P G l : ℝ) / 2 ≤ ((run.Z0 G l a).card : ℝ) / 2) ∧
    (∀ v : V, v ∉ run.D G l →
      ((run.prePartAddrs G l).filter (fun a => v ∈ run.Z0 G l a)).card ≤ 1) ∧
    (∀ a ∈ run.Std G l, ∀ b ∈ run.Std G l, a ≠ b →
      Disjoint (run.ports G l a) (run.ports G l b)) ∧
    (∀ a ∈ run.prePartAddrs G l, run.isLight G l a → ∀ v ∈ run.partVerts G l a,
      run.home G l v = some a) ∧
    (∀ v : V, ((run.prePartAddrs G l).filter
      (fun a => run.isLight G l a ∧ v ∈ run.partVerts G l a)).card ≤ 1)

end EG.Spec
