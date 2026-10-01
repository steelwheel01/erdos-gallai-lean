module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statements of Proposition "degree recursion" (manuscript s2:propDegRec)

Statement file (`EG/Spec/**`) of the P2 s2b Spec unit (`formal/work/p2s/s2b.md`); blueprint s2b,
node s2:propDegRec. Definitions: `EG/Defs/HB/SplitTree.lean`, `Round.lean`, `Run.lean`,
`EG/Defs/Gamma/Core.lean` (locked).

Manuscript v6.1, `s2.tex`, Proposition [s2:propDegRec]:
"Let `l` be a round of a valid `HB^tp` run with `d_l ≥ D_*` (that is, `l ≤ R`), and put
`x := λ_l`. Then `M_l ≤ d_l^2`, `Λ_l ≤ 2x`, `s_l ≤ P_l`, and
`d_{l+1} ≤ 1.21 P_l + 9 s_l log M_l ≤ 6P_l + 9 s_l log M_l + 1.2 s_l ≤ 7x^{103} ≤ x^A < d_l`
(`A = 104` would suffice; `A = 105` is used). More precisely, every edge of `G_{l+1}` is of one of
the following kinds:
(a) an edge deleted by the `τ`-run of a piece `𝒫` with `|𝒫| ≥ P_l`; there are at most
`4 s_l |𝒫| log|𝒫|` of them for each piece and at most `4.5 n s_l log M_l` in total;
(b) an edge of a leaf of the two-level recursion with fewer than `P_l` vertices (a small leaf of a
`τ`-run, or a piece with `|𝒫| < P_l`); a leaf with `q` vertices has fewer than `qP_l/2` edges;
(c) a *guest edge*: an edge of `X^0_Z` with an end in `S_Z`, for a light pre-part `Z`; there are at
most `|Z^0| s_l/2` of them for each light `Z`.
Standalone pre-parts, GC-parts included, pass none of the edges of their leaf graphs down; in
particular, declaring a pre-part a GC-part (instead of light) can only decrease the set of
passed-down edges."

Four statements: the bounds (`DegRecRoundStatement`) and the classification
(`DegRecKindsRoundStatement`) at round level, and their run-level forms (`DegRecStatement`,
`DegRecKindsStatement`). TRIAGE §2.2 (DR-ROUND-LOCAL): s2:propExists applies propDegRec "to every
round `l` with `d_l ≥ D_*` of any (possibly unfinished) execution", i.e. to one round
`(H = G_l, c)` with `Round.Valid H c` and `D_* ≤ d(H)`; [s2:lemLacunary] and [s2:lemTower] apply
it to the rounds of a valid run.

Formal reading.
* "a round of a valid run with `d_l ≥ D_*`": at round level, an input graph `H` (= `G_l`) and
  choices `c` with `Round.Valid H c` and `D_* ≤ d(H)`; `G_{l+1} = Round.next H c`,
  `d_{l+1} = Round.d (Round.next H c)` (same vertex set, so the same `n`). At run level,
  `run.Valid G Dstar` and `l ∈ Finset.Icc 1 run.R` (which gives `d_l ≥ D_*`).
* Condition on `D_*`: the bounds use `Γ1` (a), (b) at `μ = log λ_l ≥ log log D_*` (blueprint
  DR-GAMMA), so `DegRecRoundStatement` and `DegRecStatement` carry `Gamma1core Dstar` (items
  (a)–(e) of `Γ1`, the standing assumption). The classification and the counts use only Lemma
  [s2:lemCap] (ii) and Proposition [s2:propOV] (both under `Γ2(a)`), so the kinds statements carry
  `Gamma2a Dstar` (weaker hypothesis, stronger statement).
* Constants: `x = λ_l = lamOf d_l`, `M_l = MOf d_l` (a natural number, cast to `ℝ`),
  `Λ_l = LamOf d_l = log M_l`, `s_l = sOf d_l`, `P_l = POf d_l`; "`log M_l`" in the chain is written
  `Real.logb 2 (M_l : ℝ)` (literally; it is `Λ_l`). `x^{103}`, `x^A` are natural powers
  (`A = EG.Aexp = 105`).
* (a) "deleted by the `τ`-run of a piece `𝒫` with `|𝒫| ≥ P_l`": `e` lies in the deleted set
  (`STree.deleted`) of the tree `c.tauRun q` rooted at the piece graph, for a big piece `q`
  (`Round.bigPieceAddrs`). "at most `4.5 n s_l log M_l` in total": the union of these deleted sets
  over the big pieces has at most that many edges.
* (b) the leaves of the two-level recursion are `(Round.twoLevel H c).leafAddrs` with leaf graphs
  `Round.X0 H c b` (for every leaf, not only pre-parts). "a leaf with `q` vertices has fewer than
  `qP_l/2` edges" is stated for the leaves with `q < P_l` vertices (those of kind (b)) as
  `2|E| < q P_l` in `ℝ`. For `q = 0` it would read `0 < 0`; it holds because every leaf of a valid
  round is nonempty (children of `s = 0` and `τ`-rule splits have at least one vertex; blueprint
  DR-LEAF-NONEMPTY), which a proof must show; no hypothesis `q ≥ 1` is added.
* (c) guest edges of a light pre-part `a`: the edges of `X^0_a` with an end in `S_a`
  (`∃ v ∈ S_a, v ∈ e`). The count bounds all guest edges (not only the passed-down ones).
* "Standalone pre-parts, GC-parts included, pass none of the edges of their leaf graphs down":
  for `a ∈ Std_l` (GC-parts are in `Std_l`, `EG.Spec.HBStdStatement`),
  `E(X^0_a) ∩ E(G_{l+1}) = ∅`. The clause "declaring a pre-part a GC-part (instead of light) can
  only decrease the set of passed-down edges" compares two different procedures and is not a
  proposition about a run; it is not formalized (blueprint DR-COUNTERFACTUAL); its content in the
  run is the standalone clause.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propDegRec], the bounds, round level: "Then `M_l ≤ d_l^2`, `Λ_l ≤ 2x`, `s_l ≤ P_l`, and
`d_{l+1} ≤ 1.21 P_l + 9 s_l log M_l ≤ 6P_l + 9 s_l log M_l + 1.2 s_l ≤ 7x^{103} ≤ x^A < d_l`"
(`x = λ_l`), for one round with input graph `H = G_l` and choices `c`: `Round.Valid H c`,
`D_* ≤ d(H)`, `Γ1` (a)–(e). -/
def DegRecRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V) (Dstar : ℝ),
    Gamma1core Dstar → Dstar ≤ Round.d H → Round.Valid H c →
    (MOf (Round.d H) : ℝ) ≤ Round.d H ^ 2 ∧
    LamOf (Round.d H) ≤ 2 * lamOf (Round.d H) ∧
    sOf (Round.d H) ≤ POf (Round.d H) ∧
    Round.d (Round.next H c) ≤
      1.21 * (POf (Round.d H) : ℝ) +
        9 * (sOf (Round.d H) : ℝ) * Real.logb 2 (MOf (Round.d H) : ℝ) ∧
    1.21 * (POf (Round.d H) : ℝ) + 9 * (sOf (Round.d H) : ℝ) * Real.logb 2 (MOf (Round.d H) : ℝ) ≤
      6 * (POf (Round.d H) : ℝ) + 9 * (sOf (Round.d H) : ℝ) * Real.logb 2 (MOf (Round.d H) : ℝ) +
        1.2 * (sOf (Round.d H) : ℝ) ∧
    6 * (POf (Round.d H) : ℝ) + 9 * (sOf (Round.d H) : ℝ) * Real.logb 2 (MOf (Round.d H) : ℝ) +
        1.2 * (sOf (Round.d H) : ℝ) ≤
      7 * lamOf (Round.d H) ^ 103 ∧
    7 * lamOf (Round.d H) ^ 103 ≤ lamOf (Round.d H) ^ Aexp ∧
    lamOf (Round.d H) ^ Aexp < Round.d H

/-- [s2:propDegRec], the classification, round level: "every edge of `G_{l+1}` is of one of the
following kinds: (a) an edge deleted by the `τ`-run of a piece `𝒫` with `|𝒫| ≥ P_l`; there are at
most `4 s_l |𝒫| log|𝒫|` of them for each piece and at most `4.5 n s_l log M_l` in total; (b) an
edge of a leaf of the two-level recursion with fewer than `P_l` vertices …; a leaf with `q`
vertices has fewer than `qP_l/2` edges; (c) a guest edge: an edge of `X^0_Z` with an end in `S_Z`,
for a light pre-part `Z`; there are at most `|Z^0| s_l/2` of them for each light `Z`. Standalone
pre-parts, GC-parts included, pass none of the edges of their leaf graphs down" (one round with
`Round.Valid H c`, `D_* ≤ d(H)`, `Γ2(a)`; module docstring). -/
def DegRecKindsRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V) (Dstar : ℝ),
    Gamma2a Dstar → Dstar ≤ Round.d H → Round.Valid H c →
    (∀ e ∈ (Round.next H c).edges,
      (∃ q ∈ Round.bigPieceAddrs H c, e ∈ (c.tauRun q).deleted (Round.piece H c q)) ∨
      (∃ b ∈ (Round.twoLevel H c).leafAddrs, (Round.X0 H c b).card < POf (Round.d H) ∧
        e ∈ (Round.X0 H c b).edges) ∨
      (∃ a ∈ Round.prePartAddrs H c, Round.isLight H c a ∧ e ∈ (Round.X0 H c a).edges ∧
        ∃ v ∈ Round.guests H c a, v ∈ e)) ∧
    (∀ q ∈ Round.bigPieceAddrs H c,
      (((c.tauRun q).deleted (Round.piece H c q)).card : ℝ) ≤
        4 * (sOf (Round.d H) : ℝ) * ((Round.piece H c q).card : ℝ) *
          Real.logb 2 ((Round.piece H c q).card : ℝ)) ∧
    ((((Round.bigPieceAddrs H c).biUnion
        (fun q => (c.tauRun q).deleted (Round.piece H c q))).card : ℕ) : ℝ) ≤
      4.5 * (H.card : ℝ) * (sOf (Round.d H) : ℝ) * Real.logb 2 (MOf (Round.d H) : ℝ) ∧
    (∀ b ∈ (Round.twoLevel H c).leafAddrs, (Round.X0 H c b).card < POf (Round.d H) →
      2 * ((Round.X0 H c b).edges.card : ℝ) <
        ((Round.X0 H c b).card : ℝ) * (POf (Round.d H) : ℝ)) ∧
    (∀ a ∈ Round.prePartAddrs H c, Round.isLight H c a →
      ((((Round.X0 H c a).edges.filter (fun e => ∃ v ∈ Round.guests H c a, v ∈ e)).card : ℕ) : ℝ) ≤
        ((Round.Z0 H c a).card : ℝ) * (sOf (Round.d H) : ℝ) / 2) ∧
    (∀ a ∈ Round.Std H c, Disjoint (Round.X0 H c a).edges (Round.next H c).edges)

/-- [s2:propDegRec], the bounds, run level: for every round `l ≤ R` of a valid run (so
`d_l ≥ D_*`), "`M_l ≤ d_l^2`, `Λ_l ≤ 2x`, `s_l ≤ P_l`, and
`d_{l+1} ≤ 1.21 P_l + 9 s_l log M_l ≤ 6P_l + 9 s_l log M_l + 1.2 s_l ≤ 7x^{103} ≤ x^A < d_l`"
(`x = λ_l`; under `Γ1` (a)–(e)). -/
def DegRecStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ l ∈ Finset.Icc 1 run.R,
      (run.M G l : ℝ) ≤ run.d G l ^ 2 ∧
      run.Lam G l ≤ 2 * run.lam G l ∧
      run.s G l ≤ run.P G l ∧
      run.d G (l + 1) ≤
        1.21 * (run.P G l : ℝ) + 9 * (run.s G l : ℝ) * Real.logb 2 (run.M G l : ℝ) ∧
      1.21 * (run.P G l : ℝ) + 9 * (run.s G l : ℝ) * Real.logb 2 (run.M G l : ℝ) ≤
        6 * (run.P G l : ℝ) + 9 * (run.s G l : ℝ) * Real.logb 2 (run.M G l : ℝ) +
          1.2 * (run.s G l : ℝ) ∧
      6 * (run.P G l : ℝ) + 9 * (run.s G l : ℝ) * Real.logb 2 (run.M G l : ℝ) +
          1.2 * (run.s G l : ℝ) ≤
        7 * run.lam G l ^ 103 ∧
      7 * run.lam G l ^ 103 ≤ run.lam G l ^ Aexp ∧
      run.lam G l ^ Aexp < run.d G l

/-- [s2:propDegRec], the classification, run level: for every round `l ≤ R` of a valid run, "every
edge of `G_{l+1}` is of one of the following kinds: (a) …; (b) …; (c) …" with the counts, and
"Standalone pre-parts, GC-parts included, pass none of the edges of their leaf graphs down"
(quoted at `DegRecKindsRoundStatement`; under `Γ2(a)`). -/
def DegRecKindsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    ∀ l ∈ Finset.Icc 1 run.R,
      (∀ e ∈ (run.graph G (l + 1)).edges,
        (∃ q ∈ run.bigPieceAddrs G l, e ∈ (run.tauRun l q).deleted (run.piece G l q)) ∨
        (∃ b ∈ (run.twoLevel G l).leafAddrs, (run.X0 G l b).card < run.P G l ∧
          e ∈ (run.X0 G l b).edges) ∨
        (∃ a ∈ run.prePartAddrs G l, run.isLight G l a ∧ e ∈ (run.X0 G l a).edges ∧
          ∃ v ∈ run.guests G l a, v ∈ e)) ∧
      (∀ q ∈ run.bigPieceAddrs G l,
        (((run.tauRun l q).deleted (run.piece G l q)).card : ℝ) ≤
          4 * (run.s G l : ℝ) * ((run.piece G l q).card : ℝ) *
            Real.logb 2 ((run.piece G l q).card : ℝ)) ∧
      ((((run.bigPieceAddrs G l).biUnion
          (fun q => (run.tauRun l q).deleted (run.piece G l q))).card : ℕ) : ℝ) ≤
        4.5 * (G.card : ℝ) * (run.s G l : ℝ) * Real.logb 2 (run.M G l : ℝ) ∧
      (∀ b ∈ (run.twoLevel G l).leafAddrs, (run.X0 G l b).card < run.P G l →
        2 * ((run.X0 G l b).edges.card : ℝ) < ((run.X0 G l b).card : ℝ) * (run.P G l : ℝ)) ∧
      (∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
        ((((run.X0 G l a).edges.filter (fun e => ∃ v ∈ run.guests G l a, v ∈ e)).card : ℕ) : ℝ) ≤
          ((run.Z0 G l a).card : ℝ) * (run.s G l : ℝ) / 2) ∧
      (∀ a ∈ run.Std G l, Disjoint (run.X0 G l a).edges (run.graph G (l + 1)).edges)

end EG.Spec
