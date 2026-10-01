module

public import EG.Defs.Expander

/-!
# Witnesses, the generic split and the `τ`-rules (manuscript s2:defWitness, s2:defTauRules)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s2.tex`, Definitions [s2:defWitness] and [s2:defTauRules] (quoted in the
docstrings below). Design note: `formal/work/p2d/hb.md`. Namespace `EG.HB`.

Contents:
* `IsWitness H ε s U F`: a witness `(U,F)` at `H` with parameter `s`; the conjuncts are literally
  the negated body of `EG.FGraph.IsExpander` (same casts, `2 * card / 3`, `logb 2 card ^ 2`),
  so that `¬ H.IsExpander ε s ↔ ∃ U F, IsWitness H ε s U F` is `push_neg` plus reordering
  (`EG.HB.not_isExpander_iff_exists_isWitness` in `EG.Lib.HB.SplitTree`);
* `witN H U F` (`N = Nbr_{H-F}(U)`) and `witF0 H U N` (`F_0 = E_H(U, V(H) \ (U ∪ N))`); `witF0`
  takes `N`, not `F`, so that Fact (c) of [s2:defTauRules] is definitional (blueprint
  TAU-SIGNATURE-UN);
* the generic split of Lemma SEP ([s2:lemSEP]) and of (eqSplit) ([s2:eqSplit]):
  `splitFst H U' N'' = H[U' ∪ N'']`, `splitSnd H U' N'' = H[V(H) \ U'] - E(H[N''])` and the
  deleted set `splitDel H U' N'' = E_H(U', V(H) \ (U' ∪ N''))`; they are shared by both levels
  of the two-level recursion (the `s = 0` level and the `τ`-runs);
* the `τ`-rules as functions of `(H, U, N, τ)`: `tauHout`, `tauU1` (`U'`), `tauN1` (`N'`),
  `tauF1`, `tauHin`, `tauN2` (`N''`), `tauF2` (`F''`), and the literal children
  `tauG1 = H[U' ∪ N''] - F''`, `tauG2 = H - U' - E(G_1) - F''` of the manuscript (their
  equality with `splitFst`/`splitSnd` is the equation (eqSplit), a statement, not a definition).

Totality. `ε`, `s`, `τ` are arbitrary reals; the definitions do not assume `τ > s`, `U ⊆ V(H)`
or that `(U,F)` is a witness. The comparison "`deg_{F_0}(v) ≥ τ`" is the real inequality
`τ ≤ (degE F₀ v : ℝ)` (blueprint TAU-REALCOMPARE).
-/

@[expose] public section

namespace EG.HB

variable {V : Type*} [DecidableEq V]

/-- [s2:defWitness] "Let `s ≥ 0` and let `H` be a graph on `m = |H|` vertices that is not an
`(ε,s)`-expander (Cited result [s1:citDef11]). … A *witness* at `H` is a pair `(U,F)` with
`U ⊆ V(H)` and `F ⊆ E(H)` such that
`1 ≤ |U| ≤ (2/3)m, |F| ≤ s|U|, |Nbr_{H-F}(U)| < ε|U| / log² m`."

Formal reading: the parameter `ε` is an argument (the manuscript fixes `ε = 2^{-5}` throughout
s2; statements instantiate `EG.epsC`), `s : ℝ`, `log = log₂`, `m = H.card`. The conjuncts are
the hypotheses of `EG.FGraph.IsExpander` followed by the negation of its conclusion, with the
same casts. The definition does not assume that `H` is not an expander: a witness exists iff it
is not (the sentence "Since `H` is not an `(ε,s)`-expander, a witness exists" is a lemma). -/
def IsWitness (H : FGraph V) (ε s : ℝ) (U : Finset V) (F : Finset (Sym2 V)) : Prop :=
  U ⊆ H.verts ∧ F ⊆ H.edges ∧ 1 ≤ U.card ∧ (U.card : ℝ) ≤ 2 * (H.card : ℝ) / 3 ∧
    (F.card : ℝ) ≤ s * U.card ∧
    (((H.deleteEdges F).nbrSet U).card : ℝ) < ε * U.card / Real.logb 2 H.card ^ 2

/-- [s2:defWitness] "For a witness `(U,F)` put `N := Nbr_{H-F}(U)`". Defined for all `U`, `F`. -/
def witN (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) : Finset V :=
  (H.deleteEdges F).nbrSet U

/-- [s2:defWitness] "`F_0 := E_H(U, V(H) \ (U ∪ N))`". A function of `(H, U, N)`: the manuscript
defines `F_0` from `U` and `N` (Fact (c) of [s2:defTauRules]: "they are defined from
`F_0 = E_H(U, V \ (U ∪ N))`"). -/
def witF0 (H : FGraph V) (U N : Finset V) : Finset (Sym2 V) :=
  H.edgesBetween U (H.verts \ (U ∪ N))

/-! ### The generic split ([s2:lemSEP], (eqSplit)) -/

/-- [s2:lemSEP] "at every non-leaf node `ν` there are disjoint sets `U'_ν, N''_ν ⊆ V(H_ν)` for
which the two children `ν_1, ν_2` of `ν` carry `H_{ν_1} = H_ν[U'_ν ∪ N''_ν]`, …": the first
child `H[U' ∪ N'']` (also the first child `G_1 = H[U' ∪ N'']` of (eqSplit), [s2:eqSplit]). -/
def splitFst (H : FGraph V) (U' N'' : Finset V) : FGraph V :=
  H.induce (U' ∪ N'')

/-- [s2:lemSEP] "… `H_{ν_2} = H_ν[V(H_ν) \ U'_ν] - E(H_ν[N''_ν])`": the second child
`H[V(H) \ U'] - E(H[N''])` (also `G_2` of (eqSplit), [s2:eqSplit]). -/
def splitSnd (H : FGraph V) (U' N'' : Finset V) : FGraph V :=
  (H.induce (H.verts \ U')).deleteEdges (H.induce N'').edges

/-- [s2:lemSEP] "the *deleted set* at `ν` is `F''_ν := E_{H_ν}(U'_ν, V(H_ν) \ (U'_ν ∪ N''_ν))`".
-/
def splitDel (H : FGraph V) (U' N'' : Finset V) : Finset (Sym2 V) :=
  H.edgesBetween U' (H.verts \ (U' ∪ N''))

/-! ### The `τ`-rules ([s2:defTauRules]) -/

/-- [s2:defTauRules] rule (1) "`H_out := {v ∈ U : deg_{F_0}(v) ≥ τ}`", with
`F_0 = witF0 H U N`. -/
noncomputable def tauHout (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset V :=
  U.filter (fun v => τ ≤ (degE (witF0 H U N) v : ℝ))

/-- [s2:defTauRules] rule (1) "`U' := U \ H_out`". -/
noncomputable def tauU1 (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset V :=
  U \ tauHout H U N τ

/-- [s2:defTauRules] rule (1) "`N' := N ∪ H_out`". -/
noncomputable def tauN1 (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset V :=
  N ∪ tauHout H U N τ

/-- [s2:defTauRules] rule (2) "`F_1 := E_H(U', V \ (U' ∪ N'))`" (`V = V(H)`). -/
noncomputable def tauF1 (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset (Sym2 V) :=
  H.edgesBetween (tauU1 H U N τ) (H.verts \ (tauU1 H U N τ ∪ tauN1 H U N τ))

/-- [s2:defTauRules] rule (2) "`H_in := {x ∈ V \ (U' ∪ N') : deg_{F_1}(x) ≥ τ}`". -/
noncomputable def tauHin (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset V :=
  (H.verts \ (tauU1 H U N τ ∪ tauN1 H U N τ)).filter
    (fun x => τ ≤ (degE (tauF1 H U N τ) x : ℝ))

/-- [s2:defTauRules] rule (2) "`N'' := N' ∪ H_in`". -/
noncomputable def tauN2 (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset V :=
  tauN1 H U N τ ∪ tauHin H U N τ

/-- [s2:defTauRules] rule (2) "`F'' := E_H(U', V \ (U' ∪ N''))`"; "its *deleted set* is `F''`".
Definitionally the deleted set `splitDel` of the generic split at `(U', N'')`. -/
noncomputable def tauF2 (H : FGraph V) (U N : Finset V) (τ : ℝ) : Finset (Sym2 V) :=
  splitDel H (tauU1 H U N τ) (tauN2 H U N τ)

/-- [s2:defTauRules] "The *split of `H` by the `τ`-rules* has the two children
`G_1 := H[U' ∪ N''] - F''` and …": the literal first child. By (eqSplit) ([s2:eqSplit]) it equals
`splitFst H U' N''` (a statement for the Spec layer); split recursions use `splitFst`. -/
noncomputable def tauG1 (H : FGraph V) (U N : Finset V) (τ : ℝ) : FGraph V :=
  (H.induce (tauU1 H U N τ ∪ tauN2 H U N τ)).deleteEdges (tauF2 H U N τ)

/-- [s2:defTauRules] "… and `G_2 := H - U' - E(G_1) - F''`": the literal second child. By
(eqSplit) it equals `splitSnd H U' N''` (a statement for the Spec layer). -/
noncomputable def tauG2 (H : FGraph V) (U N : Finset V) (τ : ℝ) : FGraph V :=
  (((H.deleteVerts (tauU1 H U N τ)).deleteEdges (tauG1 H U N τ).edges)).deleteEdges
    (tauF2 H U N τ)

end EG.HB
