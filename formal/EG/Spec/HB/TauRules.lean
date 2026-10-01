module

public import EG.Defs.HB.Witness
public import EG.Defs.Constants

/-!
# Statements: the witness Fact, the `τ`-rules and the split (manuscript s2:defWitness,
s2:defTauRules, s2:eqSplit)

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). Design note
`formal/work/p2b/P3A.md`. Definitions: `EG/Defs/HB/Witness.lean` (locked).

Manuscript v6.1, `s2.tex`, Definition [s2:defWitness] (Fact) and Definition [s2:defTauRules]
(equation (eqSplit), Facts (a)–(c)); quoted in the docstrings. Throughout s2, `ε = 2^{-5}`; the
witness parameter `ε` is written `EG.epsC`.

Formal reading (common to all statements).
* The context of [s2:defTauRules] is "Let `H`, `m` and `s` be as in Definition [s2:defWitness]
  (`s ≥ 0`), let `(U,F)` be a witness at `H` with `N` and `F_0` as there, write `V := V(H)`, and
  let `τ > s` be real." It is kept as the hypotheses `0 ≤ s`, `IsWitness H epsC s U F`, `s < τ`
  and `N = witN H U F` (`N` is a bound variable equal to `Nbr_{H-F}(U)`, to avoid repeating the
  expression). `F_0 = witF0 H U N`.
* The sets of the rules are the Defs `tauHout`, `tauU1` (`U'`), `tauN1` (`N'`), `tauF1`,
  `tauHin`, `tauN2` (`N''`), `tauF2` (`F''`), and the literal children `tauG1`
  (`G_1 = H[U'∪N''] - F''`), `tauG2` (`G_2 = H - U' - E(G_1) - F''`).
* Two facts that the manuscript uses but does not state are added as conjuncts of Fact (a):
  `U' ⊆ V(H)` and `N'' ⊆ V(H)` (blueprint TAU-IMPLICIT-SUBSETS; they make the split a split of
  Lemma SEP, [s2:lemSEP]).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:defWitness] (first sentences) "Let `s ≥ 0` and let `H` be a graph on `m = |H|`
vertices that is not an `(ε,s)`-expander (Cited result [s1:citDef11]). Then `m ≥ 2`, since a
graph on one vertex has no set `U` with `1 ≤ |U| ≤ 2m/3`. … Since `H` is not an
`(ε,s)`-expander, a witness exists." (`ε = 2^{-5}`.) -/
def WitnessExistsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℝ), 0 ≤ s → ¬ H.IsExpander epsC s →
    2 ≤ H.card ∧ ∃ (U : Finset V) (F : Finset (Sym2 V)), IsWitness H epsC s U F

/-- [s2:defWitness] (Fact) "For a witness `(U,F)` put `N := Nbr_{H-F}(U)`,
`F_0 := E_H(U, V(H) \ (U ∪ N))`. *Fact.* `F_0 ⊆ F` and `Nbr_{H-F_0}(U) = N`. In particular
`(U,F_0)` is again a witness at `H`, with the same set `N`." -/
def WitnessFactStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℝ) (U : Finset V) (F : Finset (Sym2 V))
    (N : Finset V), 0 ≤ s → IsWitness H epsC s U F → N = witN H U F →
      witF0 H U N ⊆ F ∧ witN H U (witF0 H U N) = N ∧ IsWitness H epsC s U (witF0 H U N)

/-- [s2:eqSplit] ([s2:defTauRules]) "The *split of `H` by the `τ`-rules* has the two children
`G_1 := H[U'∪N''] - F''` and `G_2 := H - U' - E(G_1) - F''`, and its *deleted set* is `F''`.
Every edge of `F''` has one end in `U'` and the other outside `U'∪N''`, so no edge of `F''` lies
inside `U'∪N''`, and every edge of `F''` meets `U'`. Hence
`G_1 = H[U'∪N'']`, `G_2 = H[V\U'] - E(H[N''])`." (equation (eqSplit); the right-hand sides are
the generic split `splitFst`, `splitSnd`; the equalities are equalities of graphs. The first
conjunct records, for every `e ∈ F''`, the premise "one end in `U'` and the other outside
`U'∪N''`" (outside within `V = V(H)`) and its two consequences.) -/
def TauEqSplitStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s τ : ℝ) (U : Finset V) (F : Finset (Sym2 V))
    (N : Finset V), 0 ≤ s → IsWitness H epsC s U F → s < τ → N = witN H U F →
      (∀ e ∈ tauF2 H U N τ,
        (∃ x ∈ tauU1 H U N τ, ∃ y ∈ H.verts \ (tauU1 H U N τ ∪ tauN2 H U N τ), e = s(x, y)) ∧
        e ∉ (tauU1 H U N τ ∪ tauN2 H U N τ).sym2 ∧
        ∃ x ∈ tauU1 H U N τ, x ∈ e) ∧
      tauG1 H U N τ = splitFst H (tauU1 H U N τ) (tauN2 H U N τ) ∧
      tauG2 H U N τ = splitSnd H (tauU1 H U N τ) (tauN2 H U N τ)

/-- [s2:defTauRules] Fact (a) "`U' ∩ N'' = ∅`, `U' ∪ N' = U ∪ N`, and
`F'' ⊆ F_1 ⊆ F_0 ⊆ F`." Two implicit facts are added (module docstring): `U' ⊆ V(H)` and
`N'' ⊆ V(H)`. -/
def TauFactAStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s τ : ℝ) (U : Finset V) (F : Finset (Sym2 V))
    (N : Finset V), 0 ≤ s → IsWitness H epsC s U F → s < τ → N = witN H U F →
      Disjoint (tauU1 H U N τ) (tauN2 H U N τ) ∧
      tauU1 H U N τ ∪ tauN1 H U N τ = U ∪ N ∧
      tauF2 H U N τ ⊆ tauF1 H U N τ ∧ tauF1 H U N τ ⊆ witF0 H U N ∧ witF0 H U N ⊆ F ∧
      tauU1 H U N τ ⊆ H.verts ∧ tauN2 H U N τ ⊆ H.verts

/-- [s2:defTauRules] Fact (b) "`E(H) = E(G_1) ⊔ E(G_2) ⊔ F''` (disjoint union),
`V(G_1) = U' ∪ N''` and `V(G_2) = V \ U'`. A vertex of `U'` lies only in `G_1`, a vertex of
`N''` lies in both children, and a vertex of `V \ (U' ∪ N'')` lies only in `G_2`." (`G_1`,
`G_2` are the literal children `tauG1`, `tauG2`; "disjoint union" = pairwise disjoint with union
`E(H)`.) -/
def TauFactBStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s τ : ℝ) (U : Finset V) (F : Finset (Sym2 V))
    (N : Finset V), 0 ≤ s → IsWitness H epsC s U F → s < τ → N = witN H U F →
      Disjoint (tauG1 H U N τ).edges (tauG2 H U N τ).edges ∧
      Disjoint (tauG1 H U N τ).edges (tauF2 H U N τ) ∧
      Disjoint (tauG2 H U N τ).edges (tauF2 H U N τ) ∧
      (tauG1 H U N τ).edges ∪ (tauG2 H U N τ).edges ∪ tauF2 H U N τ = H.edges ∧
      (tauG1 H U N τ).verts = tauU1 H U N τ ∪ tauN2 H U N τ ∧
      (tauG2 H U N τ).verts = H.verts \ tauU1 H U N τ ∧
      (∀ v ∈ tauU1 H U N τ, v ∈ (tauG1 H U N τ).verts ∧ v ∉ (tauG2 H U N τ).verts) ∧
      (∀ v ∈ tauN2 H U N τ, v ∈ (tauG1 H U N τ).verts ∧ v ∈ (tauG2 H U N τ).verts) ∧
      (∀ v ∈ H.verts \ (tauU1 H U N τ ∪ tauN2 H U N τ),
        v ∉ (tauG1 H U N τ).verts ∧ v ∈ (tauG2 H U N τ).verts)

/-- [s2:defTauRules] Fact (c) "Given the pair `(U,N)`, the objects `H_out`, `U'`, `N'`, `F_1`,
`H_in`, `N''`, `F''`, `G_1`, `G_2` depend only on `(U,N)`, because they are defined from
`F_0 = E_H(U, V \ (U ∪ N))`. The choice of `F` matters only through `N = Nbr_{H-F}(U)`: every
witness `(U,F)` yields the same split as its minimal part `(U,F_0)`."

Formal reading. The first sentence is definitional: the Defs take `(H, U, N, τ)` and no `F`
(blueprint TAU-SIGNATURE-UN). The second sentence: `(U, F_0)` is a witness whose set
`Nbr_{H-F_0}(U)` is `N`, so all nine objects computed from `(U, Nbr_{H-F_0}(U))` coincide with
those computed from `(U, N)`. -/
def TauFactCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s τ : ℝ) (U : Finset V) (F : Finset (Sym2 V))
    (N N₀ : Finset V), 0 ≤ s → IsWitness H epsC s U F → s < τ → N = witN H U F →
      N₀ = witN H U (witF0 H U N) →
      IsWitness H epsC s U (witF0 H U N) ∧ N₀ = N ∧
      tauHout H U N₀ τ = tauHout H U N τ ∧ tauU1 H U N₀ τ = tauU1 H U N τ ∧
      tauN1 H U N₀ τ = tauN1 H U N τ ∧ tauF1 H U N₀ τ = tauF1 H U N τ ∧
      tauHin H U N₀ τ = tauHin H U N τ ∧ tauN2 H U N₀ τ = tauN2 H U N τ ∧
      tauF2 H U N₀ τ = tauF2 H U N τ ∧ tauG1 H U N₀ τ = tauG1 H U N τ ∧
      tauG2 H U N₀ τ = tauG2 H U N τ

end EG.Spec
