module

public import EG.Defs.Fnum
public import EG.Defs.Graph
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Statement of Fact EG0, the long-cycle bound (manuscript s1:factEG0, new in v6)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Found/EG0.lean` proves it.

Manuscript, Fact [s1:factEG0] ("the long-cycle bound"), s1.tex:
"(a) Every graph `H` with `h ≥ 1` vertices has a decomposition into at most `h(log h + 1)`
objects, at most `h − 1` of which are single edges. In particular `f(H) ≤ h(log h + 1)`.
(b) Let `N > 1` and `L := log N`, and let `α` and `β` be real numbers with `0 ≤ α ≤ N`, `β > 0`
and `4β ≤ L`. If `F` is the edge set of a (simple) graph, so that `F` has no loops and no parallel
edges, and every edge of `F` has both ends in a set `W` with `|W| ≤ βα/L`, then `F` has a
decomposition into at most `βα` objects, at most `|W|` of which are single edges."

Formal reading.
* "graph `H` with `h` vertices": `H : EG.FGraph V` (finite, simple, loopless), `h = H.card`.
* `log = log₂` ([s1:convGraphs] (b)): `Real.logb 2`. The bounds `h(log h + 1)` and `βα` are
  compared in `ℝ` with the number of objects `D.length`.
* "a decomposition of `E(H)` (of `F`)": `EG.IsDecomp ↑H.edges D` (`EG.IsDecomp ↑F D`), a list of
  well-formed objects ([s1:defObject]) partitioning the edge set.
* "the number of single edges of `D`": `D.countP (fun o => o matches .edge _)` (the objects of the
  form `EG.Obj.edge e`; the same as `D.countP EG.Obj.isEdge` of `EG/Lib/Found/Fnum.lean`, inlined
  here so that the statement depends on `EG/Defs` only).
* "In particular `f(H) ≤ h(log h + 1)`": `EG.fnum H.edges` (`H.edges` is loopless), a separate
  statement `FactEG0aFnumStatement`.
* (b) `N`, `α`, `β` are reals (the uses in s4 take `N = |Z|` and `α ∈ {|P|, |P_ℓ|, N}`).
  "`F` is the edge set of a (simple) graph": `F : Finset (Sym2 V)` with no loops,
  `∀ e ∈ F, ¬ e.IsDiag` (a `Finset (Sym2 V)` has no parallel edges); this is the T0 encoding
  decision **T0-eg0-loop** (CONVENTIONS.md). "every edge of `F` has both ends in `W`":
  `∀ e ∈ F, ∀ v ∈ e, v ∈ W`, for a `W : Finset V`.
-/

@[expose] public section


namespace EG.Spec

universe u

/-- [s1:factEG0] (a) "Every graph `H` with `h ≥ 1` vertices has a decomposition into at most
`h(log h + 1)` objects, at most `h − 1` of which are single edges."
Here `h = H.card`, `log = Real.logb 2`, and the single edges of `D` are its objects
`EG.Obj.edge e`. -/
def FactEG0aStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : EG.FGraph V), 1 ≤ H.card →
    ∃ D : List (EG.Obj V), EG.IsDecomp (H.edges : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ (H.card : ℝ) * (Real.logb 2 (H.card : ℝ) + 1) ∧
      D.countP (fun o => o matches .edge _) ≤ H.card - 1

/-- [s1:factEG0] (a) "In particular `f(H) ≤ h(log h + 1)`."
Here `h = H.card`, `f(H) = EG.fnum H.edges`, `log = Real.logb 2`. -/
def FactEG0aFnumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : EG.FGraph V), 1 ≤ H.card →
    (EG.fnum H.edges : ℝ) ≤ (H.card : ℝ) * (Real.logb 2 (H.card : ℝ) + 1)

/-- [s1:factEG0] (b) "Let `N > 1` and `L := log N`, and let `α` and `β` be real numbers with
`0 ≤ α ≤ N`, `β > 0` and `4β ≤ L`. If `F` is the edge set of a (simple) graph, so that `F` has no
loops and no parallel edges, and every edge of `F` has both ends in a set `W` with
`|W| ≤ βα/L`, then `F` has a decomposition into at most `βα` objects, at most `|W|` of which are
single edges."
Here `L = Real.logb 2 N`, `F : Finset (Sym2 V)` without loops, `W : Finset V`, and the single
edges of `D` are its objects `EG.Obj.edge e`. -/
def FactEG0bStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (N α β : ℝ) (F : Finset (Sym2 V)) (W : Finset V),
    1 < N → 0 ≤ α → α ≤ N → 0 < β → 4 * β ≤ Real.logb 2 N →
    (∀ e ∈ F, ¬ e.IsDiag) → (∀ e ∈ F, ∀ v ∈ e, v ∈ W) →
    (W.card : ℝ) ≤ β * α / Real.logb 2 N →
    ∃ D : List (EG.Obj V), EG.IsDecomp (F : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ β * α ∧
      D.countP (fun o => o matches .edge _) ≤ W.card

end EG.Spec
