module

public import EG.Defs.HB.SplitTree
public import EG.Defs.Constants

/-!
# Statement of Lemma OV, the generic overlap bound (manuscript s2:lemOVgeneric)

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). Design note
`formal/work/p2b/P3A.md`. Definitions: `EG/Defs/HB/SplitTree.lean` (locked: `OVHyp`,
`DeltaGe`, `dupGe`, `leafMass`, `IsS0Rec`, `cOV`).

Manuscript v6.1, `s2.tex`, Lemma [s2:lemOVgeneric]:
"Let `c > 0` with `3.42 c ε < 1`, and put `c_OV := log₂(4/3)`. Consider a split recursion (Lemma
[s2:lemSEP]) on a root graph with `n_0 ≥ 1` vertices such that at every non-leaf node `ν`, with
`m := |ν|`, `m ≥ 2`, `|ν_1| ≤ (3/4)m`, `|N''_ν| ≤ c ε |U'_ν| / log² m`. (Recall that vertices of
`U'_ν` go only to the first child `ν_1`.) Let `S` be the total size of the leaves. For `M ≥ 2` let
`Δ_{≥M} := Σ_ν |N''_ν|`, the sum over the non-leaf nodes `ν` with `|ν| ≥ M` (…), and for a vertex
`v` let `dup_{≥M}(v)` be the number of non-leaf nodes `ν` with `|ν| ≥ M` and `v ∈ N''_ν` (so
`Σ_v dup_{≥M}(v) = Δ_{≥M}`). Then:
(a) `Δ_{≥M} ≤ c ε (1/log² M + 1/(c_OV log M)) S ≤ 3.42 c ε S / log M`;
(b) for every vertex `v`, the number of leaves `Leaf` with `|Leaf| ≥ M` containing `v` is at most
`1 + dup_{≥M}(v)`; consequently `Σ_{Leaf:|Leaf|≥M} |Leaf| - |⋃_{Leaf:|Leaf|≥M} V(Leaf)| ≤ Δ_{≥M}`;
(c) `S ≤ n_0/(1 - 3.42 c ε)`.
*Instance `c = 1` (the `s = 0` recursion).* …" (quoted at `OVInstanceStatement`).

Formal reading.
* `ε = 2^{-5}` (`EG.epsC`; "Throughout, `ε = 2^{-5}`" in s2). The hypotheses on the recursion are
  `t.OVHyp epsC c H` (split recursion + the three node conditions; `ν_1` is `a ++ [false]`).
  `n_0 ≥ 1` is kept (`1 ≤ H.card`), although it is not needed (blueprint OV-N0-POS).
* (a) is stated in its **sharp** first form (with `c_OV = cOV`) and the second inequality of the
  chain separately: lem14tau (b) needs the sharp form (`1.6 (1 + 1/c_OV) ≤ 5.46` needs
  `log₂(4/3) ≥ 0.414508`; blueprint OV-CONST-546).
* `M` is real, `|ν| ≥ M` is the real comparison (as in `DeltaGe`, `dupGe`).
* The "so `Σ_v dup_{≥M}(v) = Δ_{≥M}`" identity is a conjunct (sum over `v ∈ V(H_0)`; every
  `N''_ν` lies in `V(H_0)`).
* The consequence of (b) is written additively, `Σ ≤ |⋃| + Δ` (no truncated subtraction; blueprint
  OV-NATSUB).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemOVgeneric] (a), (b), (c) and the identity `Σ_v dup_{≥M}(v) = Δ_{≥M}` (see the module
docstring for the quoted text): "(a) `Δ_{≥M} ≤ c ε (1/log² M + 1/(c_OV log M)) S ≤
3.42 c ε S / log M`; (b) for every vertex `v`, the number of leaves `Leaf` with `|Leaf| ≥ M`
containing `v` is at most `1 + dup_{≥M}(v)`; consequently
`Σ_{Leaf:|Leaf|≥M} |Leaf| - |⋃_{Leaf:|Leaf|≥M} V(Leaf)| ≤ Δ_{≥M}`; (c) `S ≤ n_0/(1 - 3.42 c ε)`."
(Hypotheses: `c > 0`, `3.42 c ε < 1`, `n_0 ≥ 1`, the node conditions `OVHyp`; (a), (b) for every
real `M ≥ 2`.) -/
def OVStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V) (c : ℝ),
    0 < c → 3.42 * c * epsC < 1 → 1 ≤ H.card → t.OVHyp epsC c H →
    (∀ M : ℝ, 2 ≤ M →
      (t.DeltaGe H M : ℝ) ≤
          c * epsC * (1 / Real.logb 2 M ^ 2 + 1 / (cOV * Real.logb 2 M)) * t.leafMass H ∧
        c * epsC * (1 / Real.logb 2 M ^ 2 + 1 / (cOV * Real.logb 2 M)) * t.leafMass H ≤
          3.42 * c * epsC * t.leafMass H / Real.logb 2 M) ∧
    (∀ M : ℝ, 2 ≤ M → ∑ v ∈ H.verts, t.dupGe H M v = t.DeltaGe H M) ∧
    (∀ M : ℝ, 2 ≤ M → ∀ v : V,
      (t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ) ∧
          v ∈ (t.graphAtD H L).verts)).card ≤ 1 + t.dupGe H M v) ∧
    (∀ M : ℝ, 2 ≤ M →
      ∑ L ∈ t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ)),
          (t.graphAtD H L).card ≤
        ((t.leafAddrs.filter (fun L => M ≤ ((t.graphAtD H L).card : ℝ))).biUnion
            (fun L => (t.graphAtD H L).verts)).card + t.DeltaGe H M) ∧
    (t.leafMass H : ℝ) ≤ H.card / (1 - 3.42 * c * epsC)

/-- [s2:lemOVgeneric] (Instance `c = 1`) "Call a split recursion an *`s = 0` recursion* if at every
non-leaf node `ν` there is a witness `(U_ν,F_ν)` at `H_ν` with parameter `s = 0` (Definition
[s2:defWitness]) and `U'_ν = U_ν`, `N''_ν = Nbr_{H_ν}(U_ν)`. This is exactly the recursion in the
proof of [BM, Lemma 14] with `s = 0` (Cited result [s1:citLem14]): there `F_ν = ∅`, the children
are `H_ν[U_ν ∪ N_ν]` and `H_ν \ U_ν - E(H_ν[U_ν ∪ N_ν]) = H_ν[V(H_ν) \ U_ν] - E(H_ν[N_ν])`, and
the deleted set `E_{H_ν}(U_ν, V(H_ν) \ (U_ν ∪ N_ν))` is empty. (It is also the split by the
`τ`-rules at `s = 0` for any `τ > 0`: then `F_0 = ∅` and `H_out = H_in = ∅`.) Every `s = 0`
recursion satisfies the hypotheses with `c = 1`; hence its total leaf size is at most
`n_0/(1 - 3.42ε) ≤ 1.12 n_0`."

Formal reading. For every non-leaf address `a` and every witness `(U, F)` at `H_a` with parameter
`0` whose sets are the label (`N = Nbr_{H_a}(U)`): `F = ∅`, `Nbr_{H_a - F}(U) = N`, the two
children, the B-M form of the second child, `F''_a = ∅`, and for every `τ > 0` the `τ`-rules at
`(U, N)` give `F_0 = ∅`, `H_out = H_in = ∅`, `U' = U`, `N'' = N`. Globally: the recursion is a
split recursion by the `τ`-rules at every `τ > 0` (`IsTauSplitTree`, witness parameter
`0 < τ`), it satisfies `OVHyp` with `c = 1`, and `S ≤ n_0/(1 - 3.42ε) ≤ 1.12 n_0`. The first
sentence of the remark (identification with the recursion of [BM]) is commentary (blueprint
OV-BM-COMMENTARY). The instance does not need `n_0 ≥ 1`. -/
def OVInstanceStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V), t.IsS0Rec epsC H →
    (∀ a ∈ t.internalAddrs, ∀ (K : FGraph V) (U N : Finset V) (F : Finset (Sym2 V)),
      K = t.graphAtD H a → IsWitness K epsC 0 U F → N = K.nbrSet U →
      t.labelAt a = some (U, N) →
        F = ∅ ∧ witN K U F = N ∧
        t.graphAtD H (a ++ [false]) = K.induce (U ∪ N) ∧
        t.graphAtD H (a ++ [true]) = (K.deleteVerts U).deleteEdges (K.induce (U ∪ N)).edges ∧
        (K.deleteVerts U).deleteEdges (K.induce (U ∪ N)).edges =
          (K.induce (K.verts \ U)).deleteEdges (K.induce N).edges ∧
        t.delAt H a = ∅ ∧
        ∀ τ : ℝ, 0 < τ →
          witF0 K U N = ∅ ∧ tauHout K U N τ = ∅ ∧ tauHin K U N τ = ∅ ∧
            tauU1 K U N τ = U ∧ tauN2 K U N τ = N) ∧
    (∀ τ : ℝ, 0 < τ → t.IsTauSplitTree epsC τ H) ∧
    t.OVHyp epsC 1 H ∧
    (t.leafMass H : ℝ) ≤ H.card / (1 - 3.42 * epsC) ∧
    (H.card : ℝ) / (1 - 3.42 * epsC) ≤ 1.12 * H.card

end EG.Spec
