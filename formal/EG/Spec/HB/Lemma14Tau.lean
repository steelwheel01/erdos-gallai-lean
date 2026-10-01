module

public import EG.Defs.HB.SplitTree
public import EG.Defs.Constants

/-!
# Statement of Lemma 14^τ (manuscript s2:lem14tau)

Statement file (`EG/Spec/**`), unit P3A (probe P-3, part 1). Design note
`formal/work/p2b/P3A.md`. Definitions: `EG/Defs/HB/SplitTree.lean`, `EG/Defs/HB/Witness.lean`
(locked; the `τ`-run is `STree.IsTauRun`).

Manuscript v6.1, `s2.tex`, Lemma [s2:lem14tau]:
"Let `H_0` be a graph on `n_0` vertices, `s ≥ 1` an integer, `ε = 2^{-5}`, and
`τ ≥ 128 s log² n_0`. The *`τ`-run* of `H_0` (with parameters `s, τ`) is the recursion that, at a
node `H`, stops if `H` is an `(ε,s)`-expander (the node is then a leaf), and otherwise picks any
witness `(U,F)` at `H` with parameter `s` (Definition [s2:defWitness]) and splits `H` by the
`τ`-rules at threshold `τ` (Definition [s2:defTauRules]; note `τ ≥ 128s > s` whenever
`n_0 ≥ 2`). Let `Dup` be the set of vertices lying in at least two leaves. Then, for every choice
of witnesses:
(a) at every split, at a node of size `m`,
`|H_out| + |H_in| ≤ |F_0|/τ ≤ s|U|/τ ≤ |U|/(128 log² m)`,
`|N''| < 1.25 ε|U|/log² m < 1.5 ε|U|/log² m`,
`|U'| ≥ (127/128)|U| > 0`, `U ⊆ U' ∪ N''`, `n_1 := |U' ∪ N''| ≤ 0.698 m < (3/4) m` and
`n_2 := m - |U'| < m`. The recursion terminates; it is a split recursion; at most
`4 s n_0 log n_0` edges are deleted; the remaining edges are partitioned into the leaves; every
leaf is an `(ε,s)`-expander; and the total size of the leaves is at most
`2n_0 - 2n_0/(2 + log n_0)`;
(b) (OV at `1.6ε`) at every split, `|N''| ≤ 1.6 ε|U'|/log² m`, the vertices of `U'` go only to
`G_1`, and `|G_1| ≤ (3/4)m`. Hence, by Lemma [s2:lemOVgeneric] with `c = 1.6`, the total leaf size
`S` satisfies `S ≤ n_0/(1 - 5.5ε) ≤ 1.21 n_0`, and for every `M ≥ 2` the duplication at nodes of
size at least `M` is `Δ_{≥M} ≤ 5.46 ε S / log M`;
(c) for every leaf `Leaf` and every vertex `h`,
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1` (`= τ - 1` for integer `τ`), and the number
is `0` if `h ∈ V(Leaf)`;
(d) if `u ∉ Dup`, every edge at `u` is deleted or lies in the unique leaf containing `u`."

Formal reading.
* Common hypotheses: `s : ℕ` with `1 ≤ s`, `τ : ℝ` with `128 s log₂² n_0 ≤ τ` (`n_0 = H.card`),
  and a tree `t` with `t.IsTauRun epsC s τ H` ("for every choice of witnesses" = for every tree
  satisfying the predicate: split recursion, leaf iff `(ε,s)`-expander, every split made by the
  `τ`-rules from some witness with parameter `s`).
* (a) "at every split": for every non-leaf address `a`, with `K = H_a`, and **every** witness
  `(U,F)` at `K` with parameter `s` whose `τ`-rules give the label of `a` (`N = Nbr_{K-F}(U)`,
  `F_0 = witF0 K U N`), the listed inequalities hold (`L14SplitStatement`). Each link of the
  manuscript's chains is a separate conjunct. `n_2 := m - |U'|` is the natural-number difference.
* "The recursion terminates" (for every choice of witnesses) is `L14TermStatement`: (T1) every
  `τ`-rule split of a graph `K` with `2 ≤ |K| ≤ n_0` (by a witness with parameter `s`) has both
  children of size `< |K|` (and `≥ 1`), so every chain of splits has length `≤ n_0`; (T2) for
  every choice rule `W` (a witness `W a K` at every non-expander `K`, possibly depending on the
  address `a`) there is a finite `τ`-run that uses the witnesses of `W` (blueprint
  LEM14-TERMINATION). "It is a split recursion" is `t.WF H`, part of `IsTauRun`.
* The rest of (a) is `L14GlobalStatement` (deletions, partition of the edges, leaves are
  expanders, the B-M leaf bound).
* (b) is `L14OVStatement`; (c), (d) are `L14ThinStatement`.
* **Repair (T1, math finding `L14-C-TAU0`).** The bound `≤ ⌈τ⌉ - 1` of (c) is false as stated when
  `τ = 0`, which the hypotheses allow for `n_0 = 1` (then `128 s log² n_0 = 0`; in Lean also for `n_0 = 0`, as `logb 2 0 = 0`): the `τ`-run is a
  single leaf, the count is `0` and `⌈0⌉ - 1 = -1` (Lean check:
  `EGTest.ProbeP3A.lem14tau_c_literal_false`). The two bounds of (c) carry the hypothesis
  `0 < τ` (as in Lemma [s2:lemThinCut]); it holds whenever `n_0 ≥ 2` (`τ ≥ 128 s`) and in every
  application (`τ = τ_l = ⌈128 s_l Λ_l²⌉ ≥ 128`, matching the lemma's own remark
  "`τ ≥ 128 s > s` whenever `n_0 ≥ 2`"). The other parts of (c) and (d) are unconditional.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lem14tau] (a), local part: "at every split, at a node of size `m`,
`|H_out| + |H_in| ≤ |F_0|/τ ≤ s|U|/τ ≤ |U|/(128 log² m)`,
`|N''| < 1.25 ε|U|/log² m < 1.5 ε|U|/log² m`, `|U'| ≥ (127/128)|U| > 0`, `U ⊆ U' ∪ N''`,
`n_1 := |U' ∪ N''| ≤ 0.698 m < (3/4) m` and `n_2 := m - |U'| < m`." -/
def L14SplitStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℕ) (τ : ℝ) (t : STree V),
    1 ≤ s → 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ → t.IsTauRun epsC s τ H →
    ∀ a ∈ t.internalAddrs, ∀ (K : FGraph V) (U N : Finset V) (F : Finset (Sym2 V)),
      K = t.graphAtD H a → IsWitness K epsC s U F → N = witN K U F →
      t.labelAt a = some (tauU1 K U N τ, tauN2 K U N τ) →
        (((tauHout K U N τ).card + (tauHin K U N τ).card : ℕ) : ℝ) ≤ (witF0 K U N).card / τ ∧
        ((witF0 K U N).card : ℝ) / τ ≤ s * U.card / τ ∧
        (s : ℝ) * U.card / τ ≤ U.card / (128 * Real.logb 2 K.card ^ 2) ∧
        ((tauN2 K U N τ).card : ℝ) < 1.25 * epsC * U.card / Real.logb 2 K.card ^ 2 ∧
        1.25 * epsC * U.card / Real.logb 2 K.card ^ 2 <
          1.5 * epsC * U.card / Real.logb 2 K.card ^ 2 ∧
        (127 / 128 : ℝ) * U.card ≤ (tauU1 K U N τ).card ∧ 0 < (tauU1 K U N τ).card ∧
        U ⊆ tauU1 K U N τ ∪ tauN2 K U N τ ∧
        ((tauU1 K U N τ ∪ tauN2 K U N τ).card : ℝ) ≤ 0.698 * K.card ∧
        0.698 * (K.card : ℝ) < 3 / 4 * K.card ∧
        K.card - (tauU1 K U N τ).card < K.card

/-- [s2:lem14tau] (a) "The recursion terminates", for every choice of witnesses (module
docstring):
(T1) a `τ`-rule split of a graph `K` with `2 ≤ |K| ≤ n_0` by a witness with parameter `s` has
children `G_1 = K[U' ∪ N'']`, `G_2 = K[V(K) \ U'] - E(K[N''])` with `1 ≤ |G_i| < |K|`
("Both children of every split have fewer vertices than their parent, so every root-to-node path
has at most `n_0` nodes, and the binary tree is finite");
(T2) for every rule `W` choosing a witness `W a K` with parameter `s` at every graph `K` that is
not an `(ε,s)`-expander (the choice may depend on the address `a` of the node), the recursion
that uses these witnesses is a finite tree: there is a `τ`-run `t` of `H_0` whose label at every
non-leaf address `a` is given by the `τ`-rules for the witness `W a H_a`. -/
def L14TermStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℕ) (τ : ℝ),
    1 ≤ s → 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ →
    (∀ (K : FGraph V) (U N : Finset V) (F : Finset (Sym2 V)),
      2 ≤ K.card → K.card ≤ H.card → IsWitness K epsC s U F → N = witN K U F →
        1 ≤ (splitFst K (tauU1 K U N τ) (tauN2 K U N τ)).card ∧
        (splitFst K (tauU1 K U N τ) (tauN2 K U N τ)).card < K.card ∧
        1 ≤ (splitSnd K (tauU1 K U N τ) (tauN2 K U N τ)).card ∧
        (splitSnd K (tauU1 K U N τ) (tauN2 K U N τ)).card < K.card) ∧
    ∀ W : Addr → FGraph V → Finset V × Finset (Sym2 V),
      (∀ (a : Addr) (K : FGraph V), ¬ K.IsExpander epsC s →
        IsWitness K epsC s (W a K).1 (W a K).2) →
      ∃ t : STree V, t.IsTauRun epsC s τ H ∧
        ∀ a ∈ t.internalAddrs,
          t.labelAt a = some
            (tauU1 (t.graphAtD H a) (W a (t.graphAtD H a)).1
                (witN (t.graphAtD H a) (W a (t.graphAtD H a)).1 (W a (t.graphAtD H a)).2) τ,
              tauN2 (t.graphAtD H a) (W a (t.graphAtD H a)).1
                (witN (t.graphAtD H a) (W a (t.graphAtD H a)).1 (W a (t.graphAtD H a)).2) τ)

/-- [s2:lem14tau] (a), global part: "at most `4 s n_0 log n_0` edges are deleted; the remaining
edges are partitioned into the leaves; every leaf is an `(ε,s)`-expander; and the total size of
the leaves is at most `2n_0 - 2n_0/(2 + log n_0)`." ("the remaining edges are partitioned into
the leaves": every edge of `H_0` is deleted at exactly one node or lies in exactly one leaf, the
count form of [s2:lemSEP] (i).) -/
def L14GlobalStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℕ) (τ : ℝ) (t : STree V),
    1 ≤ s → 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ → t.IsTauRun epsC s τ H →
      ((t.deleted H).card : ℝ) ≤ 4 * s * H.card * Real.logb 2 H.card ∧
      (∀ e ∈ H.edges,
        (t.leafAddrs.filter (fun L => e ∈ (t.graphAtD H L).edges)).card +
          (t.internalAddrs.filter (fun a => e ∈ t.delAt H a)).card = 1) ∧
      (∀ L ∈ t.leafAddrs, (t.graphAtD H L).IsExpander epsC s) ∧
      (t.leafMass H : ℝ) ≤ 2 * H.card - 2 * H.card / (2 + Real.logb 2 H.card)

/-- [s2:lem14tau] (b) "(OV at `1.6ε`) at every split, `|N''| ≤ 1.6 ε|U'|/log² m`, the vertices of
`U'` go only to `G_1`, and `|G_1| ≤ (3/4)m`. Hence, by Lemma [s2:lemOVgeneric] with `c = 1.6`,
the total leaf size `S` satisfies `S ≤ n_0/(1 - 5.5ε) ≤ 1.21 n_0`, and for every `M ≥ 2` the
duplication at nodes of size at least `M` is `Δ_{≥M} ≤ 5.46 ε S / log M`." (`G_1` is the first
child `a ++ [false]`; "every non-leaf node has `m ≥ 2`", from the proof, is a conjunct; the
hypotheses of Lemma OV with `c = 1.6` are `OVHyp epsC 1.6`.) -/
def L14OVStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℕ) (τ : ℝ) (t : STree V),
    1 ≤ s → 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ → t.IsTauRun epsC s τ H →
      (∀ a ∈ t.internalAddrs,
        ((t.labelN a).card : ℝ) ≤
            1.6 * epsC * (t.labelU a).card / Real.logb 2 (t.graphAtD H a).card ^ 2 ∧
        (∀ v ∈ t.labelU a, v ∈ (t.graphAtD H (a ++ [false])).verts ∧
          v ∉ (t.graphAtD H (a ++ [true])).verts) ∧
        ((t.graphAtD H (a ++ [false])).card : ℝ) ≤ 3 / 4 * (t.graphAtD H a).card ∧
        2 ≤ (t.graphAtD H a).card) ∧
      t.OVHyp epsC 1.6 H ∧
      (t.leafMass H : ℝ) ≤ H.card / (1 - 5.5 * epsC) ∧
      (H.card : ℝ) / (1 - 5.5 * epsC) ≤ 1.21 * H.card ∧
      ∀ M : ℝ, 2 ≤ M → (t.DeltaGe H M : ℝ) ≤ 5.46 * epsC * t.leafMass H / Real.logb 2 M

/-- [s2:lem14tau] (c), (d) "(c) for every leaf `Leaf` and every vertex `h`,
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1` (`= τ - 1` for integer `τ`), and the number
is `0` if `h ∈ V(Leaf)`; (d) if `u ∉ Dup`, every edge at `u` is deleted or lies in the unique
leaf containing `u`." (`Dup = t.dup H`, the `Dup` of this `τ`-run. The two bounds of (c) carry
the added hypothesis `0 < τ`: T1 repair `L14-C-TAU0`, module docstring.) -/
def L14ThinStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (s : ℕ) (τ : ℝ) (t : STree V),
    1 ≤ s → 128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ → t.IsTauRun epsC s τ H →
      (∀ L ∈ t.leafAddrs, ∀ h : V,
        (0 < τ →
          (((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
            e = s(h, u))).card : ℤ) ≤ ⌈τ⌉ - 1) ∧
        (0 < τ → ∀ k : ℕ, τ = k →
          ((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
            e = s(h, u))).card ≤ k - 1) ∧
        (h ∈ (t.graphAtD H L).verts →
          ((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
            e = s(h, u))).card = 0)) ∧
      ∀ u : V, u ∉ t.dup H → ∀ e ∈ H.edges, u ∈ e →
        e ∈ t.deleted H ∨
          ∃ L ∈ t.leafAddrs, u ∈ (t.graphAtD H L).verts ∧ e ∈ (t.graphAtD H L).edges ∧
            ∀ L' ∈ t.leafAddrs, u ∈ (t.graphAtD H L').verts → L' = L

end EG.Spec
