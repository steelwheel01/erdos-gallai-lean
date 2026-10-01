# P1b pilot [hi]: Theorem HI″, layered quotient induction (s7:thmHI): design note

Status: statement and complete proof, no `sorry`. `scripts/check.sh` on the three files:
0 errors, 0 warnings. `lake build EG.Proof.Quot.HIMain` OK (builds `EG.Spec.Quot.HI`,
`EG.Proof.Quot.HI`). `python3 scripts/lint.py`: 0 findings. Axiom scan
(`--prefix EG --no-sorry EG.Spec.Quot.HI EG.Proof.Quot.HI EG.Proof.Quot.HIMain`): 559 constants,
0 sorryAx, 0 violations.

## Files and modules (not yet in `EG.lean`; the integrator should add them via `gen_roots.py`)
| File | Module | Contents |
|---|---|---|
| `EG/Spec/Quot/HI.lean` | `EG.Spec.Quot.HI` | `EG.Spec.HIHyp` (the hypothesis), `EG.Spec.HIStatement` (the theorem) |
| `EG/Proof/Quot/HI.lean` | `EG.Proof.Quot.HI` | `EG.hi : EG.Spec.HIStatement`, helper lemmas, `EG.hi_simpleGraph`, adapter `EG.hiHyp_of_fintype_index` |
| `EG/Proof/Quot/HIMain.lean` | `EG.Proof.Quot.HIMain` | `EG.mainInternal_of_hiHyp` (for `EG/Proof/Main.lean`), explicit-constant forms, fidelity iff |

Imports: Spec imports `EG.Defs.Graph`, `EG.Defs.Fnum` and small Mathlib modules (reals, big
operators). Proof imports `EG.Lib.Found.FGraphFnum`; HIMain imports `EG.Lib.Found.FnumMain`.

## Statement (EG/Spec/Quot/HI.lean)
Manuscript [s7:thmHI] (s7.tex l. 1354): "Let C ≥ D_*/2 and ϑ ∈ [0,1/2) be constants with the
following property. Every graph G without isolated vertices, with n ≥ N₀ vertices and
d₁ = 2|E(G)|/n ≥ D_*, admits finitely many simple graphs Q₁,…,Q_k (k ≥ 0) such that
f(G) ≤ C n + 2 Σ f(Q_i) and Σ |V(Q_i)| ≤ ϑ n. Then f(G) ≤ c |V(G)| for every graph G, where
c := max(C/(1−2ϑ), N₀/2)."

```lean
def HIHyp (Dstar N₀ C ϑ : ℝ) : Prop :=
  ∀ (V : Type) (G : EG.FGraph V),
    (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) →          -- no isolated vertices
    N₀ ≤ (G.card : ℝ) →                               -- n ≥ N₀
    Dstar ≤ 2 * (G.edges.card : ℝ) / (G.card : ℝ) →   -- d₁ = 2|E(G)|/n ≥ D_*
    ∃ (k : ℕ) (W : Fin k → Type) (Q : (i : Fin k) → EG.FGraph (W i)),
      (EG.fnum G.edges : ℝ) ≤ C * (G.card : ℝ) + 2 * ∑ i, (EG.fnum (Q i).edges : ℝ) ∧
      ∑ i, ((Q i).card : ℝ) ≤ ϑ * (G.card : ℝ)

def HIStatement : Prop :=
  ∀ (Dstar N₀ C ϑ : ℝ), Dstar / 2 ≤ C → 0 ≤ ϑ → ϑ < 1 / 2 → HIHyp Dstar N₀ C ϑ →
    ∀ (V : Type) (G : EG.FGraph V),
      (EG.fnum G.edges : ℝ) ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * (G.card : ℝ)
```

Design decisions.
1. **Graphs are `EG.FGraph` on `V : Type`**, for G and for the Q_i (PLAN §3: the graph layer is
   `FGraph`; the s2–s7 producers of the hypothesis work with `FGraph`). f(G) = `fnum G.edges`
   (loopless, so the loop convention of `fnum` is irrelevant), n = `G.card`, |E(G)| =
   `G.edges.card`. A Mathlib `SimpleGraph` Q on a `Fintype` enters as `FGraph.ofSimpleGraph Q`
   (`ofSimpleGraph_edges`/`ofSimpleGraph_card` are `rfl` simp lemmas in `EG.Lib.Found.Graph`).
   The universe is `Type`, as in `EG.Spec.MainInternal`; the induction needs the Q_i in the same
   universe as G.
2. **"finitely many simple graphs Q₁,…,Q_k (k ≥ 0)"**: `k : ℕ`, `W : Fin k → Type`,
   `Q i : FGraph (W i)` (each on its own vertex type, as the quotients live on tagged subtypes).
   `EG.hiHyp_of_fintype_index` converts an index set that is any `Fintype ι` (e.g. the rounds
   `l = 3,…,R` of s7:thmJVps) to `Fin k`.
3. **"without isolated vertices"** is instance-free: every vertex is an end of an edge.
   `EG.FGraph.noIsolated_iff_deg_ne_zero` proves it equivalent to `∀ v ∈ V(G), d_G(v) ≠ 0`.
4. **d₁ is a real division** exactly as written. At n = 0 Lean gives 2·0/0 = 0; the manuscript
   does not consider n = 0, and the proof never applies the hypothesis to a graph with n = 0
   (the multiplied-out form `D_* n ≤ 2|E|` would make the hypothesis apply to more graphs at
   n = 0, i.e. make the theorem weaker; the division form is the faithful one).
5. **Constants.** `D_*, N₀, C, ϑ : ℝ`, universally quantified, no sign conditions on `D_*` or
   `N₀` (the manuscript's N₀ ≥ 2^40 and D_* ≥ 2^117 are special cases; a natural-number N₀ is
   cast). The constant c is written out inline as `max (C / (1 - 2 * ϑ)) (N₀ / 2)` (no separate
   Spec definition), so "C and ϑ do not depend on c" is syntactic.

## Proof (EG/Proof/Quot/HI.lean)
`EG.hi_induction`: for a real c with `0 ≤ c`, `N₀/2 ≤ c`, `C ≤ c(1−2ϑ)`, strong induction on
`n = G.card` (`Nat.strong_induction_on`, over all `V : Type`, `G : FGraph V`), following the
manuscript's minimal counterexample steps:
- n = 0: `FGraph.fnum_edges_eq_zero_of_card_eq_zero` ("the graph without vertices has f = 0").
- (1) isolated vertex v: `FGraph.fnum_edges_deleteVerts_singleton_of_deg_eq_zero` (s1:factAdd(d))
  and `card_deleteVerts_singleton`; IH at n − 1, then c(n−1) ≤ cn.
- (2) n < N₀: `fnum_le_card` (s1:factAdd(a)) and `FGraph.two_mul_card_edges_le`
  (2|E| ≤ n(n−1), from the handshake lemma and d(v) ≤ n−1), then n(n−1)/2 ≤ (N₀/2)n ≤ cn.
- (3) d₁ < D_*: |E| < D_* n/2 ≤ Cn ≤ cn (trivial bound only).
- (4)–(5): the hypothesis; each |V(Q_i)| ≤ Σ ≤ ϑn < n (`FGraph.card_le_of_sum_card_le`), IH gives
  f(Q_i) ≤ c|V(Q_i)|; then f(G) ≤ Cn + 2cϑn ≤ c(1−2ϑ)n + 2cϑn = cn.
`EG.hi` instantiates c := max(C/(1−2ϑ), N₀/2): `N₀/2 ≤ c` and `C ≤ c(1−2ϑ)` (`div_le_iff₀`) are
immediate; **`0 ≤ c` is `EG.hi_const_nonneg`**. This is the one step not in the manuscript (where
N₀, D_* > 0 make c > 0 obvious): since the Spec allows arbitrary real N₀, D_*, the case c < 0 is
excluded by applying the hypothesis to K₂ (`EG.hiK2` on `Fin 2`): C < 0 and N₀ < 0, so K₂
qualifies, Σ|V(Q_i)| ≤ 2ϑ < 1 forces every Q_i to be empty, and 1 = f(K₂) ≤ 2C < 0.
(Nonnegativity of c is used in steps (1) and (5), and C ≤ c in step (3).)

Extra: `EG.hi_simpleGraph` (conclusion for `SimpleGraph` on a `Fintype`, via `ofSimpleGraph`).

## Main-theorem interface (EG/Proof/Quot/HIMain.lean)
- `EG.mainInternal_of_hiHyp (hC : Dstar/2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1/2)
  (h : Spec.HIHyp Dstar N₀ C ϑ) : Spec.MainInternal` — **what `EG/Proof/Main.lean` should use**,
  with the constant `⌈max(C/(1−2ϑ), N₀/2)⌉₊` (real c rounded up; MainInternal wants `c : ℕ`).
- `EG.decomp_le_of_hiHyp`: the explicit form (every `SimpleGraph` on a finite `V : Type` has a
  decomposition of length ≤ ⌈c⌉₊·|V|); `EG.fnum_edges_le_ceil_of_hiHyp` (FGraph form).
- `EG.mainInternal_of_hiHyp'`: same conclusion via `EG.mainInternal_of_fnum_edges_le`
  (consistency with `EG.Lib.Found.FnumMain`).
- Fidelity check `EG.mainInternal_iff_exists_hiHyp : MainInternal ↔ ∃ D_* N₀ C ϑ, D_*/2 ≤ C ∧
  0 ≤ ϑ ∧ ϑ < 1/2 ∧ HIHyp D_* N₀ C ϑ`: the hypothesis is neither vacuous nor stronger than the
  internal main theorem (→ with k = 0 quotients).

## Deviations / open questions
- No `Defs` change and no `Lib` change; the small FGraph helpers
  (`FGraph.edges_eq_empty_of_card_eq_zero`, `FGraph.fnum_edges_eq_zero_of_card_eq_zero`,
  `FGraph.two_mul_card_edges_le`, `FGraph.noIsolated_iff_deg_ne_zero`,
  `FGraph.card_le_of_sum_card_le`) live in `EG/Proof/Quot/HI.lean`; they could move to
  `EG/Lib/Found/FGraphFnum.lean` / `Graph.lean` if other files need them.
- The hypothesis is stated for `G : FGraph V`. If s7:thmJVps ends up stated for a Mathlib
  `SimpleGraph` G on a `Fintype`, an adapter FGraph → `SimpleGraph ↥G.verts` (with `fnum_map` along
  the subtype embedding) will be needed on the producer side; not written here.
- `EG.hiK2` (K₂ on `Fin 2`) is a public `@[expose]` def in namespace `EG`; rename if it clashes
  with a later test fixture.
- Not added to `EG.lean` (root files are integrator-owned).
