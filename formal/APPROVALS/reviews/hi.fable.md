# Clean-room review — group `hi` — reviewer `fable`

Date: 2026-09-26. Model: Claude (Fable 5.1). Independent review from scratch; the earlier review
`work/p1b/hi.review1.md` was read only after my back-translation and scratch checks were complete,
and no verdict here rests on it; the other approval review (`hi.opus.md`) was not opened.
The design note `work/p1b/hi.md` was read for the module map.

**Scope.** `EG/Spec/Quot/HI.lean`: `EG.Spec.HIHyp`, `EG.Spec.HIStatement` (Theorem HI″,
manuscript [s7:thmHI]); its proof `EG.hi` in `EG/Proof/Quot/HI.lean`; the link to the internal main
theorem in `EG/Proof/Quot/HIMain.lean` (`EG.mainInternal_of_hiHyp`, `EG.mainInternal_iff_exists_hiHyp`).
Manuscript: `proofs/manuscript/s7.tex` l. 1354–1386 (statement and proof), l. 1436–1462
(s7:thmMainProof, the consumer), l. 1317–1333 (s7:thmJVps, the producer); `s1.tex` l. 66–80
(s1:thmMain), l. 321–353 (s1:convGraphs), l. 354–362 (s1:defObject), l. 364–395 (s1:factAdd),
l. 911–947 (s1:defConstants), l. 296–318 (overview of the induction).

**Method.** `#print` of both Spec constants with `pp.numericTypes`/`pp.coercions.types` to see the
elaborated term; a fully parenthesised restatement of each proved equal by `Iff.rfl` (pins the
precedence of `*`, `/`, `∑`, `∧` and every cast); an independent restatement written from the
manuscript text (degree form of "no isolated vertices", `≥` orientation, `ϑ ∈ Set.Ico 0 (1/2)`,
`let c := …`) proved equivalent to the Spec; edge cases (`n = 0`, `ϑ = 0`, `k = 0`, negative
constants, the universe) worked out by hand and checked in Lean; non-triviality witnesses; the
axiom scan; `python3 scripts/lint.py`; `lake build EG.Proof.Quot.HIMain` (up to date, 2043 jobs);
`scripts/check.sh` on all three files (source-level, `rc=0 errors=0 sorry-warnings=0` each). The
scratch file is reproduced in Appendix A; it compiles with 0 errors. No repository file was
edited; the only file written is this review.

**Verdict: APPROVE (`EG.Spec.HIHyp`, `EG.Spec.HIStatement`; link theorems in HIMain checked),
with non-blocking notes in §6.**

---

## 0. Manuscript text (s7.tex l. 1354–1365)

> **Theorem HI″ (layered quotient induction).** Let `C ≥ D_*/2` and `ϑ ∈ [0,1/2)` be constants
> with the following property. Every graph `G` without isolated vertices, with `n ≥ N₀` vertices
> and `d₁ = 2|E(G)|/n ≥ D_*`, admits finitely many simple graphs `Q₁,…,Q_k` (`k ≥ 0`) such that
> `f(G) ≤ C n + 2 ∑_{i=1}^k f(Q_i)` and `∑_{i=1}^k |V(Q_i)| ≤ ϑ n`.
> Then `f(G) ≤ c |V(G)|` for every graph `G`, where `c := max(C/(1−2ϑ), N₀/2)`.
> deps: s1:factAdd, s1:defObject.

Conventions it relies on: s1:convGraphs (a) "Graphs are finite and simple … `n := |V(G)|` … `|H| :=
|V(H)|`"; s1:defObject "`f(F)` is the least number of objects in a decomposition of `F` (so
`f(∅) = 0`); `f(H) := f(E(H))`"; s1:defConstants (ii) `N₀` an absolute constant `≥ 2^40`, (iii)
`D_*` a constant satisfying G1–G4 (in particular `D_* ≥ 2^117`).

## 1. What Lean elaborated (`#print`, numeric types shown)

```
def EG.Spec.HIHyp : ℝ → ℝ → ℝ → ℝ → Prop :=
fun Dstar N₀ C ϑ =>
  ∀ (V : Type) (G : FGraph V),
    (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) →
      N₀ ≤ (↑G.card : ℝ) →
        Dstar ≤ (2 : ℝ) * (↑G.edges.card : ℝ) / (↑G.card : ℝ) →
          ∃ k W Q,
            (↑(fnum G.edges) : ℝ) ≤ C * (↑G.card : ℝ) + (2 : ℝ) * ∑ i, (↑(fnum (Q i).edges) : ℝ) ∧
              ∑ i, (↑(Q i).card : ℝ) ≤ ϑ * (↑G.card : ℝ)
def EG.Spec.HIStatement : Prop :=
∀ (Dstar N₀ C ϑ : ℝ),
  Dstar / (2 : ℝ) ≤ C → (0 : ℝ) ≤ ϑ → ϑ < (1 / 2 : ℝ) → Spec.HIHyp Dstar N₀ C ϑ →
    ∀ (V : Type) (G : FGraph V),
      (↑(fnum G.edges) : ℝ) ≤ max (C / ((1 : ℝ) - (2 : ℝ) * ϑ)) (N₀ / (2 : ℝ)) * (↑G.card : ℝ)
```

The fully parenthesised versions `HIHypP`, `HIStatementP` of Appendix A are `Iff.rfl`-equal to
the Spec, so: `2 * |E| / n` is `(2·|E|)/n` in `ℝ`; `2 * ∑ i, f i` multiplies the whole sum; the
`∑` body stops before `∧`; `1 / 2` is the real number `0.5` (checked by `norm_num`); every
`fnum`/`card` is a `ℕ → ℝ` cast; `k : ℕ`, `W : Fin k → Type`, `Q : (i : Fin k) → FGraph (W i)`.

## 2. Back-translation of `EG.Spec.HIHyp Dstar N₀ C ϑ`

"For every type `V` (in universe 0) and every finite simple graph `G` with vertex set
`V(G) ⊆ V` and edge set `E(G)`: if every vertex of `G` lies on some edge of `G`, and `N₀ ≤ |V(G)|`,
and `D_* ≤ 2|E(G)| / |V(G)|` (real division), then there exist `k ∈ ℕ`, vertex types
`W_0,…,W_{k−1}` and finite simple graphs `Q_i` on `W_i` such that
`f(E(G)) ≤ C·|V(G)| + 2·∑_{i<k} f(E(Q_i))` and `∑_{i<k} |V(Q_i)| ≤ ϑ·|V(G)|`."

Clause by clause against the manuscript hypothesis:

| Manuscript | Lean | Check |
|---|---|---|
| "Every graph `G`" (finite, simple; s1:convGraphs (a)) | `∀ (V : Type) (G : FGraph V)`; `FGraph` = finite vertex `Finset`, finite loopless `Finset (Sym2 V)` of edges with ends in the vertex set (reviewed in group `graph`) | exact up to the universe, §4.5 |
| "without isolated vertices" | `∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e` | exact; ≡ `∀ v ∈ V(G), d_G(v) ≠ 0` (`EG.FGraph.noIsolated_iff_deg_ne_zero`, and my own `myHyp_iff` with `0 < G.deg v`) |
| "`n ≥ N₀` vertices", `n := |V(G)|` | `N₀ ≤ (G.card : ℝ)`, `G.card = G.verts.card` | exact (`≥` written as `≤`; `N₀` real, see §4.3) |
| "`d₁ = 2|E(G)|/n ≥ D_*`" | `Dstar ≤ 2 * (G.edges.card : ℝ) / (G.card : ℝ)` | exact for `n ≥ 1` (`le_div_iff₀`: ⇔ `D_* n ≤ 2|E|`); `n = 0` see §4.1 |
| "finitely many simple graphs `Q₁,…,Q_k` (`k ≥ 0`)" | `∃ (k : ℕ) (W : Fin k → Type) (Q : (i : Fin k) → FGraph (W i))` | exact: a finite family of finite simple graphs, each on its own vertex type, `k = 0` allowed (`Fin 0`, empty sums) |
| "`f(G) ≤ C n + 2 ∑ f(Q_i)`", `f(H) := f(E(H))` | `(fnum G.edges : ℝ) ≤ C * G.card + 2 * ∑ i, (fnum (Q i).edges : ℝ)` | exact; `fnum` on the loopless `edges` of an `FGraph` is literally the manuscript's `f` (`fnum`'s loop convention is inert) |
| "`∑ |V(Q_i)| ≤ ϑ n`" | `∑ i, ((Q i).card : ℝ) ≤ ϑ * G.card` | exact |

Order of quantifiers: the constants are parameters of `HIHyp` (fixed before any graph), the graph
is universally quantified, the `Q_i` existentially inside — exactly "constants with the following
property: every graph … admits …". Nothing in the Lean existential asks more of the `Q_i` than the
manuscript does (in particular not "without isolated vertices", which s7:thmJVps happens to
deliver but Theorem HI″ does not need), and nothing in the Lean premises asks less of `G`.

## 3. Back-translation of `EG.Spec.HIStatement`

"For all real `D_*, N₀, C, ϑ` with `D_*/2 ≤ C`, `0 ≤ ϑ` and `ϑ < 1/2`: if `HIHyp D_* N₀ C ϑ`,
then for every type `V` (universe 0) and every `G : FGraph V`,
`f(E(G)) ≤ max(C/(1−2ϑ), N₀/2) · |V(G)|`."

| Manuscript | Lean | Check |
|---|---|---|
| "`C ≥ D_*/2`" | `Dstar / 2 ≤ C` (real) | exact |
| "`ϑ ∈ [0,1/2)`" | `0 ≤ ϑ`, `ϑ < 1 / 2` (real `1/2`) | exact (closed at 0, open at 1/2) |
| "with the following property" | `HIHyp Dstar N₀ C ϑ →` | exact |
| "`c := max(C/(1−2ϑ), N₀/2)`" | `max (C / (1 - 2 * ϑ)) (N₀ / 2)` inline | exact; `1 − 2ϑ > 0` so no division-by-zero convention is touched |
| "`f(G) ≤ c |V(G)|` for every graph `G`" | `∀ (V : Type) (G : FGraph V), (fnum G.edges : ℝ) ≤ c * G.card` | exact up to the universe, §4.5; includes graphs with isolated vertices, `n < N₀`, `d₁ < D_*`, `n = 0` |
| "The constants `C` and `ϑ` do not depend on `c`" (non-circularity) | `c` is a closed expression in `C, ϑ, N₀` | syntactic |

My independent restatement `myHI` (Appendix A, §B) — written from the manuscript text with
`C ≥ Dstar / 2`, `ϑ ∈ Set.Ico 0 (1/2)`, `0 < G.deg v`, `≥` orientation for `n` and `d₁`, and
`let c := …` — is provably equivalent: `myHI_iff : myHI ↔ EG.Spec.HIStatement`, and
`example : myHI := myHI_iff.2 EG.hi`.

## 4. Edge cases and Lean conventions

4.1 **`n = 0`.** Lean's `x / 0 = 0` makes the third premise `D_* ≤ 0` for the vertex-free graph;
so, when `N₀ ≤ 0` and `D_* ≤ 0`, `HIHyp` also demands the property of the empty graph, a case the
manuscript never considers (its `N₀ ≥ 2^40`). This adds nothing: for `G.card = 0`, `k = 0` always
witnesses the conclusion (`fnum ∅ = 0 ≤ C·0 + 0`, `0 ≤ ϑ·0`; Appendix A §C). For `n ≥ 1` the
division form is equivalent to `D_* n ≤ 2|E|` (checked). So `HIHyp` has exactly the manuscript's
strength for every choice of constants.

4.2 **`ϑ = 0`, `k = 0`.** `ϑ = 0` is allowed, as in the manuscript's closed interval end; the
hypothesis then forces `∑|V(Q_i)| ≤ 0`, i.e. all `Q_i` vertex-free, so `HIHyp D_* N₀ C 0` is the
"high-degree case with no quotients". `k = 0` gives empty sums `= 0` (`Fin 0`). Both consistent.

4.3 **Constants generalised to arbitrary reals.** The manuscript's `N₀` is a natural number
`≥ 2^40` and `D_* ≥ 2^117`; the Spec quantifies over all real `D_*, N₀` with no sign condition,
so the manuscript's theorem is the instance `N₀ := (N₀ : ℝ)`, `D_* := D_*`. This is a
*strengthening*, hence safe for consumers, and it is proved: the only place the manuscript's proof
silently uses positivity is `c ≥ 0` (step (1): `cn ≥ c(n−1)`; step (5): `2c∑|V(Q_i)| ≤ 2cϑn`), which
the manuscript gets from `c ≥ N₀/2 > 0`. The formal proof derives `0 ≤ c` from `HIHyp` applied to
`K₂` (`EG.hi_const_nonneg`; I re-derived it by hand: `c < 0 ⇒ C < 0 ∧ N₀ < 0 ⇒ D_* ≤ 2C < 0`, so
`K₂` qualifies, `∑|V(Q_i)| ≤ 2ϑ < 1` forces all `Q_i` empty, and `1 = f(K₂) ≤ 2C < 0`). No
manuscript action is needed (the manuscript's constants are positive).

4.4 **Strictness.** `ϑ < 1/2` strict, `0 ≤ ϑ` non-strict, `D_*/2 ≤ C` non-strict, `n ≥ N₀` and
`d₁ ≥ D_*` non-strict, the two conclusions non-strict — all as written. No `ℕ` subtraction, no
`ℕ` division, no `Real.logb` occurs in the Spec; `n − 1` appears only inside the proof
(`Nat.cast_sub hn0` guarded by `0 < n`).

4.5 **Universe.** Both the hypothesis and the conclusion range over `V : Type` (universe 0), as
`EG.Spec.MainInternal` does. The manuscript's "every graph" is universe-agnostic. Direction of
the deviation: `HIHyp` demands the property only of graphs on `Type`-level vertex types (weaker
hypothesis, so the theorem is stronger), and the conclusion is stated only for `Type`-level graphs
(weaker conclusion). The latter loses nothing: every finite graph is isomorphic to one on
`Fin n : Type` and `f` is invariant under relabelling, so `EG.hi` gives the bound for `G : FGraph V`
with `V : Type u` for every `u` (Appendix A §E, proved via `fnum_edges_le_fmax`,
`exists_fnum_eq_fmax`). Producers of `HIHyp` (s7:thmJVps) will be stated for `FGraph V` with
`V : Type` or `Type*`, either of which instantiates at `Type`; the quotients live on subtypes of
`V` or on `Fin m`, all in `Type`. Consistent with the project convention.

4.6 **Family vs set of quotients.** The Lean `Q_i` are a family indexed by `Fin k` (repetitions
allowed). If the manuscript's list `Q₁,…,Q_k` is read as a set, the family form only makes the
hypothesis easier to satisfy (stronger theorem); the proof handles repetitions (each `Q_i` is
bounded by the induction hypothesis individually). Not a mismatch.

4.7 **Typeclass assumptions.** None in the Spec: `FGraph` needs no `DecidableEq`, the isolated-
vertex clause is instance-free (`v ∈ e` on `Sym2`), `fnum` is noncomputable and instance-free.
`EG.hi_simpleGraph` (Proof) adds the expected `[Fintype V] [Fintype G.edgeSet]` for the Mathlib
`SimpleGraph` form only.

## 5. Non-vacuity, proof, hygiene

* **Hypotheses satisfiable, conclusion not trivial.** The constant hypotheses are satisfiable
  (`D_* = 2, C = 1, ϑ = 1/4`). The conclusion is not trivially true: with `C = N₀ = 0` it fails for
  `K₂` (`1 ≤ 0`), so the hypothesis carries the theorem; consequently `HIHyp 0 0 0 0` is false
  (Appendix A §C), i.e. `HIHyp` is not a tautology. `HIHyp` cannot be shown satisfiable
  unconditionally because `EG.mainInternal_iff_exists_hiHyp` (author's theorem, re-checked,
  statement `MainInternal ↔ ∃ D_* N₀ C ϑ, D_*/2 ≤ C ∧ 0 ≤ ϑ ∧ ϑ < 1/2 ∧ HIHyp D_* N₀ C ϑ`) shows its
  satisfiability is *exactly* the internal main theorem (the `→` direction uses `k = 0`). This is
  the right fidelity property: the hypothesis of HI″ is neither vacuous nor stronger than what the
  Main Theorem needs.
* **The proof proves exactly the Spec.** `theorem EG.hi : Spec.HIStatement` is stated against the
  Spec constant; no auxiliary definition or weakened variant enters. `EG.hi_induction` is strong
  induction on `n = |V(G)|` over all `V : Type`, `G : FGraph V`, following the manuscript's steps:
  `n = 0` (`fnum_edges_eq_zero_of_card_eq_zero`); (1) isolated vertex via s1:factAdd(d)
  (`fnum_edges_deleteVerts_singleton_of_deg_eq_zero`, `card_deleteVerts_singleton`) and `c ≥ 0`;
  (2) `n < N₀` via `fnum_le_card` (s1:factAdd(a)) and `2|E| ≤ n(n−1)` (`two_mul_card_edges_le`);
  (3) `d₁ < D_*` via `f ≤ |E| < D_* n/2 ≤ Cn ≤ cn` (the trivial bound only, as the manuscript's
  RT-a M6 fix requires); (4) the hypothesis, `|V(Q_i)| ≤ ϑn < n` (strict because `n ≥ 1`,
  `ϑ < 1/2`), induction hypothesis on each `Q_i`; (5) `Cn + 2cϑn ≤ cn` from `C ≤ c(1−2ϑ)`. `EG.hi`
  instantiates `c := max(C/(1−2ϑ), N₀/2)` with `N₀/2 ≤ c` (`le_max_right`), `C ≤ c(1−2ϑ)`
  (`div_le_iff₀`), `0 ≤ c` (`hi_const_nonneg`).
* **Link to `MainInternal`.** `EG.mainInternal_of_hiHyp : Dstar/2 ≤ C → 0 ≤ ϑ → ϑ < 1/2 →
  Spec.HIHyp Dstar N₀ C ϑ → Spec.MainInternal` concludes literally the frozen
  `EG.Spec.MainInternal` (re-checked against its unfolded statement, Appendix A §D), with the
  natural-number constant `⌈max(C/(1−2ϑ), N₀/2)⌉₊` (`EG.decomp_le_of_hiHyp`), which is the last
  step of s7:thmMainProof ("Theorem HI″ … therefore gives `f(G) ≤ c_EG |V(G)|` for every graph
  `G`"). The `[DecidableEq V]` binder of `MainInternal` is absorbed (inert). The adapter
  `EG.hiHyp_of_fintype_index` (any `Fintype ι` index set → `Fin k`) matches the producer's
  round-indexed quotients `Q_3,…,Q_R`.
* **Axioms / hygiene.** `lake env lean --run scripts/Axioms.lean --prefix EG EG.Spec.Quot.HI
  EG.Proof.Quot.HI EG.Proof.Quot.HIMain`: `inspected 559 constants under [EG]; 0 use sorryAx;
  0 violations`. `#print axioms` of `EG.hi`, `EG.hi_const_nonneg`, `EG.hi_simpleGraph`,
  `EG.hiHyp_of_fintype_index`, `EG.decomp_le_of_hiHyp`, `EG.mainInternal_of_hiHyp`,
  `EG.mainInternal_iff_exists_hiHyp`: `[propext, Classical.choice, Quot.sound]`.
  `python3 scripts/lint.py`: `0 findings`. `lake build EG.Proof.Quot.HIMain`: up to date.
  `scripts/check.sh` on each of the three files: `rc=0 errors=0 sorry-warnings=0`. Module headers
  as required (`@[expose] public section` in Spec, `public section` in Proof). The Spec imports
  only `EG.Defs.*` and Mathlib (no `Lib`), so its lock closure is Defs-only. All three modules are
  in `EG.lean`.

## 6. Notes (non-blocking)

1. The docstring of `HIHyp` claims "`G.edges` is loopless, so the loop convention of `fnum` plays
   no role" and "no sign condition on `D_*` or `N₀` is assumed" — both verified (§2, §4.3).
2. General `FGraph` helpers (`FGraph.edges_eq_empty_of_card_eq_zero`,
   `FGraph.fnum_edges_eq_zero_of_card_eq_zero`, `FGraph.two_mul_card_edges_le`,
   `FGraph.noIsolated_iff_deg_ne_zero`, `FGraph.card_le_of_sum_card_le`) and the fixture
   `EG.hiK2` are public declarations in shared namespaces inside a `Proof` file. No clash exists
   today (grepped `EG/`, `EGTest/`, `EGCheck/`); moving the helpers to `EG/Lib/Found/` at
   integration time would avoid a future one. Cosmetic.
3. Producer interface: `HIHyp` is `FGraph`-based on `V : Type`. If s7:thmJVps is later stated for
   a Mathlib `SimpleGraph` on a `Fintype`, an adapter is needed on the producer side (already
   flagged in `work/p1b/hi.md`). Not a defect of the Spec.
4. The generalisation to arbitrary real constants makes the formal theorem strictly stronger than
   the manuscript's and costs one extra lemma (`hi_const_nonneg`). No T0 entry is needed: the
   manuscript's wording is correct for its positive constants, and the Lean statement covers it.

---

## Appendix A. Scratch file (compiles with 0 errors; `lake env lean` under `formal/`)

```lean
import EG.Proof.Quot.HIMain

open EG

section Print
set_option pp.numericTypes true
set_option pp.coercions.types true
#print EG.Spec.HIHyp
#print EG.Spec.HIStatement
end Print

#print axioms EG.hi
#print axioms EG.mainInternal_of_hiHyp
#print axioms EG.mainInternal_iff_exists_hiHyp
#print axioms EG.hi_simpleGraph
#print axioms EG.hiHyp_of_fintype_index
#print axioms EG.decomp_le_of_hiHyp
#print axioms EG.hi_const_nonneg

/-! ## A. Fully parenthesised restatement: pins the parse. -/

def HIHypP (Dstar N₀ C ϑ : ℝ) : Prop :=
  ∀ (V : Type) (G : EG.FGraph V),
    (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) →
    (N₀ ≤ ((G.card : ℕ) : ℝ)) →
    (Dstar ≤ (((2 : ℝ) * ((G.edges.card : ℕ) : ℝ)) / ((G.card : ℕ) : ℝ))) →
    ∃ (k : ℕ) (W : Fin k → Type) (Q : (i : Fin k) → EG.FGraph (W i)),
      ((((EG.fnum G.edges : ℕ) : ℝ)) ≤
          ((C * ((G.card : ℕ) : ℝ)) +
            ((2 : ℝ) * (Finset.univ.sum (fun i : Fin k => ((EG.fnum (Q i).edges : ℕ) : ℝ)))))) ∧
      ((Finset.univ.sum (fun i : Fin k => (((Q i).card : ℕ) : ℝ))) ≤ (ϑ * ((G.card : ℕ) : ℝ)))

example (Dstar N₀ C ϑ : ℝ) : HIHypP Dstar N₀ C ϑ ↔ EG.Spec.HIHyp Dstar N₀ C ϑ := Iff.rfl

def HIStatementP : Prop :=
  ∀ (Dstar N₀ C ϑ : ℝ),
    (Dstar / (2 : ℝ) ≤ C) → ((0 : ℝ) ≤ ϑ) → (ϑ < ((1 : ℝ) / (2 : ℝ))) →
    EG.Spec.HIHyp Dstar N₀ C ϑ →
    ∀ (V : Type) (G : EG.FGraph V),
      (((EG.fnum G.edges : ℕ) : ℝ)) ≤
        ((max (C / ((1 : ℝ) - ((2 : ℝ) * ϑ))) (N₀ / (2 : ℝ))) * ((G.card : ℕ) : ℝ))

example : HIStatementP ↔ EG.Spec.HIStatement := Iff.rfl

example : ((1 : ℝ) / 2) = 0.5 := by norm_num
example (a b : ℝ) : 2 * a / b = (2 * a) / b := rfl

/-! ## B. Independent restatement from the manuscript text. -/

def myHyp (Dstar N₀ C ϑ : ℝ) : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : FGraph V),
    (∀ v ∈ G.verts, 0 < G.deg v) →
    (G.card : ℝ) ≥ N₀ →
    2 * (G.edges.card : ℝ) / (G.card : ℝ) ≥ Dstar →
    ∃ (k : ℕ) (W : Fin k → Type) (Q : ∀ i, FGraph (W i)),
      (fnum G.edges : ℝ) ≤ C * G.card + 2 * ∑ i, (fnum (Q i).edges : ℝ) ∧
      ∑ i, ((Q i).card : ℝ) ≤ ϑ * G.card

def myHI : Prop :=
  ∀ (Dstar N₀ C ϑ : ℝ), C ≥ Dstar / 2 → ϑ ∈ Set.Ico (0 : ℝ) (1 / 2) → myHyp Dstar N₀ C ϑ →
    let c := max (C / (1 - 2 * ϑ)) (N₀ / 2)
    ∀ (V : Type) (G : FGraph V), (fnum G.edges : ℝ) ≤ c * G.card

theorem myHyp_iff (Dstar N₀ C ϑ : ℝ) : myHyp Dstar N₀ C ϑ ↔ Spec.HIHyp Dstar N₀ C ϑ := by
  constructor
  · intro h V G hiso hN hD
    classical
    refine h V G ?_ hN hD
    intro v hv
    obtain ⟨e, he, hve⟩ := hiso v hv
    rcases Nat.eq_zero_or_pos (G.deg v) with h0 | h0
    · exact absurd hve (G.deg_eq_zero_iff.1 h0 e he)
    · exact h0
  · intro h V _ G hiso hN hD
    refine h V G ?_ hN hD
    intro v hv
    by_contra hne
    push Not at hne
    exact absurd (G.deg_eq_zero_iff.2 hne) (Nat.pos_iff_ne_zero.1 (hiso v hv))

theorem myHI_iff : myHI ↔ Spec.HIStatement := by
  constructor
  · intro h Dstar N₀ C ϑ hC hϑ0 hϑ hh V G
    exact h Dstar N₀ C ϑ hC ⟨hϑ0, hϑ⟩ ((myHyp_iff _ _ _ _).2 hh) V G
  · intro h Dstar N₀ C ϑ hC hϑ hh
    intro c V G
    exact h Dstar N₀ C ϑ hC hϑ.1 hϑ.2 ((myHyp_iff _ _ _ _).1 hh) V G

example : myHI := myHI_iff.2 EG.hi

/-! ## C. Non-triviality. -/

example : ¬ ∀ (V : Type) (G : FGraph V),
    (fnum G.edges : ℝ) ≤ max ((0 : ℝ) / (1 - 2 * 0)) (0 / 2) * G.card := by
  intro h
  have := h (Fin 2) hiK2
  rw [hiK2_fnum, hiK2_card] at this
  norm_num at this

example : ¬ Spec.HIHyp 0 0 0 0 := by
  intro h
  have := EG.hi 0 0 0 0 (by norm_num) le_rfl (by norm_num) h (Fin 2) hiK2
  rw [hiK2_fnum, hiK2_card] at this
  norm_num at this

example (Dstar N₀ C ϑ : ℝ) (V : Type) (G : FGraph V) (h0 : G.card = 0) :
    ∃ (k : ℕ) (W : Fin k → Type) (Q : (i : Fin k) → FGraph (W i)),
      (fnum G.edges : ℝ) ≤ C * G.card + 2 * ∑ i, (fnum (Q i).edges : ℝ) ∧
      ∑ i, ((Q i).card : ℝ) ≤ ϑ * G.card := by
  have h0' : ((G.card : ℕ) : ℝ) = 0 := by exact_mod_cast h0
  refine ⟨0, fun _ => PEmpty, fun i => i.elim0, ?_, ?_⟩
  · rw [G.fnum_edges_eq_zero_of_card_eq_zero h0, h0']; simp
  · rw [h0']; simp

example : (2 * ((0 : ℕ) : ℝ)) / ((0 : ℕ) : ℝ) = 0 := by simp

example (D E : ℝ) (n : ℕ) (hn : 0 < n) : D ≤ 2 * E / (n : ℝ) ↔ D * n ≤ 2 * E := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ this]

example : (2 : ℝ) / 2 ≤ 1 ∧ (0 : ℝ) ≤ 1 / 4 ∧ (1 / 4 : ℝ) < 1 / 2 := by norm_num

example (C N₀ ϑ : ℝ) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2) (hC : 0 ≤ C) :
    N₀ / 2 ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) ∧ C ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) := by
  refine ⟨le_max_right _ _, le_trans ?_ (le_max_left _ _)⟩
  have hpos : 0 < 1 - 2 * ϑ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

/-! ## D. The HIMain link concludes literally `EG.Spec.MainInternal`. -/

example {Dstar N₀ C ϑ : ℝ} (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) :
    ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V :=
  EG.mainInternal_of_hiHyp hC hϑ0 hϑ h

example {Dstar N₀ C ϑ : ℝ} (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) (V : Type) [Fintype V] (G : SimpleGraph V) :
    ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧
      D.length ≤ ⌈max (C / (1 - 2 * ϑ)) (N₀ / 2)⌉₊ * Fintype.card V :=
  EG.decomp_le_of_hiHyp hC hϑ0 hϑ h V G

/-! ## E. The universe restriction `V : Type` in the conclusion is harmless. -/

universe u
example (Dstar N₀ C ϑ : ℝ) (hC : Dstar / 2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1 / 2)
    (h : Spec.HIHyp Dstar N₀ C ϑ) (V : Type u) (G : FGraph V) :
    (fnum G.edges : ℝ) ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * G.card := by
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax G.card
  have h1 : fnum G.edges ≤ fmax G.card := G.fnum_edges_le_fmax
  have h2 := hi Dstar N₀ C ϑ hC hϑ0 hϑ h (Fin G.card) (FGraph.ofSimpleGraph H)
  simp only [FGraph.ofSimpleGraph, FGraph.card_def] at h2
  have hc : (((Finset.univ : Finset (Fin G.card)).card : ℕ) : ℝ) = G.card := by
    rw [Finset.card_univ, Fintype.card_fin]
  calc (fnum G.edges : ℝ) ≤ fmax G.card := by exact_mod_cast h1
    _ = fnum H.edgeFinset := by rw [hH]
    _ ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * ((Finset.univ : Finset (Fin G.card)).card : ℝ) := h2
    _ = _ := by rw [hc]
```

Output of the `#print axioms` lines: every listed constant `depends on axioms: [propext,
Classical.choice, Quot.sound]`.
