# Clean-room review, round 1: [hi] Theorem HI″ (s7:thmHI)

Reviewer: clean-room reviewer (round 1). Files reviewed (from `work/p1b/hi.md`):
`EG/Spec/Quot/HI.lean`, `EG/Proof/Quot/HI.lean`, `EG/Proof/Quot/HIMain.lean`.
Manuscript: `proofs/manuscript/s7.tex` l. 1354–1386 (statement and proof), l. 1436–1460
(s7:thmMainProof, the consumer), `s1.tex` l. 66–80 (s1:thmMain), l. 915 ff. (s1:defConstants).
No Lean file was edited.

**Verdict: APPROVE.** Only cosmetic remarks.

## 1. Fidelity (back-translation)

Manuscript [s7:thmHI]: "Let C ≥ D_*/2 and ϑ ∈ [0,1/2) be constants with the following property.
Every graph G without isolated vertices, with n ≥ N₀ vertices and d₁ = 2|E(G)|/n ≥ D_*, admits
finitely many simple graphs Q₁,…,Q_k (k ≥ 0) such that f(G) ≤ C n + 2 Σ_{i=1}^k f(Q_i) and
Σ_{i=1}^k |V(Q_i)| ≤ ϑ n. Then f(G) ≤ c |V(G)| for every graph G, where
c := max(C/(1−2ϑ), N₀/2)."

Back-translation of `EG.Spec.HIStatement` (with `EG.Spec.HIHyp` inlined):
"For all real numbers D_*, N₀, C, ϑ with D_*/2 ≤ C, 0 ≤ ϑ and ϑ < 1/2 the following holds.
Suppose that for every type V and every finite simple graph G on a finite vertex set
V(G) ⊆ V such that every vertex of G lies on an edge of G, N₀ ≤ |V(G)|, and
D_* ≤ 2|E(G)|/|V(G)| (real division), there are a natural number k and finite simple graphs
Q_0,…,Q_{k−1}, each on its own vertex type, with f(E(G)) ≤ C·|V(G)| + 2·Σ_i f(E(Q_i)) and
Σ_i |V(Q_i)| ≤ ϑ·|V(G)|. Then every finite simple graph G (on any V : Type) satisfies
f(E(G)) ≤ max(C/(1−2ϑ), N₀/2)·|V(G)|."

Comparison, item by item:
| Manuscript | Formal | OK |
|---|---|---|
| C ≥ D_*/2 | `Dstar / 2 ≤ C` | yes |
| ϑ ∈ [0,1/2) | `0 ≤ ϑ`, `ϑ < 1 / 2` | yes |
| C, ϑ constants (fixed before G) | quantified before `∀ V G` inside `HIHyp` | yes |
| "graph" (s1:convGraphs(a): finite, simple) | `G : EG.FGraph V`, `V : Type` (same universe as `Spec.MainInternal`) | yes |
| without isolated vertices | `∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e` (≡ `deg v ≠ 0`, proved) | yes |
| n ≥ N₀ | `N₀ ≤ (G.card : ℝ)` | yes |
| d₁ = 2\|E(G)\|/n ≥ D_* | `Dstar ≤ 2 * \|E\| / n` in ℝ | yes (n = 0: see below) |
| finitely many simple graphs Q₁…Q_k, k ≥ 0 | `∃ k : ℕ, W : Fin k → Type, Q i : FGraph (W i)` | yes |
| f(G) ≤ Cn + 2Σ f(Q_i) | `fnum G.edges ≤ C * n + 2 * ∑ i, fnum (Q i).edges` (ℝ) | yes |
| Σ\|V(Q_i)\| ≤ ϑ n | `∑ i, (Q i).card ≤ ϑ * n` (ℝ) | yes |
| c := max(C/(1−2ϑ), N₀/2) | `max (C / (1 - 2 * ϑ)) (N₀ / 2)` inline | yes |
| f(G) ≤ c\|V(G)\| for every graph G | `∀ V G, fnum G.edges ≤ c * G.card` | yes |

Notes.
* **Generalized constants.** D_*, N₀ are arbitrary reals (manuscript: fixed constants,
  N₀ ≥ 2^40 an integer, D_* ≥ 2^117). Universal quantification only strengthens the theorem;
  the manuscript's instance is a special case (N₀ via cast). The price is one extra proof step,
  `EG.hi_const_nonneg` (c ≥ 0 via the hypothesis applied to K₂), which I checked by hand: if
  c < 0 then C < 0, N₀ < 0, D_* ≤ 2C < 0, so K₂ qualifies; Σ|V(Q_i)| ≤ 2ϑ < 1 forces all Q_i
  empty; 1 = f(K₂) ≤ 2C < 0. Correct.
* **n = 0.** The hypothesis additionally covers the empty graph when N₀ ≤ 0 and D_* ≤ 0
  (Lean's x/0 = 0). This does not change its strength: for the empty graph k = 0 always
  works (checked in the scratch file). Graphs with n ≥ 1 are treated exactly as in the
  manuscript.
* **Freedom of the Q_i.** `W i : Type` arbitrary only makes the existential easier to meet
  (stronger theorem), and keeps the Q_i in the universe of G, as the induction needs.
* **f.** `fnum` of `FGraph.edges` (loopless), so the loop convention of `fnum` plays no role.
* **Corollary (HIMain).** `EG.mainInternal_of_hiHyp : Dstar/2 ≤ C → 0 ≤ ϑ → ϑ < 1/2 →
  Spec.HIHyp … → Spec.MainInternal` concludes exactly the integrator-owned `EG.Spec.MainInternal`
  (checked with `#check`/`example` against `EG.Spec.MainInternal`), with c rounded up to
  `⌈c⌉₊`. This is the last step of s7:thmMainProof ("Theorem HI″ … gives f(G) ≤ c_EG|V(G)| for
  every graph G").

**Independent restatement.** In `/tmp/…/scratchpad/HIReview.lean` I wrote my own version
`myHI` from the manuscript text (degree form of "no isolated vertices", `≥` orientation,
`ϑ ∈ Set.Ico 0 (1/2)`, `let c := …`) and proved `myHI ↔ EG.Spec.HIStatement` (and
`myHyp ↔ EG.Spec.HIHyp`); `example : myHI := myHI_iff.2 EG.hi` compiles.

## 2. Vacuity

* `HIStatement` is not trivially provable: its conclusion for any fixed constants is a linear
  bound on f, and `EG.mainInternal_iff_exists_hiHyp` (proved by the author, re-checked) shows
  `MainInternal ↔ ∃ D_* N₀ C ϑ, D_*/2 ≤ C ∧ 0 ≤ ϑ < 1/2 ∧ HIHyp …`. So `HIHyp` is consistent
  relative to the internal main theorem and cannot be refuted from the constants; it is also
  not stronger than needed (k = 0 recovers MainInternal).
* Scratch check: `HIHyp D_* N₀ C 0 ↔ (∀ G without isolated vertices, n ≥ N₀, d₁ ≥ D_*,
  f(G) ≤ Cn)` — with ϑ = 0 the hypothesis is exactly the "high-degree case" of the conjecture,
  as expected; no hidden contradiction.
* The hypotheses on the constants (`D_*/2 ≤ C`, `0 ≤ ϑ < 1/2`) are satisfiable.

## 3. Hygiene

* `python3 scripts/lint.py`: `lint (development): 0 findings`.
* `lake env lean --run scripts/Axioms.lean --prefix EG --no-sorry EG.Spec.Quot.HI
  EG.Proof.Quot.HI EG.Proof.Quot.HIMain`: `inspected 559 constants under [EG]; 0 use sorryAx;
  0 violations`.
* `#print axioms` for `EG.hi`, `EG.mainInternal_of_hiHyp`, `EG.mainInternal_iff_exists_hiHyp`:
  `[propext, Classical.choice, Quot.sound]`.
* `lake build --no-build EG.Proof.Quot.HIMain`: all targets up to date (oleans match sources).
* `scripts/check.sh` on the three files: rc=0, 0 errors, 0 sorry warnings each.
* Module headers follow AGENTS.md (`@[expose] public section` in Spec, `public section` in
  Proof). No `Defs`/`Lib`/root file changed.

## 4. The proof proves the Spec

`theorem EG.hi : Spec.HIStatement` is stated directly against the Spec def; no auxiliary
definition enters the statement. `hi_induction` (strong induction on n = |V(G)| over all
`V : Type`, `G : FGraph V`) follows the manuscript's steps (1)–(5): n = 0; isolated vertex via
s1:factAdd(d) (`fnum_edges_deleteVerts_singleton_of_deg_eq_zero`); n < N₀ via
f ≤ |E| ≤ n(n−1)/2; d₁ < D_* via f ≤ |E| < D_* n/2 ≤ Cn ≤ cn; otherwise the hypothesis, each
|V(Q_i)| ≤ ϑn < n (strict, since n ≥ 1 and ϑ < 1/2), IH on each Q_i, and the final
Cn + 2cϑn ≤ cn. `hi` instantiates c := max(C/(1−2ϑ), N₀/2) with `N₀/2 ≤ c`,
`C ≤ c(1−2ϑ)` (`div_le_iff₀`), `0 ≤ c` (`hi_const_nonneg`). No weakening.

## 5. Remarks (cosmetic)

1. General FGraph helpers (`FGraph.edges_eq_empty_of_card_eq_zero`,
   `FGraph.fnum_edges_eq_zero_of_card_eq_zero`, `FGraph.two_mul_card_edges_le`,
   `FGraph.noIsolated_iff_deg_ne_zero`, `FGraph.card_le_of_sum_card_le`) and the fixture
   `EG.hiK2` are declared in shared namespaces inside a `Proof` file. No clash today (grepped),
   but a later `Lib` lemma of the same name would clash when both are imported. Suggest moving
   the helpers to `EG/Lib/Found/Graph.lean` / `FGraphFnum.lean` and renaming `hiK2` (e.g. into
   a `private`/`EG.HI` namespace) at integration time.
2. Producer interface: `HIHyp` is `FGraph`-based. If s7:thmJVps ends up stated for a Mathlib
   `SimpleGraph`, an adapter will be needed on the producer side (already flagged by the author
   in `hi.md`). Not a defect of this task.
