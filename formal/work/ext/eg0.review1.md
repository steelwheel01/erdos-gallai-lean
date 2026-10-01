# Clean-room review, round 1: Fact EG0 (s1:factEG0), task [eg0]

Reviewer: clean-room agent, 2026-09-26. Files reviewed (not edited):
`EG/Spec/Found/EG0.lean` (statements), `EG/Proof/Found/EG0.lean` (523 lines, proofs).
Manuscript: `proofs/manuscript/s1.tex` l. 635-708 (statement and proof), uses in s4.tex
l. 371, 595, 790 and s5.tex l. 400; CONVENTIONS.md (T0-eg0-loop); blueprint_s1.md rows
EG0-UNREVIEWED, EG0-LOOP, EG0-ISEDGE, EG0-LONGESTPATH, EG0-REAL.

**Verdict: APPROVE.** One minor process issue (missing author notes), no issue with the Lean.

## 1. Fidelity of the Spec

Manuscript (s1.tex l. 636-645):
> (a) Every graph H with h ≥ 1 vertices has a decomposition into at most h(log h+1) objects,
> at most h−1 of which are single edges. In particular f(H) ≤ h(log h+1).
> (b) Let N>1 and L := log N, and let α and β be real numbers with 0 ≤ α ≤ N, β>0 and 4β ≤ L.
> If F is the edge set of a (simple) graph, so that F has no loops and no parallel edges, and
> every edge of F has both ends in a set W with |W| ≤ βα/L, then F has a decomposition into at
> most βα objects, at most |W| of which are single edges.

| Manuscript | Spec | OK |
|---|---|---|
| graph H, h = \|V(H)\| ≥ 1 | `H : EG.FGraph V`, `1 ≤ H.card` (`card = verts.card`) | yes |
| log = log₂ (s1:convGraphs(b)) | `Real.logb 2` | yes |
| decomposition of E(H) | `EG.IsDecomp ↑H.edges D` (WF objects, disjoint, exact cover) | yes |
| ≤ h(log h + 1) objects | `(D.length : ℝ) ≤ H.card * (logb 2 H.card + 1)` | yes |
| ≤ h−1 single edges | `D.countP (· matches .edge _) ≤ H.card - 1` (ℕ-subtraction harmless, h ≥ 1) | yes |
| f(H) ≤ h(log h+1) | `FactEG0aFnumStatement`, `fnum H.edges` (loopless, per CONVENTIONS) | yes |
| N > 1, L = log N | `1 < N`, `Real.logb 2 N` | yes |
| 0 ≤ α ≤ N, β > 0, 4β ≤ L | `0 ≤ α`, `α ≤ N`, `0 < β`, `4 * β ≤ logb 2 N` | yes |
| F edge set of a simple graph | `F : Finset (Sym2 V)`, `∀ e ∈ F, ¬ e.IsDiag` (T0-eg0-loop; Finset excludes parallels) | yes |
| both ends of every edge in W | `W : Finset V`, `∀ e ∈ F, ∀ v ∈ e, v ∈ W` | yes |
| \|W\| ≤ βα/L | `(W.card : ℝ) ≤ β * α / logb 2 N` | yes |
| ≤ βα objects, ≤ \|W\| single edges | `(D.length : ℝ) ≤ β * α`, `countP ≤ W.card` | yes |

* No hypothesis is added beyond the manuscript except the recorded T0 decision (no loops), which
  the v6 text itself states ("so that F has no loops"). The loop hypothesis is necessary:
  `{s(0,0)}` has no decomposition at all (checked in Lean, see §2).
* The single-edge counts (load-bearing for s4:thmVXp, blueprint EG0-ISEDGE) are included; the
  match is inlined, so the Spec depends only on `EG/Defs` (as the blueprint note suggests).
* W is an arbitrary finite set, not tied to a vertex set, as in the manuscript; all three s4
  consumers (β = 48, 64, 13; α = |P|, |P_ℓ|, N) instantiate the Spec directly.
* Universe-polymorphic (`V : Type u`), arbitrary `DecidableEq` instance: no restriction.
* Edge cases: h = 1 (bound 1, no edges, D = []); W = ∅ forces F = ∅ and the bound βα ≥ 0; α = 0
  forces W = ∅. All consistent with the manuscript.

## 2. Non-vacuity (scratch file /tmp/eg0rev/T.lean, compiled with `lake env lean`)

* (a) applied to the triangle on `Fin 3` (hypothesis `1 ≤ card` discharged by `decide`); the
  conclusion yields a decomposition with ≤ 2 single edges.
* (b) applied to the triangle with N = 256 (L = 8), α = 256, β = 2, W = univ (3 ≤ 64): every
  hypothesis discharged, conclusion obtained.
* A loop-only set `{s(0,0)}` on `Fin 1` has no `IsDecomp` (so the no-loop hypothesis of (b) is
  needed, confirming T0-eg0-loop).
* `#print axioms` for `EG.factEG0a`, `EG.factEG0aFnum`, `EG.factEG0b`:
  `[propext, Classical.choice, Quot.sound]`.

## 3. The proof proves exactly the Spec

`theorem factEG0a : EG.Spec.FactEG0aStatement.{u}`, `factEG0aFnum : FactEG0aFnumStatement.{u}`,
`factEG0b : FactEG0bStatement.{u}` — the locked Prop constants themselves, no restatement.
Structure follows s1.tex: `exists_core` (peeling vertices of degree ≤ d−1, with
`(|S|−1)(d−1) < e(H[S])`), `exists_long_cycle_of_deg` (longest path, neighbour of v₀ of largest
index), `exists_cycle_of_card_le` (the Claim, in the strict form m' < h·ℓ), `block` /
`decomp_of_card_lt` (removal of long cycles; h removals halve the edge count) and
`exists_decomp_log` (the relative form for an edge set with ends in W, |W| = h ≥ 1); (b) is the
manuscript's reduction h ≤ N/4 ⇒ log h ≤ L−2. Harmless deviations from the text, all documented
in docstrings: d = max(2, ⌊m'/h⌋) instead of the ceiling (gives the same strict bound);
(1−1/h)^h ≤ e⁻¹ ≤ 1/2 instead of the binomial argument; |E| < C(h+1,2) ≤ 2^⌊log h⌋·h (via
E ⊊ W.sym2) instead of m ≤ h²/2. None changes a statement.

## 4. Hygiene

* `lake build EG.Proof.Found.EG0`: success (up to date).
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Found.EG0 EG.Spec.Found.EG0`:
  557 constants, 0 use sorryAx, 0 meta-scan hits, 0 violations.
* `python3 scripts/lint.py`: 0 findings. No `sorry`, no `set_option` in either file.
* Module headers correct: Spec `@[expose] public section`, imports `EG.Defs.*` and Mathlib only;
  Proof `public section`. Every formalizing declaration carries a `[s1:factEG0]` docstring.

## 5. Issues

1. (minor, process) The author notes `formal/work/ext/eg0.md` named in the task do not exist
   (the directory has bbd/haxell/lemma25 notes only). Fix: the author writes eg0.md (encoding
   decisions, T0-eg0-loop, the proof deviations of §3).
2. (note, integrator) `EG.Spec.Found.EG0` is not yet in LOCK.json; the blueprint row status
   "risk (EG0-UNREVIEWED)" can be updated after this review.
