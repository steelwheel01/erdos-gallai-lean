# Clean-room review, round 1: task [lemma25] (`EG.bmLemma25 : EG.Spec.BMLemma25Statement`)

Reviewer: clean-room agent (no Lean files edited). Date 2026-09-26.
Files reviewed: `EG/Spec/Ext/BMLemma25.lean` (locked, unchanged), `EG/Proof/Ext/BMLemma25.lean`
(237 l.), `EG/Lib/Ext/DFS.lean` (215 l.), `EG/Lib/Ext/DFSCycle.lean` (293 l.), design note
`work/ext/lemma25.md`, manuscript `proofs/manuscript/s1.tex` l.1035–1057 and l.810–824.

**Verdict: approve.** The Spec is faithful, non-vacuous, and proved with the constant 18
exactly, with no `sorry` and only the standard axioms.

## 1. Fidelity of the Spec to the manuscript
Manuscript v6, s1:citLem25: "Let ε ≥ 2^{-5} and m ≥ max(2, 2^{30}/ε²) ... Every m-vertex
(ε,0)-expander contains a cycle of length at least ε²m/(18 log⁴m)."
* `2^(-5:ℤ) ≤ ε`, `2^30/ε² ≤ G.card`, `2 ≤ G.card`: this is exactly `m ≥ max(2, 2^30/ε²)`
  (the hypothesis `m ≥ 2` is now in the manuscript text too, with the reason given there).
* `G.IsExpander ε 0` is Def. 11 with `s = 0` (`|F| ≤ 0`, so `F = ∅`), log₂, `n = G.card`.
* Cycle: `(Obj.cycle c).WF` (nodup, ≥ 3 vertices) and every edge of `cycleEdges c`
  (including the closing edge) in `E(G)`; length `c.length` = number of edges. Correct.
* Bound: `ε²·m/(18·(logb 2 m)^4) ≤ c.length` in ℝ, constant 18, log₂. Correct; no Lean
  division-by-zero issue since `m ≥ 2` gives `log₂ m > 0`.
* `bmLemma25_literal_false` confirms the added `2 ≤ m` is needed (m = 1, ε = 2^15), T0-cap-1.
* The Spec is in universe `u` and the downstream use `EG/Proof/HB/Cap.lean:189` instantiates
  it at `ε = 2^{-5}`; signature compatible.

## 2. Non-vacuity (scratch test `/tmp/lemma25rev/Test.lean`, compiles, no sorry)
* `Kc_expander`: the complete graph on `Fin m` (`m ≥ 2`) is a `(log²m/2, 0)`-expander.
* Applying `EG.bmLemma25` to `K_{2^20}` with `ε = log²(2^20)/2 = 200` discharges all
  hypotheses and yields a cycle of length `≥ 2^20/72`: the hypotheses are jointly satisfiable
  and the conclusion is a nontrivial long cycle. (EGTest/Cap.lean also has a satisfiability
  test with `K_{2^40}`, `ε = 2^-5`.)

## 3. The proof proves exactly the Spec
`theorem bmLemma25 : EG.Spec.BMLemma25Statement.{u}`: the type is the locked Spec itself.
Mathematics checked by hand:
* DFS invariant (`DFS.Inv`): partition of V(G) into U, R, P; P a path; no U–R edge. The three
  steps (restart / extend / backtrack) preserve it and lower `|U| - |R|` by one; induction gives
  a state with `|U| = |R|`; `Nbr(U) ⊆ V(P)`. Restarts replace BM's use of connectivity (sound).
* Numerics: `β = ε/L² ≤ 1` (expansion of a set of size ⌈n/2⌉; `3⌈n/2⌉ ≤ 2n` for n ≥ 2);
  `24L⁴ ≤ ε²n` (case split at 2^40, monotonicity of y/log⁴y), so `a = ε²n/(18L⁴) ≥ 4/3`;
  `|P| ≥ βn/3` at the balanced moment (two cases 3u ≥ n / 3u < n); `k = ⌈a⌉`,
  `x = ⌊(p-k)/2⌋`; `βx > k` iff `6a > 3k + 1`, true since `3k + 1 < 3a + 4 ≤ 6a`.
* X/Y/Z step: `X*` = X plus vertices reachable from X through `V(G) \ V(P)`; an edge X*–Z
  closes a cycle through all of Y (length ≥ k + 2); otherwise `Nbr(X*) ⊆ Y` and
  `Nbr(V \ (X* ∪ Y)) ⊆ Y`, one of the two disjoint sets has size ≤ n/2 and ≥ x, and expansion
  gives `k < |Nbr| ≤ k`. Correct; replaces BM's shortest-path formulation without changing the
  statement.
* **Constant: 18 is achieved exactly** (the proof gives length `≥ ⌈ε²m/(18 log⁴ m)⌉ + 2`).
  So the L25-CONST18 risk (s2:lemCap margin 65534 ≤ 65536) is resolved.
* Hypothesis `ε ≥ 2^{-5}` is used only via `ε > 0` and `ε² ≥ 2^{-10}` (in `24L⁴ ≤ ε²n`).

## 4. Hygiene
* `scripts/check.sh` on the three files: rc=0, errors=0, sorry-warnings=0 (no warnings shown).
* `lake build EG.Proof.Ext.BMLemma25`: success.
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Ext.BMLemma25 EG.Lib.Ext.DFS
  EG.Lib.Ext.DFSCycle`: 582 constants, 0 sorryAx, 0 meta-scan hits, 0 violations.
  `#print axioms EG.bmLemma25`: propext, Classical.choice, Quot.sound.
* `python3 scripts/lint.py`: 0 findings. `scripts/lock.py check`: 0 violations (Spec unchanged).
* Files are modules with `public section`; `insideGraph` is a plain `def` (not needed
  downstream); file sizes well below 1500 lines.

## 5. Issues (none blocking)
1. cosmetic: the module docstring of the locked `EG/Spec/Ext/BMLemma25.lean` says the proof is
   "at present with `sorry`" and quotes the pre-v6 wording "`m ≥ 2^{30}/ε²`" as the manuscript
   text (v6 now reads `m ≥ max(2, 2^{30}/ε²)`). Integrator action (locked file).
2. cosmetic: `EG/Proof/HB/Cap.lean` lines 15 and 181 still say `EG.bmLemma25` is "currently
   `sorry`". Update when Cap is next edited.
3. cosmetic: `EG.DFS.Inv.card_nbrSet_le` has no docstring; the design note says `k ≥ 2` where
   the code proves and uses only `1 ≤ k` (harmless).
