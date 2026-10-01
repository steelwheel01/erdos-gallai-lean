# Clean-room review, round 2: task [cap]

Reviewer: clean-room agent (round 2). I did not edit any Lean file. My scratch checks are in
`CapReview2.lean` in the session scratchpad
(`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/`), outside
the repo. It imports `EG.Proof.HB.Cap` and `EG.Lib.Found.Graph` and compiles with no errors.

**Verdict: APPROVE.** I found no fidelity, vacuity, hygiene or soundness defects. Every round-1
item is handled. Two orchestrator actions from round 1 are still open: the central T0 entry, and
the roots and `LOCK.json`. The author could not do either within the task's scope.

Files reviewed (current working tree, after fix round 1):
- `EG/Spec/Ext/BMLemma25.lean`
- `EG/Proof/Ext/BMLemma25.lean`
- `EG/Spec/HB/Cap.lean`
- `EG/Proof/HB/Cap.lean`
- `EG/Lib/Found/LogMono.lean`
- `EGTest/Cap.lean`
- `work/p1b/cap.md` and `work/p1b/cap.review1.md`

Foundations read:
- `EG/Defs/Objects.lean`: `cycleEdges`, `Obj.WF`
- `EG/Defs/Graph.lean`: `FGraph`, `card`, `nbrSet`, `deleteEdges`
- `EG/Defs/Expander.lean`: `IsExpander`

Manuscript passages compared:
- s1.tex:716–734: s1:citLem25
- s1.tex:321–330: s1:convGraphs (a), (b)
- s2.tex:622–677: s2:lemCap, with its statement, remark and proof
- the source of the cited lemma, `papers/2211.07689.txt` l.1502–1558 (B–M Lemma 25 and its proof)
- v6work: R6 lists lemCap as "Uses Γ2(a) only, D\* ≥ 2¹¹⁷. Unchanged". R1 renumbers citLem25 but
  leaves its text unchanged. No v6 revision changes the statements formalized here.

## 1. Fidelity: back-translation

I read the definitions pretty-printed with `pp.parens` and `pp.numericTypes`, not only the source.
All numerals are real and all exponents are `ℕ` literals:
- `(2:ℝ)^(40:ℕ)`
- `Real.logb (2:ℝ) m ^ (4:ℕ)`, which is `(log₂ m)^4`
- `2 ^ (-5:ℤ)`, which is a `zpow`

The quotient parses as `((ε^2 * m) / (18 * (logb 2 m)^4))`.

### `EG.Spec.BMLemma25Statement` vs s1:citLem25

Manuscript: "Let `ε ≥ 2^{-5}` and `m ≥ 2^{30}/ε²` (so `m ≥ 2^{40}` suffices at `ε = 2^{-5}`).
Every `m`-vertex `(ε,0)`-expander contains a cycle of length at least `ε²m/(18 log⁴m)`."

Back-translation. Take any type `V` (in any universe), any decidable equality, any finite simple
graph `G` on `V` with `m := |V(G)|`, and any real `ε`. Suppose:
- `2^{-5} ≤ ε`;
- `2^{30}/ε² ≤ m`;
- `2 ≤ m`;
- `G` is an `(ε,0)`-expander in the sense of Def. 11 (log₂).

Then there is a list `c` of pairwise distinct vertices with `|c| ≥ 3` such that:
- all the edges `c₀c₁, …, c_{k−1}c₀` lie in `E(G)`;
- `ε²m/(18 (log₂ m)^4) ≤ |c|`.

Checks:
- **Inequalities.** Both hypotheses and the conclusion are non-strict. So is the manuscript.
- **Log base.** The log is `log₂` (convGraphs (b)). `log⁴` is a power; an iterate would be written
  `log^{[k]}`.
- **Length.** The length is `c.length`, which equals the number of edges of the closed walk.
- **Closing edge.** `EGTest/Cap.lean` checks that `cycleEdges [1,2,3]` includes it (`decide`).
- **Vertices.** The vertices of `c` lie in `V(G)` via `edge_verts`.

**The only deviation is the extra hypothesis `2 ≤ m`.** I re-checked the author's argument.
- At `m = 1`, `ε = 2^{15}`, every hypothesis of the literal statement holds:
  - `2^{30}/ε² = 1`;
  - Def 11 is vacuous, since no `U` has `1 ≤ |U| ≤ 2/3`.
- The bound `ε²·1/(18·0)` is undefined in the manuscript, and `0` in Lean. There is no cycle, so
  the literal statement is false. `EG.bmLemma25_literal_false` proves this, sorry-free, at every
  universe.
- `m = 0` contradicts `m ≥ 2^{30}/ε²`. So `2 ≤ m` is the minimal repair, of class T0 (encoding).
- My scratch file proves that the Spec is *equivalent* to "the literal statement, for `m ≥ 2`".
  So the extra hypothesis is the only difference.
- The only use (lemCap (ii)) has `m ≥ 2^{40}`.

**Plausibility of the sorry'd statement.** I compared with the B–M source (l.1502–1558) and
re-derived the DFS proof for every instance of the Lean statement.
- **Bound on `ε`.** For `m ≥ 2`, take `|U| = ⌈m/2⌉ ≤ 2m/3`. Then `|N(U)| ≤ ⌊m/2⌋ ≤ |U|`, so
  every `(ε,0)`-expander has `ε ≤ log²m`. This supplies the step "`|P| ≥ m/3 ≥ εm/(3log²m)`",
  which B–M leave implicit.
- **Size of the target length.** With `ε ≥ 2^{-5}` and `ε²m ≥ 2^{30}`, we get
  `a := ε²m/(18 log⁴m) ≥ 23.3`. The minimum is at `m = 2^{40}`.
- **Choice of `Y`.** Since `|P|/3 ≥ 2a`, an integer `|Y| ∈ [a, 2a)` exists with
  `|X|, |Z| ≥ |P|/3`.
- **Contradiction step.** Let `S` be the smaller side, so `|S| ≤ m/2`. Its neighbourhood lies in
  `Y`, so `|N(S)| ≤ |Y| < 2a`. But `|S| ≥ |P|/3` gives `|N(S)| ≥ ε|P|/(3 log²m) ≥ 2a`.
- **Cycle case.** The cycle has at least `|Y| + 2 ≥ 25` vertices, so `Obj.WF` holds.

So the statement behind the one allowed `sorry` is true, as far as I can check by hand.

### `EG.Spec.CapStatement` vs s2:lemCap (i)

Manuscript: "(i) If `m ≥ 2^{40}`, `T ≥ 2^{117}` and `m < 18432 T log⁴ m`, then
`m ≤ 2^{16} T log⁴ T`."

Lean, pretty-printed:
`∀ m T : ℝ, 2^40 ≤ m → 2^117 ≤ T → m < 18432*T*(logb 2 m)^4 → m ≤ 2^16*T*(logb 2 T)^4`.

This is verbatim:
- the strict hypothesis `<` and the three non-strict ones are as in the manuscript;
- the constants are the same;
- the log base is the same.

`m` is real, which is at least as strong as the natural `m = |𝒫|` of (ii).

### `EG.Spec.CapUniformStatement` vs the remark

Manuscript: "The uniform form `m ≤ max(2^{40}, 2^{16}T(log T+40)^4)` holds for all `T ≥ 1`". The
proof of the remark ends with "`m > max(2^{40},B')` would give `χ(m) > χ(B') ≥ 18432 T`". So the
implicit hypothesis is `m < 18432 T log⁴ m`.

Lean: `∀ m T : ℝ, 1 ≤ T → m < 18432*T*(logb 2 m)^4 → m ≤ max (2^40) (2^16*T*(logb 2 T + 40)^4)`.

The hypothesis `m ≥ 2^{40}` is omitted. My scratch file proves that the Spec is equivalent to the
version with this hypothesis, since the case `m < 2^{40}` is trivial through the `max`. The
docstring now says "equivalent" (round-1 issue 2 is fixed).

### `EG.Spec.CapGraphStatement` vs task (3) and the proof of lemCap (ii)

Task: "an m-vertex (2⁻⁵,0)-expander with m ≥ 2⁴⁰ containing no cycle of length ≥ T (T ≥ 2¹¹⁷)
has m ≤ 2¹⁶ T log⁴ T".

Back-translation. For every `V` and every `G`, and every real `T`, suppose:
- `2^{117} ≤ T`;
- `2^{40} ≤ |V(G)|`;
- `G` is a `(2^{-5},0)`-expander;
- every cycle of `G` has length `< T`.

Then `|V(G)| ≤ 2^{16} T (log₂T)^4`.

Checks:
- "No cycle of length at least `T`" is negated correctly.
- The hypothesis is placed on `G` itself. That is weaker than placing it on `G'_l`, so the
  statement is at least as strong as (ii) needs: a cycle of the graph of `𝒫` is a cycle of
  `G'_l` by `edges ⊆` monotonicity.
- This matches s2.tex l.664–670: "Otherwise the graph of `𝒫` is an `(ε,0)`-expander … on
  `m ≥ 2^{40}` vertices … Hence `m < 18432 T log⁴m`, and (i) gives `m ≤ 2^{16}T log⁴T`".

**Part (ii) itself is correctly left out**, and cap.md §Deviations 2 lists what it needs. I checked
the list against s2.tex l.660–676; it is complete:
- `T = t^{HB}_l d_l ≥ 2^{117}` from `\Gc{2}(a)` (= Γ2(a), label `s1:condG2`);
- `M_l` from (R2);
- the (R3) stopping rule;
- (R1);
- pre-parts as leaves of `τ`-runs;
- (R5);
- `τ_l ≥ 128 s_l log² M_l`.

## 2. Vacuity

These checks come from `EGTest/Cap.lean`, which I re-ran (0 errors, 0 sorries), and from my own
scratch file.
- **CapStatement's hypotheses are satisfiable,** at `m = 2^{40}`, `T = 2^{117}` (test file).
  **They are also satisfiable close to the cap** (scratch file):
  - take `T = 2^{117}` and `m = 2^{15}·T·117^4`, which is half the conclusion's bound;
  - then `m ≥ 2^{40}` and `m < 18432 T log⁴m`, via `log₂ m ≥ 159`.

  The conclusion is therefore a real restriction, not a consequence of contradictory
  hypotheses.
- **Load-bearing hypotheses** (test file):
  - dropping `m < 18432 T log⁴m` makes (i) false (`m = 2^{200}`);
  - weakening `T ≥ 2^{117}` to `T ≥ 2^{20}` makes (i) false (the remark's counterexample);
  - dropping the hypothesis of the uniform form makes it false (`m = 2^{200}`, `T = 1`).
- **CapGraphStatement and BMLemma25Statement have jointly satisfiable hypotheses:**
  - `K_{2^{40}}` is a `(2^{-5},0)`-expander, proved through Def 11;
  - all its cycles have length `≤ 2^{40} < 2^{117}`.
- **The no-long-cycle hypothesis of CapGraphStatement is load-bearing:** `K_{2^{200}}` violates the
  conclusion.
- **The conclusion of BMLemma25Statement is non-trivial** (scratch file): at `ε = 2^{-5}`,
  `m = 2^{40}` the bound is `> 23`, whereas `Obj.WF` only gives `|c| ≥ 3`.

None of the Specs can be discharged trivially.

## 3. Hygiene

- `lake build EG.Proof.HB.Cap`: success. The only warning is `declaration uses 'sorry'` at
  `EG/Proof/Ext/BMLemma25.lean:23`, which is the allowed one.
- `scripts/check.sh EGTest/Cap.lean`: `errors=0 sorry-warnings=0`.
- `python3 scripts/lint.py`: `lint (development): 0 findings`.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.HB.Cap EG.Lib.Found.LogMono
  EG.Proof.Ext.BMLemma25 EG.Spec.HB.Cap EG.Spec.Ext.BMLemma25`: 150 constants, 2 use `sorryAx`,
  0 violations. The sorry frontier is exactly:
  - `EG.bmLemma25`, which is allowed;
  - `EG.cap_graph`, which depends on it, as the task intends.
- `#print axioms` shows only `propext, Classical.choice, Quot.sound` for:
  - `EG.cap`;
  - `EG.cap_uniform`;
  - `EG.bmLemma25_literal_false`.
- A grep of the six files finds:
  - no `set_option`, `attribute`, `instance`, `macro` or `local notation`;
  - `sorry` only at `EG/Proof/Ext/BMLemma25.lean:24`, plus mentions in docstrings.
- Module headers follow AGENTS.md:
  - `@[expose] public section` in the Spec files;
  - `public section` in the Proof and Lib files;
  - the test file is a plain non-module `import`.
- Every declaration that formalizes a manuscript statement has a docstring starting with its
  label (`[s1:citLem25]` or `[s2:lemCap] …`).
- No new name clashes with existing `EG` theorems (grep).
- All files are under 200 lines.

## 4. The proofs prove the Specs

- The theorems have exactly the Spec types. I checked this by type ascription in the scratch file:
  - `(EG.cap : EG.Spec.CapStatement)`;
  - `(EG.cap_uniform : EG.Spec.CapUniformStatement)`;
  - `(EG.cap_graph.{u} : EG.Spec.CapGraphStatement.{u})` at `u = 0, 3`;
  - `(EG.bmLemma25.{2} : EG.Spec.BMLemma25Statement.{2})`.
- The Specs mention only Mathlib's `Real.logb` and the foundation objects (`FGraph`, `IsExpander`,
  `Obj.WF`, `cycleEdges`). No auxiliary definition could hide a weakening.
- I checked the proof of (i) by hand against the manuscript:
  - **`div_log_pow_le_div_log_pow`:** `(q/p)^k ≤ e^{k(q−p)/p} ≤ e^{q−p} = b/a`, which uses
    `k ≤ p = ln a`.
  - **`cap_core`:**
    - `m > B ≥ 2^{16}` gives `ln B ≥ 16 ln 2 > 4`;
    - `log₂ m, log₂ B > 0`;
    - so `18432T ≤ χ(B) ≤ χ(m) < 18432T`.
  - **`cap_numeric`:**
    - start from `log₂ x ≤ log₂117 + (x−117)/(117 ln 2)`;
    - `log₂ 117 ≤ 55/8` (from `117^8 ≤ 2^{55}`) and `117 ln 2 ≥ 80` give
      `16 + x + 4 log₂x ≤ 43.5 + x + (x−117)/20`;
    - `1.37317x` exceeds this at `x = 117` (`160.66` against `160.5`);
    - its slope `0.37317` beats `0.05`.
  - **`cap_const`:** `18432·1.37317⁴ ≈ 65531 ≤ 65536`.
- **`cap_uniform`** uses the same argument with `B' = 2^{16}T(x+40)^4`, together with
  `log₂40 ≤ 6` and `40 ln 2 ≥ 27`.
- **`cap_graph`:**
  - `ε = 2^{-5}` gives `2^{30}/ε² = 2^{40}` and `ε²/18 = 1/18432`;
  - `log₂m > 0` clears the division;
  - `bmLemma25` then applies, with `2 ≤ m` from `m ≥ 2^{40}`.

## 5. Round-1 items

| Round-1 issue | Status |
|---|---|
| 1 (minor): record `2 ≤ m` as a T0 entry | Author side done: module docstring, and a ready-to-copy entry **T0-cap-1** in cap.md. The central record is **still open** (orchestrator action; grep finds no `T0-cap` outside `work/p1b/cap*`). |
| 2 (cosmetic): "stronger" should be "equivalent" | Fixed (Spec docstring and cap.md). Equivalence is machine-checked in my scratch file. |
| 3 (cosmetic): universe of `bmLemma25_literal_false` | Fixed: universe-polymorphic, via `PUnit.{u+1}`. |
| 4 (cosmetic): non-vacuity tests | Fixed: `EGTest/Cap.lean` compiles sorry-free. |
| 5 (cosmetic): roots and `LOCK.json` | Orchestrator/integrator action, still open. Not the author's scope. |

## 6. Issues

1. **minor, orchestrator:** the T0 entry **T0-cap-1** (`BMLemma25Statement` adds `2 ≤ m`;
   proposed v6 wording "`m ≥ max(2, 2^{30}/ε²)`" for s1:citLem25) is not yet in the central
   conventions record (STATE.md "Manuscript notes forwarded to v6", or the PLAN §7 conventions
   file).
   **Fix:** copy the entry from `work/p1b/cap.md`, "Fix round 1", item 1.
2. **cosmetic, orchestrator:** the six new modules are not yet in the roots:
   - `EG.Spec.Ext.BMLemma25`
   - `EG.Proof.Ext.BMLemma25`
   - `EG.Spec.HB.Cap`
   - `EG.Proof.HB.Cap`
   - `EG.Lib.Found.LogMono`
   - `EGTest.Cap`

   The two Spec files also need `LOCK.json` entries at the freeze.
   **Fix:** run `scripts/gen_roots.py` at integration, and lock the Spec files at the freeze.
