# Clean-room review, round 1: task [cap]

Reviewer: clean-room agent (round 1). I did not edit any Lean file. My scratch checks are in
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/CapReview.lean`,
which imports `EG.Proof.HB.Cap` and `EG.Lib.Found.Graph`. It compiles with no errors.

**Verdict: APPROVE.** I found no fidelity, vacuity or hygiene defect. There is one documented
deviation: `BMLemma25Statement` adds the hypothesis `2 ≤ m`. It is necessary and correctly argued
(T0, an encoding issue). It should be recorded centrally; see issue 1. The other items are
cosmetic.

Files reviewed (as listed in `work/p1b/cap.md`):
- `EG/Spec/Ext/BMLemma25.lean`
- `EG/Proof/Ext/BMLemma25.lean`
- `EG/Spec/HB/Cap.lean`
- `EG/Proof/HB/Cap.lean`
- `EG/Lib/Found/LogMono.lean`

Foundations used by the Specs, which I also read:
- `EG/Defs/Objects.lean` (`cycleEdges`, `Obj.WF`)
- `EG/Defs/Graph.lean` (`FGraph`, `card`, `nbrSet`, `deleteEdges`)
- `EG/Defs/Expander.lean` (`IsExpander`)

Manuscript passages checked:
- s1.tex l.716–734 (`s1:citLem25`)
- s1.tex l.321–330 (`s1:convGraphs` (b): `log = log₂`)
- s2.tex l.622–677 (`s2:lemCap`, statement, remark and proof)

## 1. Fidelity: back-translation

I printed the four Spec definitions with `set_option pp.parens true`. The parse is as intended:
- `18432 * T * (logb 2 m)^4`
- `(ε^2 * m) / (18 * (logb 2 m)^4)`
- `2^30 / ε^2`
- `(logb 2 T + 40)^4`

### `EG.Spec.BMLemma25Statement` vs s1:citLem25

Manuscript: "Let `ε ≥ 2^{-5}` and `m ≥ 2^{30}/ε²` (so `m ≥ 2^{40}` suffices at `ε = 2^{-5}`).
Every `m`-vertex `(ε,0)`-expander contains a cycle of length at least `ε²m/(18 log⁴ m)`."

Back-translation of the Lean statement: for every type `V` (any universe, any decidable equality),
every finite simple graph `G` on `V` with `m := |V(G)|`, and every real `ε`, if
- `2^{-5} ≤ ε`,
- `2^{30}/ε² ≤ m`,
- `2 ≤ m`, and
- `G` is an `(ε,0)`-expander in the sense of Definition 11 (log₂),

then there is a vertex list `c` such that
- `c` has no repeated vertex and at least 3 vertices,
- every edge `c₀c₁, …, c_{k-1}c₀` (including the closing edge) lies in `E(G)`, and
- `ε² m / (18 (log₂ m)^4) ≤ |c|`.

| Item | Lean | Manuscript | OK? |
|---|---|---|---|
| ε range | `2^(-5:ℤ) ≤ ε`, real | `ε ≥ 2^{-5}` | yes (non-strict) |
| size | `2^30/ε^2 ≤ G.card` | `m ≥ 2^{30}/ε²` | yes (non-strict) |
| `m`-vertex | `m = G.card = \|verts\|` | `\|G\| = \|V(G)\|` (convGraphs (a)) | yes |
| expander | `G.IsExpander ε 0` | `(ε,0)`-expander, Def 11 | yes (Def 11 reviewed in graph.review1) |
| log | `Real.logb 2`, `(·)^4` | `log = log₂` (convGraphs (b)); `log⁴` is a power, not an iterate (iterates are `log^{[k]}`) | yes |
| cycle | `Obj.WF` (Nodup, length ≥ 3) + all `cycleEdges c ∈ G.edges` | "contains a cycle" | yes. Its vertices are in `V(G)` via `edge_verts`. I checked `cycleEdges [1,2,3] = [s(1,2), s(2,3), s(3,1)]` by `decide`, so the closing edge is included. |
| length | `(c.length : ℝ)` | number of edges | yes (`\|cycleEdges c\| = \|c\|`) |
| bound | `ε^2*m/(18*logb 2 m^4) ≤ c.length` | "length at least `ε²m/(18 log⁴ m)`" | yes (non-strict) |
| **extra** | `2 ≤ G.card` | absent | **deviation, justified: see issue 1** |

**The added hypothesis `2 ≤ m`.** I checked the author's argument independently.
- At `m = 1`, `log 1 = 0`, so the manuscript bound `ε²m/(18 log⁴ m)` is undefined.
- With `ε = 2^{15}` all hypotheses of the literal statement hold at `m = 1`:
  - `2^{30}/ε² = 1`;
  - Def 11 is vacuous, since no `U` has `1 ≤ |U| ≤ 2/3`.
- A one-vertex graph has no cycle. So under any reading (Lean's `x/0 = 0`, or `+∞`), the literal
  statement fails at `m = 1`. `EG.bmLemma25_literal_false` proves this, and it is sorry-free
  (axioms `propext, Classical.choice, Quot.sound`).
- The rewriting `ε²m ≤ 18 log⁴m · |c|` also fails at `m = 1`. So some extra hypothesis is
  unavoidable, and `2 ≤ m` is the minimal one.

`m = 1` is also the **only** degenerate case:
- For `m ≥ 2`, take `U` with `|U| = ⌈m/2⌉ ≤ 2m/3`. Then `|N(U)| ≤ ⌊m/2⌋ ≤ |U|`, so an
  `(ε,0)`-expander has `ε ≤ log² m`. Combined with `ε²m ≥ 2^{30}`, this forces `m ≳ 2^{14.5}`.
- The target length `a = ε²m/(18 log⁴m)` then satisfies
  `a ≥ max(2^{30}, m/2^{10})/(18 log⁴ m) ≥ 23.3`. The minimum is at `m = 2^{40}`.
- Also `|P|/3 ≥ εm/(9 log²m) ≥ 2a`.

So the B–M DFS argument sketched in s1:citLem25 (a DFS moment with `|U| = |R|`, then the split
`X, Y, Z` and expansion of the side of size at most `m/2`) goes through with integer sizes for
every instance of the Lean statement. I re-derived the steps and see no obstruction. The Spec is
therefore plausibly true, so the `sorry` does not hide a false statement.

The only use is s2:lemCap (ii), with `ε = 2^{-5}` and `m ≥ 2^{40}`, so the extra hypothesis has
no downstream cost.

### `EG.Spec.CapStatement` vs s2:lemCap (i)

Manuscript: "(i) If `m ≥ 2^{40}`, `T ≥ 2^{117}` and `m < 18432 T log⁴ m`, then
`m ≤ 2^{16} T log⁴ T`."

Back-translation: for all real `m, T`, if `2^{40} ≤ m`, `2^{117} ≤ T` and
`m < 18432 · T · (log₂ m)^4`, then `m ≤ 2^{16} · T · (log₂ T)^4`.

This is verbatim:
- the same strict and non-strict inequalities;
- the same constants (18432 = 18·2^{10} = ε^{-2}·18 at `ε = 2^{-5}`);
- the same log base.

Real `m` is at least as strong as natural `m`, which is how (ii) uses it. Yes.

### `EG.Spec.CapUniformStatement` vs the remark

Manuscript: "The uniform form `m ≤ max(2^{40}, 2^{16}T(log T+40)^4)` holds for all `T ≥ 1`." The
proof of the remark ends: "`m > max(2^{40},B')` would give `χ(m) > χ(B') ≥ 18432 T`", i.e. the
implicit hypothesis is `m < 18432 T log⁴ m`.

Back-translation: for all real `m, T`, if `1 ≤ T` and `m < 18432 T (log₂ m)^4`, then
`m ≤ max(2^{40}, 2^{16} T (log₂ T + 40)^4)`.

Yes. The hypothesis `m ≥ 2^{40}` is omitted. This is logically **equivalent** to including it:
for `m < 2^{40}` the conclusion holds trivially. It is not strictly stronger, as the docstring
claims (cosmetic; issue 2).

### `EG.Spec.CapGraphStatement` vs the task and the proof of s2:lemCap (ii)

Task: "an m-vertex (2⁻⁵,0)-expander with m ≥ 2⁴⁰ containing no cycle of length ≥ T (T ≥ 2¹¹⁷)
has m ≤ 2¹⁶ T log⁴ T".

Back-translation: for every `V`, every `G : FGraph V` and every real `T`, if
- `2^{117} ≤ T`,
- `2^{40} ≤ |V(G)|`,
- `G` is a `(2^{-5},0)`-expander, and
- every cycle of `G` (as above) has length `< T`,

then `|V(G)| ≤ 2^{16} T (log₂ T)^4`.

Yes. "No cycle of length ≥ T" is correctly negated to "every cycle has length `< T`". The
hypothesis is placed on `G` itself rather than on `G'_l`. That is the weaker hypothesis, so the
statement is at least as strong as needed: downstream, a cycle of the piece graph is a cycle of
`G'_l` by `edges ⊆` monotonicity, and (R1) applies.

The author's notes on what (ii) still needs agree with the proof text in s2.tex l.660–676:
- `T = t^{HB}_l d_l = d_l log² d_l ≥ d_l ≥ D_* ≥ 2^{117}` (G2(a));
- `M_l` from (R2);
- the (R3) stopping rule;
- (R1);
- pre-parts as leaves of `τ`-runs;
- (R5);
- `τ_l ≥ 128 s_l log² M_l`.

PLAN §7 T2 lists Cap(ii) as simplicity-dependent. That concerns the later task.

## 2. Vacuity

All of the following examples compile in the scratch file with no `sorry`.

- **CapStatement hypotheses are satisfiable:** `m = 2^{40}`, `T = 2^{117}` (`logb 2 2^{40} = 40`).
- **The hypothesis `m < 18432 T log⁴ m` is load-bearing:** without it the statement is false
  (`m = 2^{200}`, `T = 2^{117}`).
- **The threshold `T ≥ 2^{117}` matters:** the same statement with `T ≥ 2^{20}` is false, derived
  from `EG.cap_remark_counterexample`.
- **CapUniformStatement's hypothesis restricts `m`:** without it the statement is false
  (`m = 2^{200}`, `T = 1`).
- **CapGraphStatement and BMLemma25Statement hypotheses are jointly satisfiable:**
  - the complete graph `K_n` on `Fin (2^{40})` is a `(2^{-5},0)`-expander (`Kn_expander`, a real
    proof through `IsExpander`: `F = ∅`, `Nbr(U) = V∖U`, `2^{-5}|U|/1600 ≤ n − |U|`);
  - every cycle of it has length `≤ 2^{40} < 2^{117}`;
  - `2^{30}/(2^{-5})^2 ≤ 2^{40}` and `2 ≤ 2^{40}`.
- **The no-long-cycle hypothesis of CapGraphStatement is load-bearing:** `K_{2^{200}}` is a
  `(2^{-5},0)`-expander (`Kn_expander'`, for any `n = 2^k`, `k ≥ 1`) that violates the
  conclusion at `T = 2^{117}`. So the content of `cap_graph` really comes from Lemma 25.

The Specs cannot be discharged trivially, and none of their hypothesis sets is contradictory.

## 3. Hygiene

- `python3 scripts/lint.py`: `lint (development): 0 findings`.
- `lake build EG.Proof.HB.Cap`: success. The only warning is the `sorry` in
  `EG/Proof/Ext/BMLemma25.lean:22`.
- `scripts/check.sh` on each of the five files (from source): 0 errors in each. The only sorry
  warning is in `EG/Proof/Ext/BMLemma25.lean`.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.HB.Cap EG.Lib.Found.LogMono
  EG.Proof.Ext.BMLemma25 EG.Spec.HB.Cap EG.Spec.Ext.BMLemma25`: 150 constants, 0 violations.
  The sorry frontier is exactly:
  - `SORRY EG.bmLemma25`, the one allowed sorry;
  - `SORRY EG.cap_graph`, which depends on it, as the task intends.
- `#print axioms`: `EG.cap`, `EG.cap_uniform` and `EG.bmLemma25_literal_false` use only
  `propext, Classical.choice, Quot.sound`.
- Module headers follow AGENTS.md:
  - `module` and `public import`;
  - `@[expose] public section` in Spec, `public section` in Proof and Lib.
- Docstrings carry `[s1:citLem25]` / `[s2:lemCap]` tags and quote the manuscript accurately.
- All files are under 200 lines. There are no `maxHeartbeats` options.

## 4. The proofs prove the Specs

- `theorem bmLemma25 : EG.Spec.BMLemma25Statement.{u} := by sorry`. This is the allowed sorry.
- `theorem cap : EG.Spec.CapStatement` is derived from `cap_of_T_ge`, whose conclusion is
  syntactically the Spec conclusion. The unused hypothesis `m ≥ 2^{40}` is simply dropped, which
  is a strengthening.
- `theorem cap_uniform : EG.Spec.CapUniformStatement` and
  `theorem cap_graph : EG.Spec.CapGraphStatement.{u}` also have the Spec types exactly.
- No auxiliary definitions are involved. The Specs mention only Mathlib's `Real.logb` and the
  foundation objects, so there is no room for a hidden weakening.
- I checked the proof of (i) by hand:
  - `cap_core` handles `m > B ≥ 2^{16}`, so `log m > 0` and `ln B ≥ 16 ln 2 > 4`;
  - `div_log_pow_le_div_log_pow` gives `(q/p)^k ≤ e^{k(q−p)/p} ≤ e^{q−p} = b/a`, which uses
    `k ≤ p`;
  - `cap_numeric` bounds `16 + 4·log₂117 ≤ 16 + 27.5 = 43.5 < 43.66 = 0.37317·117`, and the slope
    uses `4/(117 ln 2) ≤ 4/80 < 0.37317`;
  - `cap_const`: `18432·1.37317⁴ ≈ 65531 ≤ 65536`.
- In `cap_graph` the constant step `(2^{-5})²/18 = 1/18432` is done by `norm_num`, and the
  division is cleared with `log₂ m > 0`. Correct.

## 5. Issues

1. **minor (documentation):** `BMLemma25Statement` adds the hypothesis `2 ≤ m`, which the
   manuscript does not state. The deviation is necessary (the literal statement is false or
   undefined at `m = 1` with `ε ≥ 2^{15}`, and this is machine-checked), minimal, and costs nothing
   downstream.
   **Fix:** record it as a T0 (encoding) entry in the central conventions/ledger (PLAN §7: "Fix
   the Lean only; record it in a conventions file"). Propose the manuscript wording "…and
   `m ≥ max(2, 2^{30}/ε²)`" for s1:citLem25.
2. **cosmetic:** The Spec docstring and `cap.md` call `CapUniformStatement` (without
   `m ≥ 2^{40}`) "the stronger reading". It is logically equivalent, since the `max` with
   `2^{40}` makes the case `m < 2^{40}` trivial.
   **Fix:** say "equivalent" instead of "stronger".
3. **cosmetic:** `bmLemma25_literal_false` refutes the literal statement only at `V : Type`
   (universe 0). That is enough as evidence.
   **Fix:** none needed, or note the universe in the docstring.
4. **cosmetic:** There is no `EGTest` non-vacuity file. The scratch examples above (`K_{2^{40}}` is
   a `(2^{-5},0)`-expander with all cycles `< 2^{117}`; the hypotheses of CapStatement are
   satisfiable at `m = 2^{40}`, `T = 2^{117}`) could be added as `EGTest/HB/Cap.lean`.
   **Fix:** optional; the integrator may copy them from the scratch file.
5. **cosmetic:** The roots do not yet list the five new modules (`EG.Spec.Ext.BMLemma25`,
   `EG.Proof.Ext.BMLemma25`, `EG.Spec.HB.Cap`, `EG.Proof.HB.Cap`, `EG.Lib.Found.LogMono`).
   **Fix:** the orchestrator runs `scripts/gen_roots.py`. The Spec files also need `LOCK.json`
   entries at the freeze.
