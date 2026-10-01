# P1b pilot [cap]: Lemma-25 size cap (s2:lemCap (i)) and B–M Lemma 25 (s1:citLem25)

Status: all files compile with 0 errors and 0 warnings, apart from the one allowed `sorry`
(`EG.bmLemma25`). `lake build EG.Proof.HB.Cap` succeeds. `python3 scripts/lint.py` reports
0 findings. The axiom scan (`--prefix EG`, modules `EG.Proof.HB.Cap EG.Lib.Found.LogMono`) covers
150 constants and finds 0 violations. Only two of them use `sorryAx`:
- `EG.bmLemma25`, the allowed `sorry`;
- `EG.cap_graph`, which depends on it.

`EG.cap` (part (i)) and `EG.cap_uniform` (the remark) are sorry-free.

## Files
| File | Contents |
|---|---|
| `EG/Spec/Ext/BMLemma25.lean` | `EG.Spec.BMLemma25Statement` (s1:citLem25, explicit form) |
| `EG/Proof/Ext/BMLemma25.lean` | `EG.bmLemma25 : BMLemma25Statement` (**sorry**, a later task); `EG.bmLemma25_literal_false` (see Deviations) |
| `EG/Spec/HB/Cap.lean` | `EG.Spec.CapStatement` (s2:lemCap (i)); `EG.Spec.CapUniformStatement` (the remark's uniform form); `EG.Spec.CapGraphStatement` (the graph-level step of the proof of (ii)) |
| `EG/Proof/HB/Cap.lean` | `EG.cap`, `EG.cap_uniform`, `EG.cap_remark_counterexample`, `EG.cap_graph`, plus helpers `cap_core`, `cap_of_T_ge`, `cap_numeric`, `cap_numeric_uniform`, `cap_const`, `cap_chi_ge`, `logb_cap_bound`, `logb_two_117_le`, `logb_two_40_le` |
| `EG/Lib/Found/LogMono.lean` (new Lib) | `EG.div_log_pow_le_div_log_pow` (`y/ln^k y` is non-decreasing on `[e^k,∞)`), `EG.div_logb_pow_le_div_logb_pow` (the same for `log_c`, `c > 1`), `EG.logb_sub_logb_le` (`log_c y − log_c x ≤ (y−x)/(x ln c)`) |
| `EGTest/Cap.lean` (fix round 1) | non-vacuity and load-bearing-hypothesis tests for all four Specs (namespace `EGTest.Cap`) |

The root files (`EG.lean`, `EGTest.lean`, etc.) are not edited. The orchestrator must add the five
new `EG` modules and the test module `EGTest.Cap` (regenerate the roots with
`scripts/gen_roots.py`).

## Statements
- **`BMLemma25Statement`** (universe-polymorphic in `V : Type u`):
  ```
  ∀ V [DecidableEq V] (G : FGraph V) (ε : ℝ),
    2^(-5:ℤ) ≤ ε → 2^30/ε^2 ≤ (G.card:ℝ) → 2 ≤ G.card → G.IsExpander ε 0 →
    ∃ c : List V, (Obj.cycle c).WF ∧ (∀ e ∈ cycleEdges c, e ∈ G.edges) ∧
      ε^2 * G.card / (18 * logb 2 G.card ^ 4) ≤ c.length
  ```
  A cycle is a list cycle: `Obj.WF` (Nodup, length ≥ 3) with all edges (including the closing
  edge) in `E(G)`. Its length is `c.length`, which equals the number of edges.
- **`CapStatement`**, verbatim (i), with `m T : ℝ` and `log = Real.logb 2`:
  `2^40 ≤ m → 2^117 ≤ T → m < 18432*T*logb 2 m^4 → m ≤ 2^16*T*logb 2 T^4`.
- **`CapUniformStatement`**: `1 ≤ T → m < 18432*T*logb 2 m^4 →
  m ≤ max (2^40) (2^16*T*(logb 2 T + 40)^4)`. The hypothesis `m ≥ 2^40` of (i) is omitted.
  The manuscript's argument does not use it. The two readings are logically equivalent: for
  `m < 2^40` the conclusion `m ≤ max(2^40, …)` holds trivially.
- **`CapGraphStatement`**: for `G : FGraph V` and `T : ℝ`,
  `2^117 ≤ T → 2^40 ≤ G.card → G.IsExpander (2^(-5:ℤ)) 0 →
  (∀ c, (Obj.cycle c).WF → (∀ e ∈ cycleEdges c, e ∈ G.edges) → c.length < T) →
  G.card ≤ 2^16*T*logb 2 T^4`.
  "No cycle of length ≥ T" is said of `G` itself. In (ii), `G` is the graph of an `s = 0` piece
  and a subgraph of `G'_l`, so a cycle of `G` is a cycle of `G'_l`, which (R1) excludes.

## Proof of (i)
This follows the manuscript, with the derivative argument replaced by elementary inequalities.
1. `χ(y) = y/log⁴y` is non-decreasing on `[e^4, ∞)` (`div_logb_pow_le_div_logb_pow`). Put
   `p = ln a` and `q = ln b`. Then `(q/p)^k ≤ exp((q−p)/p)^k = exp(k(q−p)/p) ≤ exp(q−p) = b/a`,
   using `1 + t ≤ e^t` and `k ≤ p`.
2. `cap_core`: if `B ≥ 2^16`, `18432 T log⁴B ≤ B` and `m < 18432 T log⁴m`, then `m ≤ B`.
   Otherwise `χ(B) ≤ χ(m)` (since `ln B ≥ 16 ln 2 > 4`), and
   `18432T ≤ χ(B) ≤ χ(m) < 18432T`.
3. `x = log T ≥ 117` and `B = 2^16 T x^4`. Then `log B = 16 + x + 4 log x` (`logb_cap_bound`),
   and this is `≤ 1.37317 x` (`cap_numeric`). The proof of `cap_numeric` uses:
   - `log x ≤ log 117 + (x−117)/(117 ln 2)` (`logb_sub_logb_le`);
   - `117 ln 2 ≥ 80`, from `Real.log_two_gt_d9`;
   - `log₂117 ≤ 55/8`, since `117^8 ≤ 2^55`.

   At `x = 117` the margin is about `0.16`, as in the manuscript (`43.66` against `43.48`).
4. `18432 · 1.37317^4 ≤ 2^16` (`cap_const`, by `norm_num`; this is `1.37317 ≤ (32/9)^{1/4}`).
   So `18432 T log⁴B ≤ 18432 T (1.37317x)^4 ≤ 2^16 T x^4 = B` (`cap_chi_ge`).

The hypothesis `m ≥ 2^40` is not needed: `cap_of_T_ge` omits it, and `cap` is derived from it.
The uniform form is the same argument with `B' = 2^16 T (x+40)^4` (`cap_numeric_uniform`: bound
`log₂40 ≤ 6` and `40 ln 2 ≥ 27`).

## Proof of the graph step (3)
With `ε = 2^-5`: `2^30/ε² = 2^40 ≤ m`, and `2 ≤ m`. So `bmLemma25` gives a cycle `c` with
`m/(18432 log⁴m) = ε²m/(18 log⁴m) ≤ |c| < T`. Hence `m < 18432 T log⁴m` (since `log m > 0`),
and `cap` gives the bound.

## Deviations and open points
1. **`BMLemma25Statement` has the extra hypothesis `2 ≤ m` (class T0, encoding: degenerate
   case, no downstream effect; see the T0 entry under "Fix round 1").** The manuscript's bound
   `ε²m/(18 log⁴m)` is undefined at `m = 1`, where `log 1 = 0`. In Lean `x/0 = 0`, so without the hypothesis the literal statement is false:
   - take `ε = 2^15`; then `2^30/ε² = 1 ≤ m = 1`;
   - the one-vertex graph is an `(ε,0)`-expander, because Def 11 is vacuous (no `U` has
     `1 ≤ |U| ≤ 2/3`);
   - but a one-vertex graph has no cycle.

   `EG.bmLemma25_literal_false` proves this (in every universe `u`). `m = 0` is already excluded by `m ≥ 2^30/ε²`. The
   only use (s2:lemCap (ii)) has `ε = 2^-5` and `m ≥ 2^40`. Suggested manuscript wording for
   s1:citLem25: "…and `m ≥ max(2, 2^{30}/ε²)`", or "(for `m ≥ 2`, so that `log m > 0`)".

   Check that the fixed statement is plausibly true (for the later proof task). For `m ≥ 2`,
   an `(ε,0)`-expander needs `ε ≤ log²m`: take `U` of size `⌈m/2⌉ ≤ 2m/3`; then
   `|N(U)| ≤ |U|`. With `m ≥ 2^30/ε²` this gives `a := ε²m/(18 log⁴m) ≥ 23`. Also `|P|/3 ≥ 2a`,
   so the B–M choice of `X, Y, Z` with integer sizes goes through.
2. **Part (ii) is not formalized** (the task excludes it). It needs the s2 hierarchy, which is
   not yet defined:
   - `HB^tp` runs and rounds `l ≤ R`;
   - `s = 0` pieces, with (R3): a piece with `|𝒫| ≥ 2^40` is a `(2^-5,0)`-expander;
   - `T = t^HB_l d_l = d_l log² d_l`, with `d_l ≥ D_* ≥ 2^117` from G2(a), so `T ≥ 2^117`;
   - (R1): `G'_l` has no cycle of length `≥ T`;
   - (R2): `M_l = max(2^40, 2^16 T log⁴T)` and `τ_l ≥ 128 s_l log²M_l`;
   - pre-parts as leaves of `τ`-runs (`Z^0 ⊆ V(𝒫)`), and (R5): the edges of `E_l(Z)` have both
     ends in `Z^0`;
   - Lemma 14^τ.

   Given these, (ii) is `cap_graph` applied to `G =` the graph of `𝒫`, plus `2^16 T log⁴T ≤ M_l`
   and elementary counting. A cycle of the piece's graph must be transported to a cycle of
   `G'_l`; with list cycles and edge sets this is `edges ⊆` monotonicity.
3. `CapUniformStatement` omits the hypothesis `m ≥ 2^40` (logically equivalent to the literal
   reading; see above). The remark's counterexample is `cap_remark_counterexample`: `2^40 ≤ 2^55`,
   `2^55 < 18432·2^20·log⁴(2^55)` and `2^16·2^20·log⁴(2^20) < 2^55`. It checks the inequalities
   only, not the decimal exponents `57.29…` and `53.28…`.
4. The helper lemmas in `EG.Lib.Found.LogMono` are general (any `k`, any base `c > 1`) and may
   be reused, e.g. for other `y/log^k y` monotonicity arguments. The file name was chosen to
   avoid a clash with a future `Found.Log` / numerics module (PLAN §3 "Found.Log / Numerics").
   Merge it there if one is created.
5. Non-vacuity tests: `EGTest/Cap.lean` (added in fix round 1; see below).

## Fix round 1 (review `cap.review1.md`)

Build after the fixes: `lake build EG.Proof.HB.Cap` succeeds (only warning: the allowed `sorry`
in `EG/Proof/Ext/BMLemma25.lean`); `scripts/check.sh EGTest/Cap.lean` gives 0 errors and
0 sorry warnings; `python3 scripts/lint.py` gives 0 findings; the axiom scan (`--prefix EG`,
modules `EG.Proof.HB.Cap EG.Lib.Found.LogMono EG.Proof.Ext.BMLemma25 EG.Spec.HB.Cap
EG.Spec.Ext.BMLemma25`) covers 150 constants with 0 violations, and the sorry frontier is still
exactly `EG.bmLemma25` and `EG.cap_graph`. No statement (`def … : Prop`) changed; only
docstrings in the two Spec files changed.

1. **minor, `2 ≤ m` in `BMLemma25Statement` not recorded centrally: valid; fixed as far as this
   task's scope allows.** Re-checked: at `m = 1`, `ε = 2^15` every hypothesis of the literal
   statement holds (`2^30/ε² = 1`, Def 11 vacuous) and there is no cycle; `m = 0` violates
   `m ≥ 2^30/ε²`; for `m ≥ 2`, `log₂ m ≥ 1 > 0` so the bound is defined. So `2 ≤ m` is the
   minimal repair and it is an encoding issue (class T0, PLAN §7: "Fix the Lean only; record it
   in a conventions file"). The Lean was already fixed. Changes:
   - the module docstring of `EG/Spec/Ext/BMLemma25.lean` now names the class (T0), says
     `m = 1` is the only degenerate case, and gives the proposed manuscript wording;
   - the T0 entry below, ready to be copied.

   There is no central T0 conventions file yet (PLAN §7 names one; the existing T0 notes are
   in `STATE.md`, "Manuscript notes forwarded to v6"). `STATE.md`, `LEDGER.md` and
   `formal/AGENTS.md` are orchestrator-owned, so I did not edit them. **Orchestrator action:**
   copy this entry into the central list:

   > **T0-cap-1** [s1:citLem25] (B–M Lemma 25, explicit form). Lean `EG.Spec.BMLemma25Statement`
   > adds the hypothesis `2 ≤ m` (`m = G.card`). Reason: at `m = 1` the bound
   > `ε²m/(18 log⁴ m)` has `log 1 = 0`; with `ε = 2^15` the literal statement is false (the
   > one-vertex graph is vacuously an `(ε,0)`-expander, `2^30/ε² = 1`, no cycle); proved in Lean
   > by `EG.bmLemma25_literal_false`. `m = 1` is the only degenerate case. No proof affected (only
   > use: s2:lemCap (ii), `ε = 2^-5`, `m ≥ 2^40`). Proposed v6 wording for s1:citLem25:
   > "Let `ε ≥ 2^{-5}` and `m ≥ max(2, 2^{30}/ε²)`."
2. **cosmetic, "stronger" should be "equivalent": valid; fixed.** For `m < 2^40` the conclusion
   `m ≤ max(2^40, …)` holds trivially, so omitting `m ≥ 2^40` gives a logically equivalent
   statement. Changed in the module docstring of `EG/Spec/HB/Cap.lean` and in this file
   (§Statements and Deviations item 3). No other occurrence (`grep -n stronger`).
3. **cosmetic, `bmLemma25_literal_false` only at universe 0: valid; fixed (beyond the
   suggestion).** The theorem is now stated for `V : Type u`, i.e. it refutes exactly
   `EG.Spec.BMLemma25Statement.{u}` with the hypothesis `2 ≤ G.card` deleted, at every universe
   `u` (witness: the one-vertex graph on `PUnit.{u+1}`). Its docstring and the module docstring
   say so. Still sorry-free (the axiom scan lists no `sorryAx` for it).
4. **cosmetic, no committed non-vacuity test: valid; fixed.** New file `EGTest/Cap.lean`
   (namespace `EGTest.Cap`; flat path like the other test files `EGTest/Gate.lean` etc., rather
   than the suggested `EGTest/HB/Cap.lean`). Adapted from the reviewer's scratch file; the two
   expander proofs are merged into one lemma `Kn_expander` (`K_n`, `n = 2^k`, `k ≥ 1`). Contents:
   - `cycleEdges [1,2,3]` includes the closing edge;
   - `CapStatement`: hypotheses satisfiable (`m = 2^40`, `T = 2^117`); the hypothesis
     `m < 18432 T log⁴m` is load-bearing (`m = 2^200`); the threshold `T ≥ 2^117` is
     load-bearing (false with `T ≥ 2^20`, from `EG.cap_remark_counterexample`);
   - `CapUniformStatement`: its hypothesis is load-bearing (`m = 2^200`, `T = 1`);
   - `CapGraphStatement`: hypotheses jointly satisfiable (`K_{2^40}`, `T = 2^117`); the
     no-long-cycle hypothesis is load-bearing (`K_{2^200}`);
   - `BMLemma25Statement`: hypotheses jointly satisfiable (`ε = 2^-5`, `K_{2^40}`).

   The file does not use `EG.bmLemma25` or `EG.cap_graph`, so it is sorry-free.
5. **cosmetic, roots and `LOCK.json`: not an issue for this task (orchestrator/integrator
   owned).** I did not edit `EG.lean`, `EGTest.lean` or `LOCK.json`. At integration: run
   `scripts/gen_roots.py` (adds `EG.Spec.Ext.BMLemma25`, `EG.Proof.Ext.BMLemma25`,
   `EG.Spec.HB.Cap`, `EG.Proof.HB.Cap`, `EG.Lib.Found.LogMono`, `EGTest.Cap`), and lock the two
   Spec files at the freeze.

## Fix round 2 (review `cap.review2.md`, verdict APPROVE)

Build after the round: `lake build EG.Proof.HB.Cap` succeeds (only warning: the allowed `sorry`
at `EG/Proof/Ext/BMLemma25.lean:23`); `scripts/check.sh EGTest/Cap.lean` gives 0 errors and
0 sorry warnings; `python3 scripts/lint.py` gives 0 findings; the axiom scan (`--prefix EG`, the
same five modules as in round 1) covers 150 constants with 0 violations. The sorry frontier is
still exactly `EG.bmLemma25` (allowed) and `EG.cap_graph` (depends on it). No statement
(`def … : Prop`) and no proof changed; only two docstrings changed.

1. **minor, T0-cap-1 not in the central T0 record: valid, but an orchestrator action; author
   side complete.** Re-checked: `grep -rn T0-cap` over the repository finds the entry only in
   `work/p1b/cap*`. The central T0 notes are in `STATE.md` ("Manuscript notes forwarded to v6"),
   which is orchestrator-owned. PLAN §7's "conventions file" does not exist yet
   (`find -iname '*convention*'` finds nothing). So I did not create or edit either of them.
   To make the cross-reference stable, the module docstring of `EG/Spec/Ext/BMLemma25.lean` and
   the module docstring of `EG/Proof/Ext/BMLemma25.lean` now name the entry ID **T0-cap-1**. Once
   the entry is copied, a grep for `T0-cap-1` links the central record to the Lean files.
   **Orchestrator action (unchanged):**
   - copy the T0-cap-1 entry ("Fix round 1", item 1 above) into `STATE.md` (or the §7
     conventions file, once it exists);
   - forward the wording "Let `ε ≥ 2^{-5}` and `m ≥ max(2, 2^{30}/ε²)`" for s1:citLem25 to v6.
2. **cosmetic, roots and `LOCK.json`: valid, but not an issue for this task.** Re-checked:
   `EG.lean` does not import any of the five modules, and `LOCK.json` has no entry for the two
   Spec files. The task forbids editing the root files, and `LOCK.json` is integrator-owned.
   **Integrator action (unchanged):**
   - run `scripts/gen_roots.py`. This adds `EG.Spec.Ext.BMLemma25`, `EG.Proof.Ext.BMLemma25`,
     `EG.Spec.HB.Cap`, `EG.Proof.HB.Cap` and `EG.Lib.Found.LogMono` to `EG.lean`, and
     `EGTest.Cap` to `EGTest.lean`;
   - add `EG/Spec/Ext/BMLemma25.lean` and `EG/Spec/HB/Cap.lean` to `LOCK.json` at the
     statement freeze.
