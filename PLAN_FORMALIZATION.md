# Plan: full Lean 4 formalization of the Erdős–Gallai candidate proof, and submission readiness

## 0. Immediate step: hand off to a new cloud chat (done in this chat, before anything else)

The user has created an empty private GitHub repo and will continue in a new Claude Code **cloud** chat linked to it. The new chat will have none of this conversation's memory, and the project files currently exist only locally. So this chat must:

1. **Write handoff files into the local project:**
   - `HANDOFF.md`: the project's state and history, the status (candidate, AI-reviewed only), a map of key files, the decisions made, lessons learned, and the working rules and pause triggers;
   - `PLAN_FORMALIZATION.md`: a copy of this plan;
   - `CLOUD_START_PROMPT.md`: the prompt the user pastes into the new chat.

   Commit.
2. **Prepare a clean copy for pushing** at `~/Desktop/eg-project`: a `git clone` of the local repo with full history, about 15 MB of git data. Check that no file exceeds GitHub's 100 MB limit.
3. **The user pushes it**, which needs their credentials. The agent gives exact commands:
   - `cd ~/Desktop/eg-project`
   - `git remote set-url origin https://github.com/<user>/<repo>.git` (or `add`)
   - `git push -u origin main`

   If git asks for a password, the user either installs GitHub CLI (`brew install gh`, then `gh auth login`) or uses a personal access token. The agent never handles the token.
4. **In the new cloud chat** (connected to that repo), the user pastes `CLOUD_START_PROMPT.md`. The cloud session reads HANDOFF.md and PLAN_FORMALIZATION.md and starts **P0**:
   - the feasibility test in its own sandbox: disk, RAM, CPU, installing Lean v4.33.1 and Mathlib v4.33.1, `lake exe cache get`;
   - then the scaffold.

   Everything then proceeds per §1–§14.

## Context

**Where things stand.** The project has produced a 148-page candidate proof that every n-vertex simple graph decomposes into O(n) cycles and single edges (Erdős Problem #184). The manuscript is `proofs/manuscript/ms.tex` with `s1.tex`–`s7.tex`; the PDF is `EG_candidate_proof_v5.pdf`. Only AI referees have checked it: six review rounds, one major gap found and repaired, and clean verdicts after that, plus blinded calibration.

**Why formalize.** AI review cannot rule out a conceptual gap, or a blind spot shared by the model family. A complete Lean proof of the *independently written* target statement `Erdos184.erdos_184` would settle correctness mechanically. That statement is in google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/184.lean`) and is currently marked `@[category research open]`. What would remain to trust is the kernel, three standard axioms, and one short statement.

**Intended outcome:**
1. A public, reproducible Lean project whose theorem is checked with `exact` against `Erdos184.erdos_184`, using only the axioms {propext, Classical.choice, Quot.sound}.
2. A formalization-aligned manuscript v6 and a short overview paper.
3. A community-verification and submission sequence, carried out by the user.

**If Lean exposes a fatal error:** stop that line, report it honestly, and never weaken statements to force them through.

**Scale:**
- Manuscript: 124 labelled statements, about 85–90 proof obligations, 8,164 LaTeX lines. The Main Theorem's dependency closure is 107 blocks: 86 manuscript nodes and 21 cited results.
- Lean estimate: about 115k lines (range 80k–170k).
- Wall-clock: about 10–20 weeks locally, or 7–12 weeks with cloud machines. This assumes the mathematics survives.

**Decisions already made by the user (2026-09-25):**
- **Resources.** Lift the self-imposed limits to about 15 GB disk and 16 GB RAM, and install Lean + Mathlib, both locally and in the cloud.
- **Compute.** Run on **Claude Code cloud sessions** from the start, working against a private GitHub repo.
  - **The Mac installs no Lean or Mathlib by default.** Builds, integration and CI all run in the cloud (cloud sessions plus GitHub Actions).
  - The Mac keeps only the small git checkout and this orchestrating session (§5).
- **Mathematics.** Apply the simplifications R1–R7 first (§2), producing manuscript v6.
- **Control.** **Pause only on problems** (§6, §9): gates are checked automatically, and the user gets status reports without having to approve each one.

---

## 1. Target and trust boundary

- **Target** (verbatim upstream; Lean v4.33.1, Mathlib tag v4.33.1):
  `∃ f : ℕ → ℝ, (f =O[atTop] fun n ↦ (n:ℝ)) ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ (D.card:ℝ) ≤ f (Fintype.card V)`.
  - `IsCycleOrEdge H := (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1`.
  - `IsDecomposition` means the edge sets are pairwise disjoint and their union is `G.edgeSet`. It is defined in `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`.
- **What a reader must trust:**
  - the kernel and the three axioms;
  - the text of those upstream definitions at a pinned commit;
  - the pinned toolchain.

  Every internal definition is kernel-checked, so a mistaken internal definition can block progress but cannot make the result false.
- **Final check** (`EGCheck/Final.lean`, the only library that imports formal-conjectures):
  - `theorem EGCheck.erdos_184.{u} : type_of% @Erdos184.erdos_184.{u} := Bridge.solution`;
  - `#guard_msgs in #print axioms`;
  - a meta-check that the two types are syntactically equal;
  - `lean4checker --fresh`;
  - leanprover/comparator with a `Challenge.lean` that CI verifies is byte-identical to the pinned upstream source.
- **Staged trust:**
  - **Stage α.** The main theorem takes explicit Prop hypotheses for three published classical results only: Lovász 1968 (path/cycle decomposition), Haxell 1995 (hypergraph matching condition), and Euler (connected, all degrees even ⇒ Euler circuit). No `axiom`, no `sorry`, and no Bucić–Montgomery-specific hypotheses.
  - **Stage β.** Discharge the three: Euler first (Mathlib PRs #41524/#41631 may land), then Haxell, then Lovász.
  - **Stage γ.** Unconditional. This is **required before any claim of "formally verified"**.

---

## 2. Mathematical surface reduction (manuscript v6; done first, each change re-reviewed)

These cut the external formalization from about 45–80k lines to about 10–20k, and remove every Bucić–Montgomery (B–M) black box.

| # | Change | Where | Effect |
|---|---|---|---|
| R1 | Replace B–M Theorem 2 (O(n log* n)) in the three vortex finishes with **Fact EG0**, f(H) ≤ h(log₂h + 2), the elementary long-cycle-removal bound. The finish sizes are at most c\|P\|/L with c ∈ {48, 64, 13}, and x(log₂x + 2) ≤ c\|P\| once L ≥ 4c, which the size condition L ≥ 2¹⁰ already guarantees. | s1:citThm2 (s1.tex:736–749); s4.tex:292–301, 504–517, 536–537, 585–587, 697–700; s7.tex:1478–1480; drop C_BM from N₀ (s1.tex:915–917, 937) | With two re-accountings the text supports (TPV steps ≤ 84\|P\|; PV uses 28 per step), the constants 169, 369, 80, 745 and 1085 are **unchanged**. Otherwise they change linearly, which is harmless. Saves about 25–50k Lean lines. By-product: a formal proof of `erdos_184.variants.n_log_n`. |
| R2 | Replace Freedman with a **Bernstein bounded-differences lemma (BBD)** for independent Bernoulli coordinates, proved by coordinate induction over finite sums. Azuma–Hoeffding is too weak here: it loses a factor ≳ 2¹⁰L³/ρ against a 3% margin. | s1:citFreedman; s3:lemL17s case (b), s3.tex:495–546 | Same constants; about 500–900 lines. |
| R3 | Replace Aharoni–Haxell with **Haxell 1995** (combinatorial alternating trees). The claim inside the proof of Lemma 9_ρ supplies Haxell's condition. | s3.tex:733–770 | Check Haxell's exact constant against the paper. If s̄* moves from 2²⁸ to 2²⁹, T16*'s 2¹³⁵ becomes 2¹³⁶ and PV's own-class threshold becomes 2¹⁴⁶L⁴¹. R6 absorbs all of this. |
| R4 | Replace max-flow in Lemma HB with **m rounds of Mathlib's Hall theorem** on V × [⌈2L²/ε′⌉]. | s3:lemHB (s3.tex:885–965); consumers of b at s4.tex:151–153, 335–337, 396–399, 600–604 and s5.tex:80 | b′ ≤ b + m. Every inequality 2 + b ≤ t keeps its slack. |
| R5 | Truncate vortex levels at J, and replace auxiliary-coin thinning with one monotone-comparison lemma. | s4.tex:112, 348, 573; 176–178, 410–411, 616–617 | Every probability space becomes finite. |
| R6 | State the galactic and size conditions (Γ1–Γ4, (G*), the COL-JV rows, N₀, the tower facts) as `∀ᶠ … in atTop` eventualities. The literal 2840 disappears. | s1:condGamma; s3:lemCOLJV; s7:lemGammaSat | Only existence is used, so no giant numerics are needed. |
| R7 | Add the missing Hall citation (s7.tex:441), declare every dependency that is currently undeclared (32–40 statements), and skip items marked "not used". | s1:tabDAG; s4.tex:708–722 | Housekeeping. |

Lean proves directly:
- B–M Prop 8 and Prop 12;
- the explicit B–M Lemma 25 (the DFS proof, as an invariant relation);
- Cor 22 from Lovász;
- Chernoff in Poisson-binomial form;
- T-joins;
- Euler via subdivision (loops and parallel edges become simple paths).

**Gate G0.** Manuscript v6 includes R1–R7, and a targeted clean-room re-review returns verdict (A) on the changed statements (the same pattern used for the CR1-PV repair).

---

## 3. Lean architecture

**Projects and pinning:**
- Lean `v4.33.1` and Mathlib `v4.33.1`, the same as formal-conjectures. One Mathlib copy on disk.
- No toolchain bump during bulk proving.
- Libraries:
  - `EG`: the proof; Mathlib only.
  - `EGTest`: unit tests, non-vacuity, multigraph falsity.
  - `EGCheck`: bridge and final check; the only library that requires formal-conjectures, pinned by SHA.
- Record the blob SHAs of `184.lean` and `Decomposition.lean`.
- Write files as `module`s if the toolchain requires it, and check at setup whether that avoids rebuilds after proof-only edits.

**Namespaces and modules**, mapped to the manuscript (root `ErdosGallai`/`EG`):

| Layer | Modules | Covers |
|---|---|---|
| Found.Graph | `EdgeSet` (FGraph: explicit `verts : Finset V`, `edges : Finset (Sym2 V)`), `Walk` (list walks, trails, paths, cycles; observations (S), (E), (C)), `Objects` (`Obj`, `IsDecomp`, `fnum`), `Multigraph` (`MGraph N E := E → Sym2 N`, loops allowed), `Orientation` | s1:convGraphs, defObject, factAdd, s4 observations |
| Found.Expander / PathConn | Def 11 on FGraph; balls; Def 7 over **indexed multisets** `(ι → V×V)`; joint routing; monotonicity | s1:citDef7, citDef11, s3:lemMonotone, remMultiset |
| Found.Log / Numerics | `logb 2`, `logStar`, tower; `Numerics.Exact` (small constants via integer powers); `Numerics.Asymp` (eventualities); `Lacunary` | s2:lemLacunary, lemTower |
| Found.Prob | **`FinDist`** (real-weighted finite distributions, `pi`/`prod`/`map`/`bind`, Fubini on prefixes), `Basic` (union bound, `exists_of_prob_pos`, `exists_le_E`, Markov), `Chernoff`, `Bernstein` (BBD), `RandomSets` (ρ-random sets, thinning, uniform permutations and k-subsets) | all probability |
| Ext | `LongCycle` + `EGLog` (Fact EG0), `Lovasz` + `Cor22`, `Haxell`, `BMProp8`, `BMProp12`, `BMLemma25`, `Euler` + `TJoin` + `EvenCycles` + `DirectedCycles` | cited results |
| HB (s2) | `Witness`, `SplitTree`, `Overlap`, `Lemma14Tau`, `Run`, `Basic`, `DegRec`, `Tower`, `Origin` | s2 (21 statements) |
| Link / Lend (s3) | L15+, P13*, L17*, P18*/L19*, L9ρ, T16*, HB via Hall; `Stage1` (the whole stage-1 space, including zone and pool data), `COLTable`, `LemmaCOL` | s3 |
| Vortex (s4) | TPV, PV, VX+ | s4 |
| Light (s5) | Zones, Stages, E1, Expect, Child, Parent, Demoted, K-RED | s5 |
| Chain (s6) | GATE, Cluster, MED, EQ-LPT, PAR, HCC-P, HCCglob, Design, CONC, CONC-L, Lending, Lost, JS-LC, J⁺, Jconsumer, Order, Lent, MIX-C | s6 |
| Quot (s7) | Pool, Cand, Schedule, Round, WellDef, MULT, Simple, Lift, CC, Ultra, Vstar, Pay, Xprime, UHsplit, OneOutcome, Cost, JV⁺* | s7 |
| Main | constants as eventualities, HI″, GammaSat, internal main theorem | s1, s7 |

**Key design decisions:**
1. **Objects.** Internally an object is `inductive Obj | edge (e : Sym2 V) | cycle (c : List V)`, with `WF` (Nodup and length ≥ 3) and `edges`. A decomposition is a `List Obj`; the count is `D.length`.
   - Graphs change constantly (deletions, colour classes, lent sets), so list-based walks avoid transport lemmas.
   - The bridge converts `Obj` → `Subgraph`:
     - a cycle becomes `Walk.IsCycle.toSubgraph`, which is connected and 2-regular on its coe;
     - an edge becomes the single-edge subgraph;
     - the list becomes a `Finset` via `toFinset` (card ≤ length).
2. **Multigraphs** (s5 quotient, s7 layers `B_κ`) use their own small type `MGraph`. The s7 rank split makes each sub-layer simple, so `Q_l` becomes a real `SimpleGraph` on a tagged subtype.
3. **Randomness: custom `FinDist`, not Mathlib measure theory.**
   - Every random object is a finite family of independent labels with real parameters (so uniform counting cannot express them).
   - Every conclusion is deterministic existence, from positive probability or from Markov.
   - "Conditioning" is always fixing a prefix of coordinates, which is Fubini over finite sums.
4. **Constants.**
   - Galactic and size conditions are eventualities (R6). `norm_num`/`nlinarith` is used only for small absolute constants (3.42, 1.12, 0.698, the Chernoff arithmetic).
   - Never compute 2^{2^{2840}}; never use `native_decide`.
5. **The hierarchy.** `Run G` is a record of **choices only**: long-cycle lists, `SplitTree`s for the s=0 and τ-runs, home orders. `Run.Valid` is a Prop. Everything else is a derived `irreducible_def` with characterization lemmas. Existence (s2:propExists) is proved by well-founded recursion.
6. **Downward processing and circularity.** The downward processing (s6:consOrder) and the s7 round step form one recursion on R−l producing the "past". s6 proves MIX-C for **any** consumer family satisfying JC1–JC3, and s7 supplies the instance. This matches s7:remNonCirc.
7. **Fixed rules** ("lexicographically first") become `Classical.choose`/existentials. Only properties are carried forward.
8. **Internal main theorem:** `∃ c, ∀ (V : Type) [Fintype V] [DecidableEq V] G, ∃ D, IsDecomp (edgeFinset G) D ∧ D.length ≤ c·|V|`, proved via HI″ (strong induction over n = |V|).
   - The bridge transports to the universe-polymorphic target along `Fintype.equivFin`.
   - It sets `f := fun n ↦ c·n`.

---

## 4. Blueprint, statement locking, and CI

- **Blueprint** (leanblueprint):
  - Generated from the manuscript by `usesgen`: all 124 environments, with `\uses{}` taken from backward `\ref`s in statements **and proofs**. The `\deps` lines under-report.
  - Each Lean declaration carries `@[ms "s2:lem14tau"]`.
  - `checkdecls` runs in CI. `\leanok` is written only by CI.
- **Statement/proof split.**
  - Frozen statements are `abbrev X : Prop := …` in protected `EG/Spec/**` files, and definitions live in `EG/Defs/**`.
  - Provers edit only `EG/Proof/**`.
  - `EG/Proof/Main.lean` consumes only the Spec props.
- **Lock** (`lake exe eg_lock`):
  - For every Spec/Defs constant it records the `pp.all` type hash, a closure hash over the EG definitions it uses, and the file SHA-256, together with the manuscript label and an approval file.
  - Changing a Tier-1 statement requires two independent reviewer verdicts (one cross-model) and an `APPROVALS/<date>-<label>.md` record, and the user is notified.
  - Changes to the trusted boundary (target pin, allowed axioms, TRUST.md) need the user (§9).
- **Tools** (`lean_exe`s using `collectAxioms`):
  - `msreport`: per-label status; fails if the **Lean** dependency graph has an edge that is missing from the blueprint.
  - `defcheck`: no data definition depends on `sorryAx`.
  - `axiomcheck --prefix`.
  - `eg_status`: dashboard plus a sorry-frontier **ratchet**, where the set may only shrink.
- **CI (GitHub Actions, ubuntu):**
  - build `EG EGTest EGCheck`;
  - lint with forbidden tokens: `sorry` (release only), `admit`, `axiom`, `native_decide`, `decide +native`, `bv_decide`, `implemented_by`, `@[extern]`, `unsafe`, `ofReduceBool`, `trustCompiler`, `debug.skipKernelTC`, `maxHeartbeats 0`;
  - the lock check;
  - an environment axiom scan;
  - the dashboard.

  The release workflow adds `lean4checker --fresh`, comparator, the Challenge byte-diff, and a generated `AXIOMS.md`.
- **Defence in depth** (set up in P0 as part of this plan; applies only inside the new `~/eg-formal` repo): a project-local `.claude/settings.json` that denies prover agents edits to `EG/Spec/**`, `EG/Defs/**`, `EGCheck/**`, the lock file, `scripts/**` and `.github/**`, plus CODEOWNERS on those paths. The integrator's lock check remains the real guarantee.

---

## 5. Execution and agent orchestration

- **One-time setup by the user** (it needs their accounts, so the agent can't do it):
  - (a) create a **private GitHub repo**, e.g. `eg-formal`;
  - (b) connect GitHub to Claude Code (claude.ai → Code: install or authorize the Claude GitHub app for that repo);
  - (c) run `gh auth login` on the Mac, so this session can push the initial scaffold.

  The agent never handles credentials. After this, everything else is automated.
- **Mac footprint: only a git checkout** (tens of MB) plus this orchestrating session. **No Lean or Mathlib on the Mac.** That saves about 10–13 GB.
- **Claude Code cloud sessions do the work:**
  - **Provers.** Remote agents (Agent tool with `isolation: "remote"`, launched from this session) each clone the repo, install elan and Lean v4.33.1 in their own sandbox, run `lake exe cache get` for Mathlib v4.33.1, work on one batch of `sorry` items on a branch `work/<item-id>`, and push the branch plus a short JSON result file.
  - **Integrator.** A dedicated cloud session (or GitHub Actions) merges branches into `main` after the protected-path check, the lock check, a build and the lint.
  - **This session.** It orchestrates, reads results from the repo (cloud sessions cannot message back) and reports to the user.
  - **CI** (GitHub Actions on ubuntu) builds every merge. Watch the private-repo Actions minutes quota; cache `.lake`.
- **Per-sandbox tooling** (in the repo): `scripts/check.sh` runs `lake env lean` on one file, with a wall-clock limit (`timeout` on Linux) and an axiom check. It uses `LEAN_NUM_THREADS` sized to the sandbox's CPU count.
- **P0 cloud feasibility test** (must pass before relying on the cloud). One remote agent reports its sandbox's disk, RAM, CPU, session-time and network limits, then runs `lake exe cache get` and `lake build` on a small EG module, and records timings.
  - If Mathlib doesn't fit (about 12 GB disk, or at least about 8 GB RAM per Lean process), or remote agents aren't available on the user's plan, that is a **pause point**.
  - Fallbacks, for the user to choose: run locally on the Mac (limits already lifted; about 10–13 GB), or rented VMs.
- **Concurrency:** as many parallel remote agents as the service allows. Start with 8, and scale up while merges keep pace.
- **Work items.**
  - `work/nodes.json` is generated from `outline.txt` and the LaTeX.
  - `work/queue.json` has a single writer, so the run can resume.
  - Every `sorry` is a `prove` item. Priority = risk × fan-in × critical-path depth.
- **Roles:**
  - statement authors (≤ 8 statements per run);
  - 2 clean-room statement reviewers plus a back-translator;
  - sketchers;
  - provers (12–24 concurrent locally; ≤ 25 checks or 60 minutes per attempt; at most 5 helper lemmas each);
  - a falsifier after 3 failed attempts;
  - a repairer;
  - an integrator (a script, with an agent for conflicts);
  - a math liaison;
  - final auditors.
- **Lessons from this project:**
  - Sub-agents write to files and return short JSON; one giant final message stalls, as the first manuscript attempt showed.
  - Blind calibrations must sanitize paths; the first calibration attempt leaked plant locations.
  - Reviewers under-call severity, so every definition-vs-use mismatch must be resolved.
- **Stuck items.** The falsifier tries small instances with `decide`/`plausible`, then explicit counterexamples, then vacuity. The outcome is classified as:
  - prover weakness;
  - a false helper;
  - a misformalized Spec;
  - **a manuscript error**, which triggers §7.

---

## 6. Phases, milestones and go/no-go gates

Gates are checked automatically, and the user gets a short status report at each one. Work **pauses only on a pause trigger (§9)**. A gate that passes does not wait for approval.

| Phase | Deliverables | Exit gate (machine-checkable where possible) |
|---|---|---|
| **P0 Setup** (2–4 days) | User's one-time GitHub setup (§5). Agent pushes the scaffold repo (pinned toolchain, lakefile, CI, scripts, `.claude/settings.json` deny rules). Cloud feasibility test. Smoke test in the cloud: `theorem t.{u} : type_of% @Erdos184.erdos_184.{u} := sorry` elaborates | **GNG-1:** upstream 184 builds on v4.33.1 inside a cloud session; the sandbox has enough disk and RAM for Mathlib; remote agents can push branches. On failure, pause and offer the local-Mac or VM fallback |
| **P1 Math v6 + foundations + pilot** (1.5–2.5 weeks) | R1–R7 written and re-reviewed (G0). Design decisions frozen; `EG/Defs` with unit tests; FinDist API. **Bridge proved** with the internal main theorem as `sorry`. Pilot nodes: s6:lemGATE, s3:lemL15p, s7:thmHI, s2:lemCap (Lemma 25 as `sorry`) | **GNG-2:** pilot proved; token and time projection recorded as the baseline for the overrun trigger. Definitions, TRUST.md and the bridge are approved by two independent agent reviews and logged in `APPROVALS/` (the user is notified; they are not a blocking step) |
| **P2 Statement freeze** (2–3 weeks) | Every node in the Main closure plus the External statements, as locked Specs. `Main` proved from Specs (HI″ + cost line + GammaSat). All node sketches compile against their dependencies' Specs. Statement review Q1 | **GNG-3:** `msreport` shows the blueprint graph equals the Lean graph and no data definition uses sorry; Q1 mutant recall ≥ 90%. About 15 interface statements get two agent reviews plus a cross-model review, and the user receives the list |
| **P2b De-risking probes** (overlaps P2 and P3; 3–5 weeks) | Each probe proved in full modulo its declared `sorry`d inputs. **P-1:** s7 lift, Q_l simple, MULT, WellDef (assuming J⁺). **P-2:** routing engine GATE/MED/EQ-LPT/PAR/HCC-P → JS-LC → J⁺. **P-3:** τ-rules → Lemma 14^τ → thin cut → GC → ORIGIN → CONC/CONC-L(iv). **P-4:** CR1-PV sites: PV(c) core, Child/Parent Steps 1–9, COL(c), COL-JV rows 4, 7, 8, (P4). Cheap numeric probes: Cap(i), the Lemma 17* margin, the WellDef(iii) SDR bound | **GNG-4 (critical):** `msreport --frontier` shows each probe's frontier ⊆ its declared inputs. **Any confirmed manuscript error stops everything downstream (§7).** |
| **P3 Bulk proving** (5–9 weeks locally) | Foundations → Ext → s2 → s3 → s4 → s5 → s6 → s7 lanes in parallel; sorry ratchet to 0 | **GNG-5 at 50%:** re-plan if the projected overrun exceeds 50%. Per-milestone `axiomcheck --prefix` for EG.Found, EG.Ext, EG.HB, EG.Link/Lend, EG.Vortex, EG.Light, EG.Chain, EG.Quot |
| **P4 Closure and audit** (1–2 weeks) | Stage α → β → γ (discharge Euler, Haxell, Lovász); release lint; Q2–Q4; fresh-clone reproduction on Linux and macOS | **GNG-6:** `#print axioms EGCheck.erdos_184` = [propext, Classical.choice, Quot.sound]; zero sorry; lean4checker and comparator pass; syntactic type equality with upstream |
| **P5 Packaging** (2–4 weeks, overlaps P4) | Manuscript v6 aligned with Lean (with an errata file), overview paper, blueprint site, formalization paper, disclosure | **GNG-7:** user (and Lean expert) sign TRUST.md, AXIOMS.md and the disclosure |
| **P6 Announcement** | §10 sequence | **GNG-8** before any journal: at least one human mathematician has read the overview |

---

## 7. Policy when formalization finds a problem

Rule 0: a Lean proof that won't go through is not a refutation. Classify only when there is an explicit counterexample or a proof of the negation, and both a formalizer agent and a math-review agent agree.

| Class | Action |
|---|---|
| T0 Encoding (log base, ceilings, empty sets) | Fix the Lean only; record it in a conventions file |
| T1 Minor (statement true, proof gap) | Patch the manuscript proof; ledger entry; the Lean proof counts as the review |
| T2 Major (statement false, repairable; like PV-ARC-END) | Minimal counterexample → manuscript repair → recompute constants for every consumer, found from the **Lean** dependency graph → re-lock the Spec (approval) → targeted clean-room re-review of consumers not yet formalized → version bump |
| T3 Fatal (no repair within the architecture) | Freeze downstream; formalize the counterexample if feasible; mark the manuscript "refuted at ⟨label⟩"; tell the user immediately; publish the verified independent parts honestly. Any repair counts as a new candidate |

---

## 8. Quality gates

- **Q1: statement fidelity.**
  - Two clean-room reviewers per statement; one from a different model family where possible.
  - A back-translation diff.
  - A too-easy detector: `aesop/simp_all/omega/grind/exact?` for 60 s, plus a `False`-from-hypotheses check.
  - Definition unit tests, e.g. f(K₃) = 1, f(star) = number of edges, K_n is an expander, a long path is not.
  - Planted-mutant calibration, with a recall gate of ≥ 90%.
- **Q2: axiom audit.**
  - `#guard_msgs` on `#print axioms`;
  - an environment scan for `axiom`, `unsafe`, `extern`, `ofReduceBool` and `trustCompiler`;
  - lean4checker;
  - comparator, with the nanoda kernel if available.
- **Q3: exact equality with the target.**
  - `EGCheck/Final.lean` checks `type_of%` plus syntactic `Expr` equality;
  - a fresh-clone reproduction using only the README command;
  - 3 independent auditor agents plus 1 human Lean expert.
- **Q4: "proves too much" and non-vacuity** (`EGTest`):
  - **T1:** in Lean, the multigraph analogue is **false**: two vertices joined by m parallel edges need at least m/2 objects.
  - **T2:** dependency assertions showing that the simplicity-dependent lemmas (DegRec kind (b), Cap(ii), PV(c), GATE, CONC(ii), JS-LC Step 5, lemUltra) really use the simple-graph facts.
  - **T3:** any f satisfying the target has f(n) ≥ (n−1)/2 (via K_n). Optionally also formalize `erdos_184.variants.lower_bound`.

---

## 9. Pause triggers and user actions ("pause only on problems")

**Already decided (H0):** resource limits lifted, Lean and Mathlib allowed, Claude Code cloud sessions, simplify first, pause only on problems.

**The agent pauses and asks only when:**
1. **A math problem:** a confirmed T2 or T3 manuscript error (§7). A T2 error is repaired and re-reviewed automatically, and the user is told. A T3 error stops the line and waits for the user.
2. **A budget or time overrun:** the projected cost or duration exceeds the P1 baseline by more than 50% (GNG-5), or a cloud feasibility or resource failure occurs (for example Mathlib doesn't fit in cloud sessions).
3. **Credentials, accounts or payments:** creating the private GitHub repo and `gh auth login` (P0); any cloud-account or billing step. **The user always does these.**
4. **Anything public or irreversible:** making the repo public, publishing the blueprint site, Zulip, forum or formal-conjectures posts or PRs, arXiv, journals, emails to experts. The user writes and sends all of them.
5. **A change to the trusted boundary:** the pinned target commit, the allowed axioms, or TRUST.md after GNG-6.

**Non-blocking by default:**
- Definition and statement approvals are handled by two independent agent reviews plus a cross-model review, logged in `APPROVALS/`.
- Weekly progress reports.
- Gate status reports.

**Strongly recommended, and non-blocking:**
- the user recruits a Lean expert (20–40 hours, paid) to spot-check TRUST.md, the bridge and about 15 interface statements before release;
- human mathematicians review the math, in parallel, starting now with EXPERT_REVIEW_PACKAGE.md.

**Before arXiv or a journal (blocking, as it's public):** at least one human mathematician has read the overview, authorship is settled, and the references have been checked by hand.

---

## 10. Submission-readiness package and announcement sequence

- **Repo** (made public only at GNG-6/7):
  - README with the claim, the trust boundary and a one-command reproduction (`lake exe cache get && lake build EGCheck && lake env lean EGCheck/Final.lean`);
  - TRUST.md, AXIOMS.md (generated by CI), AI_DISCLOSURE.md, CITATION.cff;
  - a Zenodo DOI for the release.
- **Blueprint site** on GitHub Pages, with a dependency graph coloured by `\leanok` and doc-gen4 docs.
- **Papers:**
  - an overview paper (15–25 pages): result, architecture, "where log* disappears", formal verification and trust boundary, limitations;
  - manuscript v6, cleaned up: AI-review codes moved to a supplement, a real bibliography checked by a human, the randomness schedule moved earlier, the errata;
  - a formalization paper (cs.LO; venues ITP, CPP or Annals of Formalized Mathematics).
- **Announcements, in order:**
  1. Lean Zulip: the user's own post, asking for scrutiny of the bridge.
  2. After about 1–2 weeks, the erdosproblems.com #184 forum thread, with courtesy notes to Bucić, Montgomery and the site maintainer beforehand.
  3. A formal-conjectures issue and PR adding `@[formal_proof using lean4 at "<commit permalink>"]` and following their PROOFS.md checklist. Moving the problem to `research solved` is the maintainers' call.
  4. arXiv: math.CO, with the formalization cross-listed to cs.LO. This needs an endorser, and AI policy applies: the authors take full responsibility, and unchecked LLM content risks a ban.
  5. A journal, after feedback: Annals / JAMS / Inventiones / Forum of Math Pi for the mathematics; ITP/CPP for the formalization.
- **Authorship:** only humans can be authors. The user takes full responsibility, with an honest AI disclosure, and co-authors only with their consent. Say "candidate" until GNG-6/7 and "formally verified" only after.

---

## 11. Timeline, resources, budget

- **Wall-clock**, if the mathematics survives and cloud sessions pass the P0 feasibility test: about **7–12 weeks** with Claude Code cloud sessions. The local-only fallback is about 10–20 weeks.
- **Mac:** only the git checkout and this session. A local Lean install is an optional fallback (24 GB RAM, 10 cores and about 700 GB free are enough if it is ever needed).
- **Tokens:** roughly 2–8 billion input (mostly cache reads) and 80–300 million output in total. **Recalibrate after the P1 pilot**, using tokens per accepted Lean line. Each phase gets a hard cap, and the orchestrator pauses at 80% of it.
- **Human time:**
  - user: 3–6 hours per week plus checkpoints;
  - Lean expert: 20–40 hours, paid, recommended;
  - math experts: in parallel, starting now with EXPERT_REVIEW_PACKAGE.md.

---

## 12. Top risks and mitigations

1. **The manuscript has a fatal gap** (high likelihood, critical impact). Mitigations: probes first (P2b); stop-the-line; human expert review in parallel from day 1.
2. **Misformalized definitions or statements.** Mitigations: Q1; the bridge proved in week 1; the kernel checks every interface once sketches compile.
3. **Agents game the checks** (weakened statements, hidden sorry, axioms, native code). Mitigations: Spec/Proof split; lock hashes; deny rules; axiom audits; lean4checker; comparator.
4. **The probability layer is hard in Lean.** Mitigations: FinDist; existential ("an outcome exists") statements; BBD instead of Freedman.
5. **External theorems grow** (Lovász 3–6k lines, Haxell 2–4k, Lemma 25 1–2k). Mitigations: start them in parallel with P2; use the stage-α hypotheses meanwhile.
6. **Galactic numerics.** Mitigation: eventualities (R6).
7. **Local compute, memory or disk ceilings.** Mitigations: slot pool, watchdog, no worktrees, cloud option.
8. **Upstream drift.** Mitigations: pinned SHA; a vendored copy with an `rfl` drift check.
9. **Orchestration failures and token overrun.** Mitigations: a single integrator; file outputs; phase caps; GNG-5.
10. **Community and authorship problems** (premature publicity, arXiv policy). Mitigations: nothing public before GNG-6/7; the user writes every post; references checked by hand.

---

## 13. Verification (how we'll know it worked, end to end)

1. From a **fresh clone** on a clean GitHub Actions Linux runner and in a fresh cloud session: `lake exe cache get && lake build EGCheck` succeeds. A macOS run is optional, and only with the user's OK, since it needs about 12 GB on the Mac.
2. `lake env lean EGCheck/Final.lean` prints exactly `'EGCheck.erdos_184' depends on axioms: [propext, Classical.choice, Quot.sound]`. The `#guard_msgs` test passes.
3. The meta-check confirms that `EGCheck.erdos_184`'s type is syntactically identical to `Erdos184.erdos_184`'s at the pinned upstream commit. CI shows `Challenge.lean` is byte-identical to upstream.
4. `lean4checker --fresh` and comparator (permitted axioms: the three) pass.
5. The release lint finds zero forbidden tokens, and the environment scan finds no `axiom` or `unsafe` declarations in `EG*`.
6. `EGTest` passes: the multigraph analogue is false, the non-vacuity lower bound holds, the dependency assertions hold, and the definition unit tests pass.
7. The blueprint is fully `\leanok`, and `msreport` shows the Lean dependency graph equals the blueprint graph.
8. Three independent auditor agents and one human Lean expert confirm 1–7 independently.

---

## 14. Critical files

- **Manuscript sources** (v6 edits for R1–R7): `proofs/manuscript/s1.tex` (citations, constants, DAG), `s3.tex` (Freedman, AH, HB), `s4.tex` (finishes, levels), `s7.tex` (Hall citation, GammaSat).
- **Inputs for the blueprint and work queue:** `proofs/manuscript/outline.txt`, `EXPERT_REVIEW_PACKAGE.md` (probe targets), `crossmodel_review.md` (simplicity sites).
- **Reference only:** `code/e2e/e2e_sim.py` (round-step bookkeeping model; not a proof).
- **To create:** a new repo `~/eg-formal/` with the structure in §3–4.
- **Project records:** `STATE.md`, `LEDGER.md` and `SUMMARY.md` get a formalization section.
