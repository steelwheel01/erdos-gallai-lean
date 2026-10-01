# Trust-boundary audit of `formal/` (TRUST.md, check_pins.sh, EGCheck/Final.lean, lint.py, Axioms.lean)

Reviewer: independent auditor (Fable 5.1), 2026-09-26. Read-only audit; all experiments were run in a
scratch directory under `/tmp` against a **byte-identical copy of `EGCheck/Final.lean`**
(sha256 `d070539d…`), with a malicious `EGCheck/Bridge.olean` placed earlier on `LEAN_PATH`. No
repository file was modified.

Question audited: *if one day `lake build EGCheck.Final` passes with the `#guard_msgs` demanding
`[propext, Classical.choice, Quot.sound]`, can a reader trust exactly what TRUST.md says, with
nothing more needed?*

**Verdict: reject (targeted).** The *specification of what is trusted* (TRUST.md items 1–4) is
correct and every pin recomputes exactly. The *specification of how it is enforced* is not: the
documented check (`lake build EGCheck.Final` + `#guard_msgs` + `run_cmd`) is an elaborator-level
check, and I constructed three independent attacks, each confined to the unprotected file
`EGCheck/Bridge.lean`, that make it pass with a false, unproven, or vacuous `EGCheck.erdos_184`
while also passing `scripts/lint.py --release`, `scripts/Axioms.lean` and `scripts/lock.py`. TRUST.md
currently presents lean4checker and comparator as things release CI "adds"; they (or the
equivalents proposed below) are *necessary*. The stage-α trust story is also unspecified. All fixes
are small and listed in §7.

---

## 1. Pins (TRUST.md items 1, 3, 4) — all verified

Recomputed from `.lake/packages` (commands: `git rev-parse`, `git hash-object`, `git rev-parse
HEAD:<path>`, `sha256sum`, `lean --version`):

| Pin | TRUST.md | Recomputed | Match |
|---|---|---|---|
| toolchain name | `leanprover/lean4:v4.33.1` | `lean-toolchain` = same; `lean --version` = `4.33.1 … commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | yes |
| Lean commit | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | `lean --githash` = same | yes |
| formal-conjectures commit | `2424bb480c590237ffbb2cc831ae4cb8977e045a` (2026-09-24) | `git -C FC rev-parse HEAD` = same; commit date 2026-09-24 19:42:19 +0000; `git describe` = `v4.33.1-613-g2424bb4`; worktree clean; remote = `https://github.com/google-deepmind/formal-conjectures.git` | yes |
| `184.lean` blob | `36cc140cb3d8e60b08a842f1691fe9b73602f92b` | `hash-object` (worktree) = `rev-parse HEAD:…` = same | yes |
| `184.lean` SHA-256 | `9f36e4e0…03e020d6` | `sha256sum` (worktree) = `git show HEAD:… \| sha256sum` = same | yes |
| `Decomposition.lean` blob | `a4d3f066158b799e851dd8c6ac511ef2b6731111` | same (worktree and HEAD tree) | yes |
| `Decomposition.lean` SHA-256 | `86bf339a…8fceff2` | same (worktree and HEAD tree) | yes |
| Mathlib commit / tag | `0df444a360eaa60ab8c11dca51a86af692955474` = `v4.33.1` | `rev-parse HEAD` = same; `git tag --points-at HEAD` = `v4.33.1`; worktree clean | yes |

Additional consistency (not in TRUST.md, all fine): the formal-conjectures package's own
`lean-toolchain` is `v4.33.1` and its `lake-manifest.json` pins Mathlib to the same `0df444a3…`;
`lake-manifest.json` of this project has `inputRev` = full SHA for `formal_conjectures`.

The text of `184.lean` and `Decomposition.lean` at the pin matches TRUST.md's rendering of the
statement, `IsCycleOrEdge` and `IsDecomposition`.

## 2. `scripts/check_pins.sh` — runs, covers the pins it claims

Run: all 7 checks print `pin ok` (toolchain text, FC HEAD, Mathlib HEAD, both SHA-256s, both
manifest revs), exit 0. It checks exactly what TRUST.md says it checks (items 1 name, 3, 4).

Gaps (none is a mismatch today; they are checks a release reader would want):

- It does not check the Lean **binary** commit (TRUST.md item 1 lists it). Add
  `lean --version | grep -q 819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- It does not check that the package worktrees are **clean** (`git -C $FC status --porcelain`
  empty). A locally modified `FormalConjecturesUtil/**` or `Mathlib/**` would not change any pinned
  hash but would change what `Erdos184.erdos_184` elaborates to if rebuilt.
- It does not tie the **built `.olean`** of `FormalConjectures.ErdosProblems.184` to the pinned
  source. A stale or hand-crafted olean (e.g. restored from CI's `actions/cache`, which caches
  `formal/.lake/packages/formal_conjectures/.lake` under a prefix `restore-key`) would make both
  `type_of%` and the `run_cmd` agree on a wrong statement. This is only closed by building
  formal-conjectures from source in a fresh clone (or by the comparator's independent Challenge
  build). TRUST.md's "How to check" must say so.
- It does not record `lake --version` or check `$FC/lean-toolchain` == ours and `$FC` manifest
  Mathlib rev == ours (both true today).

## 3. `EGCheck/Final.lean`

### 3.1 What it checks, and whether that is exact

- `theorem EGCheck.erdos_184.{u} : type_of% @Erdos184.erdos_184.{u} := EGCheck.Bridge.solution`
  — `type_of%` of a constant is its declared type with the level parameter instantiated, so the
  statement is the upstream `Expr` verbatim. Confirmed: the `run_cmd` currently passes silently
  and the only failure is the guard (`[propext, sorryAx, Classical.choice, Quot.sound]`).
- `#guard_msgs` compares the full message text after whitespace normalization; `#print axioms`
  sorts with `qsort Name.lt` (`Lean/Elab/Print.lean:245`), so the expected string
  `[propext, Classical.choice, Quot.sound]` is deterministic and exact. `Lean.ofReduceBool`
  (`native_decide`, `bv_decide`, `decide +native`) and `sorryAx` would appear and fail the guard.
- The `run_cmd` looks both constants up by **literal `Name`** (immune to `open`/namespace/alias
  tricks), requires equal level-parameter counts, instantiates `b`'s levels with `a`'s, and uses
  `Expr.equal` — which per `Lean/Expr.lean:814–818` takes binder names **and** binder annotations
  into account (unlike `==`/`eqv`). Universes are compared after renaming; there is one parameter.
  This is as strict as a syntactic comparison can be. Good.

### 3.2 Can an imported module change what Final.lean means while still passing? Yes.

Everything in Final.lean runs inside the Lean **elaborator**, whose behaviour is extended by every
imported module. `elabCommand` tries macros first (`Lean/Elab/Command.lean:507`), and user
`@[term_elab]`/`@[command_elab]` entries are prepended to the builtin ones
(`KeyedDeclsAttribute.Table.insert`, `v::vs`), so an imported module overrides builtins. No current
check (lint, Axioms.lean, lock.py, check_pins) looks for such content. Concretely (each attack is a
complete replacement `EGCheck/Bridge.lean`; the repo's Final.lean is unchanged, byte for byte):

| # | Attack (all code in unprotected `EGCheck/Bridge.lean`) | `lake build EGCheck.Final` | `lint.py --release` | `Axioms.lean` (CI args) | `Axioms.lean --no-sorry` | lean4checker | comparator |
|---|---|---|---|---|---|---|---|
| A1 | `@[term_elab Lean.Parser.Term.typeOf]` returns `PUnit.{u+1} → True`; `@[command_elab Lean.runCmd]` does nothing; `solution : PUnit → True` proved via `Classical.em` | **passes**; `EGCheck.erdos_184 : ∀ (x : PUnit.{u+1}), True`, axioms exactly the three | passes (0 findings) | passes | passes | **not caught** (every declaration is kernel-valid) | caught (statement ≠ Challenge) |
| A2 | `theorem EGCheck.Erdos184.erdos_184 : PUnit → True` (namespace shadowing) | **caught by the `run_cmd`** — but note `type_of%` *did* resolve to the fake, because `theorem EGCheck.erdos_184` elaborates its type inside namespace `EGCheck` | — | — | — | — | — |
| A2b | `export EGCheck.Fake (erdos_184)` inside `namespace Erdos184` | caught at elaboration (real constant chosen; type mismatch) | — | — | — | — | — |
| A3 | `@[command_elab Lean.Parser.Command.printAxioms]` prints the expected line; `solution := sorryAx _ false` | **passes** | **passes** (`\bsorry\b` does not match `sorryAx`) | **passes** (`SORRY …` listed, exit 0) | caught | not caught (`sorryAx` is an ordinary axiom to the kernel) | caught (allow-list) |
| A4 | `set_option «debug».skipKernelTC true in #eval show CommandElabM Unit from … addDecl (.thmDecl {name := \`EGCheck.Bridge.solution, type := <honest upstream type>, value := helper})` where `helper : True` uses the three axioms | **passes** (honest type, honest `run_cmd`, honest axiom list) | **passes** (0 findings: `«debug».` evades `\bdebug\.`; `#eval`, `addDecl` are not tokens) | passes | **passes** (0 violations) | **caught**: replaying the stored declaration through the kernel gives `(kernel) declaration type mismatch, … has type True but is expected to have type ∃ f, …` | caught (replays) |

Evidence: transcripts in this session; scratch files under
`/tmp/claude-0/…/scratchpad/atk{1,2,2b,3,4}/EGCheck/Bridge.lean`, `…/Final.lean` (identical copy),
`…/atk4/Replay.lean` (kernel replay).

Conclusions:

1. **The `run_cmd` is load-bearing** (A2): `type_of%` alone can be redirected by a declaration
   named `EGCheck.Erdos184.erdos_184` in any imported module. Recommend anchoring:
   `type_of% @_root_.Erdos184.erdos_184.{u}`.
2. **`Final.lean`'s own checks are not evidence against an adversarial or careless import** (A1,
   A3, A4). They are only evidence *given* that every module in the import closure contains no
   `@[term_elab]`, `@[command_elab]`, `@[macro]`, `macro_rules`, `elab`, `syntax`, `initialize`,
   `#eval`, high-priority `MonadEnv`/`MonadOptions` instances, or `set_option debug.*`. Today the
   closure under `EG/`, `EGCheck/` is clean (grep: none of these constructs appear), but nothing
   enforces that.
3. **Two independent external checks are both required**, because A1/A3 and A4 are caught by
   different mechanisms: (i) a kernel replay (lean4checker, or comparator's replay) catches A4 and
   any `debug.skipKernelTC`/`addDeclWithoutChecking`/environment hacking, but not a *valid* theorem
   with the wrong statement or a `sorryAx` proof; (ii) an **external** statement-and-axiom check
   (comparator, or a `--run` script using `importModules`, which executes none of the imported
   modules' elaborators) catches A1/A3 but not A4. Together with a from-source build of the pinned
   upstream file (or comparator's Challenge byte-diff) they close every attack above.
4. lean4checker's README (fetched) confirms scope: it "replay[s] the environment … ensuring that the
   kernel accepts all declarations", detects "environment hacking", and "is not an external
   verifier"; it does not check axioms, `sorryAx`, or olean↔source correspondence. comparator's
   README (fetched): builds Challenge and Solution separately with `lake`, exports with
   `lean4export`, "verif[ies] that all declarations used in the statement of all relevant theorems
   in Challenge are the same as in the Solution environment", checks the body against
   `permitted_axioms`, and replays the Solution into the kernel — i.e. it covers A1, A3, A4 and a
   tampered upstream olean, provided Challenge.lean is byte-identical to the pinned `184.lean` and
   is built against the pinned Mathlib.

### 3.3 Smaller observations on Final.lean

- The second `/-! … -/` (line 18) triggers `linter.style.moduleDocstring`; it does not affect the
  guard, but should be `/- … -/` (it would fail under any future `warningAsError`).
- TRUST.md says the check "must print `'EGCheck.erdos_184' depends on axioms: …` through the
  `#guard_msgs`". A **passing** `#guard_msgs` prints nothing (verified: A3/A4 runs exit 0 silently).
  The success criterion is exit 0; the docstring in Final.lean pins the expected list.
- `EGCheck.erdos_184` is never scanned by `scripts/Axioms.lean` in CI: the scan imports the
  `EGCheck` root, which deliberately excludes `EGCheck.Final`. Only the in-file (hijackable)
  `#print axioms` sees it.
- CI runs `lake build EGCheck.Final` with `continue-on-error: true`; fine now, but the release
  workflow does not exist yet, so the release path (lint `--release`, `--no-sorry`, lean4checker,
  comparator, `lock.py check --strict`) has never been exercised.

## 4. `scripts/lint.py` and `scripts/Axioms.lean`

### 4.1 lint.py — evasions found (scratch copy of lint.py on a scratch tree; Lean accepts every spelling)

| Test | Spelling | Flagged? | Caught downstream by |
|---|---|---|---|
| t1 | `axiom` at end of line, name on the next line | no (`(^\|\s)axiom\s` needs trailing whitespace on the same line) | Axioms.lean (`axiomInfo`), `#print axioms`, comparator |
| t2 | `@[simp]axiom bad2 : (1:Nat) = 1` | no (no whitespace before `axiom`) | same |
| t3 | `def c : Char := '"'` then `axiom …`, `set_option debug.skipKernelTC true`, `run_cmd …`, later a real string | **no** — the stripper treats the `"` inside the char literal as a string start and deletes everything up to the next `"` (newlines included), hiding arbitrary lines | axiom: as above; `debug.*`/`run_cmd`: only lean4checker / external checks |
| t4 | `set_option «debug».skipKernelTC true` | no (`\bdebug\.` needs a literal `.`) | lean4checker / comparator only |
| t5 | `sorryAx _ false` | no, even with `--release` (`\bsorry\b` does not match `sorryAx`) | `Axioms.lean --no-sorry`, comparator |
| t6 | `#eval show CommandElabM Unit from liftCoreM (addDecl (.axiomDecl …))` | no (no token) | Axioms.lean (`axiomInfo` and `collectAxioms`) |
| t8 | `macro "close_it" : tactic => \`(tactic\| exact sorryAx _ false)` | no | as t5 |
| t9 | `@[macro Lean.runCmd]`, `@[command_elab …printAxioms]`, `@[term_elab …typeOf]`, `instance (priority := high) : MonadEnv CommandElabM`, `initialize` | no | comparator / external statement check only (see §3.2) |
| ctrl | `attribute [implemented_by …]`, `@[extern …]`, `private axiom`, `native_decide`, `set_option debug.skipKernelTC`, `sorry`, `opaque` | yes | — |

Notes on items in the task list: `decide +kernel`/`decide := true` produce kernel-checked terms
with no extra axiom — sound, nothing to catch. `@[csimp]`, `@[implemented_by]`, `@[extern]`
affect compiled code only; they matter for soundness only through `Lean.ofReduceBool`
(`native_decide`), which the axiom list catches. Unicode look-alikes of keywords do not parse as
keywords (no evasion). Attributes reachable "via other syntax" are a real gap only through
`#eval`/`initialize` meta code (t6/t9), not through spelling.

The lint is therefore hygiene, not a guarantee. It should be documented as such; §7 lists cheap
hardening (string/char-literal stripping, `axiom` at EOL/after `]`, `sorryAx`, `skipKernelTC`,
`«debug»`, and hygiene rules for `#eval`/`initialize`/`@[macro|command_elab|term_elab]`/
`macro_rules`/`elab`/`syntax` in `EG/` and `EGCheck/`).

### 4.2 Axioms.lean — works as designed

- Verified experimentally that `@[implemented_by]` and `@[extern]` **are** detected although
  `importModules` is called with the default `loadExts := false`: `ParametricAttribute.getParam?`
  reads `getModuleEntries`, which `finalizeImport` populates via `setImportedEntries` regardless
  of `loadExts` (`Lean/Environment.lean` ~2380–2405; scratch module `AtkExt` → 2 violations).
- `collectAxioms` and `isUnsafe`/`axiomInfo` are environment-data checks, unaffected by imported
  elaborators (the script runs no imported code). This is why an external `--run` script is the
  right place for the statement/axiom check (§7, R3).
- Gaps: `--no-sorry` is not used in CI (correct now; must be in release CI); the CI invocation
  never imports `EGCheck.Final` (§3.3); `opaqueInfo` is not reported (it is sound — kernel-checked
  body with `Inhabited` — so this is only a hygiene mismatch with the lint).

## 5. Is anything missing from TRUST.md? Are α/β/γ coherent?

Missing or under-stated trusted components:

1. **The Lean frontend, for two things.** (a) The *elaboration* of the pinned upstream text into the
   kernel `Expr` (instances such as `Subtype.fintype` with `Classical.propDecidable`,
   `SetLike.instMembership`, `Real.norm`, `Nat.cast`, `Filter.atTop`). This is inherent and
   standard, but TRUST.md item 3 speaks only of "the text". The reader should be given the
   elaborated form: I dumped `set_option pp.all true in #print Erdos184.erdos_184` and the
   constants it references; **all statement constants are from Init/Mathlib plus exactly
   `Erdos184.IsCycleOrEdge` and `SimpleGraph.IsDecomposition`**, and the bodies of those two
   reference Mathlib only (`Connected`, `IsRegularOfDegree`, `edgeFinset`, `fintypeEdgeSet`,
   `neighborSet.memDecidable`, `Set.PairwiseDisjoint`, `Set.iUnion`, `Subgraph.edgeSet`,
   `edgeSet`, lattice instances on `Set (Sym2 V)`). So the two-file pin is adequate *for the
   constants*, but the elaboration depends on the whole import closure of `184.lean`
   (`FormalConjecturesUtil`, `FormalConjecturesForMathlib`) at the pinned commit — which the commit
   pin covers. Recommend a generated `STATEMENT.md` (pp.all form + constants grouped by module)
   as the artifact the reader actually reads. (b) The `#guard_msgs`/`run_cmd` machinery, which
   TRUST.md implicitly trusts; per §3 it must be replaced as evidence by external checks.
2. **Lake and build caches.** Which oleans get loaded is decided by Lake and `LEAN_PATH`; CI restores
   `formal/.lake/build` and the formal-conjectures build directory from `actions/cache` with a
   prefix restore-key. The release check must be a fresh clone with no restored caches and
   formal-conjectures built from the pinned source.
3. **Mathlib oleans come from `lake exe cache get`** (Mathlib's Azure cache), not from the pinned
   source. lean4checker `--fresh` establishes kernel validity of those oleans, not their
   correspondence to the source at `0df444a3…`. Either state "we trust the Mathlib cache
   infrastructure" or build Mathlib from source for the release check (hours, feasible once).
4. **Lean binary commit** is listed but not checked (§2).
5. **Stage α is incoherent with Final.lean and unspecified.** TRUST.md/PLAN say the stage-α internal
   theorem takes explicit `Prop` hypotheses for Lovász 1968, Haxell 1995 and Euler; CONVENTIONS.md
   says these go on `EG.Proof.mainInternal`. But `EGCheck.Bridge.solution := of_mainInternal
   EG.Proof.mainInternal` and `Final.lean` require an unconditional theorem, so Final.lean cannot
   pass at stage α, and there is no protected stage-α artifact, no guard on *which* hypotheses are
   taken, and TRUST.md does not list the three hypothesis **statements** as trusted items — which
   they are at stage α (a mis-stated or too-strong hypothesis makes the stage-α result vacuous).
   Stage β/γ wording ("only γ may be called formally verified") is coherent.
6. **Release hygiene not yet reflected**: `EGCheck/Smoke.lean` contains `sorry` and is in the
   `EGCheck` root (fails `lint --release`; TRUST/PLAN say it is "replaced by Final.lean" — delete
   it before release). `lakefile.toml` comments reference `scripts/lint.sh` (it is `lint.py`).
7. **Process protections are weaker than README implies.** CODEOWNERS is inert without branch
   protection and a PR flow (the orchestrator commits directly to `main`); `.claude/settings.json`
   denies only file-edit tools (shell edits are unconstrained); `LOCK.json` and `scripts/**` are
   agent-editable. PLAN §4 already says "the integrator's lock check remains the real guarantee";
   TRUST.md/README should say plainly that the real guarantee is the user reading `git diff` of the
   protected files (their hashes are in `LOCK.json`) at each approval and at release.

## 6. What a reader may trust today, precisely

If `lake build EGCheck.Final` passes: **only** that some declaration named `EGCheck.erdos_184` was
accepted by the elaborator in an environment produced by the whole import closure — not that its
type is the upstream statement (A1), not that its proof is kernel-valid (A4), not that its axioms
are the three (A3). With the fixes in §7 (fresh clone + from-source upstream, `check_pins`,
lean4checker replay, external statement/axiom check or comparator), the reader trusts exactly
TRUST.md items 1–4 plus the elaborated statement in `STATEMENT.md` — which is the intended boundary.

## 7. Recommended changes (concrete)

Marked **[TB]** = trusted-boundary change (needs the user after GNG-6); others are integrator changes.

- **R1 [TB] TRUST.md "How to check"** — replace with: (1) fresh clone, no `.lake` restored,
  `lake exe cache get`, formal-conjectures built from source; (2) `./scripts/check_pins.sh`;
  (3) `lake build EGCheck.Final` exits 0 (a passing `#guard_msgs` prints nothing; the expected axiom
  list is the docstring in Final.lean); (4) `lean4checker --fresh EGCheck.Final` (kernel replay);
  (5) `lake env lean --run scripts/FinalCheck.lean` (R3) — external `Expr.equal` of
  `EGCheck.erdos_184` against `Erdos184.erdos_184`, exact axiom set, no `sorryAx`; (6) comparator
  with `Challenge.lean` byte-identical to the pinned `184.lean` and `permitted_axioms` the three.
  State explicitly that (3) alone is not evidence and why (imported modules can redefine
  `type_of%`, `run_cmd`, `#print axioms`, `#guard_msgs`, or skip the kernel).
- **R2 [TB] TRUST.md trusted components** — add: the Lean frontend's elaboration of the pinned text
  (point to `STATEMENT.md`); Mathlib oleans from the cache (or build from source); Lake/fresh-clone
  requirement; Lean binary commit checked by `check_pins`. Change "release CI adds …" to "release
  verification requires …". Change "checked syntactically by a meta-program in the same file" to
  "… and independently by `scripts/FinalCheck.lean` and comparator".
- **R3 scripts/FinalCheck.lean (new)** — `importModules #[EGCheck.Final]` (no imported code runs);
  find both constants by literal name; equal level-param count; `Expr.equal` after level
  instantiation; `collectAxioms EGCheck.erdos_184` == `{propext, Classical.choice, Quot.sound}`
  exactly; also run the Axioms.lean policy over `EG`/`EGCheck` with `--no-sorry`. Run it in release
  CI; keep Final.lean's in-file checks as a fast first line.
- **R4 [TB] EGCheck/Final.lean** — `type_of% @_root_.Erdos184.erdos_184.{u}` (A2); second `/-! -/`
  → `/- -/`. Re-lock the file hash in `LOCK.json` under an approval record.
- **R5 scripts/check_pins.sh** — add Lean binary commit; clean worktrees for FC and Mathlib;
  `$FC/lean-toolchain` == ours; `$FC` manifest Mathlib rev == ours; print `lake --version`.
- **R6 scripts/lint.py** — fix the stripper for char literals (`'"'`, `'\''`), raw strings and
  interpolated strings; match `axiom` at EOL and after `]` (`(^|[\s\]])axiom(\s|$)`); add
  `\bsorryAx\b` (release), `\bskipKernelTC\b`, `«debug»`, `\baddDecl\b` outside `scripts/`; add
  hygiene rules for `#eval`, `initialize`, `@[macro`, `@[command_elab`, `@[term_elab`,
  `macro_rules`, `elab`, `elab_rules`, `syntax`, `instance.*Monad(Env|Options)` in `EG/` and
  `EGCheck/` (allow in `EGTest/` if needed). Document in the file that lint is hygiene, not the
  guarantee.
- **R7 .github/workflows/release.yml (new, may fail until P4)** — `lint.py --release`,
  `lock.py check --strict`, `Axioms.lean --no-sorry` importing `EGCheck.Final`, `lake build
  EGCheck.Final` without `continue-on-error`, lean4checker, `FinalCheck.lean`, comparator with the
  Challenge byte-diff, generated `STATEMENT.md`/`AXIOMS.md` diffed against committed copies. Also
  remove `EGCheck/Smoke.lean` before release, and fix the `lakefile.toml` comment (`lint.sh` →
  `lint.py`) when the file is next touched.
- **R8 scripts/Statement.lean + STATEMENT.md (new)** — generate the `pp.all` form of
  `Erdos184.erdos_184`, `IsCycleOrEdge`, `IsDecomposition` and the constants they reference with
  their defining modules; commit it; CI fails if it changes. TRUST.md points the reader to it.
- **R9 [TB] Stage α** — decide and document: either (a) a protected `EGCheck/FinalAlpha.lean` with
  `theorem EGCheck.erdos_184_of_classical (hL : EG.Spec.Ext.Lovasz…) (hH : …Haxell…) (hE : …Euler…)
  : type_of% @_root_.Erdos184.erdos_184.{u}`, its own `#guard_msgs`, and a `run_cmd`/external check
  that the conclusion equals the upstream type after stripping exactly those three named
  hypotheses; TRUST.md lists the three statement files (and their `LOCK.json` closure hashes) as
  trusted-at-α items and requires the two-reviewer + "False-from-hypotheses" check on them; or
  (b) state that stage α has no checkable release artifact and `Final.lean` fails by design until β.
- **R10 README/TRUST process note** — say that CODEOWNERS needs branch protection to bind, that the
  `.claude` deny rules cover edit tools only, and that the operative guarantee is the user's review
  of diffs to the `LOCK.json`-hashed protected files at each approval and at release.

## 8. Attacks tried (summary)

| Attack | Caught by | Caught? |
|---|---|---|
| A1 imported `@[term_elab typeOf]` + `@[command_elab Lean.runCmd]` → `EGCheck.erdos_184 : PUnit → True` with the three axioms | nothing in the current repo/CI; comparator or external `Expr.equal` script would | no |
| A2 namespace shadowing `EGCheck.Erdos184.erdos_184` | Final.lean `run_cmd` ("different statements") | yes |
| A2b `export` alias into `Erdos184` | elaboration (real constant chosen, type mismatch) | yes |
| A3 `@[command_elab printAxioms]` + `sorryAx _ false` | nothing in current CI (lint `--release` and dev-mode Axioms pass); `Axioms.lean --no-sorry` / comparator would | no |
| A4 `set_option «debug».skipKernelTC true in #eval … addDecl` bogus proof, honest type | nothing in current CI (lint, Axioms `--no-sorry`, Final all pass); kernel replay (lean4checker/comparator) rejects with "declaration type mismatch" | no |
| lint t1–t9 (axiom at EOL, `@[simp]axiom`, char-literal hiding, `«debug»`, `sorryAx`, `#eval addDecl`, macro→`sorryAx`, meta attributes/instances/`initialize`) | lint.py | no (controls t7/t10 caught) |
| Axioms.lean vs `@[implemented_by]`/`@[extern]` in an imported module | Axioms.lean | yes (2 violations) |
