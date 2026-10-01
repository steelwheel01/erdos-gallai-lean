# TRUST.md.proposed doc-fix pass after the round-4 consistency check (2026-09-26)

Input: `APPROVALS/reviews/trust4.consistency.md` (mismatches M1–M9) and TRUST.md §8 item 8 (the
external red-team expectations for the proposed `Final.lean`).

Rules kept:
* No edit-denied file was touched: `TRUST.md`, `EGCheck/Final.lean`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`, `.claude/**`.
* No git command modified the repository.
* No file of the gate's trusted zone was changed, so all 100 pins still match. After this pass
  `sh formal/scripts/pristine.sh --dev` reports `100 matching their pins` and `DEV-PASS`.
* Red-team runs used `mktemp -d` copies under the harness's read-only bind mount.

## 1. Files written

| File | What |
|---|---|
| `staging/TRUST.md.proposed` | M1–M9 fixed (§2 below), plus one further error found while fixing M1 (§2, "extra") |
| `staging/redteam.sh.proposed` | New: the complete updated `redteam/external/redteam.sh`, guarded by the `Final.lean` in use (§3) |
| `staging/redteam-expectations.proposed.md` | New: why, the exact expectation lines that change, and the integrator steps |
| `work/trust/docfix.md` | This note |

**Why the harness change is staged rather than edited in `redteam/**`.**
`redteam/external/redteam.sh` is pinned by the gate (`c6705aaa…`). Any edit, even a guarded one,
makes `pristine.sh` report `REJECT pin` in strict mode and in `--dev`. That would fail CI's gate
step and the gate red-team baseline until the next `--write-pins`, which is an approval step. So
the edited harness is `staging/redteam.sh.proposed`, which the gate admits as inert data. It is to
be copied over the pinned file in the approval of §8 item 9. This is the "document exactly which
expectation lines change" option of the task, with the concrete file ready to copy.

## 2. Mismatches and fixes in `staging/TRUST.md.proposed`

**M1: Python rule.**
* §2 item 7a now states exactly what `deny()`/`formal_zone()` reject:
  * every `*.py` in `formal/` outside `formal/scripts/` (`pristine.sh` l. 458);
  * every `*.py` at the repository root, i.e. a path without `/` (l. 415–418);
  * in `formal/scripts/`, only pinned files (trusted zone);
  * anywhere: `.pth`, `site/usercustomize.py`, `__pycache__/`, bytecode, native modules,
    `pyvenv.cfg`, `.python-version`.
* It also says that other `*.py` outside `formal/`, such as `code/`, is accepted and never
  executed. I verified this by reading both workflows in full:
  * `release.yml` `build` runs only in the checkout's `formal/`: the gate, elan/Lean,
    `lake exe cache get`, `check_pins.sh`, `lake build`, `tar`.
  * `verify` and `comparator` run everything after the gate from `$RUNNER_TEMP/trusted/formal`,
    and the snapshot holds only `formal/`, `.github/` and `.claude/`.
  * `ci.yml` runs the gate, then from the snapshot: gate red-team, lock, lint, tooling red-team,
    scans. It builds in the checkout's `formal/` and runs the slow red-team from the checkout's
    `formal/`.
  * Every `python3` call in both workflows is `-I` on `formal/scripts/{lock,lint,status}.py` or an
    inline heredoc. The scripts they call (`check_pins.sh`, `comparator.sh`,
    `redteam/{tooling,external}`) likewise use only `python3 -I` on `formal/scripts/lint.py` or
    inline programs.
  * `lock.py`/`status.py` subprocesses are `lake env lean --run scripts/*.lean`.
  * The only Python without `-I` is `redteam/gate/run.sh --demo`, which CI does not pass.
  * CI's gate red-team clones the whole repository (with `code/`) into `mktemp -d` as data.
  * `grep -rn 'code/'` over `formal/scripts`, `formal/redteam` and `.github` finds only the gate
    red-team's temp-clone fixtures (`$C/code/...`).
* §4.2 now gives three `git ls-files` commands that must print nothing. I ran all three on the
  honest tree: all print nothing.
* §4.5 step 1 uses the same wording as §4.2.

**Extra, not in the review.** The §4.5 check
`git ls-files | grep -i -e 'lakefile\.lean' -e 'lean-toolchain'` prints **two** lines on the
honest tree: `formal/lean-toolchain` and the gate red-team fixture
`formal/redteam/gate/fixtures/lakefile.lean.fixture`. So "shows only `formal/lean-toolchain`" was
false. The review's claim that this "prints only formal/lean-toolchain (true)" is itself wrong.
It is replaced by the anchored `grep -i -E '(^|/)(lakefile\.lean|lean-toolchain)$'`, which was
checked to print only `formal/lean-toolchain`, with a note on the fixture.

**M2: committed vs staged `Final.lean`.**
* The intro now says that sentences naming a `staging/*.proposed` file describe that proposal,
  applied together with this file.
* §1 describes the proposed `Final.lean` (`_root_`, upstream imported first) *and* the committed
  one: it imports only `EGCheck.Bridge`, uses `type_of% @Erdos184.erdos_184.{u}`, and its
  `run_cmd` only compares statements. I checked both files.
* §3's list (`type_of%`, `#guard_msgs`, `run_cmd`) is true of both.

**M3: config keys.** §4.3 comparator step 4 now says `config.json` has only four keys and no
`definition_names`. §4.5 step 3 says "four keys … and no `definition_names`" and names them. I
checked `comparator/config.json`.

**M4: `EG_TRUST_REF` order.** §2 item 7c now says:
* tag names, branch names and abbreviated ids fail the hex/length test before any git call;
* a 40-hex non-commit (a tag-object id) passes that test, and is rejected after an optional
  `git fetch` of the id, when `git rev-parse --verify -q "$REF^{commit}"` differs
  (`release.yml` l. 138–142, `ci.yml` l. 70–74);
* the gate repeats both checks (`pristine.sh` l. 527–539).

**M5: `maxSynthPendingDepth`.** Now "not in formal-conjectures' own `lakefile.toml`", with the note
that Mathlib's `lakefile.lean` sets the same value for Mathlib (checked: l. 46; FC `lakefile.toml`
has no such line).

**M6: drifting numbers.**
* §8 item 9: "see the output of `python3 -I scripts/lock.py files --strict`". Measured now: 2
  violations, 115 pending; the number is not written into the file.
* §4.3 step 12: "their number for a given tree is in FinalCheck's output". FinalCheck prints
  `{dups.size} duplicate project …`.
* §8 item 10: "see the output of `python3 -I scripts/lint.py --release`". Today it reports
  `EG/Proof/Main.lean:17` and `EGCheck/Smoke.lean:6`. The requirement to remove
  `EGCheck/Smoke.lean` stays, and the file exists.

**M7: packages.** §2 item 5 now names all ten `lake-manifest.json` packages (checked with `json`)
and says Lake fetches all of them. It no longer claims which of them are in the import closure.

**M8: runner tools.** §2 item 6 now lists coreutils, findutils, `grep`, `sed`, `awk`,
`diff`/`cmp`, GNU `tar` with `zstd`, `curl` (downloads checksum-checked), `/usr/bin/time`, `git`,
`sudo` and systemd, besides `python3` and `bash`/`sh`.

In the same spirit, §2 item 7 now:
* describes the gate's own tools exactly (POSIX `sh`, git, coreutils, `find`, `grep`, `sed`,
  `awk`, `cmp`, `diff`: grepped from `pristine.sh`);
* replaces "runs first in every job" with "directly after the checkout (in `verify`, after a
  `/proc/meminfo`-only memory preflight)".

**M9: reader's recipe.** §4.5 has a new step 0: do the offline check of §4.2 (trust-commit gate,
or the `git diff` review plus the three `git ls-files` checks). Step 1 is declared a spot check.

**Not-mismatch notes of the review, also fixed.** §4.2's prose list of the trusted zone now names
`.github/**` (workflows and CODEOWNERS) and `.claude/**`, and spells out "the lake files".

**Consequential edits.**
* §8 item 8 points to the staged harness and describes the new expectations.
* §8 item 9 and §7 now list five proposals / five pinned files:
  `redteam/external/redteam.sh` is added.
* The intro lists this note.

## 3. External red-team expectations (TRUST.md §8 item 8)

Details and the exact changed lines are in `staging/redteam-expectations.proposed.md`. Summary:
* The guard `hardened_final` holds iff the first line of the in-band `Final.lean` is
  `import FormalConjectures.ErdosProblems.«184»` and it contains
  `type_of% @_root_.Erdos184.erdos_184`.
* When the guard holds, `EXPECT[B1]=EXPECT[C]=inband+oob`. The in-band build must fail with the
  attack's own error: `EXPECT_INBAND_RE` is `[Tt]ype mismatch` for B1 and
  `already contains.*Erdos184\.erdos_184` for C.
* FinalCheck is then run against a **dev final** in the temporary copy. The dev final is the
  committed-style theorem, `import EGCheck.Bridge` plus
  `theorem EGCheck.erdos_184.{u} : type_of% @Erdos184.erdos_184.{u} := EGCheck.Bridge.solution`.
  FinalCheck must match the unchanged `EXPECT_RE`.
* The new option `--final FILE` tests a proposed `Final.lean` in the copy only.
* With the committed `Final.lean`, the expectations and commands are unchanged.

Runs of the staged harness. To run it from `staging/`, a scratch copy had only its `HERE=` line
pointed at `formal/redteam/external`; the file is otherwise identical.

| Run | Result |
|---|---|
| `--final staging/Final.lean.proposed B1 C` | B1: in-band `caught` (`EGCheck/Final.lean:33:2: Type mismatch`), FinalCheck on dev final `[FAIL] statement: type of EGCheck.erdos_184 differs …` → `catch(dev)` OK. C: in-band `caught` (`import EGCheck.Bridge failed, environment already contains 'Erdos184.erdos_184' from FormalConjectures.ErdosProblems.«184»`), FinalCheck `[FAIL] import: … already contains` → `catch(dev)` OK. `REDTEAM: PASS` |
| `--final staging/Final.lean.proposed A2` | in-band `caught`, `n/a`, OK (A2 unchanged). `REDTEAM: PASS` |
| committed `Final.lean`, `B1 C A2` | B1 and C in-band `green`, FinalCheck `catch` OK; A2 `caught`/`n/a` OK. `REDTEAM: PASS` (unchanged behaviour) |

The committed harness with the proposed `Final.lean` gives `REDTEAM: FAIL (2 mismatches)`. That was
measured by the consistency check (§8 item 8) and not re-run here. The other attacks (A, A1, A3,
A4, D, N4, t1–t9, IO) were not re-run. Their Bridges either keep the honest upstream statement or
hijack `type_of%`/`run_cmd`/`#print axioms` themselves, so the proposed `Final.lean` does not
change their in-band outcome. A full run (`--final staging/Final.lean.proposed`, about
10–15 min) is advisable once, at the approval.

## 4. Open for the integrator

* Apply `staging/redteam.sh.proposed` over `redteam/external/redteam.sh` (mode 755) in the §8
  item 9 approval, before `--write-pins`.
* §7's gate hash `a29e7d7d…` is unchanged by this pass: no trusted-zone file was edited.
