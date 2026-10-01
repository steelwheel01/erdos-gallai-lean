# Round-5 consistency re-check of `staging/TRUST.md.proposed` (independent checker, Fable 5.1)

Date: 2026-09-26. Read-only check; the only repository file written is this one. No git command
that changes the repository was run. Nothing edit-denied was touched.

Task: re-verify every factual claim of `staging/TRUST.md.proposed` (revision of 12:39, after the
doc-fix pass `work/trust/docfix.md`) against the actual files, with special attention to the items
M1–M9 of `APPROVALS/reviews/trust4.consistency.md`.

Tree checked: HEAD `f3f1ff394868f9eb774dd6bf2ddc40510756ca64` ("Trust consolidation …", 12:26).
Working-tree changes are outside the trusted zone (`EG/**`, `EGTest/HB.lean`, `work/**`,
`staging/**`), so the pinned files read here are the committed ones: `sh scripts/pristine.sh --dev`
reports `trusted zone 100 files, 100 matching their pins`, gate SHA-256
`a29e7d7dc3dfa93f9b9e4fa42ba3431f4308b2b2eb879f1db6cddcd83c94cd9b`.

## Verdict: CONSISTENT. M1–M9 are all fixed; no factual error found

Every hash, commit id, pin, count, workflow step, script option and harness behaviour named in the
document matches the files (§2 below). The three wording nits in §3 are non-blocking: none makes a
sentence false, none changes what a reader must trust.

## 1. Status of M1–M9 (trust4.consistency.md §2)

| Item | trust4 finding | Status in the 12:39 revision | Evidence |
|---|---|---|---|
| M1 | "no `*.py` outside `formal/scripts/`" (false: `code/*.py` is tracked and accepted) | **Fixed.** §2 item 7a: "every `*.py` file in `formal/` outside `formal/scripts/`, and every `*.py` file at the repository root … Other `*.py` files outside `formal/`, such as those under `code/`, are **accepted**". §4.2 and §4.5 say the same and give three commands. | The three §4.2 commands print nothing on HEAD (rc 1 from `grep`). `git ls-files` has 10 `code/**.py`; `pristine.sh` `deny()` l. 415–418 and l. 458 match the text. §4.5's `grep -i -E '(^|/)(lakefile\.lean|lean-toolchain)$'` prints only `formal/lean-toolchain`; the plain substring grep also prints `formal/redteam/gate/fixtures/lakefile.lean.fixture`, exactly as §4.5 says. |
| M2 | §1 described the staged `Final.lean` as if committed | **Fixed.** Intro l. 17–19 states the one kind of exception (a sentence naming a `staging/*.proposed` file describes that proposal). §1 l. 73–78 now describes both: the proposal (`type_of% @_root_.Erdos184.erdos_184.{u}`, upstream imported first and directly) and the committed file (imports only `EGCheck.Bridge`, `type_of% @Erdos184.erdos_184.{u}`, `run_cmd` only compares the two statements). | `EGCheck/Final.lean`: `import EGCheck.Bridge` only; `type_of% @Erdos184.erdos_184.{u}`; `run_cmd` compares universe-parameter counts and `Expr.equal` of the two types. `staging/Final.lean.proposed`: first line `import FormalConjectures.ErdosProblems.«184»`, `_root_`, origin/kind checks. §3's "its `type_of%`, the `#guard_msgs` on `#print axioms` and the `run_cmd` meta-check" holds for both files. |
| M3 | "five fields" of `config.json` | **Fixed.** §4.3 comparator step 4: "These are its only four keys; there is no `definition_names` key". §4.5 step 3: "the four keys … and no `definition_names`". | `comparator/config.json` has exactly `challenge_module`, `solution_module`, `theorem_names`, `permitted_axioms`. |
| M4 | tag-object ids said to be rejected "before git resolves the value" | **Fixed.** §2 item 7c: tags, branches, abbreviated ids fail the hex-and-length test before any git call; a 40-hex non-commit id passes that test and is rejected afterwards by `git rev-parse --verify -q "$EG_TRUST_REF^{commit}"` (after a `git fetch` of the id if absent); the gate repeats both checks. | `release.yml` gate steps (`case … *[!0-9a-f]*`, `${#EG_TRUST_REF} -eq 40`, `git cat-file -e … \|\| git fetch`, `rev-parse --verify -q … = $EG_TRUST_REF`) in `verify` and `comparator`; `pristine.sh` l. 527–538 (`REF_OK`, `rev-parse`, "names a tag object"). |
| M5 | `maxSynthPendingDepth = 3` "not upstream" | **Fixed.** §2 item 5: "set there and not in formal-conjectures' own `lakefile.toml` … (Mathlib's `lakefile.lean` sets the same value for Mathlib's own modules.)" | `grep maxSynthPendingDepth`: `lakefile.toml:13` and `.lake/packages/mathlib/lakefile.lean:46` only; the FC `lakefile.toml` does not set it. |
| M6 | stale counts (PENDING entries, realized duplicates, sorry files) | **Fixed.** §8 item 9 refers the reader to the output of `lock.py files --strict`; §4.3 step 12 says "their number for a given tree is in FinalCheck's output"; §8 item 10 refers to `lint.py --release` output and names only `EGCheck/Smoke.lean`. | Today: `lock.py files --strict` → "2 violations, 115 pending (strict)"; `lint.py --release` → `EG/Proof/Main.lean:17`, `EGCheck/Smoke.lean:6`; `EGCheck/Smoke.lean` exists. No number in the document can drift any more. |
| M7 | import-closure package list incomplete | **Fixed.** §2 item 5 lists the ten manifest packages by name: `mathlib`, `formal_conjectures`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`. | `lake-manifest.json` has exactly these 10 packages, all present under `.lake/packages`. |
| M8 | runner tool list incomplete | **Fixed.** §2 item 6 now lists `python3`, `bash`/`sh`, coreutils, findutils, `grep`, `sed`, `awk`, `diff`/`cmp`, GNU `tar` with `zstd`, `curl` (checked against the SHA-256 pins), `/usr/bin/time`, `git`, `sudo`, systemd; Go separately. | Both workflows use each of these (`awk` on `/proc/meminfo`, `diff -u`, `tar --zstd`, `curl -sSfL`, `/usr/bin/time -v`, `sudo systemd-run` via `comparator.sh`, `find | xargs sha256sum` in CI). |
| M9 | §4.5 kept spot checks without the §4.2 offline check | **Fixed.** §4.5 step 0: "First do the offline check of §4.2 … Step 1 below is only a spot check … it does not replace §4.2." | Text present at l. 541–544. |

## 2. Other claims re-verified (all correct)

**Intro / history.** `work/trust/consolidate.md` and `work/trust/docfix.md` exist; the earlier notes
`gate2, finalcheck2, tooling, bridge, external` exist. Round-3 gaps as stated.

**§1.** Statement text, namespace and `open` line match `comparator/Challenge.lean` (= Solution
header, verbatim). `STATEMENT.md` imports only `FormalConjectures.ErdosProblems.«184»`
(`Statement.lean` l. 200, `trustLevel := 0`). Closure 1572 declarations; counted from the
"by module" block: Init 614, Mathlib 949, Batteries 6, FormalConjectures 2 + ForMathlib 1 (= 3).
The three `EG-PIN` lines are byte-identical to `STATEMENT.md` l. 13–15; `lean --githash` =
`819816b2…`; `FinalCheck.lean` `pinFile := "TRUST.md"`, `--pin-file`. Both artifacts apply
`EGCheck.Bridge.of_mainInternal_unfolded` (`EGCheck/BridgeCore.lean` l. 40) to
`EG.Proof.mainInternal` (`comparator/Solution.lean` l. 72; `EGCheck/Bridge.lean` l. 28 and
`solution := of_mainInternal EG.Proof.mainInternal`). `Challenge.lean` SHA-256 `9f36e4e0…`,
blob `36cc140c…`, `cmp` identical to the package file.

**§2.**
* Item 1: `comparator.sh tools` checks `lean --githash`, overrides both tools' `lean-toolchain`
  to v4.33.1, applies `comparator/patches/*.patch`; release.yml calls `tools` then
  `run --release --system-unit --tools`. `lint.py` forbids `unsafe`/`partial` (l. 391/403);
  FinalCheck `policy` forbids `unsafe`, `@[extern]`, `@[implemented_by]`, `@[init]`; `replay` uses
  `Environment.replay` (l. 864).
* Item 3: FC HEAD `2424bb48…` dated 2026-09-24; blobs `36cc140c…`/`a4d3f066…`, SHA-256
  `9f36e4e0…`/`86bf339a…` (worktree and `HEAD:`), also checked by `check_pins.sh`.
* Item 4: Batteries `4488d40d…`, its 6 declarations as named (`STATEMENT.md` l. 212–213);
  Mathlib `0df444a3…` = tag `v4.33.1` (`git describe --exact-match`). Provenance: `STATE.md`
  l. 269 (cache hosts unreachable, Mathlib from source), l. 298–299 ("P0 — DONE", 2 h 29 min on
  4 cores).
* Item 6: only `mathlib` and `proofwidgets` have a `lakefile.lean`; `check_pins.sh` checks every
  package HEAD and clean worktree, lakefile/manifest revs, `lean --githash`, and runs in all three
  release jobs. elan `v4.2.4` and the Lean archive SHA-256-pinned; actions pinned by SHA; Go
  unpinned (`go version` only).
* Item 7: gate first after checkout in every job (verify: `awk` preflight on `/proc/meminfo`
  first, then checkout, then gate). 7a rejections match `deny()`/`formal_zone()`; snapshot copies
  only `formal/`, `.github/`, `.claude/` (l. 580); every `python3` call in the workflows and in
  `scripts/*.sh`, `redteam/**/*.sh` (as CI runs them) uses `-I`; `PYTHONSAFEPATH=1` in both
  workflows; `redteam/gate/run.sh` clones the repository with `git clone` and executes nothing
  (the `--demo` branch is not used by CI). 7b = `in_trusted_zone` l. 251–259; strict mode =
  `hash-object --no-filters` against HEAD, file list from `find`. 7c: `info gate script sha256`
  is printed by every run; `git show $EG_TRUST_REF:formal/scripts/pristine.sh` and `--trust-ref`
  in both trusted jobs; `::warning::` and the checkout's gate without the variable. Snapshot:
  `chmod a-w`, empty `formal/.lake` (`--link-lake` symlink in CI only). Unpinned list: `LOCK.json`
  (read by `lock.py` l. 36), `status/**` (read by `status.py`), `CONVENTIONS.md` (only hashed by
  `lock.py`), `EG/Spec/**`, `EG/Defs/**`, `APPROVALS/**`, `work/**`, `staging/**`: none is in
  `in_trusted_zone`.
* Item 8: the artifact check tests names, `..` components and `isfile()/isdir()` only.
* Item 9: `comparator.sh run --release` refuses root, requires `systemd-run` and
  `/run/systemd/system`, runs `sudo systemd-run --uid --gid --property=RestrictAddressFamilies=~AF_UNIX
  --property=NoNewPrivileges=yes --wait --pipe --collect`, and inside the unit
  `canary --expect-nnp && lake env comparator config`. Canary: ABI via syscall 444 with
  `LANDLOCK_CREATE_RULESET_VERSION`, `LANDLOCK_MIN_ABI=3`, positive write, denied write (exit 98),
  `NoNewPrivs: 1` inside landrun (exit 97 otherwise), `--expect-nnp` reads the caller's
  `/proc/self/status`. go-landlock `v0.9.0` in the pinned landrun's `go.mod`. Upstream comparator
  `Main.lean`: `#["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec"]` (l. 81),
  `writablePaths := #[projectDir / ".lake"]` for the builds (l. 118–130). README assumptions 1, 2,
  4, 6 at README l. 28–39.

**§3.** `.claude/settings.json`: six `Edit(...)` deny rules, nothing else. CI header states the
`--link-lake`/same-owner limit.

**§4.**
* §4.1: `redteam/external/patches/N4` is pinned (4 files).
* §4.2: `pristine.sh -C DIR`; the `git diff` path list = trusted zone + `.github` + `.claude`;
  `info repository …, HEAD …` is logged.
* §4.3: release.yml has exactly `build`, `verify`, `comparator`; no `actions/cache`; triggers
  `workflow_dispatch` and tags `formal-v*`, `release-*`. `build` steps 1–4 verbatim (`tar -cf …
  EG EG.* EGTest EGTest.* EGCheck EGCheck.*`, artifact `project-build`). `verify` 0a–0e and 1–14
  in that order with those commands; the member regex is verbatim; `status.py --check --no-write`
  writes nothing (`no_write` guards both `open(..., "w")`) and rejects unknown arguments;
  FinalCheck strict mode = no `--allow-sorry`/`--allow-unpinned`, pin file `TRUST.md`;
  `leanchecker --fresh` figures 21–40 min / 10.2–10.3 GB = release.yml header + `tooling.md`
  l. 249. `comparator` job: checkout (`fetch-depth: 0`), gate, elan/Lean, `tools`, `cache get`,
  `check_pins`, `check`, `run --release --system-unit --tools`. `comparator.sh check` performs the
  five listed checks; `run` dies without `Challenge`/`Solution` in `lakefile.toml` (fails closed);
  the committed `lakefile.toml` lacks them, `lakefile.toml.proposed` adds them. Dry-run results
  (honest accepted, F1–F5 rejected, C0 refused) are in `consolidate.md` l. 165–174.
* §4.4: `LANDRUN_REV 811cfff5` (v0.1.18), `LEAN4EXPORT_REV 66f1fb4b`, `COMPARATOR_REV fd5d5bcf`,
  patch file `comparator/patches/comparator-fd5d5bcf-lean-v4.33.1.patch` (pinned); `proj_trick`
  note = `comparator/README.md` "Soundness backport".
* §4.5: bullets checked as in M1/M3/M9; `formal/lean-toolchain` reads `leanprover/lean4:v4.33.1`.

**§5.** `EGCheck/FinalAlpha.lean` and the α/comparator remark are `work/trust/bridge.md` §8
item 7 (l. 197–201), as cited.

**§6.** Table verified row by row against `pristine.sh` (`in_trusted_zone`), `lock.py`
`PROTECTED_FILES`/`PROTECTED_DIRS` (includes `CONVENTIONS.md`, `status/ratchet.json`,
`../.github/CODEOWNERS`, `../.claude/settings.json`, expanded `scripts/**`, `redteam/**`,
`comparator/patches/**`, `.github/workflows/**`), `.github/CODEOWNERS` (19 entries, including
`/formal/lakefile.lean`, `/formal/CONVENTIONS.md`, `/formal/status/ratchet.json`) and
`staging/claude-settings.json.proposed` (adds `STATEMENT.md`, `LOCK.json`, `lakefile.lean`,
`comparator/{Challenge.lean,config.json,patches/**}`). `comparator/README.md` is gate-pinned and in
none of the other three: correct.

**§7.** `sha256sum scripts/pristine.sh` = `a29e7d7d…`; 100 pins; `--dev` gives 100/100. The five
proposals change five pinned files: `TRUST.md` (committed copy has no `EG-PIN` line),
`EGCheck/Final.lean`, `lakefile.toml`, `.claude/settings.json`, `redteam/external/redteam.sh`
(`diff redteam/external/redteam.sh staging/redteam.sh.proposed` is non-empty; the proposal is
mode 755).

**§8.**
* Item 1: STATE.md shows an earlier `ci.yml` ran on GitHub, so "the current `ci.yml`" is right.
* Item 2: `consolidate.md` "Landlock canary" (kernel 6.18.44, ABI 7, root): pinned landrun passes;
  fails closed with a pass-through landrun, a wrapper hiding its exit code, a simulated minimum
  ABI of 99, `--expect-nnp` without `no_new_privs` (and two more cases). Never run in a real unit.
* Item 7: `redteam/external/redteam.sh` `EXPECT[IO]=miss` ("miss by design").
* Item 8: committed `EXPECT[B1]=catch [C]=catch` with `EXPECT_RE`; `trust3.fable.md` l. 65
  measured `REDTEAM: FAIL (2 mismatches)` with the proposed `Final.lean`. The description of
  `staging/redteam.sh.proposed` (guard `hardened_final`, new verdict `inband+oob`,
  `EXPECT_INBAND_RE`, dev final = committed-style theorem without `#guard_msgs`/`run_cmd`,
  `--final FILE`) matches the diff; `docfix.md` §3 records `REDTEAM: PASS` for
  `--final staging/Final.lean.proposed B1 C`, for `A2`, and for the committed `Final.lean` with
  `B1 C A2` (unchanged behaviour).
* Item 9: `lock.py files --strict` fails today (2 violations, 115 PENDING).
* Item 10: `lint.py --release` reports `EG/Proof/Main.lean:17` and `EGCheck/Smoke.lean:6`;
  R6 is `trust3.fable.md` l. 331.
* Item 12: `redteam/bridge/run.sh` calls `comparator.sh run`, which always runs the canary;
  `RT_DIR` defaults to `mktemp -d`.

Audit cross-references spot-checked: trust3.fable Y11b (l. 48, 169), trust3.opus B2 (l. 39) and R1
(l. 115), trust2.opus N4 (l. 55, 165).

## 3. Non-blocking wording nits (optional, for the integrator)

None of these is a false statement; they are listed so the next reader does not have to re-derive
them.

1. **§2 item 7a, Lake/elan names.** "`lakefile.*`" and "`lean-toolchain*`" are shorthand: the gate's
   basename list (l. 401) is `lakefile.lean`, `lakefile.toml`, `lakefile.olean*`, `lakefile.ilean`,
   `leanpkg.toml`, `lake-manifest.json`, `lean-toolchain`, `lean-toolchain.toml` (case-insensitive).
   Since the sentence says "Lake/elan configuration file", the shorthand is not misleading.
2. **§2 item 7a, inert-data zone.** "`work/**`, `status/**`, `staging/**` Markdown/JSON/`.proposed`
   files" applies one qualifier to three directories; the gate (l. 438) admits `.md`/`.json` under
   `work/` and `status/`, and `.md`/`.proposed` under `staging/`. Harmless; a precise form is
   "`work/**` and `status/**` `.md`/`.json`; `staging/**` `.md`/`.proposed`".
3. **§4.4, the comparator patch.** The text describes only the soundness backport (issue 68). Per
   `comparator/README.md` the patch has a second change: `runBuiltinKernel` uses
   `Environment.replay` because `Kernel.Environment.replay` does not exist in v4.33.1. That touches
   comparator's replay driver, which §2 item 9 lists as trusted code, so one clause ("and a
   one-line build fix in the replay driver, `Environment.replay` for `Kernel.Environment.replay`")
   would make §4.4 complete. Not an error: the README it points to says so.

Nothing in §8 needs to be added: the trust4 completeness table (its §3) still holds for the
12:39 revision, and the two new proposals (`staging/redteam.sh.proposed`,
`staging/redteam-expectations.proposed.md`) are covered by §8 items 8 and 9 and by §7.

## 4. Evidence (commands run, all read-only)

`git log -1`, `git status --short`; `sha256sum formal/scripts/pristine.sh`;
`grep -c '^[0-9a-f]\{64\}  ' formal/scripts/pristine.sh`; `sh formal/scripts/pristine.sh --dev`;
`lean --githash`; `grep EG-PIN STATEMENT.md TRUST.md staging/TRUST.md.proposed`; the three
`git ls-files | grep …` commands of §4.2 and the `grep -i -E` / plain `grep` of §4.5;
`sha256sum` / `git hash-object` / `cmp` on `Challenge.lean` and the two upstream files;
`git -C .lake/packages/{formal_conjectures,mathlib,batteries} rev-parse HEAD`,
`git -C .lake/packages/mathlib describe --tags --exact-match`; manifest package list via
`python3 -c json`; `ls .lake/packages/*/lakefile.*`; `grep maxSynthPendingDepth`; closure counts
parsed from `STATEMENT.md`; `python3 -I scripts/lint.py --release`;
`python3 -I scripts/lock.py files --strict`; `diff redteam/external/redteam.sh
staging/redteam.sh.proposed`; `grep landlock` in the pinned landrun `go.mod`; `grep` in
`/root/tools/comparator/{Main.lean,README.md}`; full reads of `.github/workflows/{release,ci}.yml`,
`scripts/{pristine.sh,comparator.sh,check_pins.sh}`, `scripts/FinalCheck.lean` header and option
parser, `comparator/{README.md,Solution.lean,config.json}`, `EGCheck/{Final.lean,Bridge.lean}`,
`staging/*`, `.claude/settings.json`, `.github/CODEOWNERS`, `lock.py`/`status.py`/`lint.py`
excerpts, `redteam/{gate,bridge,tooling,external}` harness heads, `work/trust/{consolidate,docfix,
bridge}.md` excerpts, `STATE.md` excerpts, and the cited lines of `trust2.opus.md`,
`trust3.{opus,fable}.md`.
