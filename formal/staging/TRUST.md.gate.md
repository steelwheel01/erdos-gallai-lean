# Proposed TRUST.md text from the `gate` agent (merge into staging/TRUST.md.proposed)

Source: `work/trust/gate2.md`. Answers trust2.opus §4.1 item 1, §7 blocking items 1, 2 and 4, and
trust2.fable §8 items 1 and 4. Owner of TRUST.md.proposed: merge these, do not apply them alone.

## §2, new item 8 (trusted components)

8. **The non-proof files of the release commit, fixed by the gate.** `scripts/pristine.sh` (POSIX
   sh + git) runs first in every trusted job and in the manual audit, before any `lake`, `lean` or
   `python3` call. It rejects any file through which the repository could run code before the
   checks (a `lakefile.lean` or any other Lake/elan configuration, a committed `.lake/`, Python
   files outside `formal/scripts/`, `.pth`, `sitecustomize`, bytecode and native modules, direnv
   and tool-manager files, `.gitattributes`/`.gitmodules`, symlinks, submodules, editor and agent
   hooks, local git hooks and command-running git config). It also requires every file of the
   trusted zone to equal its SHA-256 pin: `formal/scripts/**`, `formal/redteam/**`,
   `formal/comparator/**` except `Solution.lean`, the lake files, `lean-toolchain`, `TRUST.md`,
   `STATEMENT.md`, `EGCheck/Final.lean`, `.github/**` and `.claude/**`. The gate cannot pin itself.
   A reader therefore trusts:
   * the gate script with SHA-256 `<fill in at approval: sha256sum formal/scripts/pristine.sh>`;
   * or, stronger, the user-approved trust commit `<EG_TRUST_REF>`. Its copy of the gate is run
     with `--trust-ref`, which also requires every trusted file to be byte-identical to that commit.

   Everything later in the jobs runs from the snapshot the gate copies before any other code runs.
   Python always runs with `-I` (and `PYTHONSAFEPATH=1`).
9. **GitHub-hosted runners, GitHub Actions and the artifact store**, when `release.yml` is used.
   A workflow run is evidence only if the workflow files at the tested commit are the approved
   ones. The gate checks that offline (pins or `--trust-ref`); a run of a modified workflow proves
   nothing, because such a workflow may simply skip the gate. The repository variable
   `EG_TRUST_REF` makes the jobs take the gate from the trust commit.

## §4 step 0, replace the first sentence with

0. **Gate, before anything else:**
   ```
   git show "$EG_TRUST_REF:formal/scripts/pristine.sh" > "$T/gate.sh"
   sh "$T/gate.sh" --trust-ref "$EG_TRUST_REF" --snapshot "$T/trusted"
   ```
   Without a trust ref, run `sh scripts/pristine.sh --snapshot "$T/trusted"` and compare the
   printed gate SHA-256 with §2 item 8. Every later command runs in `$T/trusted/formal`.
   `python3 -I scripts/lock.py files --strict` is the first Python call. Then `./scripts/check_pins.sh`
   and `scripts/comparator.sh check`. Regenerate `STATEMENT.md` with
   `lake env lean --run scripts/Statement.lean "$T/S.md"` and require an empty `diff`.

## §4 item 1, replace the comparator command with

`scripts/comparator.sh tools DIR && scripts/comparator.sh run --release --system-unit --tools DIR`
(release.yml's `comparator` job does exactly this, from the snapshot). It needs `lakefile.toml`
with the `Challenge`/`Solution` libraries (`staging/lakefile.toml.proposed`); until that is applied
the job fails closed.

## §6, add

`scripts/pristine.sh` holds the SHA-256 pin of every file of the trusted zone. Apply every
approved change to one of them together with `sh formal/scripts/pristine.sh --write-pins` and a
review of the diff of its pin block. Then run `lock.py update`, and move `EG_TRUST_REF` to the new
approved commit.
