# Round-3 re-audit (opus): commands and details

The verdict and findings are in `APPROVALS/reviews/trust3.opus.md`. This file records how the
evidence was produced.

`$R` = `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/r3o.23iV`
(made with `mktemp -d`).

## Staged tree

```
git clone /home/user/Erdos-Proof $R/staged
cp formal/staging/Final.lean.proposed      formal/EGCheck/Final.lean
cp formal/staging/TRUST.md.proposed        formal/TRUST.md
cp formal/staging/lakefile.toml.proposed   formal/lakefile.toml
cp formal/staging/claude-settings.json.proposed .claude/settings.json
sh formal/scripts/pristine.sh --dev --write-pins     # 100 pins; gate sha256 18337c5c…
git commit -am …                                     # inside the clone only
sh formal/scripts/pristine.sh                        # PRISTINE: PASS
```

The same gate on a fresh clone of the real HEAD (`c673037`) gives `PRISTINE: PASS`, 100/100 pins,
gate sha256 `12a7eb969f635211…`, which matches `gate2.md`.

For the Lean harnesses, `$R/staged/formal/.lake` holds copies of the real `build/` and `config/`,
and `packages` is a symlink to the real package store. The external harness ran as:

```
unshare -m bash -c "mount --bind -o ro /home/user/Erdos-Proof /home/user/Erdos-Proof && \
  cd $R/staged/formal && redteam/external/redteam.sh --keep"
```

With this, the real repository (and so the package store) was read-only for every attack build.
The harness's own read-only mount then protected the staged clone as well.

## Results

- **Gate red-team** (`redteam/gate/run.sh --repo $R/staged`): 53 checks, 0 unexpected
  (`gate_rt.log`).
- **External red-team:** 17 rows OK. B1 and C are reported as `MISMATCH (out-band did not fire)`
  because the proposed `Final.lean` stops them in-band:
  - B1: `EGCheck/Final.lean:33:2: Type mismatch`;
  - C: `import EGCheck.Bridge failed, environment already contains 'Erdos184.erdos_184'`.

  The N4 FinalCheck log shows `origin` ×2 and `replay` failures on `EGCheck.RTX.bogus`, plus the
  ambient pre-γ `sorryAx` policy failures (`external.log`, `/tmp/rt-external.EhNo27/`).
- **Tooling red-team:** all 14 verdicts as expected (`tooling.log`).
- **Comparator red-team** (`RT_DIR=$(mktemp -d …)`, `--tools /root/tools`): honest accepted,
  F1–F5 rejected, 0 failures (`bridge.log`).
- **Snapshot** of a fresh staged clone: `PRISTINE: PASS`, 281 files.
  `python3 -I scripts/lock.py files --strict` then reports 108 PENDING and 5 violations: it fails
  closed until `lock.py update` is run under an approval.

## B2 (Landlock best-effort): source references

- comparator `fd5d5bcf` `Main.lean`, `buildLandrunArgs`: always passes `--best-effort`.
- landrun `811cfff5` `internal/sandbox/sandbox.go`: `llCfg.BestEffort()` then `llCfg.Restrict(...)`,
  and it logs "Landlock restrictions applied successfully" whatever happened.
- go-landlock v0.9.0 `landlock/restrict.go` `restrict()`:
  - best-effort calls `downgrade(c, rules, abi)`;
  - with ABI 0 the handled sets are empty, so it returns `nil // Success: Nothing to restrict`;
  - `PR_SET_NO_NEW_PRIVS` is set only later in the same function, so it is not set in this case.
- `scripts/comparator.sh`, `cmd_run --release --system-unit`: the unit is started as
  `sudo systemd-run --uid --gid --property=RestrictAddressFamilies=~AF_UNIX …`, without
  `NoNewPrivileges`.

This kernel (6.18.44) has Landlock ABI v7, so the fallback could not be triggered here. It was not
demonstrated.

## Concurrent activity

While the audit ran, other agents modified or added files under `formal/EG/**`, `formal/EGTest/**`
and `formal/work/p2*/**` in the real tree (`git status`). None of that came from this audit, whose
builds all ran inside read-only mounts or in scratch clones.
