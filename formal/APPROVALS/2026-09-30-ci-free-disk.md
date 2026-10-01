# 2026-09-30 — Workflows: free runner disk space at job start

**Authority.** User permission for trust-file changes "as appropriate" (2026-09-29). No check,
expectation or verdict changes.

**Why.** CI run 36717327466 (d81391c) printed the comparator red-team case logs: every case failed
with `cp: … No space left on device` while `comparator.sh run --prebuilt --scratch` copied
`formal/.lake/build` (0.93 GB), with 53 MB free on the runner (Mathlib cache, build, kernel replays and
the external red-team's copies had filled the disk). The same cases pass locally (honest:
"Your solution is okay!").

**Change.** First step of the CI `build` job and of the release `build`, `verify` and `comparator`
jobs: `sudo rm -rf` of preinstalled SDKs the jobs never use (dotnet, Android, GHC, CodeQL, Swift),
with `df -h /` before and after. Runs before checkout / any project code; touches only system
directories.

**Integrator run.** `--write-pins`: exactly two pins changed (`.github/workflows/ci.yml`,
`.github/workflows/release.yml`); `--dev` DEV-PASS. Gate SHA-256: `fbfd430c6fea1b64d0747c379f6b9ec54b1f4823170ddb2740b093c3b8480b96`.

**Correction (same day).** CI run 36728897625 (d10fdf5) failed in the new step itself: the jobs'
`defaults.run.working-directory: formal` does not exist before checkout ("An error occurred trying to
start process '/usr/bin/bash' with working directory …/formal"). The step now sets
`working-directory: /` (all four jobs). Re-pinned: exactly the two workflow pins changed; DEV-PASS.
Gate SHA-256: `68e84e43a98b3f6caff29f103817bf25a974542d8edf2a0a2c8a158d41cb0c68`.
