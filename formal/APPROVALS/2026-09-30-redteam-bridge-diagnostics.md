# 2026-09-30 — redteam/bridge/run.sh: print failing case logs (diagnostics only)

**Authority.** User permission for trust-file changes "as appropriate" (2026-09-29). Diagnostics only:
no expectation, command, case or verdict changes.

**Why.** CI run 36709745067 (d71c50c) passed steps 1–24 on GitHub — including the per-library
leanchecker, the in-band `EGCheck.Final` (now passing) and the out-of-band FinalCheck red-team — and
failed only in step 25, the comparator-layout red-team: every case including `honest` exited 1
after ~10 s without comparator's messages, while the same harness passes locally (honest:
"Your solution is okay!"). The per-case logs stay in the runner's /tmp, so the cause is not visible.

**Change.** On a failing case, `run.sh` prints the last 40 non-build lines of the case log.

**Integrator run.** `--write-pins`: exactly one pin changed (`formal/redteam/bridge/run.sh`);
`--dev` DEV-PASS. Gate SHA-256: `42d4abe8f964c9cb050a8875ac47894513a3d07bfecf21ec6f68483ba22e73a4`.
