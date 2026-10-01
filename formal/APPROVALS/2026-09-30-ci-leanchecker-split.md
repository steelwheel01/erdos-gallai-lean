# 2026-09-30 — CI: split the project-wide leanchecker step per library

**Authority.** The user granted "full permission to modify trust files as appropriate" (2026-09-29).
This change touches only `.github/workflows/ci.yml` (hygiene CI, gate-pinned), not the acceptance
procedure: `release.yml` and TRUST.md §4.3 (steps 13–14) are unchanged.

**Why.** CI run 36693519203 (commit a43a543, first run on the complete proof) passed steps 1–20
(build, gate re-check, axiom scan, FinalCheck scan, STATEMENT.md, statement lock, sorry ratchet) and
then lost its runner during `lake env leanchecker EG EGTest EGCheck` (job ended "failure" at
10:56 UTC with the step still in progress; the log could not be downloaded, HTTP 404 — the runner
died). Locally the joint call is OOM-killed in a 15 GB cgroup; per library: EG exit 0 (13.8 min,
12.1 GB), EGTest exit 0 (1.3 min, 10.7 GB); EGCheck alone needs ~13.5 GB.

**Change.** `ci.yml` runs `leanchecker EG` and `leanchecker EGTest` separately. The three EGCheck
modules (Bridge, BridgeCore, BridgeLemmas) lie in the import closure of `EGCheck.Final`
(Final → Bridge → BridgeCore → BridgeLemmas), which `release.yml` replays with
`leanchecker --fresh EGCheck.Final` (and which passed locally, exit 0, 71 min, 10.7 GB).

**Open (user decision, TRUST.md §8 item 1).** `release.yml` still runs the joint
`leanchecker EG EGTest EGCheck` (TRUST.md §4.3 step 13). On a 16 GB runner it will likely fail the
same way. Either choose a larger runner via `EG_RELEASE_RUNNER`, or approve the same per-library
split in `release.yml` and TRUST.md §4.3 step 13.

**Integrator run.** `sh scripts/pristine.sh --write-pins`: exactly one pin changed
(`.github/workflows/ci.yml`: eb1b1941… → 42f897c0…); `--dev`: DEV-PASS, 100/100.
New gate SHA-256: `04958ee2ad4896bb06067a174d3bd4218dc96f3630a156c701f77bbebd831c27`.
