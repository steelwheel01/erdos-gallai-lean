# 2026-10-01 — Public release run of this repository (record; no trusted-zone change)

**Run.** formal-release run 36795612102 of steelwheel01/erdos-gallai-lean
(https://github.com/steelwheel01/erdos-gallai-lean/actions/runs/36795612102), tag `release-2026-10-01`,
tested commit R = `a11bb45847101e0d1595089bc390c59f82ad1135` = `EG_TRUST_REF` = T (the initial commit of this repository,
exported from the private development repository steelwheel01/Erdos-Proof at `bb4d87811317c6ce978367165dcb878ce602bd41`,
whose trusted zone equals that of the development trust commit `19d0754bb69e130fd506813ceb055b0e99a19515`).

**Result: all three jobs SUCCESS.**
* comparator: release mode, unprivileged systemd unit — "Your solution is okay!".
* build: fresh build, `project-build` artifact.
* verify: trusted gate `PRISTINE: PASS` (logged `HEAD` = a11bb45); lock strict (1234 constants / 277 files, 0 violations);
  axiom scan 11,057 constants, 0 `sorryAx`, 0 meta-scan hits, 0 violations; sorry frontier 0; **FINALCHECK: PASS
  (0 failures, 0 warnings)** — statement `Expr.equal` to `Erdos184.erdos_184`, axioms exactly propext / Classical.choice /
  Quot.sound, statement-sha256 `4cb2cd56…` and closure-sha256 `39d6e8c3…` match the pins; `leanchecker EG` exit 0
  (11 min 8 s); `leanchecker EGTest` exit 0 (55 s); `leanchecker --fresh EGCheck.Final` exit 0 (33 min 19 s).

**Offline check (formal/TRUST.md §4.2), 2026-10-01.** In a fresh clone checked out at R:
`git show T:formal/scripts/pristine.sh > gate.sh` (SHA-256 `e8e10825a36148c00db43e5110937782ee2cf5553675e6a8e689f2252ca5051a`);
`sh gate.sh -C <clone> --trust-ref T` → 993 files checked, trusted zone 100/100 matching pins, **PRISTINE: PASS**; R = T so
`git diff T R` is empty; the three `git ls-files` checks print nothing. By §4.3 the run counts as evidence for `a11bb45`.

**Follow-up commit (this one; documentation only).** Adds `code/README.md` (placeholder directory used by the gate red-team
fixtures N2s/N3p; its absence made the formal-ci "Gate red-team" step fail in runs 36795542725 and 36795612140), fills the
verification rows and status line of `README.md`, completes `CITATION.cff`, and adds this record. No file of the trusted zone
changes, so the evidence above still applies to the trusted zone of later commits as long as `git diff a11bb45 <commit>` on the
trusted-zone paths of §4.2 stays empty.

Status: candidate proof, AI-generated and AI-reviewed; not yet reviewed by human experts.
