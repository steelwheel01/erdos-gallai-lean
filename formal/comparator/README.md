# comparator/ — Challenge and Solution for leanprover/comparator

Part of the out-of-band acceptance criterion (TRUST.md "How to check"; proposal in
`staging/TRUST.md.proposed`), introduced after the trust audits of 2026-09-26
(`APPROVALS/reviews/trust.{opus,fable}.md`, opus §6). Measured dry runs and exact commands:
`work/trust/bridge.md`.

| File | What | Who may change it |
|---|---|---|
| `Challenge.lean` | **byte-identical** copy of the pinned upstream `FormalConjectures/ErdosProblems/184.lean` (formal-conjectures `2424bb48`, SHA-256 `9f36e4e0…`, blob `36cc140c…`) | nobody (a pin change is a trusted-boundary change) |
| `Solution.lean` | the upstream text with the proof of `erdos_184` replaced by the bridge applied to `EG.Proof.mainInternal`; two private project imports; the five `sorry` variants removed; an Apache-2.0 modification notice | untrusted (comparator checks it) |
| `config.json` | release config: `theorem_names = ["Erdos184.erdos_184"]`, `permitted_axioms` = `propext`, `Quot.sound`, `Classical.choice`, no definition holes | integrator (checked by `scripts/comparator.sh check`) |
| `patches/*.patch` | patches that make comparator `fd5d5bcf` build and stay sound on Lean v4.33.1 | integrator |

`scripts/comparator.sh check` verifies: SHA-256 and git blob of `Challenge.lean` against the pins,
the pinned formal-conjectures commit (`HEAD` and the blob at `HEAD`), `cmp` against the package
file, the config, and that `Solution.lean` does not import `FormalConjectures.ErdosProblems.*`;
it prints the Challenge→Solution diff.

## Why the bridge is split

Comparator builds `Challenge` and `Solution` separately, exports both with `lean4export`, and
requires every constant used by the statement of `Erdos184.erdos_184` in the Challenge (in
particular `Erdos184.IsCycleOrEdge`) to be **the same declaration** in the Solution environment. So
the Solution must declare `Erdos184.IsCycleOrEdge` and `Erdos184.erdos_184` itself, and nothing it
imports may import `FormalConjectures.ErdosProblems.«184»` (the names would clash). Hence:

* `EGCheck/BridgeLemmas.lean` and `EGCheck/BridgeCore.lean` (modules, FC-184-free; they import
  only `EG.*`, Mathlib and `FormalConjecturesForMathlib…Decomposition`) prove
  `EGCheck.Bridge.of_mainInternal_unfolded`: the upstream statement with `IsCycleOrEdge H.coe`
  replaced by its body, for all instances `i₁ : H.coe.LocallyFinite`, `i₂ : Fintype H.coe.edgeSet`.
* `Solution.lean` and the thin wrapper `EGCheck/Bridge.lean` (imported by `EGCheck/Final.lean`)
  both derive the upstream statement from it by unfolding `IsCycleOrEdge` (kernel-checked).

## Lakefile change needed (protected file; proposed, not applied)

Comparator runs `lake build Challenge` and `lake build Solution` in the project directory, so
`lakefile.toml` needs two libraries (not default targets):

```toml
# Comparator challenge and solution (comparator/README.md). Only comparator builds them.
[[lean_lib]]
name = "Challenge"
srcDir = "comparator"

[[lean_lib]]
name = "Solution"
srcDir = "comparator"
```

Until it is approved, `scripts/comparator.sh run --scratch DIR` runs comparator in a scratch copy
of `formal/` with these two entries appended.

## Tools (pinned; built by `scripts/comparator.sh tools DIR`)

| Tool | Commit | Build |
|---|---|---|
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (main, v0.1.18) | `go build ./cmd/landrun` (Go 1.24) |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869` (master; = comparator's manifest pin) | `lake build lean4export` with `lean-toolchain` overridden to `leanprover/lean4:v4.33.1` |
| comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` (master) + `patches/comparator-fd5d5bcf-lean-v4.33.1.patch` | `lake build comparator` with `lean-toolchain` overridden to v4.33.1 |

The patch (2 changes, both needed on v4.33.1):
1. `Kernel.Environment.replay` does not exist in Lean v4.33.1; the patched `runBuiltinKernel`
   uses `Environment.replay` (same kernel checks) and keeps comparator's Quot post-check.
2. **Soundness backport.** Lean v4.33.1's `Expr.getUsedConstants` skips the structure name of
   `Expr.proj`; Lean v4.34 includes it and comparator relies on that (comparator issue 68,
   regression test `proj_trick`). Unpatched on v4.33.1, comparator **accepts** `proj_trick`
   (measured). The patch copies the v4.34 fold into `Comparator/Util.lean` and uses it for the
   statement comparison and the axiom walk. With it, comparator's own test suite passes on v4.33.1
   except the three tests that need the optional `nanoda` kernel.

Alternative: build comparator unpatched with its own toolchain (v4.35.0-rc3). Then the kernel that
replays the Solution is v4.35.0-rc3's, not the pinned v4.33.1 kernel; TRUST.md would have to list
it too.

## Sandbox checks of the harness (trust3.opus B2)

comparator always calls landrun with `--best-effort`. On a kernel without Landlock, go-landlock then
restricts nothing, and landrun still reports success. `scripts/comparator.sh run` therefore runs a
Landlock canary before comparator starts, in every mode (`scripts/comparator.sh canary`). The
canary fails closed unless:

* the kernel reports Landlock ABI >= 3 (`landlock_create_ruleset` version query);
* the pinned landrun, with comparator's own flags, can write inside its writable directory;
* the same landrun is denied a write outside that directory, and sets `no_new_privs`.

In `--release` mode the unit is started with `RestrictAddressFamilies=~AF_UNIX` and
`NoNewPrivileges=yes`. Inside the unit the canary runs again with `--expect-nnp`, which checks that
`NoNewPrivileges=yes` took effect. `redteam/bridge/run.sh` case `C0_UnconfinedLandrun` checks that
the harness refuses a pass-through landrun.
