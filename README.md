# A Lean 4 formalization of a proof of the Erdős–Gallai cycle decomposition conjecture

> **The theorem `Erdos184.erdos_184` of [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — every graph on `n` vertices decomposes into `O(n)` cycles and edges — is proved here in Lean 4 with Mathlib, using only the axioms `propext`, `Classical.choice` and `Quot.sound`. Verification: release run [36795612102](https://github.com/steelwheel01/erdos-gallai-lean/actions/runs/36795612102) (comparator in release mode, strict FinalCheck, three kernel replays) and the offline check of `formal/TRUST.md` §4.2. Paper: [`paper/erdos-gallai-proof.pdf`](paper/erdos-gallai-proof.pdf).**


This repository holds a Lean 4 formalization of a proof of the Erdős–Gallai cycle decomposition
conjecture (Erdős Problem #184): every graph on `n` vertices decomposes into `O(n)` cycles and
edges. The informal proof is the paper
[*A proof of the Erdős–Gallai cycle decomposition conjecture*](paper/erdos-gallai-proof.pdf)
(source in `paper/src/`). The Lean statements quote the earlier manuscript version 6.1 in
`proofs/manuscript/`; the paper applies the errata found by the formalization and keeps every
statement number. See [Trust model](#trust-model-in-brief) for exactly what the checks establish.

Author: Ryan Coffey (Yale University). Contact: via GitHub issues on this repository
(https://github.com/steelwheel01/erdos-gallai-lean/issues).

---

## Contents

1. [What is proved](#what-is-proved)
2. [Axioms](#axioms)
3. [Toolchain pins](#toolchain-pins)
4. [How to build](#how-to-build)
5. [How to verify independently](#how-to-verify-independently)
6. [Trust model in brief](#trust-model-in-brief)
7. [Repository layout](#repository-layout)
8. [How the Lean proof is organised](#how-the-lean-proof-is-organised)
9. [Verification record](#verification-record)
10. [Known limitations and open items](#known-limitations-and-open-items)
11. [Disclosure](#disclosure)
12. [Citing, license](#citing-license)

---

## What is proved

The target is the statement `Erdos184.erdos_184` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures), taken
**unchanged** at commit `2424bb480c590237ffbb2cc831ae4cb8977e045a`, file
`FormalConjectures/ErdosProblems/184.lean`. The project's copy, `formal/comparator/Challenge.lean`,
is byte-identical to that file (SHA-256
`9f36e4e053285cd8b886042eb609ace5f21f49bd81903eebca8000ff03e020d6`, git blob
`36cc140cb3d8e60b08a842f1691fe9b73602f92b`). The source text of the statement, inside
`namespace Erdos184` with `open Filter SimpleGraph`:

```lean
/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

open scoped Classical in
/--
Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.
-/
@[category research open, AMS 5]
theorem erdos_184 :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry
```

`SimpleGraph.IsDecomposition G D` (from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`
at the same commit) says that the edge sets of the members of `D` are pairwise disjoint and that
their union is the edge set of `G`. The upstream file marks the problem `research open`; this
repository does not change that file or its attributes.

**The statement a reader actually trusts is the elaborated one.** `formal/STATEMENT.md` is
generated from the pinned build by `lake env lean --run scripts/Statement.lean`, importing only
`FormalConjectures.ErdosProblems.«184»` (no project code). Its `pp.all` form of the type of
`Erdos184.erdos_184` (universe parameter `u_1`), verbatim:

<details>
<summary><code>Erdos184.erdos_184</code>, <code>pp.all</code> type (from <code>formal/STATEMENT.md</code>)</summary>

```
@Exists.{1} (Nat → Real) fun (f : Nat → Real) =>
  And
    (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm
      (@Filter.atTop.{0} Nat Nat.instPreorder) f fun (n : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast n)
    (∀ {V : Type u_1} [inst : Fintype.{u_1} V] [DecidableEq.{u_1 + 1} V] (G : SimpleGraph.{u_1} V),
      @Exists.{u_1 + 1} (Finset.{u_1} (@SimpleGraph.Subgraph.{u_1} V G))
        fun (D : Finset.{u_1} (@SimpleGraph.Subgraph.{u_1} V G)) =>
        And
          (∀ (H : @SimpleGraph.Subgraph.{u_1} V G),
            @Membership.mem.{u_1, u_1} (@SimpleGraph.Subgraph.{u_1} V G)
                (Finset.{u_1} (@SimpleGraph.Subgraph.{u_1} V G))
                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (@SimpleGraph.Subgraph.{u_1} V G))
                  (@SimpleGraph.Subgraph.{u_1} V G)
                  (@Finset.instSetLike.{u_1} (@SimpleGraph.Subgraph.{u_1} V G)))
                D H →
              @Erdos184.IsCycleOrEdge.{u_1}
                (@Set.Elem.{u_1} V (@SimpleGraph.Subgraph.verts.{u_1} V G H))
                (@Subtype.fintype.{u_1} V
                  (@Membership.mem.{u_1, u_1} V (Set.{u_1} V) (@Set.instMembership.{u_1} V)
                    (@SimpleGraph.Subgraph.verts.{u_1} V G H))
                  (fun (a : V) =>
                    Classical.propDecidable
                      (@Membership.mem.{u_1, u_1} V (Set.{u_1} V) (@Set.instMembership.{u_1} V)
                        (@SimpleGraph.Subgraph.verts.{u_1} V G H) a))
                  inst)
                (@SimpleGraph.Subgraph.coe.{u_1} V G H))
          (And (@SimpleGraph.IsDecomposition.{u_1} V G D)
            (@LE.le.{0} Real Real.instLE
              (@Nat.cast.{0} Real Real.instNatCast
                (@Finset.card.{u_1} (@SimpleGraph.Subgraph.{u_1} V G) D))
              (f (@Fintype.card.{u_1} V inst)))))
```

</details>

`formal/STATEMENT.md` also gives the `pp.all` forms of `Erdos184.IsCycleOrEdge` and
`SimpleGraph.IsDecomposition` and lists the closure of the statement (1572 declarations: `Init` 614,
Mathlib 949, Batteries 6, formal-conjectures 3). Two SHA-256 pins fix the statement and the meaning
of everything it unfolds to. They are recorded in `formal/TRUST.md` together with the Lean githash,
and `scripts/FinalCheck.lean` checks all three:

    EG-PIN lean-githash 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
    EG-PIN statement-sha256 4cb2cd5697e7916ea244e8b58041fcb2c7fa4338621335eeeb3a1d05452f6734
    EG-PIN closure-sha256 39d6e8c358b1482f9af513370d6edfba52da96857fa1066a309fa87c0ccf66fd

**In words.** There is a function `f : ℕ → ℝ` with `f(n) = O(n)` as `n → ∞` such that, for every
finite type `V` (in any universe) and every simple graph `G` on `V`, there is a finite family `D` of
subgraphs of `G` with three properties:

* each member of `D`, viewed as a graph on its own vertex set, is either connected and 2-regular
  (a cycle) or has exactly one edge;
* the members of `D` have pairwise disjoint edge sets whose union is the edge set of `G`;
* `D` has at most `f(|V|)` members.

So the statement says that every `n`-vertex graph decomposes into `O(n)` edge-disjoint cycles and
edges; the Lean kernel checks that it holds, subject to the trust model below. The proof takes `f(n) = c·n`. The natural number `c` is not computed: it is `⌈c_EG⌉₊` for constants `N_0`, `D_*`
that the proof shows to exist (see
[How the Lean proof is organised](#how-the-lean-proof-is-organised)).

Whether this Lean statement faithfully expresses the conjecture is a separate question.
`formal/TRUST.md` §2 items 3–5 cover the pinned text of the statement, the definitions in its
closure and its elaboration; they say nothing about fidelity. In addition (not covered by
`formal/TRUST.md`), the reader must judge whether the upstream statement faithfully expresses the
conjecture. The statement is the upstream project's, and no human has reviewed that fidelity for
this project.

The Lean theorem that proves it appears in two places, both obtained from the same kernel-checked
bridge `EGCheck.Bridge.of_mainInternal_unfolded` (`formal/EGCheck/BridgeCore.lean`) applied to
`EG.Proof.mainInternal`:

* `Erdos184.erdos_184` in `formal/comparator/Solution.lean`: the upstream file, with the proof of
  `erdos_184` filled in and the five `sorry` variants removed. This is what
  [comparator](https://github.com/leanprover/comparator) checks, and comparator is the
  load-bearing check;
* `EGCheck.erdos_184` in the pinned `formal/EGCheck/Final.lean`, with type
  `type_of% @_root_.Erdos184.erdos_184.{u}`. This is what `scripts/FinalCheck.lean` and
  `leanchecker --fresh EGCheck.Final` check.

## Axioms

The proof uses exactly the three standard axioms `propext`, `Classical.choice` and `Quot.sound`,
and no `sorryAx`. The project declares no `axiom`. `scripts/lint.py` and the policy check of
`scripts/FinalCheck.lean` reject `unsafe`, `partial`, `@[extern]`, `@[implemented_by]` and
`initialize`. comparator (the load-bearing check, release config `permitted_axioms`) establishes
the axioms of the exported `Erdos184.erdos_184`. FinalCheck (strict) checks the axioms of
`EGCheck.erdos_184` as defence in depth (`formal/TRUST.md` §4.1): it loads the untrusted `.olean`
files into its own process, so it does not independently establish the claim. The axiom scan of
`scripts/Axioms.lean` is hygiene (`formal/TRUST.md` §3, §4.3 step 10). The in-band
`#guard_msgs` is advisory:

* comparator, with `permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]`
  (`formal/comparator/config.json`), walks the axioms of the exported `Erdos184.erdos_184`
  (load-bearing);
* `scripts/FinalCheck.lean` (strict mode) requires the axioms of `EGCheck.erdos_184` to be exactly
  these three, computed by two methods (defence in depth);
* hygiene: `scripts/Axioms.lean --no-sorry` scans every constant of the libraries `EG`, `EGTest`
  and `EGCheck`: 0 uses of `sorryAx` and 0 violations, over 11,056 constants in the local run of
  2026-09-30 and 11,057 in the `verify` job of release run 2 (`formal/work/p3/ACCEPT.md`). The
  difference is explained by the target `EGCheck.Final`: the release command adds it, and it
  declares the one constant `EGCheck.erdos_184` (inferred from the commands,
  `formal/work/p3/ACCEPT.md` l. 17 vs `release.yml`; the root module `formal/EGCheck.lean` does not
  import `Final`; the per-constant lists were not compared). The local command also omitted
  `--cross-check`, which the release command passes. CI runs the scan without `--no-sorry` and
  without `--cross-check` (and without `EGCheck.Final`), as a regression guard;
* the in-band guard `#guard_msgs in #print axioms EGCheck.erdos_184` in `formal/EGCheck/Final.lean`.
  This one is advisory only, because it runs inside the elaborator (`formal/TRUST.md` §3).

## Toolchain pins

| Component | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.33.1` (`formal/lean-toolchain`), commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Mathlib | tag `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474` |
| formal-conjectures | commit `2424bb480c590237ffbb2cc831ae4cb8977e045a` (2026-09-24) |
| other Lake packages | `formal/lake-manifest.json`: plausible `b7eb3304…`, LeanSearchClient `5f4d51b8…`, importGraph `16f02aa7…`, proofwidgets `4be2e3d5…`, aesop `3448c0bc…`, Qq `92c15be1…`, batteries `4488d40d…`, Cli `6130a478…` |
| elan (in the workflows) | `v4.2.4`, archive SHA-256 `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63` |
| Lean release archive (in the workflows) | `lean-4.33.1-linux.tar.zst`, SHA-256 `890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235` |
| leanchecker | bundled with Lean v4.33.1 |
| comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` plus `formal/comparator/patches/comparator-fd5d5bcf-lean-v4.33.1.patch`, built with Lean v4.33.1 |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869`, built with Lean v4.33.1 |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18), built with Go ≥ 1.24 (not pinned) |

The comparator patch does two things. It adapts comparator's replay driver to Lean v4.33.1. It also
backports a Lean v4.34 soundness fix that comparator relies on: `Expr.proj` structure names in
`getUsedConstants`, comparator issue 68. Without the patch, comparator built with v4.33.1 accepts
comparator's own `proj_trick` counterexample. `formal/comparator/README.md` has the details.

`formal/lakefile.toml` sets `autoImplicit = false`, `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3`, and declares the libraries `EG`, `EGTest`, `EGCheck`, `Challenge` and
`Solution`. Only `EGCheck` and `Challenge`/`Solution` may import formal-conjectures.

## How to build

Requirements: Linux x86_64, `git`, `curl`, `python3`, and about 16 GB of RAM (or RAM plus swap) for
the checks (see the table below). The build alone ran on a 7 GiB GitHub runner.

```sh
git clone https://github.com/steelwheel01/erdos-gallai-lean.git eg184 && cd eg184
sh formal/scripts/pristine.sh     # the gate, on the fresh clone, before anything else: PRISTINE: PASS
cd formal
# install elan; it reads formal/lean-toolchain (leanprover/lean4:v4.33.1)
lake exe cache get                # Mathlib .olean cache (else Mathlib builds from source: about 2.5 h on 4 cores)
./scripts/check_pins.sh           # package HEADs, clean package trees, manifest revs, lean --githash
lake build EG EGTest EGCheck EGCheck.Final
lake env lean --run scripts/FinalCheck.lean   # must print FINALCHECK: PASS
```

A successful `lake build EGCheck.Final` is **not evidence on its own**. Its checks run inside the
Lean elaborator, and any imported module could subvert them (`formal/TRUST.md` §3). The
out-of-band checks below are what count.

## How to verify independently

This section follows the acceptance criterion of `formal/TRUST.md` §4 as `.github/workflows/release.yml`
implements it. **comparator in release mode is the load-bearing check.** FinalCheck and
`leanchecker --fresh` are defence in depth: they load the untrusted `.olean` files into their own
process, and they check the other artifact, `EGCheck.erdos_184`.

### 0. Which commit, and the offline check

Let `T` be the approved trust commit (a full 40-hex id) and `R` the commit being checked. In a
fresh clone containing both (`formal/TRUST.md` §4.2):

```sh
git show T:formal/scripts/pristine.sh > /tmp/gate.sh
sh /tmp/gate.sh -C <clone checked out at R> --trust-ref T      # must print PRISTINE: PASS
```

This requires the whole trusted zone of `R` to be byte-identical to `T`. The trusted zone is
`.github/**`, `.claude/**`, `formal/scripts/**`, `formal/redteam/**`, `formal/comparator/**` except
`Solution.lean`, `formal/lakefile.toml`, `formal/lake-manifest.json`, `formal/lean-toolchain`,
`formal/TRUST.md`, `formal/STATEMENT.md` and `formal/EGCheck/Final.lean`. The check also rejects
every file that could run code before the checks. If you prefer not to run the gate script, review
`git diff T R` on those paths yourself (it must be empty apart from
`formal/comparator/Solution.lean`) and run the three `git ls-files` checks of `formal/TRUST.md` §4.2.

For the published record: T = R = `a11bb45847101e0d1595089bc390c59f82ad1135` (the initial commit of this repository; release run 36795612102). In the
private development repository steelwheel01/Erdos-Proof, release run 2 tested
`R = T = f7398e12758c1898ca60614263a2455a9f1dc78f`.
That commit is not the tree of this repository, whose trusted zone differs from it (see
[Verification record](#verification-record)); run the check with this repository's own `T` and `R`.

### 1. Gate and snapshot

Every later step runs from a read-only snapshot that the gate makes (as in `release.yml`, which
runs the gate in the checkout's `formal/` at `R`). Work in the clone checked out at `R` from step 0.
That clone must also contain `T`, because `--trust-ref T` resolves `T` locally (as `release.yml`
ensures with `fetch-depth: 0`):

```sh
W=$(mktemp -d)                                   # work directory for snapshots, tools, logs
cd <clone checked out at R>
cd formal
sh /tmp/gate.sh --trust-ref T --snapshot "$W/trusted"   # or, without a trust commit: sh scripts/pristine.sh --snapshot "$W/trusted"
cd "$W/trusted/formal"
```

### 2. Toolchain (checksum-verified, as in `release.yml`)

```sh
ELAN_VERSION=v4.2.4
ELAN_SHA256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
LEAN_VERSION=4.33.1
LEAN_ARCHIVE_SHA256=890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
tmp=$(mktemp -d)
curl -sSfL -o "$tmp/elan.tar.gz" \
  "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz"
echo "${ELAN_SHA256}  $tmp/elan.tar.gz" | sha256sum -c -
tar xzf "$tmp/elan.tar.gz" -C "$tmp"
"$tmp/elan-init" -y --no-modify-path --default-toolchain none
curl -sSfL -o "$tmp/lean.tar.zst" \
  "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst"
echo "${LEAN_ARCHIVE_SHA256}  $tmp/lean.tar.zst" | sha256sum -c -
dest="$HOME/.elan/toolchains/leanprover--lean4---v${LEAN_VERSION}"
mkdir -p "$dest" && tar --zstd -xf "$tmp/lean.tar.zst" -C "$dest" --strip-components=1
export PATH="$HOME/.elan/bin:$PATH"
```

### 3. The `verify` sequence (trusted; never runs project code)

All commands run in `$W/trusted/formal`, with `PYTHONSAFEPATH=1` and
`PYTHONDONTWRITEBYTECODE=1` set (as in the workflow environment of `release.yml`).

```sh
export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1
python3 -I scripts/lock.py files --strict
lake exe cache get
./scripts/check_pins.sh
python3 -I scripts/lint.py --self-test && python3 -I scripts/lint.py --release
redteam/tooling/run.sh                                         # checker red-team fixtures
lake build 'FormalConjectures.ErdosProblems.«184»'             # upstream statement, from pinned sources
lake env lean --run scripts/Statement.lean "$W/STATEMENT.regen.md"
diff -u STATEMENT.md "$W/STATEMENT.regen.md"              # must be empty
# install the project .olean files here (see the note below)
python3 -I scripts/lock.py check --strict
lake env lean --run scripts/Axioms.lean --no-sorry --cross-check \
  --prefix EG --prefix EGTest --prefix EGCheck EG EGTest EGCheck EGCheck.Final
python3 -I scripts/status.py --check --no-write               # sorry ratchet
lake env lean --run scripts/FinalCheck.lean                   # must print FINALCHECK: PASS
lake env leanchecker EG                                       # per library: the joint call
lake env leanchecker EGTest                                   #   exhausts 16 GB
lake env leanchecker --fresh EGCheck.Final                    # must exit 0
```

In `release.yml` the project `.olean` files come from a separate, **untrusted** `build` job. That job
runs `lake build EG EGTest EGCheck EGCheck.Final` on another runner and hands over only
`.lake/build/lib/lean/{EG,EGTest,EGCheck}*`. The `verify` job validates the archive member names
and extracts them into the empty `.lake/build/lib/lean` of the snapshot, after the statement has been
regenerated. To reproduce that separation locally, build in a second clone and copy those files in.
Building in the snapshot itself is simpler but gives up the separation.

`lake env leanchecker EGCheck` is not run on its own. The three `EGCheck` modules (`Bridge`,
`BridgeCore`, `BridgeLemmas`) lie in the import closure of `EGCheck.Final`, which the `--fresh` step
replays in full, packages included.

### 4. The `comparator` sequence (load-bearing)

Use a **separate fresh snapshot** in which no project code has been built. comparator's assumptions
require the Challenge to be built and exported before any project code is compiled, and the
Solution to be built only inside its sandbox. Run as an **unprivileged user** (the harness refuses
root) on a Linux kernel with Landlock ABI ≥ 3, with `systemd-run` available through `sudo`, and with
Go ≥ 1.24 for landrun:

```sh
cd "$W" && git clone https://github.com/steelwheel01/erdos-gallai-lean.git eg184-cmp && cd eg184-cmp && git checkout R   # fresh clone at R
cd formal && sh /tmp/gate.sh --trust-ref T --snapshot "$W/trusted2" && cd "$W/trusted2/formal"
# toolchain as in step 2
go version
scripts/comparator.sh tools "$W/comparator-tools"   # landrun, lean4export, comparator (+patch) at pinned commits
lake exe cache get
./scripts/check_pins.sh
scripts/comparator.sh check                      # Challenge byte-identical to upstream; release config; Solution imports
scripts/comparator.sh run --release --system-unit --tools "$W/comparator-tools"
# must end with: Your solution is okay!   (exit 0)
```

`run --release --system-unit` refuses root, `--allow-sorry`, `--prebuilt` and `--solution`. It
re-runs `check` and runs a Landlock canary: this fails closed unless landrun really confines writes
and sets `no_new_privs`. It then starts comparator in a transient systemd unit with
`RestrictAddressFamilies=~AF_UNIX` and `NoNewPrivileges=yes`, runs the canary again inside the unit,
and finally runs `lake env comparator comparator/config.json`. comparator builds the Challenge,
builds the Solution inside landrun, and exports both with lean4export. On one exported view it then
checks three things: that the statement equals the Challenge's, that only permitted axioms are used,
and that the kernel replays the proof.

A reader who does not want to run any of this repository's scripts can follow the minimal recipe of
`formal/TRUST.md` §4.5:

* compare `Challenge.lean` with upstream by hand;
* write the four-key `config.json` by hand;
* build the three tools at the pinned commits, applying the patch;
* confirm that landrun confines writes on your kernel;
* run comparator unprivileged, as its README prescribes.

### Resources (measured)

| Step | Time | Peak memory | Where measured |
|---|---|---|---|
| Mathlib from source (only if the cache is unreachable) | about 2 h 29 min on 4 cores | — | development sandbox, 2026-09-26 |
| `lake build EG EGTest EGCheck EGCheck.Final` | 41 min 33 s (whole `build` job) | fits a 7 GiB runner | GitHub, release run 1 |
| `scripts/FinalCheck.lean` (strict) | 2 min 51 s | 9.1 GB | local, 2026-09-30 |
| `leanchecker EG` | 13 min 49 s | 12.1 GB | local |
| `leanchecker EG` | 13 min 25 s | 5.9 GB | GitHub, release run 2 (7 GiB runner + swap) |
| `leanchecker EGTest` | 1 min 16 s | 10.7 GB | local |
| `leanchecker EGTest` | 1 min 7 s | — | GitHub, release run 2 |
| `leanchecker EG EGTest EGCheck` (joint) | — | out of memory at 15–16 GB | local and CI; hence per library |
| `leanchecker --fresh EGCheck.Final` | 21 min to 1 h 11 min | 10.2–10.7 GB | local |
| `leanchecker --fresh EGCheck.Final` | 36 min 48 s | 6.8 GB | GitHub, release run 2 (7 GiB runner + swap, 0 swaps) |
| comparator run (after the tools are built) | 4 min 52 s | 7.0 GB | local dry run as root |
| `comparator` job, end to end | 34 min 36 s | — | GitHub, release run 1 |

On a machine with less than 16 GB, add swap, as the `verify` job of `release.yml` does (12 GiB swap
file on a 7 GiB runner). Swap changes only speed: an out-of-memory kill fails the step and never
turns into a pass.

## Trust model in brief

The authoritative description is `formal/TRUST.md`.

**What a reader must trust** (`formal/TRUST.md` §2):

1. **The Lean kernel** of Lean v4.33.1 (commit `819816b2…`). leanchecker, FinalCheck (through
   `Environment.replay`) and comparator all use this kernel; no external kernel is involved.
2. **The three axioms** `propext`, `Classical.choice`, `Quot.sound`.
3. **The upstream statement** (`formal/TRUST.md` §2 items 3–5). This means the text of `184.lean`
   and of `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean` at the pinned
   formal-conjectures commit (item 3), the Mathlib/`Init`/Batteries definitions they unfold to (the
   1572 declarations pinned by `closure-sha256`, item 4), and the elaboration of that text (item 5).
   A reader who does not want to trust the elaboration reads `formal/STATEMENT.md` instead. In
   addition (not covered by `formal/TRUST.md`), the reader must judge whether the upstream
   statement faithfully expresses the conjecture.
4. **The checkers and their environment.**
   * comparator, lean4export and landrun at the pinned commits (with the patch);
   * the Linux kernel's Landlock enforcement;
   * the Lean `.olean` loader, which reads `.olean` files that project code produced. A loader
     exploit is a residual risk that no checker covers (§2 item 10);
   * Lake and the Mathlib `.olean` cache, which is tied to the pinned sources by the closure pin,
     comparator's own Challenge build and `leanchecker --fresh`.
5. **The gate and trusted zone of the trust commit**, or your own review of them (§4.2).
6. **GitHub's runners and artifact store**, but only if you rely on the recorded CI runs instead of
   running the checks yourself.

**What a reader need not trust** (`formal/TRUST.md` §3):

* the roughly 600 project modules: 601 modules in `EG/`, about 93,000 lines;
* the test library `EGTest/` (37 modules);
* the bridge `EGCheck/Bridge*.lean` and `comparator/Solution.lean`;
* every internal definition and every intermediate statement in `EG/Defs` and `EG/Spec`. A wrong
  internal definition could block the proof, but it cannot make the checked claim false:
  comparator compares the final theorem with the independently built upstream statement and
  replays everything it depends on in the kernel;
* the manuscript, the AI reviews, the lint/lock/status tooling, `ci.yml`, and the in-band checks of
  `EGCheck/Final.lean`.

This division applies to the claim "`Erdos184.erdos_184` has a kernel-checked proof from the three
axioms". A second claim is that the Lean proof follows the manuscript lemma by lemma. That claim
depends on the intermediate statements in `EG/Spec` matching the manuscript. The kernel does not
check this; `CORRESPONDENCE.md` records it. Where the Lean route differs from the manuscript, the
record is `formal/work/p4/DEVIATIONS.md` (36 deviations, D1–D36), and the manuscript errata are in
`proofs/manuscript/ERRATA_v6.1.md` (31 errata, all T0/T1: 10 corrected in v6.1, the other 21 applied
in manuscript version 6.2; both files committed in `fbe6379` of the development repository and
included here unchanged).

## Repository layout

Paths are relative to the repository root.

| Path | Contents | Trusted? |
|---|---|---|
| `formal/EG/Defs/` (53 files) | definitions: finite simple graphs `EG.FGraph`, objects `EG.Obj`, decompositions `EG.IsDecomp`, `f(G)` = `EG.fnum`, expanders, the hierarchy run model, probability spaces (`EG.FinDist`), constants | no |
| `formal/EG/Spec/` (122 files) | the frozen statements of the manuscript's lemmas, as `def XStatement : Prop`, each with its TeX label; 113 of the files have a "Formal reading" note; `EG/Spec/Main.lean` holds the internal main theorem `EG.Spec.MainInternal` | no (hashed in `LOCK.json` as a regression guard) |
| `formal/EG/Lib/` (183 files) | general and supporting lemmas, including most of the work on the cited results (e.g. Lovász's theorem in `EG/Lib/Ext/`) | no |
| `formal/EG/Proof/` (243 files) | proofs of the `Spec` statements; `EG/Proof/Todo/*` are the per-statement theorems `EG.Todo.X : EG.Spec.XStatement`; `EG/Proof/Main.lean` proves `EG.Proof.mainInternal` | no |
| `formal/EGTest/` (37 files) | unit tests, non-vacuity tests and probes (including Lean proofs that some literal readings of manuscript statements are false) | no |
| `formal/EGCheck/` | `BridgeLemmas.lean`, `BridgeCore.lean` (the internal theorem implies the upstream statement), `Bridge.lean` (the thin wrapper that imports the upstream module), `Final.lean` (pinned) | only `Final.lean` is pinned |
| `formal/comparator/` | `Challenge.lean` (byte-identical upstream file), `Solution.lean`, `config.json`, `patches/`, `README.md` | yes, except `Solution.lean` |
| `formal/scripts/` | `pristine.sh` (the gate), `FinalCheck.lean`, `Statement.lean`, `Axioms.lean`, `comparator.sh`, `check_pins.sh`, `lint.py`, `lock.py`, `status.py`, … | yes (pinned) |
| `formal/redteam/` | red-team fixtures for the gate, the checkers, the bridge and comparator's harness | yes (pinned) |
| `formal/STATEMENT.md`, `formal/TRUST.md` | the elaborated statement and pins; the trust model and acceptance criterion | yes (pinned) |
| `formal/lakefile.toml`, `formal/lake-manifest.json`, `formal/lean-toolchain` | build configuration | yes (pinned) |
| `formal/LOCK.json`, `formal/status/` | statement lock, sorry ratchet | no (hygiene) |
| `formal/APPROVALS/` | records of every approved change to the trusted boundary, and the AI trust audits (`APPROVALS/reviews/`) | no (record) |
| `formal/work/` | the unedited working record of the formalization: blueprints (`work/p2/`), triage, design notes, trust-audit notes (`work/trust/`), acceptance record (`work/p3/ACCEPT.md`) | no (archive; may be stale) |
| `formal/staging/` | proposals for trusted files, as applied (referenced by `TRUST.md`) | no (record) |
| `.github/workflows/` | `ci.yml` (regression guard), `release.yml` (acceptance run: `build`, `verify`, `comparator` jobs) | yes (pinned) |
| `.claude/settings.json` | edit-deny list for the AI agents that wrote the code; pinned by the gate | yes (pinned) |
| `formal/README.md`, `formal/AGENTS.md`, `formal/CONVENTIONS.md`, `PLAN_FORMALIZATION.md` | the formalization plan, the conventions, and the rules the AI agents worked under | no (record) |
| `proofs/manuscript/` | the manuscript v6.1 (TeX sources and PDF) that the `EG/Spec` docstrings quote, and its errata | no |
| `CORRESPONDENCE.md` | manuscript result ↔ Lean statement ↔ Lean proof, for all 127 nodes of the manuscript | no |

## How the Lean proof is organised

Internally, the project states the theorem as `EG.Spec.MainInternal` (`formal/EG/Spec/Main.lean`):

```lean
def MainInternal : Prop :=
  ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V
```

Here an object is a single non-loop edge or a cycle given by a duplicate-free vertex list of length
at least 3. `EG.IsDecomp E D` says that the objects are well formed and that their edge lists are
pairwise disjoint and duplicate-free with union `E`. The bridge
`EGCheck.Bridge.of_mainInternal_unfolded` (`formal/EGCheck/BridgeCore.lean`) turns this into the
upstream statement, with `f n = c * n`. It transfers `G` to `Fin |V|`, which also lifts the
restriction to `Type`, and converts the objects into a `Finset G.Subgraph`.

`EG.Proof.mainInternal` (`formal/EG/Proof/Main.lean`) follows the proof of the Main Theorem in the
manuscript (Corollary 7.22, label `s7:thmMainProof`):

1. constants `N_0` and `D_*` satisfying the galactic conditions Γ1–Γ4 exist
   (`EG.exists_gammaCond`; Lemma 7.21);
2. every graph has a valid run of the hierarchy `HB*^{τ+}` once `D_*` satisfies Γ1
   (`EG.Todo.ExistsRun`; Proposition 2.15); it is applied to graphs with `n ≥ N_0` and `d_1 ≥ D_*`
   inside `EG.Proof.hiHyp_of_gammaCond`. A designation exists
   (`EG.Chain.exists_isDesignation`; Definition 6.8);
3. Theorem JV⁺* (`EG.Todo.JVps`; Theorem 7.19) gives simple quotient graphs `Q_3, …, Q_R` with
   `f(G) ≤ C_0 n + 2 Σ_l f(Q_l)` and `Σ_l |V(Q_l)| ≤ θ_Q n`, where `θ_Q ≤ 1/4`;
4. the layered quotient induction HI″ (`EG.hi`, via `EG.mainInternal_of_hiHyp`; Theorem 7.20)
   turns this into `f(G) ≤ c_EG |V(G)|` for every graph `G`, and `c = ⌈c_EG⌉₊`.

The explicit-constant form of the Main Theorem, `f(G) ≤ c_EG · n` for every admissible `N_0` and
`D_*`, is also stated and proved (`EG.Spec.CorJVpsEGStatement`, `EG.Todo.CorJVpsEG`). It is not
used on the path to `Erdos184.erdos_184`.

`CORRESPONDENCE.md` maps each of the 127 nodes of the manuscript to the formalization. The nodes are
its theorems, lemmas, propositions, definitions, cited results and remarks; the table gives each
node's Lean statement and proof.

* `formal/EG/Spec` holds 320 statements, each proved in `formal/EG/Proof` or `formal/EG/Lib`.
* 96 nodes have Lean statements; every theorem, proposition, corollary and fact is among them, and
  every lemma except one proof-internal lemma about the Lent sets.
* 11 nodes are realised by definitions only.
* 2 nodes are proof-internal constructions.
* 18 nodes are not formalized: remarks, notation, and results of Bucić–Montgomery that are cited
  only for their proof structure or are not used.

217 of the 320 statements lie in the import closure of the final theorem. The other 103 are proved
and kernel-checked but not used by it. Often the consumer calls the underlying library lemma
directly instead of the statement. `CORRESPONDENCE.md` marks these 103 with ○.

The cited results are **proved in Lean, not assumed**:

* Lovász's path-and-cycle decomposition theorem [Lov68];
* Haxell's matchability condition [Hax95];
* Bucić–Montgomery's Lemma 25 (a long cycle in an expander, in the explicit form of the
  manuscript), Proposition 8, Proposition 12 and Corollary 22;
* Chernoff bounds and Markov's inequality, and a Bernstein-type inequality for bounded differences;
* Euler circuits and T-joins;
* Hall's theorem, via Mathlib;
* the elementary `O(n log n)` long-cycle bound (manuscript Fact 1.6).

`CORRESPONDENCE.md` Part 2 lists the Lean names and says which of these theorems the final theorem
uses. [Lov68] is L. Lovász, *On covering of graphs*, in Theory of Graphs (Proc. Colloq., Tihany,
1966), Academic Press, 1968, pp. 231–236, as cited by Bucić–Montgomery. [Hax95] is P. E. Haxell,
*A condition for matchability in hypergraphs*, Graphs Combin. 11 (1995), 245–248 [CHECK: taken
from the manuscript's bibliography, not verified against the paper].

## Verification record

The run links in the table below point to the private development repository
steelwheel01/Erdos-Proof, from which this repository was exported. That repository is private (its
runners are GitHub's private-repository runners, `formal/work/p3/ACCEPT.md`), so **those links are
not publicly inspectable**: they work only for its collaborators. The detailed record of each of
those runs is `formal/work/p3/ACCEPT.md`. The public evidence for this repository is its own release
run and offline check (the last two rows). Archived logs of the
development runs may be attached to the GitHub release, labelled as coming from a private
repository.

| Date (UTC) | What | Commit | Result |
|---|---|---|---|
| 2026-09-30 | local run of the §4 checks (developer-mode gate; comparator in non-release mode as root; leanchecker per library) (`formal/work/p3/ACCEPT.md`) | tree after `d264c23` | gate DEV-PASS; build OK; `lint --release` 0 findings; lock 0 violations; axiom scan 11,056 constants, 0 `sorryAx`; **FinalCheck (strict): PASS**, kernel replay of 10,085 project declarations, both pins match; `leanchecker EG`, `EGTest`: exit 0; **`leanchecker --fresh EGCheck.Final`: exit 0**; comparator dry run as root (release config): "Your solution is okay!" |
| 2026-09-30 | formal-ci run 36739517378 (`https://github.com/steelwheel01/Erdos-Proof/actions/runs/36739517378`, private, not publicly inspectable) | `daf12f47aef15962ca87412744b587ff8d832ce7` | all 26 steps green on a GitHub-hosted runner (gate and gate red-team; checksum-verified toolchain; pins; lint; checker red-team; full build; axiom scan; FinalCheck scan; STATEMENT.md; statement lock; sorry ratchet; per-library leanchecker; `EGCheck.Final`; FinalCheck red-team; comparator-layout red-team) |
| 2026-09-30 | formal-release run 1, 36758690862 (`https://github.com/steelwheel01/Erdos-Proof/actions/runs/36758690862`, private, not publicly inspectable), tag `release-2026-09-30` | `d249d5f5387bc871519427190dc942b4f93b5ffb` (= `EG_TRUST_REF`) | **comparator job: SUCCESS**. Release mode, run as an unprivileged systemd unit; axioms `propext`, `Quot.sound`, `Classical.choice` only; "Lean default kernel accepts the solution" / "Your solution is okay!". build job: SUCCESS. verify job: stopped at the memory preflight (7 GiB runner), before any check; an infrastructure stop, not a proof failure |
| 2026-09-30 | formal-release run 2, 36767721300 (`https://github.com/steelwheel01/Erdos-Proof/actions/runs/36767721300`, private, not publicly inspectable), tag `release-2026-09-30b` | `f7398e12758c1898ca60614263a2455a9f1dc78f` (= `EG_TRUST_REF`; gate SHA-256 `99f1f34f03a9f56bd036d12b7523b3dffc4c15820b4c6209363dfbb99a0f234c`) | **comparator job: SUCCESS**: release mode, unprivileged systemd unit, "Lean default kernel accepts the solution" / "Your solution is okay!". build job: SUCCESS. verify job: SUCCESS (7 GiB runner, swap-backed preflight): trusted gate PRISTINE: PASS; pins; release lint; checker red-team (14 cases); upstream statement rebuilt from pinned sources; STATEMENT.md regenerated without diff; statement lock; axiom scan (11,057 constants under `EG`/`EGTest`/`EGCheck`, 0 `sorryAx`); sorry ratchet; **strict FinalCheck: PASS** (0 failures, 0 warnings; kernel replay of 10,085 project declarations, both pins match); **`leanchecker EG`: exit 0** (13 min 25 s); **`leanchecker EGTest`: exit 0** (1 min 7 s); **`leanchecker --fresh EGCheck.Final`: exit 0 (36 min 48 s)**. All three jobs: SUCCESS |
| 2026-09-30 | offline check of `formal/TRUST.md` §4.2 for release run 2 (`formal/work/p3/ACCEPT.md`, "TRUST.md §4.2 offline check for release run 2") | T = R = `f7398e12758c1898ca60614263a2455a9f1dc78f` | **PRISTINE: PASS**: the gate of T (SHA-256 `99f1f34f…`, equal to the tree copy), run with `--trust-ref T` in a fresh clone checked out at R, checked 1264 files, trusted zone 100/100 matching pins; `git diff T R` is empty and the three `git ls-files` checks print nothing; the gate steps of the jobs log `HEAD` = `EG_TRUST_REF` = f7398e1. Release run 2 therefore counts as evidence for `f7398e1` (`formal/TRUST.md` §4.3) |
| 2026-10-01 | formal-release run 36795612102 of this repository (https://github.com/steelwheel01/erdos-gallai-lean/actions/runs/36795612102), tag `release-2026-10-01` | `a11bb45847101e0d1595089bc390c59f82ad1135` (= `EG_TRUST_REF`; gate SHA-256 `e8e10825a36148c00db43e5110937782ee2cf5553675e6a8e689f2252ca5051a`) | **All three jobs: SUCCESS.** comparator: release mode, unprivileged systemd unit, "Your solution is okay!". build: SUCCESS. verify (7 GiB runner, swap-backed preflight): trusted gate PRISTINE: PASS (logged `HEAD` = `EG_TRUST_REF`); pins; release lint; checker red-team; upstream statement rebuilt from pinned sources (statement-sha256 `4cb2cd56…`, closure-sha256 `39d6e8c3…`); STATEMENT.md; statement lock (1234 constants / 277 files, 0 violations); axiom scan (11,057 constants, 0 `sorryAx`, 0 violations); sorry ratchet (frontier 0); **strict FinalCheck: PASS** (0 failures, 0 warnings; statement `Expr.equal` to `Erdos184.erdos_184`; axioms exactly `propext`, `Classical.choice`, `Quot.sound`; both pins match); **`leanchecker EG`: exit 0** (11 min 8 s); **`leanchecker EGTest`: exit 0** (55 s); **`leanchecker --fresh EGCheck.Final`: exit 0** (33 min 19 s) |
| 2026-10-01 | offline check of `formal/TRUST.md` §4.2 for run 36795612102 | T = R = `a11bb45847101e0d1595089bc390c59f82ad1135` | **PRISTINE: PASS**: the gate of T (SHA-256 `e8e10825…`), run with `--trust-ref T` in a fresh clone checked out at R, checked 993 files, trusted zone 100/100 matching pins; `git diff T R` is empty; the three `git ls-files` checks print nothing. Run 36795612102 therefore counts as evidence for `a11bb45` (`formal/TRUST.md` §4.3). Record: `formal/APPROVALS/2026-10-01-public-release-run.md` |


A run is evidence only together with the offline check of §4.2. A modified workflow can skip the
gate, so a run cannot certify itself (`formal/TRUST.md` §2 item 8). By `formal/TRUST.md` §4.3, a
release is accepted only if the offline check passes and all three jobs pass.

**Which tree each run checked.** Release run 2 checked `T = R = f7398e1` (approval
`formal/APPROVALS/2026-09-30-release-swap-preflight.md`, gate SHA-256 `99f1f34f…`). The published
tree has a different trusted zone: `formal/TRUST.md` was changed in `fc15866` (§8 items 1–2 marked
RESOLVED), and the gate was re-pinned in `19d0754` (gate SHA-256 `e8e10825…`,
`formal/APPROVALS/2026-09-30-trust-s8-resolved.md`). A commit at or after `fc15866` therefore fails
`--trust-ref f7398e1`. The Lean sources (`formal/EG`, `formal/EGTest`, `formal/EGCheck`,
`formal/comparator/Solution.lean`) are unchanged since `f7398e1`. Run 2 is therefore evidence for
`f7398e1` only. The evidence for this repository is the release run in the public repository (the
last two rows).

## Known limitations and open items

* **No human review.** Nobody has checked the mathematics of the manuscript, the Lean
  formalization, or the fidelity of the upstream statement.
* **Residual trust** that no checker removes (`formal/TRUST.md` §2 items 9–10 and §8):
  * the `.olean` loader on adversarial input (§8 item 6);
  * the Mathlib `.olean` cache, which is tied to the sources only through the closure pin,
    comparator's Challenge build and `leanchecker --fresh` (§8 item 13);
  * the unpinned Go toolchain that builds landrun (§8 item 11);
  * the two different parsers used to validate and extract the build artifact (§8 item 3);
  * unrestricted IO of project code in the untrusted `build` job (and in CI), bounded by job
    separation, the path-filtered artifact and comparator's sandbox (§8 item 7);
  * the offline check of `formal/TRUST.md` §4.2 is a manual step; it is not automated (§8 item 4);
  * GitHub's infrastructure, for the recorded runs.
* **Open items in `formal/TRUST.md` §8.** §8 still lists items 3–8 and 11–13 without a RESOLVED
  mark (and items 9–10, which are stale; see below). Items 5 (stage α) and 8 (red-team
  expectations for the pre-hardening `Final.lean`) are moot or stale at stage γ; items 3, 4, 6, 7,
  11, 12 (slow red-team suites run only weekly, on dispatch, or when the checkers change) and 13 are
  residual trust or process gaps that remain open. Its preamble ("No release may be claimed until
  every item below is closed") is pinned text and has not been updated. The acceptance checks
  reported in this README are therefore not a claim that §8 is closed.
* **Pinned documents with outdated status text.** Some pinned files still describe the project
  before the proof was complete:
  * `formal/TRUST.md`:
    * the header ("DRAFT — pre-release … The proof is incomplete");
    * §1 (l. 73-78), which says that the committed `EGCheck/Final.lean` "still imports only
      `EGCheck.Bridge`, uses `type_of% @Erdos184.erdos_184.{u}`". This is out of date: the pinned
      `Final.lean` imports the upstream module first and uses `@_root_`, as described
      [above](#what-is-proved);
    * §4.3: "None has yet run on GitHub" (l. 413-414) and "until that is applied, the job fails
      closed" (l. 520-521);
    * §7: the proposal-time gate hash `a29e7d7d…`;
    * §8 items 9 and 10, which read as open;
  * the docstring of `formal/EGCheck/Final.lean` ("expected to fail until phase P4");
  * `.github/workflows/release.yml`: the header comment (l. 1-4, "proposed in
    formal/staging/TRUST.md.proposed", "Expected to fail until phase P4") and l. 30-31 ("until
    that is applied the job fails closed");
  * `formal/comparator/README.md` l. 51 ("Until it is approved, …").

  They are pinned, so changing them is a trusted-boundary change: approval, re-pin and a new trust
  commit (`formal/TRUST.md` §6). The header paragraph of `formal/work/p3/ACCEPT.md` ("None of that has run
  yet") predates the release runs; its release-run sections are current. Those sections and this
  README describe the current state.
* **`formal/work/`** is an unedited AI working record. Parts of it are superseded, for example notes
  that describe statements as `sorry` that are now proved.
* **References to files that are not in this repository.** Exported files, including the pinned
  `formal/TRUST.md` (§2 item 4 cites `STATE.md`, "P0 — DONE"), `proofs/manuscript/ERRATA_v6.1.md`,
  `formal/work/p4/DEVIATIONS.md` and many `formal/work/` notes, refer to `STATE.md`, `LEDGER.md`,
  `SUMMARY.md`, `papers/`, `code/`, `proofs/manuscript/g0/`, `proofs/manuscript/v61/` and other
  files of `proofs/manuscript/` (for example `outline.txt`, `notation.txt`). Of these, only
  `proofs/manuscript/v61/PATCHES.md` and `proofs/manuscript/v61/FIXES.md` (the manuscript patch
  record cited by the errata) are included here. All other such references point to the private
  development repository steelwheel01/Erdos-Proof and cannot be followed from this repository.
* **Historical `sorry` mentions in the Lean sources.** Some Lean docstrings and comments (for
  example `formal/EG/Spec/Ext/BMLemma25.lean`) still describe proofs as `sorry` stubs; they are
  historical. The authoritative evidence is the axiom scan and comparator/FinalCheck (0 `sorryAx`).
* **Degenerate manuscript errors repaired in Lean.** For example, Lemma 14^τ (c) of manuscript v6.1 is
  false as stated for `τ = 0` (`EGTest.ProbeP3A.lem14tau_c_literal_false`); the Lean statement adds
  `0 < τ`, which holds in every application. Such cases are listed in
  `proofs/manuscript/ERRATA_v6.1.md`; manuscript version 6.2 applies all of them (it adds `τ > 0` to
  Lemma 14^τ (c)).
* **Encoding decisions.** Some intermediate statements differ from a literal reading of the
  manuscript:
  * non-degeneracy hypotheses added in Lean to the v6.1 text (for example `0 < τ` in Lemma 14^τ (c),
    above; manuscript v6.2 now states it too).
    Others were found during the formalization and have since been added to the manuscript, so they
    are no longer differences (for example `2 ≤ m` in the explicit form of Bucić–Montgomery Lemma 25,
    added in v6, commit `d6f3c49`, and present in v6.1);
  * "bipartite with sides `V_a`, `V_b`" in Lemma PAR is encoded with an explicit disjointness
    hypothesis on the two sides (implied by the manuscript's wording);
  * probabilistic lemmas stated in deterministic form;
  * hypotheses on `D_*` made explicit.

  Most `EG/Spec` files (113 of 122) have a "Formal reading" section that explains these choices; the
  numeric and assembly files `Num/{CC,L17s,OV,StarInputs}`, `Gamma/{Sat,N0}`, `Main` and
  `Chain/{JSLCSteps,EngineMult}` explain their reading in the docstrings. The cases are also listed in `CORRESPONDENCE.md`.
  Encoding decisions affect only the correspondence with the manuscript, not the checked final
  statement.

## Disclosure

The proof and this formalization were developed with substantial assistance from the AI system
Claude (Anthropic), under the author's direction. The author takes full responsibility for the
content. Comments and questions are welcome as GitHub issues on this repository.

## Citing, license

* How to cite: see `CITATION.cff`.
* License: Apache License 2.0 (`LICENSE`; copyright and provenance in `NOTICE`). `formal/comparator/Challenge.lean` is a
  copy, and `formal/comparator/Solution.lean` a modified copy, of a file of google-deepmind/formal-conjectures
  (Apache License 2.0). Both keep their Apache-2.0 headers, and `Solution.lean` carries a
  modification notice. `formal/comparator/patches/*.patch` modifies leanprover/comparator
  (Apache License 2.0).
* Context. The conjecture is due to Erdős and Gallai (1960s). Bucić and Montgomery proved the bound
  `O(n log* n)` (arXiv:2211.07689; Advances in Mathematics 437 (2024), 109434), improving the
  `O(n log log n)` bound of Conlon, Fox and Sudakov (arXiv:1310.0632). Montgomery's survey
  (arXiv:2607.26049, July 2026) surveys the method.
