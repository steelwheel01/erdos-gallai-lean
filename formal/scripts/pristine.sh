#!/bin/sh
# formal/scripts/pristine.sh — the trusted PRE-CHECK ("gate") of every trusted job and of the manual
# release audit. It must run FIRST: before any `lake`, `lean`, `python3`, `lake exe cache get`, and
# before any other script of this repository. Written in POSIX sh; it needs only git and coreutils
# (sha256sum or shasum, find, sort, comm, cmp, cp, awk, sed) and never executes a file of the
# repository. Details: formal/work/trust/gate2.md; the attacks it closes: APPROVALS/reviews/
# trust2.opus.md N1 (lakefile.lean), N2 (lock self-check), N3 (Python stdlib shadowing).
#
# Usage (from anywhere inside the checkout):
#   sh formal/scripts/pristine.sh [-C DIR] [--allow-build | --dev] [--trust-ref REF]
#                                 [--snapshot DIR [--link-lake]] [--verify-snapshot DIR] [-q]
#   sh formal/scripts/pristine.sh --print-pins | --write-pins      (integrator, at an approval)
#
# Modes:
#   (default)      STRICT. The worktree must be byte-identical to HEAD (compared by git blob id of
#                  the raw bytes, `hash-object --no-filters`, so no clean/smudge filter, textconv,
#                  fsmonitor or autocrlf is involved), with NO untracked and NO ignored files (the
#                  file list comes from `find`, so .gitignore cannot hide anything). Use it on a
#                  fresh checkout, before anything else has run.
#   --allow-build  STRICT, except that formal/.lake/ (Lake's build and package directory) may exist.
#                  For re-checks after `lake exe cache get` / `lake build` (e.g. CI post-build).
#   --dev          Developer mode: modified and untracked files are allowed (the policy below still
#                  applies to them); formal/.lake/ and __pycache__/ are skipped with a warning. The
#                  verdict is "PRISTINE: DEV-PASS", which is NOT a trusted verdict.
#   --trust-ref SHA  Additionally require every file of the trusted zone (below) and this gate
#                  script itself to be identical to the user-approved trust commit SHA. SHA must be
#                  a FULL 40-hex commit id: tags and branches are rejected, because anyone with push
#                  rights can move them (trust3.fable Y11b). This removes the self-verification
#                  problem (trust2.opus N2): run the SHA copy of this script, e.g.
#                    git show SHA:formal/scripts/pristine.sh > "$T/gate.sh" && sh "$T/gate.sh" --trust-ref SHA
#   --snapshot DIR After a PASS, copy every checked file of formal/, .github/ and .claude/ to
#                  DIR/{formal,.github,.claude} (files read-only), with DIR/formal/.lake an empty
#                  directory (or, with --link-lake, a symlink to the checkout's formal/.lake). All
#                  later steps run from DIR/formal, so nothing that runs after the gate can change
#                  the checkers they use. The copy is verified after copying.
#   --verify-snapshot DIR  Re-verify a snapshot: every pinned file matches its pin, no extra files
#                  in the pinned zone. (No tree checks unless combined with a mode.)
#   --print-pins   Print the pin block for the current worktree; --write-pins rewrites the block
#                  below in place. Only at an approval, and the diff of the block is reviewed.
#
# What is rejected (each finding prints `REJECT <category>: <path>: <reason>`; exit 1):
#   * anything that makes Lake run repository code or read repository config other than the pinned
#     formal/lakefile.toml: any `lakefile.lean` / `lakefile.toml` / `lakefile.olean` / `leanpkg.toml`
#     / `lake-manifest.json` / `lean-toolchain` / `lean-toolchain.toml` anywhere else (matched
#     case-insensitively, for case-insensitive file systems), any `.lake/` or `lake-packages/`
#     directory in the tree (a committed Lake workspace, cached `lakefile.olean` or package
#     checkout), and any change to formal/lakefile.toml, lake-manifest.json, lean-toolchain (pinned);
#   * Python code that the trusted jobs could import: any `.py` in formal/ outside formal/scripts/,
#     any file in formal/scripts/ that is not in the pinned allowlist below, `*.py` at the repository
#     root, and anywhere: `*.pth`, `sitecustomize.py`, `usercustomize.py`, `__pycache__/`, `*.pyc`,
#     `*.pyo`, `*.pyd`, native modules `*.so*`/`*.dylib`/`*.dll`, `pyvenv.cfg`, `.python-version`
#     (the scripts also run Python with -I, so this is the second layer);
#   * tool-manager / shell / editor hooks that run code on entering or opening a directory:
#     `.envrc` (direnv), `.env`, `.tool-versions` (asdf), `mise.toml`/`.mise*`/`.rtx.toml`,
#     `.node-version`/`.nvmrc`/`.ruby-version`/`.sdkmanrc`, `go.work*`/`go.env`, `.npmrc`/`.yarnrc*`,
#     shell rc files, `.curlrc`/`.wgetrc`/`.netrc`, `.vscode/`, `.devcontainer/`, `.idea/`,
#     `.husky/`, `.pre-commit-config.yaml`, `.mcp.json`, `CLAUDE.local.md`, and `.claude/` or
#     `.github/` directories other than the pinned top-level ones;
#   * git mechanisms: `.gitattributes` (filters, diff drivers), `.gitmodules`, `.lfsconfig`,
#     `.gitconfig`, nested `.git`, symlinks and submodules in HEAD, symlinks / FIFOs / devices in the
#     worktree, file names with control or non-ASCII characters, conflicted index entries; in the
#     local/worktree git config: hooksPath, fsmonitor, sshCommand, pager, askPass, gitProxy,
#     editor, filter.*, diff.external, diff.*.command/textconv, merge.*.driver, credential helpers,
#     protocol.*, uploadpack.packObjectsHook, gpg programs, url.*.insteadOf; and any non-sample hook
#     in the hooks directory;
#   * formal/ outside the allowed zones: proof zone `EG.lean`, `EGTest.lean`, `EGCheck.lean`,
#     `EG/**.lean`, `EGTest/**.lean`, `EGCheck/**.lean`, `comparator/Solution.lean` (module path
#     components [A-Za-z_][A-Za-z0-9_]*); inert data `*.md` at the top level, `LOCK.json`,
#     `APPROVALS/**.md`, `work/**.{md,json}`, `status/**.{md,json}`, `staging/**.{md,proposed}`;
#   * the TRUSTED ZONE, every file of which must be listed in the pin block with its SHA-256:
#     formal/scripts/** (this script excepted: it cannot pin itself — see --trust-ref), formal/
#     redteam/**, formal/comparator/** except Solution.lean, formal/{lakefile.toml,
#     lake-manifest.json,lean-toolchain,TRUST.md,STATEMENT.md,EGCheck/Final.lean}, .github/**,
#     .claude/**. A new, missing or changed file there is rejected.
#
# What this does NOT do: it does not decide anything about the proof (that is comparator,
# leanchecker --fresh and FinalCheck), and it cannot protect a job whose workflow file was itself
# changed so that it no longer runs this script: a GitHub run is evidence only if the workflow at
# the tested commit is the pinned one, which `--trust-ref` (or the pins) verifies offline.
# Exit code: 0 = PASS (or DEV-PASS), 1 = REJECT, 2 = usage or internal error.

set -u
LC_ALL=C; export LC_ALL
PATH="/usr/bin:/bin:${PATH:-/usr/local/bin}"; export PATH
umask 022
unset CDPATH GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES \
      GIT_CONFIG GIT_CONFIG_PARAMETERS GIT_CONFIG_COUNT GIT_EXTERNAL_DIFF GIT_NAMESPACE 2>/dev/null || true
GIT_OPTIONAL_LOCKS=0; export GIT_OPTIONAL_LOCKS   # never write the index while checking
GIT_TERMINAL_PROMPT=0; export GIT_TERMINAL_PROMPT

SELF_PATH="formal/scripts/pristine.sh"
NL='
'
TAB=$(printf '\t')

# ---- pins (the trusted zone). Regenerate ONLY at an approval: --write-pins; review the diff. --------
pins() {
cat <<'PINS'
# BEGIN-PINS
32baa7c3641db97458dbec15d04530cd5e6e41891d4b45f873ead276b4eb379f  .claude/settings.json
f0a3e348c035bad19596312158ec3300e1f14b731b4be3c90b40c700e3e0f889  .github/CODEOWNERS
8d17bad904e13782af9867fe25a6ce876d5b880faabfc807c669a4958358b6a0  .github/workflows/ci.yml
8121c569542b802d6a7e9a39639595cd9ba47d5bd4a6b0c814ef69b5ee4d9117  .github/workflows/release.yml
7e50b44d892e2f7b74ec80c29629b22268da907b1e1ccff03ff83fc05e43e4f1  formal/EGCheck/Final.lean
b59334ff883f239753846581b9919b11f6bf91c7475b53386e34d1ba837eb7e0  formal/STATEMENT.md
b428e6b301f9a26705060968ded2be1b187f479388c86994610f16aede6f043c  formal/TRUST.md
9f36e4e053285cd8b886042eb609ace5f21f49bd81903eebca8000ff03e020d6  formal/comparator/Challenge.lean
13aecef9434763439a8ae5ec9f2fc2738fadc264bc44bec6218734e291e5cb0b  formal/comparator/README.md
a699ad9e88eef161fdff5853300cc827268cb691475ec7ded9c2992ccd0b3c83  formal/comparator/config.json
16c5b0e6db4f620e2cbb47a179b7705efc3f3b3e70eac9addbca1840fd07328d  formal/comparator/patches/comparator-fd5d5bcf-lean-v4.33.1.patch
0b9e8a00f07b57e5ad34c461ff00786767c0f91038b61de02b07c13384dd82b4  formal/lake-manifest.json
6aa41d0cd97ff7128887cec7cc36085140f03a68f1ff90a4a80602cd873566b5  formal/lakefile.toml
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  formal/lean-toolchain
773ed230c46746d647adbff814c868c37a18122ecacc4ab80e52a9de8363f938  formal/redteam/bridge/F1_DefinitionChanged.lean
71ac646eb4286d013bef1a07e2e6af8e1c9104f4e8f1d8eb5e60b3f41c2ac6b4  formal/redteam/bridge/F2_StatementWeakened.lean
246ee32e39f23e52e36fa71de3c78784da67ca77c51af08c2eab79e590d0b2d5  formal/redteam/bridge/F3_KernelBypass.lean
5c89b06cdf028070d199cb263a09ba304e4c21d599db332e720a39e7a71823e2  formal/redteam/bridge/F4_ExtraAxiom.lean
31d990832740d29007627803a0ce50ea29d7cbc81e6ac9d4a08cb8a5bd79a880  formal/redteam/bridge/F5_ImportsUpstream.lean
9f25c099897d3acf78b986fe63b75d02a3c970df350e3e69f1aaf1a64d47c192  formal/redteam/bridge/README.md
3a9c26b455339dc54617aafb4f9a3a1c7798a0d11ab6d6abee1198affdd65746  formal/redteam/bridge/run.sh
8ae7919ef1aa1b6f3b2923dc44c740f6bfc343bae816bbaa747c00b4a1e15617  formal/redteam/external/README.md
86c3e01bb152500689345891438eeabcba89c010eda8cfa15290593a31076132  formal/redteam/external/patches/A/EGCheck/Bridge.lean
517c9c49f00b05c8775cc5fcc000ae0fa4e53eb5452c8558286c2da02a5183a6  formal/redteam/external/patches/A/spec
ea025a9fd0a36dc88d18a8fce59043d82fe738b3e29de5697d62b9e7cf5f6adb  formal/redteam/external/patches/A1/EGCheck/Bridge.lean
bef8b0e69ef060d788ed0d6c4721b7369d908f7cee7ac0d6cf25c0344b2cea08  formal/redteam/external/patches/A1/spec
b5dc54f3f5a2766e2d9ba4edbb452563dcde7108542dbd662b1bbf3d0d025da5  formal/redteam/external/patches/A2/EGCheck/Bridge.lean
2ad84effd08310e9cfe1760a261b94bef9858edcc8684eef6e19264de995fe27  formal/redteam/external/patches/A2/spec
d2c8adb6768d5e881d94ce67c0bbfaaa4d062992058aa75cd3c32b6c4add03e4  formal/redteam/external/patches/A3/EGCheck/Bridge.lean
6b377ece94579646a32c7f8470c325f936b4015d5420ab59e0d6ff9cb6902b92  formal/redteam/external/patches/A3/spec
e0ea7b52e3820bc997fdcd9bd7c740a1c596e0101c67cade982fbf295d06074f  formal/redteam/external/patches/A4/EGCheck/Bridge.lean
bf650696cae1fcd7f23aebecb3723ba0d6bfe28f1e01707629addf59e92f6d2c  formal/redteam/external/patches/A4/spec
331dda36e84e0792dabc91f61a12a95027bf698cc1f6da377670ed20c85d34c6  formal/redteam/external/patches/B1/EGCheck/Bridge.lean
5a64c103eca4b2ab279970d1efd435a8101e985ca13e6a0652703d2068345118  formal/redteam/external/patches/B1/spec
07b8350071726dfa487a082f05880be749d850ae7909553baa1c1fc3bedb2b39  formal/redteam/external/patches/C/EGCheck/Bridge.lean
6faf2a4932aceecf546db624be65b77738a2ba9398f08f96386669f3bfef1946  formal/redteam/external/patches/C/spec
091b70769f87a402fd1cbbbfd90b5250f44e56158e2eeb6defcf12b90c83be6e  formal/redteam/external/patches/D/EGCheck/Bridge.lean
e49c3f07a539ffc265e21e04a0c326a75ebc2fe052972de31f6c7f1c6109f896  formal/redteam/external/patches/D/EGCheck/BridgeHack.lean
424ed2fe2a8306135d43528d2cc52f3a4f422cd91946ac44505cfbadd0c17e09  formal/redteam/external/patches/D/spec
238fa76e3e04aea06ab78b3df6bb9d81f55111ba35c16d55ffff0ed2f12f9e37  formal/redteam/external/patches/IO/EGCheck/RTEvade.lean
4426b60b9bd6396503facab1360cc03de4987d086f717010468788a0943cdded  formal/redteam/external/patches/IO/spec
134e9d691cdd1d4b51b43309488237f0a1724f660e43bd3d7eddca8399e5405d  formal/redteam/external/patches/N4/EGCheck/Bridge.lean
f955ecee7e899b6fbdd886405e8e136d931444bebc9bb6c8346ade74e18c2864  formal/redteam/external/patches/N4/EGCheck/RTX1.lean
e2200c46a59226b31b6d893d3449dbc88d531e52ac40c8c8d809a12316f4333c  formal/redteam/external/patches/N4/EGCheck/RTX2.lean
15fddc822e7e3efba1175f3f5c22a845c203d7bd1a4e785b15fe4c72deb0dcc5  formal/redteam/external/patches/N4/spec
a027909185b7a2536266a92b4c8b26b8e2be6776f60db079d0d3ecbf01c6a608  formal/redteam/external/patches/t1/EGCheck/RTEvade.lean
ea8cf3420c7fadd9d40a9372efdb400943a4058409ede3fbd784db6df17f2d27  formal/redteam/external/patches/t1/spec
4ce2bc058fd0b233afcf0fa50d59858e9feef594fbd5d1ae6dfd1efc6ca1d14d  formal/redteam/external/patches/t2/EGCheck/RTEvade.lean
176e6702e882c9ebb587263be01f0bb93f9ee493c9162dab113bc3e63f977e1d  formal/redteam/external/patches/t2/spec
a94447b489d0eeed3e7b09d11409a8b3611c6cbdf1937cf0b10e78064a47f08c  formal/redteam/external/patches/t3/EGCheck/RTEvade.lean
9defd8958ecd30fb6ec879af222cb9b98739e5d88f00f38fb0952cd284c82587  formal/redteam/external/patches/t3/spec
a26086e91c01cab118c0685c8f3116bbece51086db0b4694f111999909d29024  formal/redteam/external/patches/t4/EGCheck/RTEvade.lean
a1be67326333e838fc66490972b7691fbd9437cb14bc8a6b09209406f04ebd19  formal/redteam/external/patches/t4/spec
27d4b615dcc368f4a15145775b670e7c2919fa8f168624b5a270765248e2c87d  formal/redteam/external/patches/t5/EGCheck/RTEvade.lean
a2bfed90152e48496ce61fdff636173d6f8b942c33fb36251723be348fd5b9cd  formal/redteam/external/patches/t5/spec
5634153b0b0f70fcfd1607d0f320689619e9e0317ca320891dc8fdce44c811c1  formal/redteam/external/patches/t6/EGCheck/RTEvade.lean
e401f47b472fe8ff1cecbd2929377155acd625c4f7354e206273a9766261d68e  formal/redteam/external/patches/t6/spec
d249aa419e3f3b61c7a267901dc7725569b03acc07f5c1b5777137296ecabc0a  formal/redteam/external/patches/t7/EGCheck/RTEvade.lean
74c956ce2d4ed5052f9030729b88c022da30dc2f2c9b51507fdf68f680cec91f  formal/redteam/external/patches/t7/spec
fbd94e9dc89d4ffe877c644baf6d2ec2e781c8c850f669bae924c41f97da0870  formal/redteam/external/patches/t8/EGCheck/RTEvade.lean
70045cc31bfcd8aeda1068ea7835bc89358e447cb56e70c24f1d5de86e488823  formal/redteam/external/patches/t8/spec
02a70fc64950905681ad17eda248980a453bd75a92eb6c2ce28d780de675e46a  formal/redteam/external/patches/t9/EGCheck/RTEvade.lean
5af7e9aa9f13d516aa374a2d4b098fd3d6a4fc0d91eb7459ce2b3ddf68b8b6a8  formal/redteam/external/patches/t9/spec
780389fcd2f1cbf07b93559f2142579ab986873f918720ba72f970a1ffa17a07  formal/redteam/external/redteam.sh
248eec2991785953066839156b46f83cf30f5f42468fa51fcf095c966b83fb4d  formal/redteam/gate/fixtures/envrc.fixture
89922ff3ff74f07cbda5cd2316793fc04241b8f93c9703c98ecdca8d4f3ac6c3  formal/redteam/gate/fixtures/evil.yml.fixture
1d96eb2f85bb014108e90b74be0a9254b7b00ede0d844fb1df6a7eef99134cef  formal/redteam/gate/fixtures/gitattributes.fixture
94ff4f5782ea99cdcac13c0dd4f0f48c99773aaae844f776eaa3e0ef26b4b79c  formal/redteam/gate/fixtures/hashlib.py.fixture
23f6b6c55e8d1879b513a0f3835bfa5f057552027c3dc5fabb34e1daccccd449  formal/redteam/gate/fixtures/json.py.fixture
ae0ef9ff99c6ef2fa22a39b13a9b2c8b3b09239cdf3cfb50e589d94456f34b6a  formal/redteam/gate/fixtures/lakefile.lean.fixture
ec7dc575c698208c26bc9d00529e2496558b9d715097e22797480e30ef9716de  formal/redteam/gate/fixtures/settings.local.json.fixture
0994e759c72d329e8562916c7b9d9fb8599e597698f9c9937469207ac1fbeb4e  formal/redteam/gate/fixtures/sitecustomize.py.fixture
679530d13cdae360ff0113238fa81c13b3854a57dc7a8409a2b3771a9e26c087  formal/redteam/gate/fixtures/tasks.json.fixture
726bc31c500759a69e39332854cf2f303b53cbb6fef6e9dd0591ff81e30b6f86  formal/redteam/gate/run.sh
704337f23072e05ce56617a4ff3b363be2194cfb352128d8a0d9e8b8da51309b  formal/redteam/tooling/RT/Axiom.lean
838aafb852b67e89351529a3ed936ec34eaeabbd2940597fe9044a0ddf3f0aec  formal/redteam/tooling/RT/Benign.lean
7954395c6c46c73e8a30d96a6160746d318da6f0742d2c79c7ae106360a28305  formal/redteam/tooling/RT/Bypass.lean
40fc6a63e2ef52705bd7ac0976c94dab85b9e7f4e441ebc9981b7d8a9a49db90  formal/redteam/tooling/RT/CSimp.lean
14eea64eb7a7a3af002f7ea65a919cd58571b9cc0cade0d58150f7d025f1d99c  formal/redteam/tooling/RT/CmdElab.lean
ab4b4af6ddf7ed458adfb9cdc16b3dbf02110fd5e30de209aadf8865ff82b25c  formal/redteam/tooling/RT/Fake.lean
b22f49d786d059c9a120de8cc3e7c4aa46f517dfcc2ae3a9872011fb42d38d86  formal/redteam/tooling/RT/Init.lean
e04a57195b6d5191266363bbccbabc55c6a7eb66c93b8f332d0c0b9202c95d7d  formal/redteam/tooling/RT/MacroRules.lean
b949d7eb0ed8985a13aa761e21ac1a14542431559e313b9c6421df42aa83135f  formal/redteam/tooling/RT/ModHook.lean
17d093bbfd35929bbeaa620277f8f357263efae03997663677763e5b80f342b0  formal/redteam/tooling/RT/Notation.lean
8bb0c4cd511e295d930b6d5b96c69148155ca66e979125c7db5a00c1e079e835  formal/redteam/tooling/RT/PrintAxioms.lean
b653febdef19eb5e2eeebe3bffa6b8dab1c45cd244fb2945fd8abf3a6230cbf7  formal/redteam/tooling/RT/RunTac.lean
234488f7f70ba11d39694a15cb884d3565ca280fedc9d7136580c80e3da299c4  formal/redteam/tooling/RT/Sorry.lean
df8a3261a11e03b176aa6910c8dbdd7683283cbf19811f8b860edb8f79e85f1e  formal/redteam/tooling/RT/TermElab.lean
f584eb7eb066f3fc7ae4681951fff27b1920765cea89672afab4b9783a0388e3  formal/redteam/tooling/run.sh
38756f5e812b94b908a8713ea8a772babc01becc02e77f2130927e03cb530b74  formal/scripts/Axioms.lean
6e29d2fcd8a3903464195c8852576fa4bb0d3bc6921ffcea574ce9ec9c36177a  formal/scripts/FinalCheck.lean
87c31fdaca775b6afff02205b81331f5b712d9812345ba15b8e1e433b0bd2ab8  formal/scripts/Lock.lean
91ae8a54dcb5062e89aa0ae28426a7a32fbc9c2aea185a5cbe3655ea915baebd  formal/scripts/Statement.lean
f52e2275e6b5a55b0e4694e07694f24a95fcc52416a6054b1c8e1eee9d3c8488  formal/scripts/check.sh
6e5fcf64edd1bb3ece63585748f6515fb4b2267d644cb35e77a3c9d841660169  formal/scripts/check_pins.sh
f896ed2e0bc55d39edaa28b73932e06301e7787b3340685d45590d03e782eda6  formal/scripts/comparator.sh
cc25b6498b2f85c9aa00f8e8381f6926d93aed5946da997c31e8fd8d43984232  formal/scripts/gen_roots.py
16ece6f135d1ecbe7c7eec870bba1b11c60b86dc4eb477dd582c92439aeb33f3  formal/scripts/lint.py
2fae20ef807e4fe08721ed7e128f567ea7d0decf3ae7331187aaba923fb09a45  formal/scripts/lock.py
b1b1b36f19d1fd96ba7b80e04de67f2063b94468f9652842f766069a335cda0f  formal/scripts/status.py
# END-PINS
PINS
}

die() { echo "pristine.sh: $*" >&2; exit 2; }
say() { [ "$QUIET" = 1 ] || echo "$*"; }

sha256_of() {  # $1 = file; prints the hex digest
  if command -v sha256sum >/dev/null 2>&1; then sha256sum -- "$1" | cut -c1-64
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 -- "$1" | cut -c1-64
  else die "need sha256sum or shasum"; fi
}
sha256_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -c1-64
  else shasum -a 256 | cut -c1-64; fi
}

# ---- arguments ---------------------------------------------------------------------------------------
START=.; MODE=strict; TRUST_REF=""; SNAP=""; LINK_LAKE=0; VERIFY_SNAP=""; QUIET=0; ACTION=check
while [ $# -gt 0 ]; do
  case "$1" in
    -C) [ $# -ge 2 ] || die "-C needs a directory"; START=$2; shift;;
    --allow-build) MODE=build;;
    --dev) MODE=dev;;
    --trust-ref) [ $# -ge 2 ] || die "--trust-ref needs a commit id"; TRUST_REF=$2; shift;;
    --snapshot) [ $# -ge 2 ] || die "--snapshot needs a directory"; SNAP=$2; shift;;
    --link-lake) LINK_LAKE=1;;
    --verify-snapshot) [ $# -ge 2 ] || die "--verify-snapshot needs a directory"; VERIFY_SNAP=$2; shift;;
    --print-pins) ACTION=print;;
    --write-pins) ACTION=write;;
    -q) QUIET=1;;
    -h|--help) sed -n '2,/^# Exit code/p' "$0" 2>/dev/null | sed 's/^# \{0,1\}//'; exit 0;;
    *) die "unknown option $1 (see --help)";;
  esac
  shift
done
[ -z "$SNAP" ] || [ "$MODE" != dev ] || die "--snapshot is not allowed with --dev"

SELF_SHA=""
[ -f "$0" ] && SELF_SHA=$(sha256_of "$0")

TMP=$(mktemp -d "${TMPDIR:-/tmp}/pristine.XXXXXX") || die "mktemp failed"
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
: > "$TMP/reject"; : > "$TMP/warn"
reject() { printf 'REJECT %s: %s: %s\n' "$1" "$2" "$3" >> "$TMP/reject"; }
warn()   { printf 'WARN   %s: %s: %s\n' "$1" "$2" "$3" >> "$TMP/warn"; }

pins | sed -n 's/^\([0-9a-f]\{64\}\)  \(.*\)$/\1 \2/p' | sort -k2 > "$TMP/pins"         # "sha path"
cut -d' ' -f2- "$TMP/pins" > "$TMP/pins.paths"

# Predicate: is $1 in the trusted (pinned) zone?  (this script is in the zone but pinned by --trust-ref)
in_trusted_zone() {
  case "$1" in
    formal/comparator/Solution.lean) return 1;;
    formal/scripts/*|formal/redteam/*|formal/comparator/*|.github/*|.claude/*) return 0;;
    formal/lakefile.toml|formal/lake-manifest.json|formal/lean-toolchain) return 0;;
    formal/TRUST.md|formal/STATEMENT.md|formal/EGCheck/Final.lean) return 0;;
  esac
  return 1
}

# ---- verify a snapshot (may run alone) ---------------------------------------------------------------
verify_snapshot() {  # $1 = snapshot dir
  vs=$1
  [ -d "$vs/formal" ] || { reject snapshot "$vs" "not a snapshot (no formal/)"; return; }
  (cd "$vs" && find formal/scripts formal/redteam formal/comparator .github .claude \
      formal/lakefile.toml formal/lake-manifest.json formal/lean-toolchain formal/TRUST.md \
      formal/STATEMENT.md formal/EGCheck/Final.lean ! -type d -print 2>/dev/null) \
    | grep -vx "$SELF_PATH" | grep -vx 'formal/comparator/Solution.lean' | sort > "$TMP/snap.zone"
  comm -23 "$TMP/snap.zone" "$TMP/pins.paths" | while IFS= read -r p; do
    echo "REJECT snapshot: $p: file in the trusted zone of the snapshot is not pinned"; done >> "$TMP/reject"
  while IFS=' ' read -r h p; do
    if [ -L "$vs/$p" ] || [ ! -f "$vs/$p" ]; then reject snapshot "$p" "missing or not a regular file in $vs"
    elif [ "$(sha256_of "$vs/$p")" != "$h" ]; then reject snapshot "$p" "snapshot copy does not match its pin"; fi
  done < "$TMP/pins"
  if [ -n "$SELF_SHA" ] && [ -f "$vs/$SELF_PATH" ] && [ "$(sha256_of "$vs/$SELF_PATH")" != "$SELF_SHA" ]; then
    reject snapshot "$SELF_PATH" "snapshot copy differs from the running gate script"
  fi
}

finish() {
  if [ -s "$TMP/warn" ] && [ "$QUIET" = 0 ]; then cat "$TMP/warn"; fi
  n=$(wc -l < "$TMP/reject" | tr -d ' ')
  if [ "$n" -gt 0 ]; then
    cat "$TMP/reject"
    echo "PRISTINE: FAIL ($n rejected)"
    exit 1
  fi
  if [ "$MODE" = dev ]; then echo "PRISTINE: DEV-PASS (developer mode: NOT a trusted verdict)"
  else echo "PRISTINE: PASS"; fi
  exit 0
}

if [ -n "$VERIFY_SNAP" ]; then   # standalone: verify a snapshot only
  [ "$ACTION" = check ] && [ -z "$SNAP" ] && [ -z "$TRUST_REF" ] || die "--verify-snapshot runs alone"
  verify_snapshot "$VERIFY_SNAP"
  say "info snapshot $VERIFY_SNAP checked against $(wc -l < "$TMP/pins" | tr -d ' ') pins"
  finish
fi

# ---- the repository ------------------------------------------------------------------------------
ROOT=$(cd "$START" 2>/dev/null && git rev-parse --show-toplevel 2>/dev/null) || die "$START is not inside a git checkout"
[ -n "$ROOT" ] && [ -d "$ROOT" ] || die "cannot find the repository root"
g() { git -C "$ROOT" -c core.fsmonitor=false -c core.hooksPath=/dev/null -c core.quotepath=true "$@"; }
[ -e "$ROOT/.git" ] || die "$ROOT/.git missing"
HEADC=$(g rev-parse --verify -q 'HEAD^{commit}') || die "no HEAD commit"

# ---- worktree file list (find, not git status: .gitignore cannot hide anything) ------------------------
# Lists are "path<TAB>git-blob-id" or plain paths, sorted bytewise (LC_ALL=C).
if [ -n "$( (cd "$ROOT" && find . -path ./.git -prune -o -name "*${NL}*" -print) | head -1)" ]; then
  reject names "." "a file name contains a newline; refusing to analyse this tree"; finish
fi
PRUNE_LAKE=0
if [ -e "$ROOT/formal/.lake" ] || [ -L "$ROOT/formal/.lake" ]; then
  PRUNE_LAKE=1
  case "$MODE" in
    strict) reject untracked "formal/.lake" "Lake directory present: not a fresh checkout (the gate must run before any lake call; use --allow-build for later re-checks)";;
    *) warn "$MODE" "formal/.lake" "Lake build/package directory present; not analysed";;
  esac
fi
wt_find() {  # $@ = extra find predicates (before -print)
  if [ "$PRUNE_LAKE" = 1 ]; then
    (cd "$ROOT" && find . \( -path ./.git -o -path ./formal/.lake \) -prune -o "$@" -print)
  else
    (cd "$ROOT" && find . -path ./.git -prune -o "$@" -print)
  fi
}
wt_find ! -type d | sed 's|^\./||' | sort > "$TMP/wt.all"
wt_find ! -type d ! -type f | sed 's|^\./||' | sort > "$TMP/wt.special"

skip_path() {  # paths that the current mode tolerates and does not analyse
  case "$MODE" in
    dev) case "$1" in __pycache__/*|*/__pycache__/*) return 0;; esac;;
  esac
  return 1
}
: > "$TMP/wt.list"; nskip=0
while IFS= read -r p; do
  if skip_path "$p"; then nskip=$((nskip + 1)); continue; fi
  printf '%s\n' "$p" >> "$TMP/wt.list"
done < "$TMP/wt.all"
[ "$nskip" = 0 ] || warn "$MODE" "__pycache__" "$nskip bytecode file(s) not analysed"
while IFS= read -r p; do
  skip_path "$p" && continue
  reject special "$p" "symlink, FIFO, socket or device file in the worktree"
done < "$TMP/wt.special"
grep -E '[^ -~]|["\\]' "$TMP/wt.list" | while IFS= read -r p; do
  echo "REJECT names: $p: control, non-ASCII, quote or backslash character in a file name"; done >> "$TMP/reject"

# ---- HEAD tree -------------------------------------------------------------------------------------
g ls-tree -r --full-tree "$HEADC" > "$TMP/head.raw" || die "git ls-tree failed"
: > "$TMP/head.oid"
while IFS= read -r line; do
  meta=${line%%"$TAB"*}; p=${line#*"$TAB"}
  mode=${meta%% *}; oid=${meta##* }
  case "$p" in \"*) reject names "$p" "HEAD path needs quoting (control/non-ASCII/quote/backslash)"; continue;; esac
  case "$mode" in
    100644|100755) printf '%s\t%s\n' "$p" "$oid" >> "$TMP/head.oid";;
    120000) reject git "$p" "symlink committed in HEAD";;
    160000) reject git "$p" "submodule (gitlink) in HEAD";;
    *) reject git "$p" "unexpected git file mode $mode";;
  esac
done < "$TMP/head.raw"
sort -t "$TAB" -k1,1 "$TMP/head.oid" -o "$TMP/head.oid"
cut -f1 "$TMP/head.oid" > "$TMP/head.list"
if [ -n "$(g ls-files -u | head -1)" ]; then reject git "index" "unmerged (conflicted) index entries"; fi

# ---- STRICT: worktree == HEAD, byte for byte ----------------------------------------------------------
if [ "$MODE" != dev ]; then
  comm -23 "$TMP/wt.list" "$TMP/head.list" | while IFS= read -r p; do
    echo "REJECT untracked: $p: file in the worktree that is not in HEAD (untracked or ignored)"; done >> "$TMP/reject"
  comm -13 "$TMP/wt.list" "$TMP/head.list" | while IFS= read -r p; do
    echo "REJECT missing: $p: file of HEAD missing from the worktree"; done >> "$TMP/reject"
  comm -12 "$TMP/wt.list" "$TMP/head.list" > "$TMP/common"
  (cd "$ROOT" && git -c core.fsmonitor=false hash-object --no-filters --stdin-paths < "$TMP/common") > "$TMP/common.oid" \
    || die "git hash-object failed"
  paste "$TMP/common" "$TMP/common.oid" > "$TMP/wt.oid"
  join -t "$TAB" -o 0,1.2,2.2 "$TMP/wt.oid" "$TMP/head.oid" | while IFS="$TAB" read -r p a b; do
    [ "$a" = "$b" ] || echo "REJECT modified: $p: worktree bytes differ from HEAD"; done >> "$TMP/reject"
  FILES="$TMP/head.list"
else
  FILES="$TMP/wt.list"
fi

# ---- per-path policy ---------------------------------------------------------------------------------
deny() {  # $1 = path; prints a reason when the path is forbidden anywhere in the repository
  p=$1; b=${p##*/}; s="/$p/"
  case "$p" in
    formal/lakefile.toml|formal/lake-manifest.json|formal/lean-toolchain) return;;
  esac
  case "$s" in
    */.lake/*|*/lake-packages/*) echo "Lake workspace/package/cache directory committed in the tree"; return;;
    */.git/*) echo "nested .git (another repository or a gitdir file)"; return;;
    */__pycache__/*) echo "Python bytecode cache"; return;;
    */.vscode/*|*/.devcontainer/*|*/.idea/*|*/.husky/*|*/.mise/*|*/.flox/*) echo "editor/container/tool config that can run tasks on open"; return;;
  esac
  case "$p" in
    .claude/*|.github/*) ;;
    *) case "$s" in */.claude/*|*/.github/*) echo "nested .claude/.github configuration"; return;; esac;;
  esac
  case "$b" in
    [Ll][Aa][Kk][Ee][Ff][Ii][Ll][Ee].[Ll][Ee][Aa][Nn]|[Ll][Aa][Kk][Ee][Ff][Ii][Ll][Ee].[Tt][Oo][Mm][Ll]|[Ll][Aa][Kk][Ee][Ff][Ii][Ll][Ee].[Oo][Ll][Ee][Aa][Nn]*|[Ll][Aa][Kk][Ee][Ff][Ii][Ll][Ee].[Ii][Ll][Ee][Aa][Nn]|[Ll][Ee][Aa][Nn][Pp][Kk][Gg].[Tt][Oo][Mm][Ll]|[Ll][Aa][Kk][Ee]-[Mm][Aa][Nn][Ii][Ff][Ee][Ss][Tt].[Jj][Ss][Oo][Nn]|[Ll][Ee][Aa][Nn]-[Tt][Oo][Oo][Ll][Cc][Hh][Aa][Ii][Nn]|[Ll][Ee][Aa][Nn]-[Tt][Oo][Oo][Ll][Cc][Hh][Aa][Ii][Nn].[Tt][Oo][Mm][Ll])
      echo "Lake/elan configuration file (Lake elaborates lakefile.lean and runs its #eval; elan follows lean-toolchain)"; return;;
    *.pth|sitecustomize.py|usercustomize.py|*.pyc|*.pyo|*.pyd|pyvenv.cfg|.python-version)
      echo "Python start-up / import hook"; return;;
    *.so|*.so.*|*.dylib|*.dll) echo "native shared library (importable/loadable code)"; return;;
    .envrc|.env|.env.*|.tool-versions|mise.toml|mise.*.toml|.mise.toml|.mise.*.toml|.rtx.toml|.node-version|.nvmrc|.ruby-version|.sdkmanrc|go.work|go.work.sum|go.env|.npmrc|.yarnrc|.yarnrc.yml)
      echo "tool-manager/direnv file (selects binaries or runs code on entering the directory)"; return;;
    .bashrc|.bash_profile|.bash_login|.bash_logout|.profile|.zshrc|.zshenv|.zprofile|.zlogin|.inputrc|.curlrc|.wgetrc|.netrc)
      echo "shell/network client rc file"; return;;
    .gitattributes|.gitmodules|.lfsconfig|.gitconfig|.git)
      echo "git attributes/submodule/config file (filters, diff drivers, submodules)"; return;;
    .pre-commit-config.yaml|.mcp.json|CLAUDE.local.md)
      echo "hook/agent configuration that runs commands"; return;;
  esac
  case "$p" in
    */*) ;;
    *.py) echo "Python module at the repository root"; return;;
  esac
}

module_path_ok() {  # $1 = path relative to formal/, ending in .lean
  case "$1" in *.lean) ;; *) return 1;; esac
  stem=${1%.lean}
  case "$stem" in ''|*[!A-Za-z0-9_/]*|/*|*/|*//*) return 1;; esac
  case "/$stem" in */[0-9]*) return 1;; esac
  return 0
}

formal_zone() {  # $1 = path under formal/ outside the trusted zone; prints a reason when not allowed
  r=${1#formal/}
  case "$r" in
    EG.lean|EGTest.lean|EGCheck.lean|comparator/Solution.lean) return;;
    EG/*|EGTest/*|EGCheck/*)
      module_path_ok "$r" || echo "proof zone admits only Lean modules with plain [A-Za-z0-9_] path components"
      return;;
    LOCK.json) return;;
    APPROVALS/*.md) return;;
    work/*.md|work/*.json|status/*.md|status/*.json|staging/*.md|staging/*.proposed) return;;
    */*) echo "not an allowed location/type in formal/ (proof zone: EG*/**.lean; data: *.md/*.json in APPROVALS, work, status, staging)"; return;;
    *.md) return;;
  esac
  echo "not an allowed top-level file in formal/"
}

: > "$TMP/zone.list"
while IFS= read -r p; do
  why=$(deny "$p")
  if [ -n "$why" ]; then reject forbidden "$p" "$why"; continue; fi
  if in_trusted_zone "$p"; then
    [ "$p" = "$SELF_PATH" ] || echo "$p" >> "$TMP/zone.list"
    continue
  fi
  case "$p" in
    formal/*)
      why=$(formal_zone "$p")
      [ -z "$why" ] || reject zone "$p" "$why";;
  esac
  case "$p" in *.py) case "$p" in formal/scripts/*) ;; formal/*) reject python "$p" "Python file in formal/ outside formal/scripts/";; esac;; esac
done < "$FILES"
sort -u "$TMP/zone.list" -o "$TMP/zone.list"
grep -qx "$SELF_PATH" "$FILES" || reject zone "$SELF_PATH" "the gate script itself is missing from the tree"

# ---- print / write pins ------------------------------------------------------------------------------
if [ "$ACTION" != check ]; then
  [ "$MODE" = dev ] || warn pins "-" "pins are computed from the worktree"
  { echo "# BEGIN-PINS"
    while IFS= read -r p; do printf '%s  %s\n' "$(sha256_of "$ROOT/$p")" "$p"; done < "$TMP/zone.list"
    echo "# END-PINS"; } > "$TMP/newpins"
  if [ "$ACTION" = print ]; then cat "$TMP/newpins"; exit 0; fi
  [ -f "$ROOT/$SELF_PATH" ] || die "cannot find $SELF_PATH to rewrite"
  awk -v f="$TMP/newpins" '
    /^# BEGIN-PINS$/ { while ((getline l < f) > 0) print l; skip = 1; next }
    /^# END-PINS$/   { skip = 0; next }
    !skip { print }' "$ROOT/$SELF_PATH" > "$TMP/self.new" || die "awk failed"
  cat "$TMP/self.new" > "$ROOT/$SELF_PATH"
  echo "pristine.sh: wrote $(grep -c '^[0-9a-f]\{64\}  ' "$TMP/newpins") pins into $SELF_PATH; review the diff"
  exit 0
fi

# ---- trusted zone: allowlist + SHA-256 pins ------------------------------------------------------------
comm -23 "$TMP/zone.list" "$TMP/pins.paths" | while IFS= read -r p; do
  echo "REJECT unpinned: $p: file in the trusted zone that is not in the pinned allowlist"; done >> "$TMP/reject"
nok=0
while IFS=' ' read -r h p; do
  if ! grep -qxF "$p" "$TMP/zone.list"; then reject pin "$p" "pinned file is missing"; continue; fi
  got=$(sha256_of "$ROOT/$p")
  if [ "$got" = "$h" ]; then nok=$((nok + 1)); else reject pin "$p" "SHA-256 $got differs from the pin $h"; fi
done < "$TMP/pins"
[ -s "$TMP/pins" ] || reject pin "-" "the pin block is empty (run --write-pins at an approval)"

# ---- the gate script itself --------------------------------------------------------------------------
TREE_SELF=""
[ -f "$ROOT/$SELF_PATH" ] && TREE_SELF=$(sha256_of "$ROOT/$SELF_PATH")
if [ -z "$TRUST_REF" ] && [ -n "$SELF_SHA" ] && [ -n "$TREE_SELF" ] && [ "$SELF_SHA" != "$TREE_SELF" ]; then
  reject self "$SELF_PATH" "the running gate script ($SELF_SHA) is not the tree's copy ($TREE_SELF); use --trust-ref"
fi

# ---- local git state (not from the repository, but it runs code on git commands) ----------------------
{ g config --list --show-scope 2>/dev/null || g config --local --list 2>/dev/null | sed "s/^/local$TAB/"; } \
  | tr 'A-Z' 'a-z' > "$TMP/gitcfg"
while IFS= read -r line; do
  scope=${line%%"$TAB"*}; kv=${line#*"$TAB"}; key=${kv%%=*}
  case "$scope" in local|worktree) ;; *) continue;; esac
  case "$key" in
    core.hookspath|core.fsmonitor|core.sshcommand|core.pager|core.askpass|core.gitproxy|core.editor|\
    core.alternaterefscommand|sequence.editor|diff.external|diff.*.command|diff.*.textconv|filter.*|\
    merge.*.driver|credential.helper|credential.*.helper|protocol.*|uploadpack.packobjectshook|\
    gpg.program|gpg.*.program|pager.*|interactive.difffilter|url.*.insteadof|url.*.pushinsteadof)
      reject gitconfig "$key" "local git configuration that runs commands or redirects fetches";;
    include.*|includeif.*) warn gitconfig "$key" "local config includes another file (its keys are checked above)";;
  esac
done < "$TMP/gitcfg"
# (not via g(): its `-c core.hooksPath=/dev/null` would hide the hooks directory)
GITCOMMON=$(git -C "$ROOT" rev-parse --git-common-dir 2>/dev/null) || GITCOMMON=.git
GITDIR=$(git -C "$ROOT" rev-parse --git-dir 2>/dev/null) || GITDIR=.git
for d in "$GITCOMMON" "$GITDIR"; do
  case "$d" in /*) ;; *) d="$ROOT/$d";; esac
  [ -d "$d/hooks" ] || continue
  find "$d/hooks" ! -type d ! -name '*.sample' -print
done | sort -u | while IFS= read -r h; do
  echo "REJECT githook: $h: git hook present (runs on checkout/commit/merge)"; done >> "$TMP/reject"
GITINFO=$(g rev-parse --git-path info/attributes 2>/dev/null) || GITINFO=""
case "$GITINFO" in ''|/*) ;; *) GITINFO="$ROOT/$GITINFO";; esac
if [ -n "$GITINFO" ] && [ -s "$GITINFO" ]; then reject gitconfig "$GITINFO" "local git attributes file"; fi

# ---- trust ref ---------------------------------------------------------------------------------------
if [ -n "$TRUST_REF" ]; then
  REF_OK=1
  case "$TRUST_REF" in
    *[!0-9a-f]*) REF_OK=0;;
  esac
  [ "${#TRUST_REF}" -eq 40 ] || REF_OK=0
  if [ "$REF_OK" = 0 ]; then
    reject trustref "$TRUST_REF" "not a full 40-hex lower-case commit id (tags, branches and abbreviated ids are movable or ambiguous; trust3.fable Y11b)"
  elif ! REFC=$(g rev-parse --verify -q "$TRUST_REF^{commit}"); then
    reject trustref "$TRUST_REF" "not a commit in this repository (fetch it first)"
  elif [ "$REFC" != "$TRUST_REF" ]; then
    reject trustref "$TRUST_REF" "names a tag object (peels to $REFC), not a commit; pass the commit id"
  else
    g ls-tree -r --full-tree "$REFC" | while IFS= read -r line; do
      p=${line#*"$TAB"}; meta=${line%%"$TAB"*}
      if in_trusted_zone "$p"; then printf '%s\t%s\n' "$p" "${meta##* }"; fi
    done | sort -t "$TAB" -k1,1 > "$TMP/ref.oid"
    if [ "$MODE" = dev ]; then
      { cat "$TMP/zone.list"; grep -xF "$SELF_PATH" "$FILES"; } | sort -u > "$TMP/cur.zone"
      (cd "$ROOT" && git hash-object --no-filters --stdin-paths < "$TMP/cur.zone") > "$TMP/cur.zone.oid"
      paste "$TMP/cur.zone" "$TMP/cur.zone.oid" > "$TMP/cur.oid"
    else
      while IFS="$TAB" read -r p o; do
        if in_trusted_zone "$p"; then printf '%s\t%s\n' "$p" "$o"; fi
      done < "$TMP/head.oid" > "$TMP/cur.oid"
    fi
    sort -t "$TAB" -k1,1 "$TMP/cur.oid" -o "$TMP/cur.oid"
    join -t "$TAB" -a 1 -a 2 -e '<absent>' -o 0,1.2,2.2 "$TMP/ref.oid" "$TMP/cur.oid" \
      | while IFS="$TAB" read -r p a b; do
          [ "$a" = "$b" ] || echo "REJECT trustref: $p: differs from the trust ref (blob $a there, $b here)"
        done >> "$TMP/reject"
    REFSELF=$(g cat-file blob "$REFC:$SELF_PATH" 2>/dev/null | sha256_stdin)
    if [ -z "$SELF_SHA" ] || [ "$SELF_SHA" != "$REFSELF" ]; then
      reject trustref "$SELF_PATH" "the running gate script is not the trust ref's copy (run: git show REF:$SELF_PATH > gate.sh; sh gate.sh --trust-ref REF)"
    fi
    say "info trust ref $TRUST_REF = $REFC"
  fi
fi

say "info repository $ROOT, HEAD $HEADC, mode $MODE"
say "info gate script sha256 ${SELF_SHA:-<stdin>} (tree copy ${TREE_SELF:-<absent>})"
say "info $(wc -l < "$FILES" | tr -d ' ') files checked; trusted zone $(wc -l < "$TMP/zone.list" | tr -d ' ') files, $nok matching their pins"

# ---- snapshot ----------------------------------------------------------------------------------------
if [ -n "$VERIFY_SNAP" ]; then verify_snapshot "$VERIFY_SNAP"; fi
if [ -n "$SNAP" ]; then
  if [ -s "$TMP/reject" ]; then finish; fi
  if [ -e "$SNAP" ] && [ -n "$(ls -A "$SNAP" 2>/dev/null)" ]; then die "--snapshot $SNAP exists and is not empty"; fi
  mkdir -p "$SNAP" || die "cannot create $SNAP"
  SNAP=$(cd "$SNAP" && pwd)
  case "$SNAP/" in "$ROOT"/*) die "--snapshot must be outside the checkout";; esac
  : > "$TMP/snap.files"
  while IFS= read -r p; do
    case "$p" in formal/*|.github/*|.claude/*) echo "$p" >> "$TMP/snap.files";; esac
  done < "$FILES"
  while IFS= read -r p; do
    d=${p%/*}; mkdir -p "$SNAP/$d" && cp -p "$ROOT/$p" "$SNAP/$p" || die "copy of $p failed"
  done < "$TMP/snap.files"
  while IFS= read -r p; do
    cmp -s "$ROOT/$p" "$SNAP/$p" || reject snapshot "$p" "copy differs from the checked file"
  done < "$TMP/snap.files"
  find "$SNAP" -type f -exec chmod a-w {} +
  if [ "$LINK_LAKE" = 1 ]; then
    mkdir -p "$ROOT/formal/.lake" && ln -s "$ROOT/formal/.lake" "$SNAP/formal/.lake"
  else
    mkdir -p "$SNAP/formal/.lake"
  fi
  verify_snapshot "$SNAP"
  { echo "repository $ROOT"; echo "head $HEADC"; echo "gate-sha256 ${SELF_SHA:-}"; echo "trust-ref ${TRUST_REF:-}"; } > "$SNAP/PRISTINE"
  say "info snapshot of $(wc -l < "$TMP/snap.files" | tr -d ' ') files in $SNAP (run every later step from $SNAP/formal)"
fi
finish
