# Review of rh/judge-oai-bridge @ 48dc34ec8 (missions judge on the materialized oai_qrh_bridge island)

Reviewer: session peterwmurphy-e9, 2026-10-08, from a detached worktree of the committed objects
(~/arda-e9-judge-review); the author's working tree was not read. Commits reviewed: 4b782799d
(judge.py, bundle, --pending, judge_materialize.sh, tests), c2da5dbb6 (missions-comparator job),
48dc34ec8 (docs). Base 60b2cade9. conjecture1_proved = False.

## Verdict: APPROVE, no blocking findings. Four non-blocking notes below.

## What I verified myself

| Check | Result |
|---|---|
| `pytest tests/test_missions_judge.py tests/test_judge_log.py` (my venv, py3.12) | 68 passed |
| `judge --check` on dbn, li_positivity, bg, quasicrystal, rvm_bridge, zeta_reflection, oai_qrh_bridge | all OK; the six existing bundles are byte-identical to 60b2cade9 (`git diff --stat` empty) |
| `mission verify rh` on the branch | OK |
| coverage gate (`artifact_coverage_error`) for both bridge artifacts and DBNZeroFreeHalfplane with the new workflow job present | None (covered); `ci_built_islands` still lists oai_qrh_bridge and dbn |
| missions-comparator.yml parses; jobs = bundles-in-sync, plan, judge, judge-oai-qrh-bridge | yes |
| `scripts/judge_materialize.sh` mode in git | 100755 |
| `--pending --out <scratch>` render | two bridges (nine_thirtyseconds, seven_eighths), MANIFEST `pending_not_proved` lists both; artifact and statement sha256 in MANIFEST match the files |
| `judge_materialize.sh <scratch> <my work/oai>` twice | exit 0 both times; `lean_lib MissionChallenges` appended exactly once |
| `lake build MissionChallenges.<both>` inside the workspace | both built (27 s each) |
| Comparator, nanoda ON, my own Comparator/nanoda builds, on the generated configs | nine_thirtyseconds: both kernels accept, okay (9.5 min); seven_eighths: both kernels accept, okay (8.7 min) |
| Rendered type == registry statement body, verbatim | yes for both; imports = artifact, AxiomGuardDBNUnconditional, AxiomGuardQRHBridge; no namespace/open context (artifacts have none) |
| `--pending` refuses without `--out`, refuses `--check`; `--configs` without `--pending` prints nothing for this island | yes (tests + my run) |
| CI job never saves the cache; restores oai-qrh-bridge.yml's key prefix byte-for-byte; ELAN_TOOLCHAIN job-wide; comparator tag v4.34.0 + toolchain v4.34.1 asserted against MANIFEST | yes |
| Docs §5 corrected (no comparator-record before grant); §8 order = operator read-back -> grant -> CI -> record; README updated | yes |

## Assessment of the declared weakening (shadowing guard scope)

The guard imports load the island's own modules (the 19-module port, the LiCriterion shim, the
bridge), not the ~2,900 OpenAI modules outside their closure. For these two nodes this is
immaterial: the registered statements mention only `DBN.H` (declared in the ported DBNDefs,
inside the guards' closure, so any second `DBN.H` in the closure is a duplicate declaration) and
Mathlib's `riemannZeta` (any redeclaration at root in a module that imports Mathlib is a
duplicate declaration), and both bridges are rendered at root with NO `open` lines, so neither
name can be redirected by namespace tricks. The residual trust is OpenAI's pinned tree itself,
which materialize.sh verifies byte-for-byte against adc7f124 and CI clones fresh at that commit.
That is the same trust the result rests on anyway. Acceptable; the docs state it correctly.

## Non-blocking notes

1. **Cache scoping.** GitHub Actions caches are visible only to runs on the same branch or on the
   default branch. judge-oai-qrh-bridge on any branch other than rh/qrh-dbn-9-32 (including
   rh/judge-oai-bridge and PRs from other branches) will NOT find the checkpoint oai-qrh-bridge.yml
   saved there, and the judge job never saves, so expect a cold build (~80 min, inside the 360-min
   limit) until a checkpoint exists on main. Worth one sentence in §8.
2. **Tag in three places.** "v4.34.0" is hard-coded in MATERIALIZED_ROOT_ISLANDS, in the CI clone
   line, and in the CI assert against MANIFEST. The assert keeps them honest; reading the tag from
   MANIFEST.json (as the matrix job does) would remove the duplication.
3. **Stanza root check is loose.** `_STANZA_ROOT_RE` treats every backticked identifier in the
   stanza (after comment stripping) as a root, including `globs` entries. Fine today; a guard named
   only inside a `globs := #[.andSubmodules ...]` would pass the check without being a root.
4. **Pending bundles and the shared workspace.** `judge_materialize.sh` `rm -rf`s the workspace's
   MissionChallenges/ and copies the bundle's; running it with a pending bundle and later with the
   committed (proved) bundle in the same workspace is fine, but the leftover `RH_*.comparator.json`
   of a node that later changes config would be refused ("exists and differs"). CI always starts
   from a fresh materialize, so this only affects local reuse.

## Not covered by this review
- The two dbn-island nodes (zeta_halfplane, qrh conditional) use the existing dbn bundle path,
  unchanged here.
- Whether a cross-pin node should be grantable at all (doc §3/§5 question 1) is an owner decision,
  not a code question.
