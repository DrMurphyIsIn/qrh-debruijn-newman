#!/bin/bash
# Materialize the verification workspace: an UNMODIFIED checkout of openai/math's lean/ directory at
# the commit pinned in lean/OAI_PIN, with this repository's Lean files copied into its root and two
# lean_lib stanzas appended to OpenAI's lakefile. OpenAI's lakefile must stay the workspace root (its
# hooks patch 23 dependencies and refuse a non-root checkout), so this is the only supported way in.
#
#   scripts/materialize.sh                 # clone openai/math at the pin into work/oai (network)
#   scripts/materialize.sh --from-local D  # reflink/copy an existing built checkout D whose sources
#                                          # equal the pin (checked file by file against $OAI_GIT)
# Then, from work/oai:
#   lake update && lake exe cache get      # fresh clone only
#   lake build ArdaQRHBridge AxiomGuardQRHBridge ArdaDBNUnconditional ArdaDBNChallenge ArdaDBNNegativeControl
#   lake env lean AxiomGuardQRHBridge.lean; lake env lean AxiomGuardDBNUnconditional.lean
#   lake env comparator dbn_real_zeros_of_qrh_unconditional.comparator.json   # must accept
#   lake env comparator tampered.comparator.json                             # must REJECT
#   lake build MissionChallenges.RH_dbn_real_zeros_nine_thirtyseconds MissionChallenges.RH_zeta_zero_free_seven_eighths
#   lake env comparator RH_dbn_real_zeros_nine_thirtyseconds.comparator.json # registry-form judge
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
. "$HERE/lean/OAI_PIN"
WORK="$HERE/work/oai"
mkdir -p "$HERE/work"
if [ "${1:-}" = "--from-local" ]; then
  SRC="$2"; GIT="${OAI_GIT:-$HOME/oai-math}"
  [ "$(git -C "$GIT" rev-parse HEAD)" = "$commit" ] || { echo "OAI_GIT is not at $commit"; exit 1; }
  diff -rq "$GIT/$subdir" "$SRC" -x .lake -x .git -x replay_configs -x replay_logs \
       -x REPLAY_REPORT.md -x ReplayChecks || { echo "source tree differs from $commit"; exit 1; }
  rm -rf "$WORK"; cp -c -R "$SRC" "$WORK" 2>/dev/null || cp -R "$SRC" "$WORK"
else
  rm -rf "$HERE/work/math"
  git clone --no-checkout "$repo" "$HERE/work/math"
  git -C "$HERE/work/math" checkout --detach "$commit"
  rm -rf "$WORK"; mv "$HERE/work/math/$subdir" "$WORK"
fi
# The bridge, the unconditional theorem, the guards, the challenges and the Comparator configs.
cp "$HERE/lean/bridge/"*.lean "$WORK/"; rm -f "$WORK/lakefile-stanza.lean"
cp "$HERE/lean/bridge/"*.comparator.json "$WORK/"
cp "$HERE/lean/bridge/negative_control/"* "$WORK/"
# The single-pin port: the 19 dbn modules, byte-identical to the Arda dbn island (provenance/ARDA_SOURCE),
# then the two recorded one-line patches, then the LiCriterion shim.
cp "$HERE/lean/dbn/"*.lean "$WORK/"
for pf in "$HERE"/lean/patches/*.patch; do (cd "$WORK" && patch -p1 --no-backup-if-mismatch < "$pf"); done
mkdir -p "$WORK/Lc/LiCriterion"
cp "$HERE/lean/Lc/XiZeros.lean" "$WORK/Lc/XiZeros.lean"
cp "$HERE/lean/Lc/LiCriterion/Basic.lean" "$WORK/Lc/LiCriterion/Basic.lean"
cat "$HERE/lean/bridge/lakefile-stanza.lean" >> "$WORK/lakefile.lean"
# The registry judge bundle (the challenge modules whose TYPE is the registered statement).
mkdir -p "$WORK/MissionChallenges"
cp "$HERE/lean/judge/MissionChallenges.lean" "$WORK/MissionChallenges.lean"
cp "$HERE/lean/judge/MissionChallenges/"*.lean "$WORK/MissionChallenges/"
cp "$HERE/lean/judge/"*.comparator.json "$WORK/"
{ echo; cat "$HERE/lean/judge/lakefile-stanza.lean"; } >> "$WORK/lakefile.lean"
[ "$(cat "$WORK/lean-toolchain")" = "$toolchain" ] || { echo "toolchain mismatch"; exit 1; }
grep -q "\"rev\": \"$mathlib\"" "$WORK/lake-manifest.json" || { echo "mathlib pin mismatch"; exit 1; }
echo "Materialized at $WORK (openai/math $commit, $toolchain, Mathlib $mathlib). See the header of this script for the next commands."
