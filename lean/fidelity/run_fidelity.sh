#!/bin/bash
# Reproduce the cross-pin fidelity check (2026-10-07).  Needs: the dbn island built
# (telperion/examples/dbn/lean), the bridge materialized and built (../work/oai), lean4export
# built at v4.34.0-rc1 (LEAN4EXPORT_RC1) and at v4.34.1 (LEAN4EXPORT_V4341; Comparator's copy).
# Peak memory of the comparison: about 7 GB.  conjecture1_proved = False.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; OUT="${OUT:-$HERE/out}"; mkdir -p "$OUT/dbn" "$OUT/oai"
DBN="$HERE/../../dbn/lean"; OAI="$HERE/../work/oai"
( cd "$DBN" && lake env lean --root="$HERE" -o "$OUT/dbn/QRHFidelityDBN.olean" "$HERE/QRHFidelityDBN.lean"
  lake env sh -c "LEAN_PATH=\$LEAN_PATH:$OUT/dbn $LEAN4EXPORT_RC1 QRHFidelityDBN -- QRHFidelity.stmt QRHFidelity.stmtMathlib > $OUT/export_dbn.ndjson" )
( cd "$OAI" && lake env lean --root="$HERE" -o "$OUT/oai/QRHFidelityOAI.olean" "$HERE/QRHFidelityOAI.lean"
  lake env sh -c "LEAN_PATH=\$LEAN_PATH:$OUT/oai $LEAN4EXPORT_V4341 QRHFidelityOAI -- QRHFidelity.stmt QRHFidelity.stmtMathlib > $OUT/export_oai.ndjson" )
cd "$OUT"
python3 "$HERE/compare_exports.py" export_dbn.ndjson export_oai.ndjson QRHFidelity.stmt \
  --also QRHFidelity.stmtMathlib --json fidelity_stmt.json > fidelity_stmt.txt
python3 "$HERE/diag_root_causes.py" > root_causes.txt
