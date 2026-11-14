#!/usr/bin/env bash
# BSD K1, fail closed: exact Hensel integer lifts AND true Mathlib Q2 source.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_bsd_q2_hensel_3705_exact.py --precision 128
python3 scripts/check_bsd_q2_eight_squareclasses_20261114.py
target=Synthesis/MillenniumBSDCMQ2Hensel3705CandidateExact.lean
test -f "$target" || { echo "BLOCKED: missing $target" >&2; exit 11; }
if grep -nE '(^[[:space:]]*(axiom|sorry|admit)[[:space:]]|\bsorry\b|\badmit\b)' "$target"; then
  echo "BLOCKED: unfinished square-root source" >&2
  exit 13
fi
command -v lake >/dev/null 2>&1 || {
  echo "BLOCKED: no pinned Lake/Lean toolchain; finite lifts are NOT a kernel receipt" >&2
  exit 12
}
for owner in "$target" Synthesis/MillenniumBSDCMQ2AllOddUnitHenselExact.lean Synthesis/MillenniumBSDCMQ2ActualCurvePointAt39Exact.lean Synthesis/MillenniumBSDCMQ2EightLocalPointWitnessesExact.lean; do
  test -f "$owner" || { echo "BLOCKED: missing $owner" >&2; exit 11; }
  lake env lean "$owner"
done
echo "KERNEL PASS: actual Q2 Hensel source, uniform odd-unit roots, x=39 and eight original-curve Q2 coordinate points."
echo "OPEN: Q2 complete Kummer image, continuous H1, original Selmer/Sha exactness."
