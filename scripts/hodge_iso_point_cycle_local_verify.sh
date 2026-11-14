#!/usr/bin/env bash
# Hodge same-object Mathlib algebraic-cycle isomorphism local golden check.
set -euo pipefail
cd "$(dirname "$0")/.."
owner=Synthesis/MillenniumHodgeActualIsoPointCycleTransportExact.lean
test -f "$owner" || { echo "BLOCKED: missing $owner" >&2; exit 11; }
if grep -nE '^[[:space:]]*axiom([[:space:]]|$)|^[[:space:]]*sorry([[:space:]]|$)|by[[:space:]]+sorry|admit' "$owner"; then
  echo "BLOCKED: unproved Hodge source" >&2; exit 13
fi
command -v lake >/dev/null 2>&1 || {
 echo "BLOCKED: local lake missing; source-written is NOT accepted" >&2
 exit 12
}
lake env lean "$owner"
scratch="$(mktemp --suffix=.lean)"
trap 'rm -f "$scratch"' EXIT
cat > "$scratch" <<'EOF'
import Synthesis.MillenniumHodgeActualIsoPointCycleTransportExact
#print axioms Synthesis.Millennium.Hodge.actualCyclePushforward_iso_pointCycle
#print axioms Synthesis.Millennium.Hodge.actualCyclePushforward_iso_pointDifference
#print axioms Synthesis.Millennium.Hodge.actualIsoSwap_pointDifference_antiInvariant
EOF
lake env lean "$scratch"
echo 'Source checked: scheme-level point/difference cycles, NOT a cohomological cycle-class naturality theorem.'
