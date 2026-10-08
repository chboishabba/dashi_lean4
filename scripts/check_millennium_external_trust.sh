#!/usr/bin/env bash
set -euo pipefail

# Source-level trust scan for the exact external acceptance surface.  Keep this
# deliberately narrower than a repository-wide grep so prose/comments elsewhere
# cannot masquerade as theorem admissions.
lean_targets=(
  MillenniumExternal/ExactTargetSurface.lean
  MillenniumExternal/ExternalTargetFrontier.lean
  MillenniumExternal/SameObjectMaxCut.lean
  MillenniumExternal/ProofResolutionMaxCut.lean
  MillenniumExternal/All.lean
  ExternalClayNS/LeanDojoForceDecayQuantitative.lean
  ExternalClayNS/LeanDojoExactTerminal.lean
  ExternalClayNS/LeanDojoMaxCut.lean
  ExternalClayNS/LeanDojoSameObjectRegression.lean
  Synthesis/MillenniumBSDProjectiveRankWeld.lean
)

for file in "${lean_targets[@]}"; do
  test -f "$file"
  if grep -n -E '^[[:space:]]*axiom[[:space:]]|^[[:space:]]*unsafe([[:space:]]|$)|(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' "$file"; then
    echo "forbidden trust escape in $file" >&2
    exit 1
  fi
done

printf 'Millennium exact-target source trust scan: PASS\n'
