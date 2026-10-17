#!/usr/bin/env bash
set -euo pipefail

if grep -R -n -E '\bsorry\b|^\s*axiom\b|^\s*unsafe\b' MillenniumExternal; then
  echo 'forbidden trust escape in MillenniumExternal' >&2
  exit 1
fi

printf 'MillenniumExternal trust scan: PASS\n'
