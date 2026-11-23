#!/usr/bin/env bash
# P10: one small JMD kernel check, independent of GWB article/full projection.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
if [[ $# -ne 1 || ! -f "$1" ]]; then
  echo "usage: bash scripts/run_gwb_q207_minimal.sh /path/to/Q207-EntityData.json" >&2
  exit 2
fi
input="$1"
cache=.lake/build/lib/lean/RequestProject/Cli/Import.olean
source=DASHI/output-final_aristotle/RequestProject/Cli/Import.lean
if [[ ! -f "$cache" || "$source" -nt "$cache" ]]; then
  echo "GWB_Q207_MINIMAL_CACHE_MISSING_OR_STALE: build targeted JMD prerequisites separately" >&2
  exit 3
fi
mkdir -p .dashi/gwb-q207
log=.dashi/gwb-q207/minimal-kernel.log
set +e
timeout 90s lake env lean --run tools/GwbQ207MinimalRunner.lean "$input" > "$log" 2>&1
status=$?
set -e
cat "$log"
if [[ "$status" -ne 0 ]] || ! grep -Fxq GWB_Q207_MINIMAL_KERNEL_OK "$log"; then
  echo "GWB_Q207_MINIMAL_UNVERIFIED exit=$status (log=$log)" >&2
  exit 1
fi
echo "GWB_Q207_MINIMAL_ACCEPTED status=$status log=$log"
