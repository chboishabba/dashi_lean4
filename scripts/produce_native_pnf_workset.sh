#!/usr/bin/env bash
# Build only the existing formal owner; then run the executable workset
# specialization. No whole Lean repository build or semantic admission.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
out="$root/.lake/build/lib/lean/RequestProject/Slr/NumericPnfRustPortContract.olean"
src="$root/DASHI/output-final_aristotle/RequestProject/Slr/NumericPnfRustPortContract.lean"
mkdir -p "$(dirname "$out")"
if [[ "${1:-}" == "--build" ]]; then
  timeout --kill-after=5s 90s lake env lean -o "$out" "$src"
  exit
fi
[[ -f "$out" && "$out" -nt "$src" ]] || { echo "Run $0 --build first" >&2; exit 2; }
exec lake env lean --run tools/NativePnfWorkset.lean
