#!/usr/bin/env bash
# Targeted P0 formal gate; no PostgreSQL and no compiler job.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TARGET="DASHI/output-final_aristotle/RequestProject/Slr/NumericPnfRustPortContract.lean"
OUT_ROOT="${GWB_RUST_FORMAL_OUTPUT_ROOT:-$ROOT/.dashi/gwb-relation/native-numeric-pnf-formal}"
mkdir -p "$OUT_ROOT"
OUT="$(mktemp -d "$OUT_ROOT/run-XXXXXXXX")"
test -f "$ROOT/$TARGET" || { echo "Missing formal contract: $TARGET" >&2; exit 2; }
command -v lake >/dev/null || { echo "lake/Lean unavailable" >&2; exit 2; }
(
  cd "$ROOT"
  timeout --signal=TERM --kill-after=5s 90s lake env lean "$TARGET"
) 2>&1 | tee "$OUT/lean-numeric-pnf-rust-formal.log"
if grep -E 'sorryAx|declaration uses .sorry.|unknown constant' \
    "$OUT/lean-numeric-pnf-rust-formal.log"; then
  echo "GWB_NATIVE_NUMERIC_PNF_FORMAL_REJECTED" >&2
  exit 1
fi
echo "GWB_NATIVE_NUMERIC_PNF_FORMAL_KERNEL_OK"
echo "This does NOT certify Rust runtime parity or physical work."
echo "Result: $OUT"
