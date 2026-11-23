#!/usr/bin/env bash
# Integrated native SLR book-source frontier / Lean / M1-M3 ledger.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${SLR_ROOT:?Set SLR_ROOT to the original SLR Rust checkout}"
: "${DATABASE_URL:?Set DATABASE_URL for native SLR PostgreSQL}"
REVIEW_ITEM="${GWB_NATIVE_REVIEW_ITEM_REF:-review-item:native-antecedent-candidate:sha256:25e927f12a0092fbed143669f6a0621fa004636d728074d576275b361da8f7d1}"
OUT="${GWB_NATIVE_MAXCUT_OUTPUT_DIR:-$ROOT/.dashi/gwb-relation/m1-m3-maxcut}"
PARSER_RUN="${GWB_NATIVE_PARSER_RUN_REF:-}"
mkdir -p "$OUT"

echo "M1-M3 bounded source-native joint acceptance"
echo "SLR_ROOT=$SLR_ROOT"
echo "OUTPUT=$OUT"
echo "review_item=$REVIEW_ITEM"
echo "No identity or QID promotion is performed."

(
  cd "$SLR_ROOT"
  cargo test -p sensiblaw-pg-source-store --lib native_antecedent_review
  cargo test -p sensiblaw-pg-source-store --lib native_antecedent_frontier
  cargo test -p sensiblaw-cli native_antecedent_review
  cargo run -p sensiblaw-cli -- native-antecedent-review inspect \
    "$REVIEW_ITEM" > "$OUT/native-inspection.json"
  cargo run -p sensiblaw-cli -- native-antecedent-review runs \
    "$REVIEW_ITEM" > "$OUT/original-parser-runs.json"
  if [[ -n "$PARSER_RUN" ]]; then
    cargo run -p sensiblaw-cli -- native-antecedent-review frontier \
      "$REVIEW_ITEM" "$PARSER_RUN" > "$OUT/native-frontier.json"
  else
    # Only auto-select uniquely complete original parser runs.
    cargo run -p sensiblaw-cli -- native-antecedent-review frontier \
      "$REVIEW_ITEM" > "$OUT/native-frontier.json"
  fi
)
(
  cd "$ROOT"
  python3 -m unittest discover -s tests \
    -p test_gwb_native_maxcut_ledger.py -v
)
(
  cd "$ROOT"
  lake env lean --run \
    DASHI/output-final_aristotle/RequestProject/Slr/GwbNativeAntecedentMaxCut.lean \
    "$OUT/native-frontier.json"
) | tee "$OUT/lean-frontier-kernel.log"

LEDGER_OPTS=(
  --inspection "$OUT/native-inspection.json"
  --frontier "$OUT/native-frontier.json"
  --lean-log "$OUT/lean-frontier-kernel.log"
  --ledger "$OUT/joint-evidence-ledger.json"
  --worksheet "$OUT/original-antecedent-review-worksheet.json"
  --adversarial
)
if [[ -n "${GWB_Q207_KERNEL_LOG:-}" ]]; then
  LEDGER_OPTS+=( --q207-log "$GWB_Q207_KERNEL_LOG" )
fi
(
  cd "$ROOT"
  python3 -m tools.gwb_native_maxcut_ledger "${LEDGER_OPTS[@]}"
)
echo "M1_M3_MAXCUT_BOUNDED_PACKET_OK"
echo "Source-local result remains unresolved until independent review."
