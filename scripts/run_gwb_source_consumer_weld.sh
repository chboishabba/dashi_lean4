#!/usr/bin/env bash
# P0 DELTA: original SLR source-local consumer, replay and Lean/ledger weld.
# Does NOT rerun previously accepted source/frontier/binder acceptance.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${SLR_ROOT:?Set SLR_ROOT to original SLR PR #78 checkout}"
: "${DATABASE_URL:?Set native SLR PostgreSQL URL}"
SLR_ROOT="$(cd "$SLR_ROOT" && pwd)"
BASE="${1:?usage: bash scripts/run_gwb_source_consumer_weld.sh PREVIOUS_ACCEPTED_RUN_DIR}"
if [[ "$BASE" != /* ]]; then BASE="$ROOT/$BASE"; fi
BASE="$(cd "$BASE" && pwd)"
for file in native-inspection.json native-frontier.json native-named-topic-inference.json; do
  test -s "$BASE/$file" || {
    echo "Missing accepted run evidence: $BASE/$file" >&2
    exit 2
  }
done
OUT_ROOT="${GWB_SOURCE_CONSUMER_OUTPUT_ROOT:-$ROOT/.dashi/gwb-relation/m2-source-consumer}"
mkdir -p "$OUT_ROOT"
OUT="$(mktemp -d "$OUT_ROOT/run-XXXXXXXX")"

REVIEW_ITEM="$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1],encoding="utf-8"))["review_item_ref"])' "$BASE/native-inspection.json")"
PARSER_RUN="$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1],encoding="utf-8"))["parser_run_ref"])' "$BASE/native-frontier.json")"

# Fail before invoking Cargo on a wrongly scoped or stale baseline.
(
  cd "$ROOT"
  python3 - "$BASE/native-inspection.json" "$BASE/native-frontier.json" \
    "$BASE/native-named-topic-inference.json" <<'PY'
import json,sys
from tools.gwb_native_maxcut_ledger import (
    validate_inspection,validate_frontier,validate_named_topic_inference,
)
i,f,p=[json.load(open(x,encoding="utf-8")) for x in sys.argv[1:]]
entries=validate_inspection(i)
validate_frontier(i,f,entries)
if not validate_named_topic_inference(i,f,p,entries):
    raise SystemExit("Accepted baseline lacks positive source-local named-topic result")
print("GWB_ACCEPTED_BASELINE_SOURCE_LOCAL_OK")
PY
)

echo "M2 CONSUMER: accepted real run=$BASE"
echo "M2 OUTPUT=$OUT"
echo "No S29 command, normative admission, Level-3 DB write or QID."

(
  cd "$SLR_ROOT"
  cargo test -p sensiblaw-pg-source-store --lib native_source_local_consumer
  cargo test -p sensiblaw-cli native_antecedent_review
  cargo run -p sensiblaw-cli -- native-antecedent-review derive \
    "$REVIEW_ITEM" "$PARSER_RUN" > "$OUT/native-named-topic-inference.json"
)
(
  cd "$ROOT"
  python3 tools/build_gwb_source_consumer.py \
    --inspection "$BASE/native-inspection.json" \
    --frontier "$BASE/native-frontier.json" \
    --inference "$OUT/native-named-topic-inference.json" \
    --consumer "$OUT/native-source-consumer.json" \
    --replay "$OUT/native-source-consumer-replay.json"
  python3 -m unittest discover -s tests \
    -p test_gwb_source_local_consumer.py -v

  ARGS=(
    --inspection "$BASE/native-inspection.json"
    --frontier "$BASE/native-frontier.json"
    --named-topic-inference "$OUT/native-named-topic-inference.json"
    --source-consumer "$OUT/native-source-consumer.json"
    --source-consumer-replay "$OUT/native-source-consumer-replay.json"
    --consumer-adversarial
    --ledger "$OUT/joint-evidence-ledger-with-source-consumer.json"
    --worksheet "$OUT/original-review-worksheet.json"
  )
  if [[ -s "$BASE/lean-named-topic-policy.log" ]]; then
    ARGS+=(--named-topic-lean-log "$BASE/lean-named-topic-policy.log")
  fi
  python3 -m tools.gwb_native_maxcut_ledger "${ARGS[@]}"

  lake env lean --run \
    DASHI/output-final_aristotle/RequestProject/Slr/GwbSourceLocalConsumer.lean \
    "$BASE/native-inspection.json" \
    "$BASE/native-frontier.json" \
    "$OUT/native-named-topic-inference.json" \
    "$OUT/native-source-consumer.json" \
    "$OUT/native-source-consumer-replay.json"
) | tee "$OUT/m2-source-local-consumer-acceptance.log"

echo "GWB_SOURCE_LOCAL_CONSUMER_DELTA_OK"
echo "Consumer answer: source-local Bush under declared policy, exact current replay."
echo "Still unpaid: typed demand witness, governed identity/Level-3, Q23505, JMD property."
echo "Output: $OUT"
