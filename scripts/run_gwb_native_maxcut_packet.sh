#!/usr/bin/env bash
# Integrated native SLR book-source frontier / Lean / M1-M3 ledger.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${SLR_ROOT:?Set SLR_ROOT to the original SLR Rust checkout}"
: "${DATABASE_URL:?Set DATABASE_URL for native SLR PostgreSQL}"
SLR_ROOT="$(cd "$SLR_ROOT" && pwd)"
REVIEW_ITEM="${GWB_NATIVE_REVIEW_ITEM_REF:-review-item:native-antecedent-candidate:sha256:25e927f12a0092fbed143669f6a0621fa004636d728074d576275b361da8f7d1}"
OUT_ROOT="${GWB_NATIVE_MAXCUT_OUTPUT_DIR:-$ROOT/.dashi/gwb-relation/m1-m3-maxcut}"
PARSER_RUN="${GWB_NATIVE_PARSER_RUN_REF:-}"
mkdir -p "$OUT_ROOT"
OUT="$(mktemp -d "$OUT_ROOT/run-XXXXXXXX")"
test -f "$SLR_ROOT/crates/sl-pg-source-store/src/native_antecedent_frontier.rs" || {
  echo "Required native SLR M1 frontier missing; checkout SLR PR #78" >&2
  exit 2
}

echo "M1-M3 bounded source-native joint acceptance"
echo "SLR_ROOT=$SLR_ROOT"
echo "OUTPUT=$OUT"
echo "review_item=$REVIEW_ITEM"
echo "No identity or QID promotion is performed."

(
  cd "$SLR_ROOT"
  cargo test -p sensiblaw-pg-source-store --lib native_antecedent_review
  cargo test -p sensiblaw-pg-source-store --lib native_antecedent_frontier
  cargo test -p sensiblaw-pg-source-store --lib native_antecedent_named_topic
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
  if [[ -n "$PARSER_RUN" ]]; then
    cargo run -p sensiblaw-cli -- native-antecedent-review derive \
      "$REVIEW_ITEM" "$PARSER_RUN" > "$OUT/native-named-topic-inference.json"
  else
    cargo run -p sensiblaw-cli -- native-antecedent-review derive \
      "$REVIEW_ITEM" > "$OUT/native-named-topic-inference.json"
  fi
)
(
  cd "$ROOT"
  python3 -m unittest discover -s tests \
    -p test_gwb_native_maxcut_ledger.py -v
  python3 -m unittest discover -s tests \
    -p test_gwb_original_binding_interop.py -v
  python3 -m unittest discover -s tests \
    -p test_gwb_native_named_topic_policy.py -v
)
(
  cd "$ROOT"
  lake env lean --run \
    DASHI/output-final_aristotle/RequestProject/Slr/GwbNativeAntecedentMaxCut.lean \
    "$OUT/native-frontier.json"
) | tee "$OUT/lean-frontier-kernel.log"

# NEW: actual kernel check of the conditional semantic repair contract.
# This is not a positive unique-antecedent admission. It proves
# omission/refutation, S29 Pending impossibility, local uniqueness from
# a complete reviewed typed set, consumer invariance and retraction.
(
  cd "$ROOT"
  lake env lean \
    DASHI/output-final_aristotle/RequestProject/Slr/GwbCoreferenceFormalRepair.lean
) | tee "$OUT/lean-coreference-formal-repair.log"
echo "GWB_COREFERENCE_CONDITIONAL_REPAIR_KERNEL_OK"

# New independent positive named-topic source/local policy check:
# evidence-based interpretation of the original Bush/he discourse;
# not a human S29 admission, QID or historical truth theorem.
(
  cd "$ROOT"
  lake env lean --run \
    DASHI/output-final_aristotle/RequestProject/Slr/GwbNamedTopicPolicy.lean \
    "$OUT/native-inspection.json" \
    "$OUT/native-frontier.json" \
    "$OUT/native-named-topic-inference.json"
) | tee "$OUT/lean-named-topic-policy.log"

# Optional original SensibLaw typed-binding graph: this runs the ORIGINAL
# producer on a full-book exact-content PNF/annotation graph, not a new binder.
# Refuse foreign source revisions, source work aliases and missing factor spans.
if [[ -n "${GWB_ORIGINAL_BINDING_ARTIFACTS:-}" ]]; then
  : "${SENSIBLAW_ROOT:?Set SENSIBLAW_ROOT to original SensibLaw Python repo}"
  (
    cd "$ROOT"
    python3 -m tools.gwb_original_binding_interop \
      --slr-inspection "$OUT/native-inspection.json" \
      --slr-frontier "$OUT/native-frontier.json" \
      --original-sensiblaw-artifacts "$GWB_ORIGINAL_BINDING_ARTIFACTS" \
      --sensiblaw-root "$SENSIBLAW_ROOT" \
      --output "$OUT/original-typed-binding-crosswalk.json"
  )
fi

# Optional independent Wikipedia Q207/JMD P5-P10 theorem lane.
# It is not used to pay the book's local antecedent identity.
if [[ "${GWB_RUN_WIKI_P10:-0}" == "1" ]]; then
  (
    cd "$ROOT"
    GWB_WORLD_JMD_REPORT="$OUT/jmd-world-proof-report.json" \
      bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
  ) | tee "$OUT/wiki-p10-conditional-kernel.log"
fi

LEDGER_OPTS=(
  --inspection "$OUT/native-inspection.json"
  --frontier "$OUT/native-frontier.json"
  --lean-log "$OUT/lean-frontier-kernel.log"
  --named-topic-inference "$OUT/native-named-topic-inference.json"
  --named-topic-lean-log "$OUT/lean-named-topic-policy.log"
  --ledger "$OUT/joint-evidence-ledger.json"
  --worksheet "$OUT/original-antecedent-review-worksheet.json"
  --adversarial
)
if [[ -f "$OUT/original-typed-binding-crosswalk.json" ]]; then
  LEDGER_OPTS+=( --typed-binding-weld "$OUT/original-typed-binding-crosswalk.json" )
fi
if [[ -n "${GWB_Q207_KERNEL_LOG:-}" ]]; then
  LEDGER_OPTS+=( --q207-log "$GWB_Q207_KERNEL_LOG" )
fi
(
  cd "$ROOT"
  python3 -m tools.gwb_native_maxcut_ledger "${LEDGER_OPTS[@]}"
)
echo "M1_M3_MAXCUT_BOUNDED_PACKET_OK"
echo "Original-source named-topic linguistic interpretation reported separately."
echo "S29 workflow, governed semantic admission, JMD QID and historical truth remain separate."
