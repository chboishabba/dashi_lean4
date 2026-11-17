#!/usr/bin/env bash
# Canonical, fail-closed Rust SLR -> JMD Lean M12/S28 acceptance.
# Needs the original persisted SLR parser run; NOT reconstructed article JSON.
# Does not use a Python, spaCy, or SensibLaw-Python producer.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${SLR_BIN:?Set SLR_BIN to a built SLR PR78 sensiblaw Rust binary}"
: "${DATABASE_URL:?Set DATABASE_URL for original SLR PostgreSQL parser run}"
: "${PARSER_RUN:?Provide original DB parser run identity}"
: "${STATEMENT_REF:?Provide original M12 statement ref}"
: "${DOCUMENT_REF:?Provide original source document ref}"
: "${SOURCE_REV:?Provide original source revision ref}"
: "${REGION_REF:?Provide original SLR region ref}"
: "${START_CHAR:?Provide original M12 start char}"
: "${END_CHAR:?Provide original M12 end char}"
: "${LITERAL_FILE:?Provide original exact source region literal file}"
command -v lake >/dev/null || { echo 'Missing Lean lake toolchain' >&2; exit 2; }
[[ -x "$SLR_BIN" ]] || { echo "Missing SLR Rust binary: $SLR_BIN" >&2; exit 2; }
[[ -s "$LITERAL_FILE" ]] || { echo "Missing original literal file: $LITERAL_FILE" >&2; exit 2; }
[[ "$START_CHAR" =~ ^[0-9]+$ && "$END_CHAR" =~ ^[0-9]+$ ]] || { echo 'Character bounds must be decimal integers' >&2; exit 2; }
(( 10#$START_CHAR < 10#$END_CHAR )) || { echo 'Start must precede end' >&2; exit 2; }
output="${1:-$root/.gwb_native_proof}"
mkdir -p "$output"
cd "$root"
# Existing Lean DB M12 producer calls Rust, verifies source/run/region.
lake build wikidata
lake exe wikidata slr-db-pnf "$SLR_BIN" "$PARSER_RUN" "$STATEMENT_REF" "$DOCUMENT_REF" \
  "$SOURCE_REV" "$REGION_REF" "$START_CHAR" "$END_CHAR" "$LITERAL_FILE" \
  | tee "$output/m12-checked.txt"
if [[ -n "${EVENT_REF:-}" ]]; then
  # Existing reviewed S28 event; fail closed on incomplete M12 source trace.
  lake exe wikidata slr-timeline "$SLR_BIN" "$EVENT_REF" \
    | tee "$output/s28-candidates.json"
fi
printf 'NATIVE_SLR_M12_JMD_ACCEPTED source=%s statement=%s\n' "$SOURCE_REV" "$STATEMENT_REF"
printf 'Semantic interpretation, event identity and world occurrence remain independent proof obligations.\n'
