#!/usr/bin/env bash
# Import an ontology back from archive.org.
#
#   bash scripts/archive_download.sh wikidata-ontology-wdkb1-… [out-dir]
#
# Downloads the deposit, then hands it to the verified tool, which reads it back
# and reports whether the two copies in the deposit (the project's own format and
# the public JSON Lines file) agree — `Archive.importKB?_bundleOf` says the answer
# is yes for anything the project deposited.
set -euo pipefail

ID="${1:-}"
OUT="${2:-archive-restore}"
[ -n "$ID" ] || { echo "usage: scripts/archive_download.sh IDENTIFIER [DIR]" >&2; exit 1; }

mkdir -p "$OUT"
if command -v ia >/dev/null 2>&1; then
  ia download "$ID" --destdir "$OUT" --no-directories --glob 'ontology.*;manifest.tsv'
else
  echo "→ no `ia` client, using plain HTTP"
  for f in ontology.wdkb ontology.jsonl manifest.tsv; do
    curl -sSL "https://archive.org/download/$ID/$f" -o "$OUT/$f" || true
  done
fi

WIKIDATA=./.lake/build/bin/wikidata
if [ -x "$WIKIDATA" ]; then
  "$WIKIDATA" unarchive "$OUT" --out "$OUT/restored.wdkb"
  "$WIKIDATA" check "$OUT/restored.wdkb"
else
  echo "build the tool (lake build wikidata) to re-import and check the deposit"
fi
