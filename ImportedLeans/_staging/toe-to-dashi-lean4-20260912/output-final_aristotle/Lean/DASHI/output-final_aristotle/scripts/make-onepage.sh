#!/usr/bin/env bash
# Regenerates the single page report: one self-contained HTML file carrying the
# whole corpus, the diagnostics, a query engine, SVG charts and PNG export.
#
#   ./scripts/make-onepage.sh                  # the whole corpus -> site/report.html
#   ./scripts/make-onepage.sh data/core.wdkb   # just one ontology
#   OUT=/tmp/small.html ./scripts/make-onepage.sh data/douglas.wdkb
#
# The stylesheet and the script it inlines are web/onepage.css and web/onepage.js.
set -euo pipefail
cd "$(dirname "$0")/.."

OUT=${OUT:-site/report.html}
FILES=("$@")
if [ ${#FILES[@]} -eq 0 ]; then
  FILES=(data/*.wdkb)
fi

lake build wikidata
./.lake/build/bin/wikidata onepage "${FILES[@]}" --out "$OUT" --assets web

echo
echo "wrote $OUT ($(wc -c < "$OUT") bytes; $(gzip -c "$OUT" | wc -c) bytes gzipped)"
echo "open it from disk, or copy it to any static host — it needs nothing else."
echo
echo "to check it headlessly:  npm install jsdom && node scripts/verify_onepage.js $OUT"
