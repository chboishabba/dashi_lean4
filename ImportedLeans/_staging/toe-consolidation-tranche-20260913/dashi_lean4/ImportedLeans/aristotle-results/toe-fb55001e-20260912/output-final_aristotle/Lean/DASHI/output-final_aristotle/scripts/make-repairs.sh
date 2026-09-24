#!/usr/bin/env bash
# Regenerates the patch reviews in docs/repairs/.
#
#   scripts/make-repairs.sh
#
# For each base listed below this runs `wikidata repairs`, which writes a
# candidate repair for *every* flagged issue — the change it makes, the reason
# for it, the verdict of the check, and what it does to the repair debt — as
# three files: NAME.csv (a table), NAME.html (a page with the summary) and
# NAME.txt (a plain text review to paste onto a talk page).
#
# Nothing is applied to the input files.  With --out-base the tool also saves the
# base the recommended changes would produce, so the two can be compared.
#
# The review is quadratic in the size of the base — every candidate is checked
# against a rebuilt closure — so this runs over the small hand-written examples
# and the smaller downloaded fragments, not over the whole corpus.
#
# `wikidata repairs` exits 1 when errors remain after the recommended changes,
# which is the normal case here, so the exit status of the individual runs is
# ignored.
set -u

cd "$(dirname "$0")/.."
WD=./.lake/build/bin/wikidata
OUT=docs/repairs

if [ ! -x "$WD" ]; then
  echo "building the tool first: lake build wikidata"
  lake build wikidata || exit 1
fi

mkdir -p "$OUT"

for f in examples/defects.skb data/douglas.wdkb data/frontier4.wdkb data/chemistry.wdkb; do
  [ -f "$f" ] || continue
  echo "== $f"
  "$WD" repairs "$f" --out "$OUT" --out-base || true
done

python3 docs/make_repair_index.py

echo "wrote $OUT/*.csv, *.html, *.txt and $OUT/README.md"
