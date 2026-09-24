#!/usr/bin/env bash
# A tour of the `wikidata` command line tool, using only the local JSON fixture
# in this directory (no network access needed).
set -e
cd "$(dirname "$0")/.."
lake build wikidata
WD=./.lake/build/bin/wikidata
OUT=$(mktemp -d)

echo "== import local Wikidata JSON =="
$WD import examples/mini-wikidata.json --name mini --out "$OUT/mini.wdkb"

echo
echo "== the file that was written =="
cat "$OUT/mini.wdkb"

echo
echo "== check it =="
$WD check "$OUT/mini.wdkb"

echo
echo "== summary =="
$WD stats "$OUT/mini.wdkb"

echo
echo "== construct the facts it implies but does not state =="
$WD derive "$OUT/mini.wdkb" --out "$OUT/mini-closed.wdkb"

echo
echo "== ask, and ask for a reason =="
$WD ask "$OUT/mini.wdkb" instance Q42 Q154954 || true
$WD why "$OUT/mini.wdkb" Q5 Q154954

echo
echo "== query with variables: who is a human, and which classes sit below Q154954? =="
$WD query "$OUT/mini.wdkb" 'inst ?x Q5' --select x || true
$WD query "$OUT/mini.wdkb" 'sub ?x Q154954' 'ne ?x Q154954' --select x || true

echo
echo "== add a new statement and see whether the ontology still holds up =="
$WD add "$OUT/mini.wdkb" inst Q42 Q215627 --out "$OUT/mini-plus.wdkb"

echo
echo "== a statement that does not fit is refused =="
$WD add "$OUT/mini.wdkb" sub Q42 Q5 || true

echo
echo "== merging two bases loses nothing =="
$WD merge "$OUT/mini.wdkb" "$OUT/mini-closed.wdkb"

echo
echo "== deduplicate a merged base, which changes no answer =="
$WD merge "$OUT/mini.wdkb" "$OUT/mini-closed.wdkb" --dedup --out "$OUT/mini-merged.wdkb"

echo
echo "== extract the module about Q42: the part of the base that concerns it =="
$WD module "$OUT/mini.wdkb" Q42 --out "$OUT/mini-q42.wdkb"

echo
echo "== the same on the downloaded corpus: 588 items down to the 93 about mathematics =="
$WD module data/core.wdkb Q395 --no-warn | head -6

echo
echo "== a base with a series layer: check it, then read the series in order =="
$WD scheck examples/trilogy.skb
$WD series examples/trilogy.skb v2

echo
echo "== a base full of defects: write the diagnostics as CSV, HTML and SVG =="
$WD report examples/defects.skb --out "$OUT/defects" || true
echo "-- the first lines of the CSV --"
head -4 "$OUT/defects.csv"

echo
echo "== compile the facts to a Lean module =="
$WD lean "$OUT/mini.wdkb" --module Demo.Mini --out "$OUT/Mini.lean" --kernel --highlights 3 --offline
echo "-- the generated module (excerpt) --"
sed -n '/derivedSub_sound/,/^$/p' "$OUT/Mini.lean" | head -20
echo "(a real one goes into RequestProject/Generated/ and is checked by lake build)"

echo
echo "== what Wikidata says about the terms: the grounded glossary =="
$WD gloss Q42 P279
echo "-- and every item of a stored base --"
$WD gloss "$OUT/mini.wdkb" | tail -3

echo
echo "== publish: the static site every mirror serves =="
$WD publish "$OUT/mini.wdkb" data/upper.wdkb --out "$OUT/site"
echo "-- what was written --"
find "$OUT/site" -type f | sort | sed "s|$OUT/site|site|"
echo "-- and every file checks out against the manifest --"
python3 scripts/verify_site.py "$OUT/site" | tail -3

echo
echo "== archive: a deposit that can be read back =="
$WD archive "$OUT/mini.wdkb" --out "$OUT/archive"
$WD unarchive "$OUT/archive/"*/ --out "$OUT/restored.wdkb"

echo
echo "== sync: two replicas that drift apart come back together =="
$WD sync "$OUT/mini.wdkb" "$OUT/mini-plus.wdkb" --out "$OUT/pooled.wdkb"

echo
echo "(With network access: wikidata fetch Q42 --depth 3 --out douglas.wdkb,"
echo " or scripts/refresh-corpus.sh to rebuild the whole compiled corpus)"
