#!/usr/bin/env bash
# Runs the auto-enrichment loop over the seven theories of docs/THEORIES.md and
# rebuilds everything it produces:
#
#   scripts/enrich.sh            # download what is not cached
#   scripts/enrich.sh --offline  # rebuild from the caches only
#
# Downloads are cached in .wikidata-cache/ (entities) and .enrich-cache/
# (Wikipedia queries and external sources), so a second run needs no network.
# The outputs — data/enrichment/*, data/enriched.wdkb and the generated modules
# under RequestProject/Generated/ — are checked into the repository.
#
# What each stage is proved to do is stated in docs/ENRICHMENT.md; the numbers
# the run produced are theorems in RequestProject/EnrichmentCorpus.lean.
set -e
cd "$(dirname "$0")/.."
lake build wikidata
WD=./.lake/build/bin/wikidata
OFFLINE="${1:-}"
mkdir -p data/enrichment

# the seven theories
THEORIES="Q42989 Q1062242 Q5891840 Q139761564 Q217413 Q903820 Q874429"
LANGS="en,de,fr,es,it,ru,ja,zh,pt,nl"

echo "== 1. every Wikipedia article about them, in every language =="
$WD sitelinks $THEORIES $OFFLINE --cache .wikidata-cache \
    --out data/enrichment/sitelinks.tsv \
    --module RequestProject.Generated.TheorySitelinks | tail -4

echo "== 2. scan those articles in ten languages =="
$WD scan $THEORIES $OFFLINE --cache .enrich-cache --langs "$LANGS" \
    --max-links 80 --max-cites 40 --out data/enrichment/theories-round1.scan | tail -2

echo "== 3. follow the sources, twice =="
cp data/enrichment/theories-round1.scan data/enrichment/theories-round2.scan
$WD sources data/enrichment/theories-round2.scan $OFFLINE --cache .enrich-cache --top 15 \
    --out data/enrichment/theories-round2.scan | tail -2
cp data/enrichment/theories-round2.scan data/enrichment/theories.scan
$WD sources data/enrichment/theories.scan $OFFLINE --cache .enrich-cache --top 10 \
    --out data/enrichment/theories.scan | tail -2

echo "== 4. what is missing, most referenced first =="
$WD frontier data/enrichment/theories.scan --base data/theories.wdkb --top 10

echo "== 5. autoformalise the eighty most referenced missing terms =="
$WD enrich data/enrichment/theories.scan --base data/theories.wdkb $OFFLINE \
    --cache .wikidata-cache --top 80 --name "theories-enriched" --out data/enriched.wdkb

echo "== 6. the external identifiers the ranking pointed at =="
$WD authority $THEORIES $OFFLINE --cache .wikidata-cache \
    --name "external identifiers of the seven theories" \
    --module RequestProject.Generated.TheoryAuthority | tail -4

echo "== 7. compile everything to Lean =="
$WD scanlean data/enrichment/theories.scan --module RequestProject.Generated.TheorySources | tail -4
$WD lean data/enriched.wdkb --module RequestProject.Generated.Enriched --highlights 6 \
    --cache .wikidata-cache $OFFLINE | tail -6

echo "== 8. let Lean check it =="
lake build RequestProject.EnrichmentCorpus
