#!/usr/bin/env bash
# Re-run the exact uploaded GWB SLR source record through the repaired
# lexical year/PROPN projection and JMD Lean without spaCy or Wikipedia re-fetch.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
input="${1:-$here/.gwb_article_proof}"
output="${2:-$here/.gwb_article_replay}"
py="${PYTHON:-python3}"
test -f "$input/article.txt" || { echo "Missing $input/article.txt" >&2; exit 2; }
test -f "$input/slr-record.json" || { echo "Missing $input/slr-record.json" >&2; exit 2; }
command -v lake >/dev/null || { echo "Missing Lean/Lake toolchain" >&2; exit 2; }
command -v sha256sum >/dev/null || { echo "Missing sha256sum" >&2; exit 2; }
revision="$("$py" - "$input/slr-record.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1],encoding="utf-8"))
ref=str(r["revision_ref"])
assert ref.startswith("enwiki-revid:"), f"unexpected revision {ref!r}"
print(ref.removeprefix("enwiki-revid:"))
PY
)"
cd "$here"
"$py" tools/gwb_article_proof.py --self-check
"$py" tools/gwb_article_proof.py \
  --output-dir "$output" \
  --source-text "$input/article.txt" \
  --source-revision "$revision" \
  --slr-record "$input/slr-record.json"
lake build wikidata
lake exe wikidata gwb-article-replay "$output"
echo "Summary: $output/summary.md"
echo "Candidate evidence: $output/article-candidates.json"
echo "Kernel-checked JMD ontology: $output/GwbArticleQ207Proof.lean"
