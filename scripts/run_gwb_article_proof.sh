#!/usr/bin/env bash
# One command: revision-pinned Wikipedia -> existing SLR spaCy producer ->
# JMD Lean source evidence -> JMD Q207 ontology theorem and source scan.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
agda="${DASHI_AGDA_ROOT:-$here/../dashi_agda}"
out="${GWB_ARTICLE_OUT:-$here/.gwb_article_proof}"
py="${PYTHON:-python3}"
command -v lake >/dev/null || { echo "Missing lake / Lean toolchain" >&2; exit 2; }
command -v sha256sum >/dev/null || { echo "Missing sha256sum" >&2; exit 2; }
"$py" -c "import spacy; import bs4; spacy.load('en_core_web_sm')" ||
  { echo "Install python -m spacy download en_core_web_sm and beautifulsoup4" >&2; exit 2; }
test -f "$agda/tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py" ||
  { echo "SLR generic source-unit producer not found: $agda" >&2; exit 2; }
cd "$here"
"$py" tools/gwb_article_proof.py --self-check
lake build wikidata
lake exe wikidata gwb-article-proof "$py" "$here/tools/gwb_article_proof.py" \
  "$agda" "$out"
echo
echo "RESULTS: $out/summary.md"
echo "EVIDENCE: $out/article-candidates.json"
echo "SLR SOURCE: $out/slr-record.json"
echo "JMD WIKI PROOF: $out/GwbArticleQ207Proof.lean"
