#!/usr/bin/env bash
# Original SLR/ITIR article output is the authority-bearing OBSERVATION input.
# This does not run the experimental sl-semantic-expansion crate, an NLP parser,
# a second world-model constructor, or a JMD-based article meaning resolver.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
source_dir="${GWB_SOURCE_DIR:-$root/.dashi/gwb-source}"
for name in article.txt slr-record.json article-candidates.json gwb_sensiblaw_p0b_mention_licences.json; do
  [[ -s "$source_dir/$name" ]] || { echo "Missing original SLR input: $source_dir/$name" >&2; exit 2; }
done
command -v lake >/dev/null || { echo "Lean 4.28 required" >&2; exit 2; }
command -v jq >/dev/null || { echo "jq required" >&2; exit 2; }
command -v python3 >/dev/null || { echo "python3 required" >&2; exit 2; }
lake env lean --version | grep -q '4.28.0' || { echo "Lean pin must be 4.28.0" >&2; exit 2; }

# Staging is local and independent of both the historical Rust receipt directory
# and the user's single TAR. Publication happens only after every check passed.
mkdir -p "$root/.dashi"
stage="$(mktemp -d "$root/.dashi/.gwb-original-slr-run.XXXXXX")"
trap 'rm -rf "$stage"' EXIT

python3 -m unittest discover -s tests -p 'test_gwb_canonical_source_boundary.py' \
  2>&1 | tee "$stage/canonical-source-regression.log"

python3 tools/gwb_canonical_slr_acceptance.py \
  --source-dir "$source_dir" --output "$stage/original-source-inventory.json" \
  | tee "$stage/original-source-inventory.log"

# The original source and original SLR-derived article candidates are checked
# by the pre-existing Lean checker: all selected predicates and DIRECT roles,
# lexical years, sentence/section structure and source references.
lake env lean --run tools/GwbProofRunner.lean article-check \
  "$source_dir/article.txt" "$source_dir/slr-record.json" \
  "$source_dir/article-candidates.json" \
  | tee "$stage/article-source-proof.log"
lake env lean --run tools/GwbProofRunner.lean semantic-scope \
  "$source_dir/article.txt" "$source_dir/slr-record.json" \
  "$source_dir/article-candidates.json" \
  | tee "$stage/semantic-scope-proof.log"

# Original-source negative controls only: no experimental candidate / residual
# mutation and no false claim that Rust's syntactic alternatives are semantic.
reject_article_mutation () {
  local label="$1"; local transform="$2"
  jq "$transform" "$source_dir/article-candidates.json" > "$stage/forged-$label.json"
  if lake env lean --run tools/GwbProofRunner.lean article-check \
      "$source_dir/article.txt" "$source_dir/slr-record.json" \
      "$stage/forged-$label.json" > "$stage/rejected-$label.log" 2>&1; then
    echo "UNSOUND: original source checker accepted $label" >&2
    exit 1
  fi
  grep -q 'JMD Lean rejected a forged or unsupported source/PNF projection' \
    "$stage/rejected-$label.log" || { echo "Unexpected negative-test failure: $label" >&2; exit 1; }
  echo "GWB_CANONICAL_SLR_NEGATIVE_REJECTED $label"
}
reject_article_mutation missing-predicate '.event_candidates |= .[1:]'
reject_article_mutation missing-direct-actor '.event_candidates[1].actors = []'
reject_article_mutation false-year-index '.timeline_candidates[0].year_candidate = 0'
reject_article_mutation promoted-world-truth '.source_assertion_is_world_truth = true'
reject_article_mutation forged-paragraph-boundary '.sections[0].end_char += 1'

# Reopen the producer's own dependency graph and P0b mention eligibility.
# This is a diagnostic only; no new semantic theory is manufactured.
python3 tools/gwb_semantic_observer_audit.py "$source_dir" \
  --output "$stage/original-scope-and-mention-audit.json" \
  | tee "$stage/original-scope-and-mention.log"

# Verify source-bearing output *before* making the new receipt visible.
python3 tools/publish_gwb_original_slr_receipts.py \
  --source "$source_dir" --run "$stage" \
  --destination "$root/artifacts/gwb-original-slr-proof"
echo "GWB_ORIGINAL_SLR_ACCEPTANCE_PASS"
echo "The experimental Rust receipt remains available only as historical diagnostics."
echo "No TAR created or modified, and no untracked outputs removed."
