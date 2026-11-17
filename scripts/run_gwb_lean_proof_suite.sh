#!/usr/bin/env bash
# Run the *existing* verified JMD/Lean kernel on the user's exact GWB TAR.
# Never starts spaCy, a Python producer, or unreviewed semantic admission.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
archive="${1:?Usage: bash scripts/run_gwb_lean_proof_suite.sh /path/to/gwb_article_proof.tar}"
archive="$(realpath "$archive")"
# One permanent artifact: the SAME TAR. All proof logs and staged files
# live inside project-local temporary directories and are packed back into it.
out="$(mktemp -d "$root/.gwb-proof-run.XXXXXX")"
trap 'rm -rf "$out"' EXIT
command -v sha256sum >/dev/null || { echo "sha256sum unavailable" >&2; exit 2; }
command -v lake >/dev/null || { echo "Pinned Lake/Lean unavailable; install repo lean-toolchain through elan" >&2; exit 2; }
command -v tar >/dev/null || { echo "tar unavailable" >&2; exit 2; }
command -v jq >/dev/null || { echo "jq required for strict negative controls" >&2; exit 2; }
command -v python3 >/dev/null || { echo "python3 needed for read-only evidence archive auditing (NOT NLP)" >&2; exit 2; }
if ! lake env lean --version | grep -q '4.28.0'; then
  echo "Pinned root Lean 4.28.0 not active; do not use /usr/bin/lean 4.27.0" >&2
  exit 2
fi

# A refreshed archive has a different TAR SHA. Pin the ORIGINAL source
# bytes and revision instead; the immutable seven-member evidence payload is
# retained across updates by refresh_gwb_single_tar.py.
expected="a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
actual="$(tar -xOf "$archive" article.txt | sha256sum | cut -d ' ' -f 1)"
if [[ "$actual" != "$expected" ]]; then
  echo "GWB canonical source UTF-8 SHA mismatch: expected $expected, found $actual" >&2
  exit 2
fi
tmp="$(mktemp -d "$root/.gwb-lean-stage.XXXXXX")"
trap 'rm -rf "$tmp" "$out"' EXIT
tar -xf "$archive" -C "$tmp" article.txt slr-record.json article-candidates.json
cd "$root"

# Compile the ONE newly introduced source-bound counterexample module
# into the existing project-local .olean cache. Reuse already cached
# WikipediaArticleProof, Batteries and Mathlib; do NOT build Wikidata.
mkdir -p "$root/.lake/build/lib/lean/RequestProject/Slr"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbRealSourceConsumer.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbRealSourceConsumer.lean" \
  2>&1 | tee "$out/source-consumer-build.log"
lake env lean tools/GwbProofRunner.lean 2>&1 | tee "$out/lean-build.log"
lake env lean --run tools/GwbProofRunner.lean fibre \
  | tee "$out/consumer-fibre-proof.log"
lake env lean tools/GwbProofRunner.lean \
  | tee "$out/axiom-audit.log"
if grep -qE 'sorryAx|admitAx' "$out/axiom-audit.log"; then
  echo "Rejected theorem with admitted proof placeholder" >&2
  exit 1
fi

# Independent Lean structural check: original article characters,
# sentence/role/predicate completeness, 311 lexical years and exact hierarchy.
lake env lean --run tools/GwbProofRunner.lean article-check \
  "$tmp/article.txt" "$tmp/slr-record.json" "$tmp/article-candidates.json" \
  | tee "$out/article-source-proof.log"

# The first real-article consumer theorem: the original dependency rows
# provide two different embedded-parent answers for an IDENTICAL flat
# scope label. Lean checks the source graph and constructs a no-factorisation
# certificate; no PNF or world event is promoted.
lake env lean --run tools/GwbProofRunner.lean semantic-scope \
  "$tmp/article.txt" "$tmp/slr-record.json" "$tmp/article-candidates.json" \
  | tee "$out/semantic-scope-proof.log"

# Adversarial replay of the *same* Lean checker. jq modifies only
# negative fixtures: it does not parse/produce language interpretations.
{
  reject_mutation() {
    local name="$1"
    local filter="$2"
    jq "$filter" "$tmp/article-candidates.json" > "$tmp/forged-$name.json"
    if lake env lean --run tools/GwbProofRunner.lean article-check \
        "$tmp/article.txt" "$tmp/slr-record.json" "$tmp/forged-$name.json" \
        > "$out/rejected-$name.log" 2>&1; then
      echo "UNSOUND: Lean accepted forged article evidence ($name)" >&2
      exit 1
    fi
    echo "LEAN_NEGATIVE_CONTROL_REJECTED $name"
  }
  reject_mutation missing-predicate '.event_candidates |= .[1:]'
  reject_mutation missing-direct-actor '.event_candidates[1].actors = []'
  reject_mutation false-year-index '.timeline_candidates[0].year_candidate = 0'
  reject_mutation promoted-world-truth '.source_assertion_is_world_truth = true'
  reject_mutation forged-paragraph-boundary '.sections[0].end_char += 1'
}
 
cat > "$out/proof-boundary.txt" <<'EOF'
LEAN_GWB_CONSUMER_PROOF_BOUNDARY_V1
Kernel proved: generic provenance-preserving fibre join ACI;
source-relative reported-claim and year-string consumer sufficiency;
nonfactorability of world occurrence, actor identity, event date, embedded scope
under the deliberately unresolved two-reading fibre.
Source-checked: exact GWB Wikipedia revision's archived SLR parser observation;
complete selected candidate predicates and direct syntactic role children;
year and proper-noun tokens, article paragraph/heading partition.
Not proved: externally reviewed PNF semantic admission, real S28 event identity,
world occurrence, actual event chronology, or a complete SLR semantic fibre.
The TAR is historical Python-parser evidence, not a Rust DB M12 receipt.
EOF
# Examine the real GWB sentences, original dependency graph, P0b
# mention eligibility and temporal candidate associations. This is an
# auditor only, never a SensibLaw/Python language producer.
python3 tools/gwb_semantic_observer_audit.py "$archive" \
  --output "$out/semantic_observer_audit.json"
# Real-sentence, cross-layer semantic regression. A generic Lean theorem alone
# cannot pay this gate, and changing parser output must not silently rebaseline.
python3 - "$out/semantic_observer_audit.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1],encoding="utf-8"))
w=r["scope_label_observer_collision"]
assert r["source_revision"]=="enwiki-revid:1385850169"
assert r["embedded_parent_conjunctions"]==57
assert r["embedded_conjunction_flat_assertion_labels"]==57
assert w["same_observation"] and w["different_consumer_answers"]
assert w["embedded_witness"]["predicate"]=="had"
assert w["embedded_witness"]["parent"]=="possessed"
assert w["embedded_witness"]["parent_dep"]=="acl"
assert w["root_witness"]["parent_dep"]=="ROOT"
assert r["unmaterialized_grammatical_role_tokens"]==73
assert r["role_missing_surfaces"]["actors:by"]==59
assert len(r["p0b_candidate_fibre_examples"])>=7
assert r["status"]["reviewed_slr_fibres"]=="NOT_IN_ARCHIVE"
assert r["status"]["query_relative_closure"]=="NOT_IN_ARCHIVE"
print("GWB_REAL_SOURCE_SEMANTIC_WITNESSES_PASS")
PY
python3 tools/refresh_gwb_single_tar.py "$archive" \
  --audit "$out/semantic_observer_audit.json" \
  --logs "$out" \
  --lean-version "$(lake env lean --version)" \
  --head "$(git rev-parse HEAD)"
echo "GWB_LEAN_CONSUMER_AND_ARCHIVE_PROOF_SUITE_PASS"
echo "All proof logs, semantic witnesses and status are INSIDE: $archive"
