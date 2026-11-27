#!/usr/bin/env bash
# Run the *existing* verified JMD/Lean kernel on the user's exact GWB TAR.
# Never starts spaCy, a Python producer, or unreviewed semantic admission.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
archive="${1:?Usage: bash scripts/run_gwb_lean_proof_suite.sh /path/to/gwb_article_proof.tar}"
archive="$(realpath "$archive")"
out="${2:-$root/.gwb_lean_proof}"
mkdir -p "$out"
out="$(realpath "$out")"
command -v sha256sum >/dev/null || { echo "sha256sum unavailable" >&2; exit 2; }
command -v lake >/dev/null || { echo "Pinned Lake/Lean unavailable; install repo lean-toolchain through elan" >&2; exit 2; }
command -v tar >/dev/null || { echo "tar unavailable" >&2; exit 2; }
if ! lake env lean --version | grep -q '4.35.0-rc3'; then
  echo "Pinned root Lean 4.35.0-rc3 not active; do not use /usr/bin/lean 4.27.0" >&2
  exit 2
fi

expected="6bbad0f9bcc2f0aa2e0e6f77f15692a945c1331a6337cfe202c19a58e2460f9e"
actual="$(sha256sum "$archive" | cut -d ' ' -f 1)"
if [[ "$actual" != "$expected" ]]; then
  echo "Archive SHA mismatch: expected $expected, found $actual" >&2
  exit 2
fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
tar -xf "$archive" -C "$tmp" article.txt slr-record.json article-candidates.json
cd "$root"

# Compiling the executable kernel-checks all imported proofs in
# GwbConsumerFibreProof, DocumentQuerySound and TemporalDocumentProof.
lake build wikidata | tee "$out/lean-build.log"
lake exe wikidata gwb-fibre-proof | tee "$out/consumer-fibre-proof.log"
lake env lean DASHI/output-final_aristotle/RequestProject/Slr/GwbProofAxiomAudit.lean \
  | tee "$out/axiom-audit.log"
if grep -qE 'sorryAx|admitAx' "$out/axiom-audit.log"; then
  echo "Rejected theorem with admitted proof placeholder" >&2
  exit 1
fi

# Independent Lean structural check: original article characters,
# sentence/role/predicate completeness, 311 lexical years and exact hierarchy.
lake exe wikidata gwb-article-check \
  "$tmp/article.txt" "$tmp/slr-record.json" "$tmp/article-candidates.json" \
  | tee "$out/article-source-proof.log"

# Adversarial replay of the *same* Lean checker. jq changes test
# fixtures only; it does not parse/produce language interpretations.
if command -v jq >/dev/null; then
  reject_mutation() {
    local name="$1"
    local filter="$2"
    jq "$filter" "$tmp/article-candidates.json" > "$tmp/forged-$name.json"
    if lake exe wikidata gwb-article-check \
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
else
  echo "Optional source-mutation negative tests SKIPPED (jq unavailable)"
fi

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
echo "GWB_LEAN_CONSUMER_AND_ARCHIVE_PROOF_SUITE_PASS"
echo "Proof logs: $out"
