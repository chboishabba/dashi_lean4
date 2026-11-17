#!/usr/bin/env bash
# Run the *existing* verified JMD/Lean kernel on the user's exact GWB TAR.
# Never starts spaCy, a Python producer, or unreviewed semantic admission.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
# Historical TAR is optional *import-only* for the first run. There is no
# new TAR, no repacking and no TAR required on subsequent proof runs.
source_dir="$root/.dashi/gwb-source"
legacy="${1:-}"
if [[ -n "$legacy" && "$legacy" != "--no-commit" ]]; then
  [[ -f "$legacy" ]] || { echo "Input TAR not found: $legacy" >&2; exit 2; }
  legacy="$(realpath "$legacy")"
fi
commit_flag=""
if [[ "$legacy" == "--no-commit" || "${2:-}" == "--no-commit" ]]; then
  commit_flag="--no-commit"
  [[ "$legacy" == "--no-commit" ]] && legacy=""
fi
mkdir -p "$root/.dashi"
if [[ ! -f "$source_dir/slr-record.json" ]]; then
  [[ -n "$legacy" ]] || {
    echo "One-time source import needed: bash scripts/run_gwb_lean_proof_suite.sh gwb_article_proof.tar" >&2
    exit 2
  }
  stage_source="$(mktemp -d "$root/.dashi/.gwb-source-stage.XXXXXX")"
  trap 'rm -rf "$stage_source"' EXIT
  # Import original evidence only; never import stale proof/ summaries.
  tar -xf "$legacy" -C "$stage_source" \
    article.html article.txt article-candidates.json slr-record.json \
    slr-source-units.jsonl summary.md gwb_sensiblaw_p0b_mention_licences.json
  mv "$stage_source" "$source_dir"
fi
command -v sha256sum >/dev/null || { echo "sha256sum unavailable" >&2; exit 2; }
command -v lake >/dev/null || { echo "Lean/Lake required" >&2; exit 2; }
command -v jq >/dev/null || { echo "jq required for negative controls" >&2; exit 2; }
command -v python3 >/dev/null || { echo "Python read-only audit tools unavailable" >&2; exit 2; }
command -v cargo >/dev/null || { echo "SLR Rust Cargo unavailable" >&2; exit 2; }
SLR_ROOT="${SLR_ROOT:-$root/../slr}"
SLR_ROOT="$(realpath "$SLR_ROOT")"
[[ -f "$SLR_ROOT/crates/sl-semantic-expansion/Cargo.toml" ]] || {
  echo "Set SLR_ROOT to existing production Rust checkout" >&2; exit 2;
}
if ! lake env lean --version | grep -q '4.28.0'; then
  echo "Pinned targeted Lean 4.28.0 not active" >&2; exit 2
fi
expected="a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
actual="$(sha256sum "$source_dir/article.txt" | cut -d ' ' -f 1)"
[[ "$actual" == "$expected" ]] || {
  echo "Original source UTF-8 SHA mismatch" >&2; exit 2;
}
# All build/proof staging is project-local and removed on exit.
tmp="$(mktemp -d "$root/.dashi/.gwb-lean-stage.XXXXXX")"
out="$(mktemp -d "$root/.dashi/.gwb-proof-run.XXXXXX")"
trap 'rm -rf "$tmp" "$out"' EXIT

# Real SLR semantic alternatives/residuals over the same original
# dependency rows. Build a transient Cargo manifest in the project worktree
# depending on EXISTING SLR crates by path: no duplicate fibre engine and no
# spaCy/Python language producer. The SLR crate itself labels this candidate
# expansion EXPERIMENTAL, so the receipt cannot masquerade as DB-native S28.
mkdir -p "$tmp/slr-cargo"
cat > "$tmp/slr-cargo/Cargo.toml" <<EOF
[package]
name = "gwb-slr-original-observation-probe"
version = "0.0.1"
edition = "2021"

[workspace]

[dependencies]
sensiblaw-core = { path = "$SLR_ROOT/crates/sl-core" }
sensiblaw-semantic-expansion = { path = "$SLR_ROOT/crates/sl-semantic-expansion" }
sensiblaw-legal-runtime = { path = "$SLR_ROOT/crates/sl-legal-runtime" }
serde_json = "1"
sha2 = "0.10"

[[bin]]
name = "gwb-slr-original-observation-probe"
path = "$root/tools/gwb_slr_fibre_probe.rs"
EOF
# Keep Cargo's compiled artifacts in the project, not a second archive.
export CARGO_TARGET_DIR="$root/.dashi/gwb-slr-observation-target"
mkdir -p "$CARGO_TARGET_DIR"
cargo test --quiet --manifest-path "$tmp/slr-cargo/Cargo.toml" \
  2>&1 | tee "$out/slr-rust-test.log"
cargo run --quiet --manifest-path "$tmp/slr-cargo/Cargo.toml" -- \
  "$source_dir/article.txt" "$source_dir/slr-record.json" "$out/slr-rust-observations.json" \
  | tee "$out/slr-rust-expansion.log"
SLR_HEAD="$(git -C "$SLR_ROOT" rev-parse HEAD)"

# Keep direct --full runs self-contained as well: the same narrow JMD
# prerequisite closure is required by the new Q207 and property proof modules.
bash "$root/scripts/build_gwb_jmd_prerequisites.sh" \
  2>&1 | tee "$out/jmd-targeted-prerequisites-build.log"
# Compile the ONE newly introduced source-bound counterexample module
# into the existing project-local .olean cache. Reuse already cached
# WikipediaArticleProof, Batteries and Mathlib; do NOT build Wikidata.
mkdir -p "$root/.lake/build/lib/lean/RequestProject/Slr"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbArticleIdentity.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbArticleIdentity.lean" \
  2>&1 | tee "$out/q207-identity-proof-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbRealSourceConsumer.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbRealSourceConsumer.lean" \
  2>&1 | tee "$out/source-consumer-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbNativeFibreReceipt.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbNativeFibreReceipt.lean" \
  2>&1 | tee "$out/native-fibre-lean-build.log"
# Reify the fully checked raw JSON into source-indexed typed candidates,
# alternatives and residuals without discarding any failed row.
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbTypedSemanticFibre.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbTypedSemanticFibre.lean" \
  2>&1 | tee "$out/typed-semantic-fibre-build.log"

# Verify the reused PR #111 DB-native source/span and S28 provenance
# checker even when this run has no live PostgreSQL ledger to accept.
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/DbSourceProducer.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/DbSourceProducer.lean" \
  2>&1 | tee "$out/db-m12-s28-build.log"
# Reuse JMD's verified property checker before compiling the composed
# world-graph proof. Keep its checked import boundary source-attributed.
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/Proof.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/Proof.lean" \
  2>&1 | tee "$out/jmd-property-proof-build.log"
# Build the previously source-written finite consumer theorem and the
# same-owner JMD/SLR composition theorem before loading the GWB runner.
# Keeping each OLEAN path explicit makes missing imports fail closed.
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/FiniteConsumerCertificate.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/FiniteConsumerCertificate.lean" \
  2>&1 | tee "$out/finite-consumer-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbProofComposition.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbProofComposition.lean" \
  2>&1 | tee "$out/proof-composition-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbWorldGraphProof.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbWorldGraphProof.lean" \
  2>&1 | tee "$out/world-graph-proof-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbHyperfabricTransport.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbHyperfabricTransport.lean" \
  2>&1 | tee "$out/hyperfabric-proof-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbArticleSystemSoundness.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbArticleSystemSoundness.lean" \
  2>&1 | tee "$out/article-system-proof-build.log"
lake env lean -o "$root/.lake/build/lib/lean/RequestProject/Slr/GwbP4SourceLicence.olean" \
  "$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbP4SourceLicence.lean" \
  2>&1 | tee "$out/p4-source-licence-build.log"
lake env lean tools/GwbProofRunner.lean 2>&1 | tee "$out/lean-build.log"
lake env lean --run tools/GwbProofRunner.lean fibre \
  | tee "$out/consumer-fibre-proof.log"
lake env lean --run tools/GwbProofRunner.lean composition \
  | tee "$out/proof-composition-proof.log"
lake env lean --run tools/GwbProofRunner.lean p4 \
  | tee "$out/p4-source-licence-proof.log"
lake env lean tools/GwbProofRunner.lean \
  | tee "$out/axiom-audit.log"
if grep -qE 'sorryAx|admitAx' "$out/axiom-audit.log"; then
  echo "Rejected theorem with admitted proof placeholder" >&2
  exit 1
fi

# Independent Lean structural check: original article characters,
# sentence/role/predicate completeness, 311 lexical years and exact hierarchy.
lake env lean --run tools/GwbProofRunner.lean article-check \
  "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" \
  | tee "$out/article-source-proof.log"

# The first real-article consumer theorem: the original dependency rows
# provide two different embedded-parent answers for an IDENTICAL flat
# scope label. Lean checks the source graph and constructs a no-factorisation
# certificate; no PNF or world event is promoted.
lake env lean --run tools/GwbProofRunner.lean semantic-scope \
  "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" \
  | tee "$out/semantic-scope-proof.log"
lake env lean --run tools/GwbProofRunner.lean rust-fibre-check \
  "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" \
  "$out/slr-rust-observations.json" \
  | tee "$out/native-fibre-source-proof.log"

# Adversarial controls on the ACTUAL Rust SLR alternative/residual and
# consumer receipts. They must fail in the Lean native-fibre consumer.
reject_rust_semantic_mutation() {
  local name="$1"
  local filter="$2"
  jq "$filter" "$out/slr-rust-observations.json" > "$tmp/forged-slr-$name.json"
  if lake env lean --run tools/GwbProofRunner.lean rust-fibre-check \
      "$source_dir/article.txt" "$source_dir/slr-record.json" "$source_dir/article-candidates.json" \
      "$tmp/forged-slr-$name.json" \
      > "$out/rejected-slr-$name.log" 2>&1; then
    echo "UNSOUND: Lean accepted forged native SLR semantic evidence ($name)" >&2
    exit 1
  fi
  echo "SLR_RUST_SEMANTIC_NEGATIVE_CONTROL_REJECTED $name"
}
reject_rust_semantic_mutation passive-by-as-actor \
  '(.sentence_observations[] | .candidates[] | select(.kind=="ReferenceRelation")).kind = "Role(Actor)"'
reject_rust_semantic_mutation event-date-falsely-closed \
  '(.consumer_adequacy.runtime_outcomes[] | select(.query_ref=="gwb:event:when")).disposition = "Adequate"'
reject_rust_semantic_mutation forged-occurrence '.world_occurrence_paid = true'
reject_rust_semantic_mutation dropped-ambiguity \
  '.sentence_observations[18].alternative_fibres |= .[1:]'
reject_rust_semantic_mutation false-residual-closure \
  '.sentence_observations[18].residuals[0].consumer_closed = true'

# Adversarial replay of the *same* Lean checker. jq modifies only
# negative fixtures: it does not parse/produce language interpretations.
{
  reject_mutation() {
    local name="$1"
    local filter="$2"
    jq "$filter" "$source_dir/article-candidates.json" > "$tmp/forged-$name.json"
    if lake env lean --run tools/GwbProofRunner.lean article-check \
        "$source_dir/article.txt" "$source_dir/slr-record.json" "$tmp/forged-$name.json" \
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
conditional complete-finite-fibre query constancy and JMD KB witness composition;
source-relative reported-claim and year-string consumer sufficiency;
nonfactorability of world occurrence, actor identity, event date, embedded scope
under the deliberately unresolved two-reading fibre.
Source-checked: exact GWB Wikipedia revision's archived SLR parser observation;
complete selected candidate predicates and direct syntactic role children;
year and proper-noun tokens, article paragraph/heading partition.
Not proved: externally reviewed PNF semantic admission, real S28 event identity,
world occurrence, actual event chronology, or a complete SLR semantic fibre.
The source fixture is archived parser evidence, not a Rust DB M12 receipt.
EOF
# Examine the real GWB sentences, original dependency graph, P0b
# mention eligibility and temporal candidate associations. This is an
# auditor only, never a SensibLaw/Python language producer.
python3 tools/gwb_semantic_observer_audit.py "$source_dir" \
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
python3 tools/publish_gwb_proof_receipts.py \
  --repo "$root" --source "$source_dir" --run "$out" \
  --slr-head "$SLR_HEAD" \
  --lean-version "$(lake env lean --version)" \
  ${commit_flag:+$commit_flag}
echo "GWB_RUST_LEAN_RECEIPTS_GIT_PASS"
echo "Tracked results: artifacts/gwb-semantic-proof/"
echo "No TAR created or modified."
