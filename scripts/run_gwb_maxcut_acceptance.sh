#!/usr/bin/env bash
# Proof-first GWB/JMD/SLR maximum-cut acceptance.
# No TAR, reparse, new ontology, or fabricated semantic licences.
set -euo pipefail
# Bound individual Lean invocations; do not bound the entire campaign.
lake() { timeout --kill-after=5s "${ITIR_STEP_TIMEOUT:-90s}" lake "$@"; }

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:---proof-only}"
case "$mode" in
  --proof-only|--full|--strict|--legacy-rust) ;;
  *)
    echo "usage: bash scripts/run_gwb_maxcut_acceptance.sh [--proof-only|--full|--strict|--legacy-rust]" >&2
    exit 2 ;;
esac

command -v lake >/dev/null || { echo "Lean 4.28.0/Lake required" >&2; exit 2; }
if ! lake env lean --version | grep -q '4.28.0'; then
  echo "Wrong Lean pin: required 4.28.0" >&2; exit 2
fi
# The cached Lean build may have the SLR owner OLEANs but not original JMD
# Cli.Import/Fetch/Derive. Build their exact transitive dependency closure
# before GwbArticleIdentity imports Cli.Import.
bash "$root/scripts/build_gwb_jmd_prerequisites.sh"
# Deterministic targeted dependency build: no whole Wikidata executable.
# The original JMD Cli.Derive/PropertyEngine OLEANs remain pinned, while all
# SLR proof-owner imports needed by this handoff are explicitly rebuilt.
outdir="$root/.lake/build/lib/lean/RequestProject/Slr"
srcdir="$root/DASHI/output-final_aristotle/RequestProject/Slr"
mkdir -p "$outdir"
compile_slr() {
  local module="$1"
  echo "GWB_MAXCUT_BUILDING_${module}"
  lake env lean -o "$outdir/${module}.olean" "$srcdir/${module}.lean"
}
compile_slr Producer
compile_slr DocumentQuerySound
compile_slr TemporalDocumentProof
compile_slr WikipediaArticleProof
compile_slr GwbCanonicalSourceProof
compile_slr GwbRelationTransport
compile_slr GwbArticleIdentity
compile_slr GwbConsumerFibreProof
compile_slr GwbRealSourceConsumer
compile_slr GwbNativeFibreReceipt
compile_slr GwbTypedSemanticFibre
compile_slr Proof
compile_slr DbSourceProducer
compile_slr GwbProductionTrace
compile_slr FiniteConsumerCertificate
compile_slr RelationalObservedMeet
compile_slr GwbProofComposition
compile_slr GwbWorldGraphProof
compile_slr GwbHyperfabricTransport
compile_slr GwbArticleSystemSoundness
compile_slr GwbP4SourceLicence
compile_slr GwbP4ArticleEndToEnd
compile_slr GwbP5P10ExactWeld
lake env lean tools/GwbProofRunner.lean
lake env lean tools/RelationalObservedMeetRunner.lean
# Additional exact original SLR receipt checks, without a new parser.
if [[ -n "${ITIR_RELATIONAL_FAMILY_JSON:-}" ]]; then
  mkdir -p "$root/artifacts/itir-native-maxcut"
  timeout 90s lake env lean --run tools/RelationalObservedMeetRunner.lean \
    "$ITIR_RELATIONAL_FAMILY_JSON" "$root/artifacts/itir-native-maxcut/observed-meet.json"
fi
if [[ -n "${ITIR_ORIGINAL_RELATION_PACKET_JSON:-}" || -n "${ITIR_ORIGINAL_RELATION_QUERY_JSON:-}" ]]; then
  [[ -s "${ITIR_ORIGINAL_RELATION_PACKET_JSON:-}" && -s "${ITIR_ORIGINAL_RELATION_QUERY_JSON:-}" ]] || {
    echo "Both original native relation packet and query receipt required" >&2; exit 2;
  }
  mkdir -p "$root/artifacts/itir-native-maxcut"
  timeout 90s python3 tools/check_original_relation_query.py \
    "$ITIR_ORIGINAL_RELATION_PACKET_JSON" "$ITIR_ORIGINAL_RELATION_QUERY_JSON" \
    > "$root/artifacts/itir-native-maxcut/original-relation-reference.json"
  timeout 90s lake env lean --run tools/RelationalObservedMeetRunner.lean relations \
    "$ITIR_ORIGINAL_RELATION_PACKET_JSON" "$ITIR_ORIGINAL_RELATION_QUERY_JSON" \
    | tee "$root/artifacts/itir-native-maxcut/original-relation-lean.log"
fi
lake env lean --run tools/GwbProofRunner.lean composition
# Historical P4 SourceQueryLicence is a theorem over the experimental
# Rust observation; it is not an original SLR semantic licence.
if [[ "$mode" == "--legacy-rust" ]]; then
  lake env lean --run tools/GwbProofRunner.lean p4
fi
echo "GWB_MAXCUT_CONDITIONAL_THEOREMS_KERNEL_ACCEPTED"
# Historical P5-P10 candidate-probe audit is not required by original SLR acceptance.
# Experimental Rust residual diagnostics are NOT part of canonical acceptance.
# They can be run only on explicit operator request, never by the default path.
if [[ "${GWB_ENABLE_EXPERIMENTAL_RESIDUAL_DIAGNOSTICS:-0}" == "1" ]]; then
  python3 -m unittest discover -s tests -p 'test_gwb_p5_p10_evidence_audit.py'
  python3 tools/gwb_p5_p10_evidence_audit.py \
    --manifest "$root/artifacts/gwb-semantic-proof/proof_run_manifest.json"
  python3 -m unittest discover -s tests -p 'test_gwb_original_dependency_fibre.py'
  mkdir -p "$root/.dashi/gwb-audit"
  python3 tools/audit_gwb_original_semantic_cases.py \
    --native "$root/artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json" \
    --output "$root/.dashi/gwb-audit/original_semantic_cases.json"
  if [[ -f "$root/.dashi/gwb-source/slr-record.json" ]]; then
    python3 tools/audit_gwb_original_dependency_fibre.py \
      --slr "$root/.dashi/gwb-source/slr-record.json" \
      --native "$root/artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json" \
      --output "$root/.dashi/gwb-audit/unsupported_dependency_fine.json"
  fi
fi


# Optional real DB-native outputs. These files must be produced by the
# original checked SLR/PostgreSQL path; no JSON or event identity is invented.
# M12 requires its exact source literal; S28 requires its event reference.
if [[ -n "${GWB_DB_M12_JSON:-}" || -n "${GWB_DB_M12_LITERAL:-}" ]]; then
  [[ -f "${GWB_DB_M12_JSON:-}" && -f "${GWB_DB_M12_LITERAL:-}" ]] || {
    echo "Supply both GWB_DB_M12_JSON and GWB_DB_M12_LITERAL" >&2
    exit 2
  }
  lake env lean --run tools/GwbProofRunner.lean db-m12-check \
    "$GWB_DB_M12_JSON" "$GWB_DB_M12_LITERAL"
fi
if [[ -n "${GWB_DB_S28_JSON:-}" || -n "${GWB_DB_S28_EVENT_REF:-}" ]]; then
  [[ -f "${GWB_DB_S28_JSON:-}" && -n "${GWB_DB_S28_EVENT_REF:-}" ]] || {
    echo "Supply both GWB_DB_S28_JSON and GWB_DB_S28_EVENT_REF" >&2
    exit 2
  }
  lake env lean --run tools/GwbProofRunner.lean db-s28-check \
    "$GWB_DB_S28_JSON" "$GWB_DB_S28_EVENT_REF"
fi


# Optional bounded GWB world: re-open every source QID via the original
# JMD entity getter, then prove each supported P-relation inside its
# independently imported PKB. Unmatched acquisition edges remain obligations.
if [[ -n "${GWB_WORLD_GRAPH_JSON:-}" ]]; then
  [[ -f "$GWB_WORLD_GRAPH_JSON" ]] || {
    echo "Missing original SLR GWB world graph: $GWB_WORLD_GRAPH_JSON" >&2
    exit 2
  }
  cache="${GWB_JMD_ENTITY_CACHE:-$root/.dashi/gwb-world/jmd-entity-cache}"
  report="${GWB_WORLD_JMD_REPORT:-$root/.dashi/gwb-world/jmd-property-proof.json}"
  mkdir -p "$cache" "$(dirname "$report")"
  graph_command="world-graph-check"
  [[ "${GWB_WIKIDATA_OFFLINE:-0}" == "1" ]] &&
    graph_command="world-graph-check-offline"
  lake env lean --run tools/GwbProofRunner.lean \
    "$graph_command" "$GWB_WORLD_GRAPH_JSON" "$cache" "$report"
fi

# The exact archived article source is local/uncommitted, not transported
# through the world graph. Independently recheck the Q207 sitelink whenever
# its JMD EntityData cache or an explicit EntityData file is available.
qid_json="${GWB_Q207_ENTITY_JSON:-}"
if [[ -z "$qid_json" && -n "${GWB_WORLD_GRAPH_JSON:-}" ]]; then
  qid_json="${GWB_JMD_ENTITY_CACHE:-$root/.dashi/gwb-world/jmd-entity-cache}/Q207.json"
fi
if [[ -n "$qid_json" ]]; then
  [[ -f "$qid_json" ]] || { echo "Missing Q207 original EntityData: $qid_json" >&2; exit 2; }
  source_dir="$root/.dashi/gwb-source"
  for f in article.txt slr-record.json article-candidates.json; do
    [[ -f "$source_dir/$f" ]] || {
      echo "Original exact GWB source required for Q207 proof: $source_dir/$f" >&2
      exit 2
    }
  done
  lake env lean --run tools/GwbProofRunner.lean article-qid-check \
    "$source_dir/article.txt" "$source_dir/slr-record.json" \
    "$source_dir/article-candidates.json" "$qid_json"
  # Exact bounded article claim -> independent JMD P39 support.
  office_json="${GWB_Q11696_ENTITY_JSON:-${GWB_JMD_ENTITY_CACHE:-$root/.dashi/gwb-world/jmd-entity-cache}/Q11696.json}"
  if [[ -f "$office_json" ]]; then
    mkdir -p "$root/.dashi/gwb-world"
    office_receipt="$root/.dashi/gwb-world/office-claim-proof.json"
    stage="$(mktemp -d "$root/.dashi/gwb-world/office-check.XXXXXX")"
    trap 'rm -rf "$stage"' EXIT
    office_check() {
      lake env lean --run tools/GwbProofRunner.lean article-office-check \
        "$source_dir/article.txt" "$source_dir/slr-record.json" \
        "$source_dir/article-candidates.json" "$1" "$2" "$3"
    }
    office_check "$qid_json" "$office_json" "$stage/first.json"
    office_check "$qid_json" "$office_json" "$stage/replay.json"
    cmp "$stage/first.json" "$stage/replay.json"
    if office_check "$office_json" "$qid_json" "$stage/wrong.json" > "$stage/wrong.log" 2>&1; then
      echo "ERROR: swapped root/office accepted" >&2; exit 1
    fi
    grep -q "GWB_OFFICE_CLAIM_REJECTED: original Q207/article mismatch" "$stage/wrong.log"
    python3 - "$qid_json" "$stage/without-office.json" <<'PY'
import json, sys
with open(sys.argv[1], encoding="utf-8") as f:
    data = json.load(f)
data["entities"]["Q207"]["claims"].pop("P39", None)
with open(sys.argv[2], "w", encoding="utf-8") as f:
    json.dump(data, f)
PY
    if office_check "$stage/without-office.json" "$office_json" "$stage/missing.json" > "$stage/missing.log" 2>&1; then
      echo "ERROR: missing original P39 accepted" >&2; exit 1
    fi
    grep -q "GWB_OFFICE_CLAIM_REJECTED: independent P39 support absent" "$stage/missing.log"
    mv "$stage/first.json" "$office_receipt"
    echo "GWB_BOUNDED_OFFICE_REPLAY_AND_NEGATIVE_CONTROLS_PASS"
    rm -rf "$stage"
    trap - EXIT
  elif [[ -n "${GWB_Q11696_ENTITY_JSON:-}" ]]; then
    echo "Missing requested Q11696 EntityData: $office_json" >&2; exit 2
  else
    echo "GWB_BOUNDED_OFFICE_NOT_RUN: supply original Q11696 EntityData"
  fi
  # The historical P4 native Rust receipt is NOT a canonical article-semantic
  # premise. Reopen it only on the explicitly selected legacy diagnostic lane.
  if [[ "$mode" == "--legacy-rust" ]]; then
    p4_native="${GWB_P4_NATIVE_JSON:-$root/artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json}"
    [[ -f "$p4_native" ]] || { echo "Legacy Rust P4 receipt absent" >&2; exit 2; }
    lake env lean --run tools/GwbProofRunner.lean article-p4-check \
      "$source_dir/article.txt" "$source_dir/slr-record.json" \
      "$source_dir/article-candidates.json" "$p4_native" "$qid_json"
  fi

fi

if [[ "$mode" == "--proof-only" ]]; then
  cat <<'EOF'
GWB_MAXCUT_PROOF_ONLY_PASS
CONDITIONAL: finite consumer closure requires exhaustive live-reading evidence
and independently checked source/reading interpretation correspondence.
Still OPEN: DB-native same-source M12/S28, real cross-sentence identity,
reviewed event/time joins, source-to-JMD alignment, 51-QID proof elaboration.
Run --full to verify original SLR records directly (no Rust probe or SLR_ROOT required).
EOF
  exit 0
fi

[[ -f "$root/.dashi/gwb-source/article.txt" ]] || {
  echo "Missing local exact original GWB fixture .dashi/gwb-source/article.txt" >&2
  exit 2
}
# SLR_ROOT is only needed by the explicitly opted-in historical Rust probe.
if [[ "$mode" == "--legacy-rust" ]]; then
  echo "GWB_EXPERIMENTAL_RUST_DIAGNOSTIC_LEGACY_OPT_IN"
  bash "$root/scripts/run_gwb_lean_proof_suite.sh" --no-commit
  echo "Legacy diagnostic artifacts only: artifacts/gwb-semantic-proof/"
else
  echo "GWB_ORIGINAL_SLR_PRODUCER_CANONICAL_ACCEPTANCE"
  bash "$root/scripts/run_gwb_original_slr_acceptance.sh"
  echo "GWB_MAXCUT_ORIGINAL_SLR_SOURCE_AND_NEGATIVE_CONTROLS_PASS"
  echo "Review and commit only artifacts/gwb-original-slr-proof/; historical Rust artifacts remain unchanged."
fi

if [[ "$mode" == "--strict" ]]; then
  # This is a fail-closed research acceptance mode: source/kernel passage is
  # insufficient to assert the as-yet-unpaid world-semantic obligations.
  echo "STRICT_PRODUCTION_CLOSURE_NOT_PAID: same-source reviewed M12/S28," >&2
  echo "complete semantic fibre, event identity, 51-QID elaboration." >&2
  exit 3
fi
