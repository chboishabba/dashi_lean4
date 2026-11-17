#!/usr/bin/env bash
# Proof-first GWB/JMD/SLR maximum-cut acceptance.
# No TAR, reparse, new ontology, or fabricated semantic licences.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:---proof-only}"
case "$mode" in
  --proof-only|--full|--strict) ;;
  *)
    echo "usage: bash scripts/run_gwb_maxcut_acceptance.sh [--proof-only|--full|--strict]" >&2
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
compile_slr GwbArticleIdentity
compile_slr GwbConsumerFibreProof
compile_slr GwbRealSourceConsumer
compile_slr GwbNativeFibreReceipt
compile_slr GwbTypedSemanticFibre
compile_slr Proof
compile_slr DbSourceProducer
compile_slr FiniteConsumerCertificate
compile_slr GwbProofComposition
compile_slr GwbWorldGraphProof
compile_slr GwbHyperfabricTransport
compile_slr GwbArticleSystemSoundness
compile_slr GwbP4SourceLicence
compile_slr GwbP4ArticleEndToEnd
lake env lean tools/GwbProofRunner.lean
lake env lean --run tools/GwbProofRunner.lean composition
lake env lean --run tools/GwbProofRunner.lean p4
echo "GWB_MAXCUT_CONDITIONAL_THEOREMS_KERNEL_ACCEPTED"
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
  # Optional real end-to-end P4 check: use original locally executed Rust
  # receipt if explicitly supplied, otherwise the prior committed receipt.
  p4_native="${GWB_P4_NATIVE_JSON:-$root/artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json}"
  if [[ -f "$p4_native" ]]; then
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
Run --full on the original source/SLR checkout to refresh evidence.
EOF
  exit 0
fi

[[ -f "$root/.dashi/gwb-source/article.txt" ]] || {
  echo "Missing local exact original GWB fixture .dashi/gwb-source/article.txt" >&2
  exit 2
}
[[ -n "${SLR_ROOT:-}" ]] || {
  echo "Set SLR_ROOT to your original SLR checkout (no TAR required)" >&2
  exit 2
}
bash "$root/scripts/run_gwb_lean_proof_suite.sh" --no-commit
echo "GWB_MAXCUT_ARTICLE_SOURCE_AND_NEGATIVE_CONTROLS_PASS"
echo "Review and commit only the regenerated artifacts/gwb-semantic-proof/ results."

if [[ "$mode" == "--strict" ]]; then
  # This is a fail-closed research acceptance mode: source/kernel passage is
  # insufficient to assert the as-yet-unpaid world-semantic obligations.
  echo "STRICT_PRODUCTION_CLOSURE_NOT_PAID: same-source reviewed M12/S28," >&2
  echo "complete semantic fibre, event identity, 51-QID elaboration." >&2
  exit 3
fi
