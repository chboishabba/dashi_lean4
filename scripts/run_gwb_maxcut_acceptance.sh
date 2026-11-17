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
compile_slr GwbConsumerFibreProof
compile_slr GwbRealSourceConsumer
compile_slr GwbNativeFibreReceipt
compile_slr Proof
compile_slr DbSourceProducer
compile_slr FiniteConsumerCertificate
compile_slr GwbProofComposition
lake env lean tools/GwbProofRunner.lean
lake env lean --run tools/GwbProofRunner.lean composition
echo "GWB_MAXCUT_CONDITIONAL_THEOREMS_KERNEL_ACCEPTED"

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
