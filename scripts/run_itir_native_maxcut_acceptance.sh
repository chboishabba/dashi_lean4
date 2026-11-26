#!/usr/bin/env bash
# Single native campaign. No reparsing, CI, generated semantic witnesses or automatic admission.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${SLR_ROOT:?existing SLR PR 79 checkout required}"
: "${ITIR_ROOT:?existing ITIR PR 74 checkout required}"
: "${SENSIBLAW_DATABASE_URL:?original numeric PostgreSQL required}"
: "${ITIR_REL_CORPUS_REF:?existing persisted REL corpus reference required}"
: "${ITIR_REL_ACCESS_CONSTRAINT_REF:?existing access constraint reference required}"
SLR_ROOT="$(cd "$SLR_ROOT" && pwd)"
ITIR_ROOT="$(cd "$ITIR_ROOT" && pwd)"
export SLR_ROOT ITIR_ROOT
export GWB_WIKIDATA_OFFLINE=1
limit="${ITIR_STEP_TIMEOUT:-90s}"
export ITIR_STEP_TIMEOUT="$limit"
for cmd in cargo lake jq git timeout python3 sha256sum; do command -v "$cmd" >/dev/null; done
seed="${ITIR_ORIGINAL_RELATION_SEED:-$SLR_ROOT/artifacts/gwb/v8-relation-reopen.json}"
[[ -s "$seed" ]] || { echo "Missing original numeric relation receipt" >&2; exit 2; }
for f in article.txt slr-record.json article-candidates.json gwb_sensiblaw_p0b_mention_licences.json; do
  [[ -s "$root/.dashi/gwb-source/$f" ]] || { echo "Missing original article input: $f" >&2; exit 2; }
done
cd "$root"
# Refuse stale checkout identities. Operator owns checkout changes.
git -C "$SLR_ROOT" merge-base --is-ancestor 9fa4b886ef386e26869e3b04b821ac378b304817 HEAD
git -C "$ITIR_ROOT" merge-base --is-ancestor 67dbf358efcab05883db023501bdfa60a9b73f61 HEAD
key="$( { git rev-parse HEAD; git -C "$SLR_ROOT" rev-parse HEAD; git -C "$ITIR_ROOT" rev-parse HEAD; sha256sum "$seed"; printf '%s\n' "$ITIR_REL_CORPUS_REF" "$ITIR_REL_ACCESS_CONSTRAINT_REF"; } | sha256sum | cut -d' ' -f1)"
out="$root/artifacts/itir-native-maxcut/$key"
mkdir -p "$out"
trap 'rc=$?; if (( rc != 0 )); then echo "Campaign stopped (exit $rc); receipts/logs: $out" >&2; fi' EXIT
bounded() { timeout --kill-after=5s "$limit" "$@"; }
step() {
  local name="$1"; shift
  echo "ITIR_STEP $name"
  bounded "$@" > "$out/$name.tmp" 2> "$out/$name.stderr"
  mv "$out/$name.tmp" "$out/$name"
}
# Only build/test checkpoints are reusable. Live readbacks always run again.
cd "$SLR_ROOT"
if [[ ! -s "$out/rust-build.done" || ! -x target/debug/sensiblaw ]]; then
  step rust-test-relational.log cargo test -p sensiblaw-pg-source-store --lib relational_family
  step rust-test-numeric.log cargo test -p sensiblaw-pg-source-store --lib numeric_pnf
  step rust-test-factor-consumer.log cargo test -p sensiblaw-pg-source-store --lib recorded_factor_consumer_tests
  step rust-build.log cargo build -p sensiblaw-cli
  sha256sum target/debug/sensiblaw > "$out/rust-build.done"
elif ! sha256sum -c "$out/rust-build.done" >/dev/null; then
  rm "$out/rust-build.done"
  echo "Native executable changed; rerun to rebuild/test." >&2
  exit 2
fi
binary="$SLR_ROOT/target/debug/sensiblaw"
export ITIR_SLR_NATIVE_EXECUTABLE="$binary"
run="$(jq -er .numeric_run_ref "$seed")"
doc="$(jq -er .document_ref "$seed")"
snapshot="$(jq -er .snapshot_ref "$seed")"
digest="$(jq -er .packet_sha256 "$seed")"
step numeric-reopen.json "$binary" numeric-pnf-native relation-reopen "$run" "$doc" "$snapshot" "$digest"
step numeric-query.json "$binary" numeric-pnf-native relation-query "$run" "$doc" "$snapshot" "$digest" all
for axis in type_ref referential_type role value; do
  step "factor-$axis.json" "$binary" numeric-pnf-native factor-consumer "$run" "$doc" "$snapshot" "$digest" "$axis"
done
# The existing endpoint receipt supplies the actual demand coordinate;
# no hard-coded substitute and no new candidate enumeration.
demand_seed="${ITIR_ORIGINAL_DEMAND_SEED:-$SLR_ROOT/artifacts/gwb/v8-typed-relation-carriers.json}"
if [[ -s "$demand_seed" ]]; then
  demand="$(jq -er --arg run "$run" '.passes[-1] | select(.numeric_run_ref==$run) | .demand_id' "$demand_seed")"
  source_sha="$(jq -er '.packet.comparison.source_sha256' "$out/numeric-reopen.json")"
  step demand-fibre.json "$binary" numeric-pnf-native demand-fibre "$run" "$doc" "$source_sha" "$demand"
fi
jq -e --arg digest "$digest" '.packet_sha256 == $digest' "$out/numeric-reopen.json" >/dev/null
step relational-corpus.json "$binary" relational-family acceptance-corpus "$ITIR_REL_CORPUS_REF" "$ITIR_REL_ACCESS_CONSTRAINT_REF"
jq -e '.cases | length > 0 and all(.[]; .exact_native_family_reopen == true)' "$out/relational-corpus.json" >/dev/null
export ITIR_ORIGINAL_RELATION_PACKET_JSON="$out/numeric-reopen.json"
export ITIR_ORIGINAL_RELATION_QUERY_JSON="$out/numeric-query.json"
# Existing owner builds/validates original source and JMD; per-tool timeouts inside it.
cd "$root"
bash scripts/run_gwb_maxcut_acceptance.sh --full 2>&1 | tee "$out/gwb.log"
for axis in type_ref referential_type role value; do
  step "factor-$axis-lean.log" lake env lean --run tools/RelationalObservedMeetRunner.lean factors "$out/numeric-reopen.json" "$out/factor-$axis.json"
done
if [[ -s "$out/demand-fibre.json" ]]; then
  step demand-fibre-lean.log lake env lean --run tools/RelationalObservedMeetRunner.lean demand "$out/demand-fibre.json"
fi
n="$(jq -er '.cases | length' "$out/relational-corpus.json")"
for ((i=0;i<n;i++)); do
  jq ".cases[$i].family" "$out/relational-corpus.json" > "$out/family-$i.json"
  step "family-$i-lean.log" lake env lean --run tools/RelationalObservedMeetRunner.lean "$out/family-$i.json" "$out/family-$i-proof.json"
done
# Unit controls plus actual native facade readback (same original DB config).
cd "$ITIR_ROOT/itir-mcp"
export PYTHONPATH="$ITIR_ROOT/itir-mcp/src${PYTHONPATH:+:$PYTHONPATH}"
step itir-tests.log "${ITIR_PYTHON:-python3}" -m pytest -q tests/test_native_relational_tools.py
cd "$SLR_ROOT"
family_ref="$(jq -er '.cases[0].family.family_ref' "$out/relational-corpus.json")"
step itir-native.json "${ITIR_PYTHON:-python3}" -c 'import json,sys; from itir_mcp.native_relational_tools import inspect_relational_family; print(json.dumps(inspect_relational_family({"action":"family","family_ref":sys.argv[1]})))' "$family_ref"
jq -e --arg ref "$family_ref" '.native_receipt.family_ref == $ref and .mutates == false and .creates_semantic_authority == false' "$out/itir-native.json" >/dev/null
cd "$root"
# Preserve actual strict/legacy discrepancies instead of passing them as equivalent.
jq '[.cases[] | {case_ref,purpose,legacy_expected_finding,strict_actual_finding,legacy_required_residuals_present,legacy_forbidden_residual_present}]' "$out/relational-corpus.json" > "$out/legacy-strict-delta.json"
jq -n --arg slr "$(git -C "$SLR_ROOT" rev-parse HEAD)" --arg lean "$(git -C "$root" rev-parse HEAD)" --arg itir "$(git -C "$ITIR_ROOT" rev-parse HEAD)" --argjson families "$n" '{slr_commit:$slr,lean_commit:$lean,itir_commit:$itir,families_checked:$families,source_observation_scope_completed:true,semantic_live_coverage_paid:false,governed_l3_paid:false,status:"HOLD",outstanding:["independent semantic interpretation and exhaustive live-fibre coverage","general article-to-JMD alignment","governed L3 admission and retraction acceptance"]}' > "$out/campaign.json"
echo "Bounded native campaign receipts: $out"
echo "HOLD: source-observation acceptance is not full semantic acceptance."
exit 3
