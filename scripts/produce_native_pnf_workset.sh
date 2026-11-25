#!/usr/bin/env bash
# Build only the existing formal owner; then run the executable workset
# specialization. No whole Lean repository build or semantic admission.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
out="$root/.lake/build/lib/lean/RequestProject/Slr/NumericPnfRustPortContract.olean"
src="$root/DASHI/output-final_aristotle/RequestProject/Slr/NumericPnfRustPortContract.lean"
mkdir -p "$(dirname "$out")"
if [[ "${1:-}" == "--build" ]]; then
  timeout --kill-after=5s 90s lake env lean -o "$out" "$src"
  # Reuse and check the existing GWB scoped-coverage owner, now welded
  # to the numeric contract. Do not infer governed admission from either.
  coref="$root/DASHI/output-final_aristotle/RequestProject/Slr/GwbCoreferenceFormalRepair.lean"
  coref_out="$root/.lake/build/lib/lean/RequestProject/Slr/GwbCoreferenceFormalRepair.olean"
  timeout --kill-after=5s 90s lake env lean -o "$coref_out" "$coref"
  exit
fi
[[ -f "$out" && "$out" -nt "$src" ]] || { echo "Run $0 --build first" >&2; exit 2; }
# Ordinary workset output remains byte-compatible. For typed evidence the
# executable emits an input-specific theorem; independently check it with
# the pinned Lean kernel before returning the projection. Keep artifacts
# under the project (never /tmp), and fail closed on any checker error.
command -v jq >/dev/null
command -v sha256sum >/dev/null
artifacts="$root/.dashi/native-typed-evidence"
mkdir -p "$artifacts"
stage="$(mktemp -d "$artifacts/run-XXXXXXXX")"
cat > "$stage/input.json"
schema="$(jq -er '.schema' "$stage/input.json")"
if [[ "$schema" != "slr-native-typed-evidence-input-v1" ]]; then
  lake env lean --run tools/NativePnfWorkset.lean < "$stage/input.json"
  rm -f "$stage/input.json"
  rmdir "$stage"
  exit
fi
timeout --kill-after=5s 90s lake env lean --run tools/NativePnfWorkset.lean \
  < "$stage/input.json" > "$stage/producer.json"
jq -er '.proof_source' "$stage/producer.json" > "$stage/Certificate.lean"
# No native_decide, sorry or untrusted elaborator plugins in the generated
# certificate; its actual equality is checked using the existing contract.
timeout --kill-after=5s 90s lake env lean "$stage/Certificate.lean" > "$stage/kernel.log" 2>&1
if grep -Eq 'sorryAx|declaration uses .sorry.' "$stage/kernel.log"; then
  cat "$stage/kernel.log" >&2
  exit 1
fi
grep -F 'slrTypedProjectionCertificate' "$stage/kernel.log" >/dev/null
proof_sha="$(sha256sum "$stage/Certificate.lean" | cut -d ' ' -f1)"
input_sha="$(sha256sum "$stage/input.json" | cut -d ' ' -f1)"
log_sha="$(sha256sum "$stage/kernel.log" | cut -d ' ' -f1)"
contract_sha="$(sha256sum "$src" | cut -d ' ' -f1)"
producer_sha="$(sha256sum "$root/tools/NativePnfWorkset.lean" | cut -d ' ' -f1)"
checker="$(lake env lean --version)"
# Python is transport only; keep exact 64-bit numeric IDs rather than
# passing the JSON number carrier through jq's floating-point representation.
python3 - "$stage" "$proof_sha" "$input_sha" "$log_sha" "$contract_sha" "$producer_sha" "$checker" <<'PY'
import json
import sys
from pathlib import Path

stage, proof, raw, log, contract, producer, checker = sys.argv[1:]
with (Path(stage) / "producer.json").open(encoding="utf-8") as stream:
    result = json.load(stream)
result.pop("proof_source")
result["kernel_receipt"] = {
    "schema": "slr-lean-typed-projection-kernel-v1",
    "input_digest": result["input_digest"],
    "input_artifact_sha256": raw,
    "proof_sha256": proof,
    "kernel_log_sha256": log,
    "contract_sha256": contract,
    "producer_sha256": producer,
    "checker": checker,
    "artifact_dir": stage,
    "theorem": "slrTypedProjectionCertificate",
    "kernel_checked": True,
    "typed_coverage_paid": False,
    "identity_paid": False,
}
print(json.dumps(result, ensure_ascii=False, separators=(",", ":")))
PY
