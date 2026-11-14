#!/usr/bin/env bash
# Local exact-source, exact-toolchain check. No CI, no vendor pin mutation.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="${1:-$repo_root/vendor/openai378-src}"
expected="7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
if [[ "$(git -C "$src" rev-parse HEAD)" != "$expected" ]]; then
  echo "OAI378 HEAD must be $expected" >&2
  exit 2
fi
if [[ "$(cat "$src/lean/lean-toolchain")" != "leanprover/lean4:v4.34.1" ]]; then
  echo "OAI378 toolchain does not match 4.34.1" >&2
  exit 3
fi
out="$repo_root/.build/openai378-staged"
mkdir -p "$out/Integration/OpenAIMath"
# Build only the source dependencies needed by the staged adapters, never
# import newer OAI into DASHI's pinned normal 4.28.0 build.
(
  cd "$src/lean"
  lake build OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final
  lake env bash -c '
    set -euo pipefail
    export LEAN_PATH="$1:${LEAN_PATH:-}"
    lean -o "$1/Integration/OpenAIMath/ListFinsetCNFTransport.olean" \
      "$2/Integration/OpenAIMath/ListFinsetCNFTransport.lean"
    lean -o "$1/Integration/OpenAIMath/Upstream378EncodingLengthExact.olean" \
      "$2/Integration/OpenAIMath/Upstream378EncodingLengthExact.lean"
    lean -o "$1/Integration/OpenAIMath/Upstream378FiniteCNFBridge.olean" \
      "$2/Integration/OpenAIMath/Upstream378FiniteCNFBridge.lean"
  ' _ "$out" "$repo_root"
)
# Audit the actual source declarations using the SAME pinned 4.34.1
# environment. A successful elaboration alone is not a trust receipt.
# Do not mark source as "kernel accepted" unless this entire script succeeds.
audit="$out/Integration/OpenAIMath/SourceAxiomAudit.lean"
cat > "$audit" <<'LEAN'
import Integration.OpenAIMath.Upstream378FiniteCNFBridge
#print axioms Integration.OpenAIMath.Upstream378EncodingLengthExact.exactFormulaBitLength
#print axioms Integration.OpenAIMath.Upstream378FiniteCNFBridge.exactUpstreamCount
#print axioms Integration.OpenAIMath.Upstream378FiniteCNFBridge.sourceListEncodedBitsIffSameNormalizedCNF
#print axioms Integration.OpenAIMath.Upstream378FiniteCNFBridge.sourceByteQuadraticBitLengthBound
#print axioms Integration.OpenAIMath.Upstream378FiniteCNFBridge.originalCountAtUpstreamCNF
#print axioms Integration.OpenAIMath.Upstream378FiniteCNFBridge.sourceListExactCountMachine
#print axioms Integration.OpenAIMath.Upstream378FiniteCNFBridge.originalCircuitExactCountMachineOfIngress
LEAN
(
  cd "$src/lean"
  lake env bash -c '
    set -euo pipefail
    export LEAN_PATH="$1:${LEAN_PATH:-}"
    lean "$2" > "$3" 2>&1
  ' _ "$out" "$audit" "$out/axiom_audit.txt"
)
if grep -Eq 'sorryAx|sorryAx\.' "$out/axiom_audit.txt"; then
  echo "UNACCEPTED: sorryAx appears in source theorem axiom closure" >&2
  exit 4
fi
echo "Staged 378 elaboration and #print axioms completed at exact upstream HEAD."
echo "Review theorem axiom closure: $out/axiom_audit.txt"
echo "The Agda↔Lean original-circuit proof and primitive frontend TM simulation remain OPEN."
