#!/usr/bin/env bash
# Run explicitly with bash; no CI and no remote certificate invention.
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "usage: bash $0 /path/to/pinned/alpoge-buckmaster-checkout" >&2
  exit 2
fi
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd -- "$1" && pwd)"
pin=ad53419de079eb8f95f60313473374624a348546
test "$(git -C "$root" rev-parse HEAD)" = "$pin"
git -C "$root" diff --quiet HEAD --
test -z "$(git -C "$root" ls-files --others --exclude-standard -- lean)"
test "$(git -C "$root" hash-object "$root/lean/Solution.lean")" = a70613926acf3ae2e0ecda7ec4fbf59f2a251d0d
test "$(git -C "$root" hash-object "$root/lean/Challenge.lean")" = 0ad1865e8651e1a136d090b9bafbac7f1f666979
test "$(git -C "$root" hash-object "$root/lean/lakefile.toml")" = 7c73cfa0e683050239b5db2538f21128237989cc
test "$(git -C "$root" hash-object "$root/lean/lean-toolchain")" = a8afa7d1b02d96f0671eba854a8dc4b416beb473
cd "$root/lean"
command -v lake >/dev/null
command -v python3 >/dev/null
lake env lean --version | grep -E 'version 4\.33\.1([ ,]|$)'
# Build the solution dependency tree, not the sorry-bearing challenge library.
lake build Solution
# Verify the actual resolved mathlib checkout, not merely the lakefile text.
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = 0df444a360eaa60ab8c11dca51a86af692955474
git -C .lake/packages/mathlib diff --quiet HEAD --
# Rebuild the canonical Clay specification in the same kernel, rather than
# trusting a root-toolchain olean or introducing a second statement.
spec="$here/../../ExternalClayNS/ClaySpec.lean"
test "$(git -C "$here/../.." hash-object "$spec")" = 4ed209d4e932f7344fa8a68fa4c97883ea018eae
mkdir -p "$here/.build/$pin"
out="$(mktemp -d "$here/.build/$pin/run.XXXXXXXX")"
log="$out/admission.log"
lake env bash -euo pipefail -c '
  here="$1"; out="$2"; spec="$3"
  export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
  lean --root="$(dirname "$spec")" -o "$out/ClaySpec.olean" "$spec"
  lean --root="$here" -o "$out/ClayDifferentialTransport.olean" "$here/ClayDifferentialTransport.lean"
  lean --root="$here" -o "$out/UnforcedAdmission.olean" "$here/UnforcedAdmission.lean"
  lean --root="$here" -o "$out/ClayUnforcedTransport.olean" "$here/ClayUnforcedTransport.lean"
' _ "$here" "$out" "$spec" 2>&1 | tee "$log"
python3 "$here/audit_admission_axioms.py" "$log"
printf '%s\n' 'PASS: original conditional terminal and literal Clay C/D transport only; original fifteen-condition witness still required.'
