#!/usr/bin/env bash
set -euo pipefail

# No Docker or CI; run in this sidecar's v4.35.0 Lake environment.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

command -v lake >/dev/null || {
  echo "lake unavailable; use the pinned Lean 4.35.0 toolchain locally" >&2
  exit 2
}
grep -Fxq 'leanprover/lean4:v4.35.0' lean-toolchain
grep -Fq 'rev = "v1.0"' lakefile.toml

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
lake exe cache get
lake build BishopZ7Admission

receipt="${TMPDIR:-/tmp}/bishop-z7-admission-axioms.$$.txt"
trap 'rm -f "$receipt"' EXIT
lake env lean BishopZ7Admission.lean 2>&1 | tee "$receipt"

for theorem in   "ZetaIrr.Z7.oneOfZeta7To21"   "BishopZ7Admission.z7WitnessFin8"   "BishopZ7Admission.z7WitnessComplexNotRational"   "BishopZ7Admission.z7WitnessForSource"; do
  grep -Fq "$theorem" "$receipt" || {
    echo "missing theorem axiom receipt: $theorem" >&2
    exit 1
  }
done

if grep -Eq 'sorryAx|Lean\.ofReduceBool|unsafe axiom|unknown constant' "$receipt"; then
  echo "unexpected axiom or elaboration escape in Z7 admission" >&2
  exit 1
fi

echo "Local v4.35 external-Z7 source admission checks complete."
