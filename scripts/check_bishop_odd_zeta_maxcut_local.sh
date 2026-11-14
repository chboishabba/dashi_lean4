#!/usr/bin/env bash
set -euo pipefail

# Native local proof checking, no Docker and no CI authority.
# This does NOT import the external v4.35 Z7 proof into this root project.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v lake >/dev/null || {
  echo "lake unavailable: run in the repository's pinned Nix/Lean environment" >&2
  exit 2
}

# Do not silently pair an incompatible Lean compiler with Mathlib.
toolchain="$(tr -d '\r\n' < lean-toolchain)"
mathlib_rev="$(grep -m1 'rev = ' lakefile.toml || true)"
if [[ "$toolchain" == *"v4.35.0-rc3"* && "$mathlib_rev" == *'v4.28.0'* ]]; then
  echo "PIN MISMATCH: toolchain $toolchain, $mathlib_rev" >&2
  echo "Version reconciliation is required before kernel admission." >&2
  exit 3
fi

modules=(
  Integration.PositiveOddZetaImaginaryZeroExact
  Integration.BishopOddZetaHalfPlaneSpecialization
  Integration.BishopOddZetaNarrowWindowTransport
  Integration.BishopOddZetaZ7FinsetBridgeExact
  Integration.RiemannXiMathlibReflectionExact
  Synthesis.PositiveOddZetaImaginaryZeroExact
)

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
for module in "${modules[@]}"; do
  lake build "$module"
done

for source in   Integration/PositiveOddZetaImaginaryZeroExact.lean   Integration/BishopOddZetaHalfPlaneSpecialization.lean   Integration/BishopOddZetaNarrowWindowTransport.lean   Integration/BishopOddZetaZ7FinsetBridgeExact.lean   Integration/RiemannXiMathlibReflectionExact.lean   Synthesis/PositiveOddZetaImaginaryZeroExact.lean; do
  lake env lean "$source"
done

echo "Local root positive-odd source theorem checks completed."
