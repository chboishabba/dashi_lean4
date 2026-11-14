#!/usr/bin/env bash
# Isolated, local-only acceptance attempt for the actual Stoll Mordell-Weil donor.
# Never modifies this repository's tracked pins or manifest.
# No Docker; compatible with entering a Nix environment before invocation.
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"
if ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: local lake executable unavailable; kernel acceptance not performed' >&2
  exit 12
fi
if ! command -v git >/dev/null 2>&1; then
  echo 'BLOCKED: git worktree is required for isolated no-mutation verification' >&2
  exit 12
fi
if [[ ! -f Integration/MillenniumBSDStollMordellWeilAdapter.lean ]]; then
  echo 'BLOCKED: adapter source missing from current checked-out PR branch' >&2
  exit 13
fi
if [[ "$(cat lean-toolchain)" != "leanprover/lean4:v4.35.0-rc3" ]]; then
  echo 'BLOCKED: root lean-toolchain changed; review version assumptions first' >&2
  exit 13
fi

scratch="$(mktemp -d)"
cleanup() {
  if [[ -d "$scratch/worktree" ]]; then
    git -C "$repo_root" worktree remove --force "$scratch/worktree" || true
  fi
  rm -rf -- "$scratch"
}
trap cleanup EXIT

git worktree add --detach "$scratch/worktree" HEAD
cd "$scratch/worktree"

# Only scratch worktree is modified.
printf 'leanprover/lean4:v4.35.0\n' > lean-toolchain
sed -i 's/^rev = "v4.28.0"$/rev = "v4.35.0"/' lakefile.toml
cat >> lakefile.toml <<'EOF'

# Optional primary source donor, isolated from authoritative root pins.
[[require]]
name = "EllipticCurves"
git = "https://github.com/MichaelStollBayreuth/EllipticCurves.git"
rev = "bad38e242a187dea006fc302a0ef0fd53eedd4ba"
EOF

export LEAN_TOOLCHAIN=leanprover/lean4:v4.35.0
echo 'LOCAL ONLY: rebuilding original DASHI Lean sources under Stoll/Mathlib 4.35.0'
echo 'No CI and no mutation of the authoritative git branch.'
lake update
lake build Integration.MillenniumBSDStollMordellWeilAdapter

cat > "$scratch/MWProofAudit.lean" <<'EOF'
import Integration.MillenniumBSDStollMordellWeilAdapter
#print axioms Synthesis.Millennium.BSD.cmRationalProjectivePoint_isAddFG_fromStoll
#print axioms Synthesis.Millennium.BSD.cmOriginalMordellWeil_rank_zero_fromStoll
EOF
lake env lean "$scratch/MWProofAudit.lean"

echo 'BUILD ATTEMPT COMPLETED: inspect axiom output and record exact toolchain/manifest SHAs.'
