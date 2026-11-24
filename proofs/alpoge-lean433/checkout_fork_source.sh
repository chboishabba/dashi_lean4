#!/usr/bin/env bash
# P0: materialize the ORIGINAL external theorem source from the user's fork.
# No source is copied into dashi_lean4; no CI; no cross-version OLean reuse.
set -euo pipefail
REPO=https://github.com/chboishabba/riemann-hypothesis-lean.git
PIN=7cbf7a0c32fca1badf05931879a37c3f8a2b03b4
MAIN_BLOB=dbd5db70bc11b35f18fa5751216ab335321e7bfc
STATEMENTS_BLOB=1cd1bce93344065936b2b392b23306254e0785ef
MATHLIB=0df444a360eaa60ab8c11dca51a86af692955474
# Entire proof/dependency source matches the community original 40e56bab.
SOURCE_TREE=b41b516b1f7baee4d83ced235ecc71fd43c97695
MANIFEST_BLOB=b4d1ec31575a26b2159ec3a262b482bc051f3f6f
LAKEFILE_BLOB=07e85dc8afcf28b4885a8f092154c8b74c8cf800
TOOLCHAIN_BLOB=a8afa7d1b02d96f0671eba854a8dc4b416beb473
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TARGET="${1:-$ROOT/.local/alpoge-rh-v4331}"
if [[ ! -d "$TARGET/.git" ]]; then
  if [[ -e "$TARGET" ]]; then echo "Refusing non-git target: $TARGET" >&2; exit 2; fi
  mkdir -p "$(dirname "$TARGET")"
  git clone "$REPO" "$TARGET"
fi
origin="$(git -C "$TARGET" remote get-url origin)"
if [[ "$origin" != "$REPO" && "$origin" != https://github.com/chboishabba/riemann-hypothesis-lean ]]; then
  echo "Unexpected source origin: $origin" >&2; exit 2
fi
git -C "$TARGET" cat-file -e "$PIN^{commit}"
git -C "$TARGET" checkout --detach "$PIN"
[[ "$(git -C "$TARGET" rev-parse HEAD)" == "$PIN" ]] || exit 3
[[ -z "$(git -C "$TARGET" status --porcelain)" ]] || {
  echo "Source checkout is dirty; refusing to claim immutable source" >&2
  exit 3
}
[[ "$(git -C "$TARGET" rev-parse HEAD:src)" == "$SOURCE_TREE" ]] || exit 4
[[ "$(git -C "$TARGET" rev-parse HEAD:lake-manifest.json)" == "$MANIFEST_BLOB" ]] || exit 4
[[ "$(git -C "$TARGET" rev-parse HEAD:lakefile.toml)" == "$LAKEFILE_BLOB" ]] || exit 4
[[ "$(git -C "$TARGET" rev-parse HEAD:lean-toolchain)" == "$TOOLCHAIN_BLOB" ]] || exit 4
[[ "$(git -C "$TARGET" rev-parse HEAD:src/Main.lean)" == "$MAIN_BLOB" ]] || exit 4
[[ "$(git -C "$TARGET" rev-parse HEAD:src/Statements.lean)" == "$STATEMENTS_BLOB" ]] || exit 4
[[ "$(cat "$TARGET/lean-toolchain")" == "leanprover/lean4:v4.33.1" ]] || exit 4
python3 - "$TARGET/lake-manifest.json" "$MATHLIB" <<'PY'
import json,sys
manifest=json.load(open(sys.argv[1],encoding="utf-8"))
assert any(p["name"]=="mathlib" and p["rev"]==sys.argv[2] for p in manifest["packages"])
PY
printf 'PINNED ORIGINAL SOURCE: %s\nSHA: %s\nComplete source tree, dependency and statement pins: MATCH\n' "$TARGET" "$PIN"
printf 'NEXT (local-only, opt-in): cd %q && lake exe cache get && lake build Main\n' "$TARGET"
printf 'After Main builds in the source environment, check the authored RHAdmission.lean against EXACT this toolchain.\n'
printf 'No Lean/Agda checker has been invoked by this script.\n'
