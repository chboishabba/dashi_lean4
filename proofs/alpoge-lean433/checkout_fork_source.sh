#!/usr/bin/env bash
# P0: materialize the ORIGINAL external theorem source from the user's fork.
# No source is copied into dashi_lean4; no CI; no cross-version OLean reuse.
set -euo pipefail
REPO=https://github.com/chboishabba/riemann-hypothesis-lean.git
PIN=7cbf7a0c32fca1badf05931879a37c3f8a2b03b4
MAIN_BLOB=dbd5db70bc11b35f18fa5751216ab335321e7bfc
STATEMENTS_BLOB=1cd1bce93344065936b2b392b23306254e0785ef
MATHLIB=0df444a360eaa60ab8c11dca51a86af692955474
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
[[ "$(git -C "$TARGET" rev-parse HEAD:src/Main.lean)" == "$MAIN_BLOB" ]] || exit 4
[[ "$(git -C "$TARGET" rev-parse HEAD:src/Statements.lean)" == "$STATEMENTS_BLOB" ]] || exit 4
[[ "$(cat "$TARGET/lean-toolchain")" == "leanprover/lean4:v4.33.1" ]] || exit 4
python3 - "$TARGET/lake-manifest.json" "$MATHLIB" <<'PY'
import json,sys
manifest=json.load(open(sys.argv[1],encoding="utf-8"))
assert any(p["name"]=="mathlib" and p["rev"]==sys.argv[2] for p in manifest["packages"])
PY
printf 'PINNED ORIGINAL SOURCE: %s\nSHA: %s\nMain and Statements blob pins: MATCH\n' "$TARGET" "$PIN"
printf 'NEXT (local-only, opt-in): cd %q && lake exe cache get && lake build Main\n' "$TARGET"
printf 'After Main builds in the source environment, check the authored RHAdmission.lean against EXACT this toolchain.\n'
printf 'No Lean/Agda checker has been invoked by this script.\n'
