#!/usr/bin/env bash
set -euo pipefail

PIN="603053dc267cf3efe422f438eb78098c0ececd6f"
REPO="https://github.com/lean-dojo/LeanMillenniumPrizeProblems.git"
DEST="${1:-vendor/LeanMillenniumPrizeProblems}"

if [[ -e "$DEST" && ! -d "$DEST/.git" ]]; then
  echo "refusing to overwrite non-git path: $DEST" >&2
  exit 2
fi

if [[ ! -d "$DEST/.git" ]]; then
  mkdir -p "$(dirname "$DEST")"
  git clone --filter=blob:none --no-checkout "$REPO" "$DEST"
fi

git -C "$DEST" fetch --depth=1 origin "$PIN"
git -C "$DEST" checkout --detach "$PIN"

ACTUAL="$(git -C "$DEST" rev-parse HEAD)"
if [[ "$ACTUAL" != "$PIN" ]]; then
  echo "wrong LeanMillenniumPrizeProblems commit: expected $PIN got $ACTUAL" >&2
  exit 3
fi

printf 'LeanMillenniumPrizeProblems vendor OK: %s\n' "$ACTUAL"
