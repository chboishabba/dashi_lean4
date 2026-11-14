#!/usr/bin/env bash
# Independent OAI378 source checkout; never rewrite the old pinned gitlink.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
expected="7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
dest="${1:-$repo_root/vendor/openai378-src}"
if [[ "$dest" == "$repo_root/vendor/openai-math-src" ||
      "$dest" == "vendor/openai-math-src" ]]; then
  echo "refusing to mutate the original 1581d4c gitlink" >&2
  exit 2
fi
if [[ ! -e "$dest" ]]; then
  git clone --no-checkout https://github.com/openai/math.git "$dest"
  git -C "$dest" fetch origin "$expected"
  git -C "$dest" checkout --detach "$expected"
fi
if ! git -C "$dest" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "refusing non-Git checkout: $dest" >&2
  exit 3
fi
actual="$(git -C "$dest" rev-parse HEAD)"
if [[ "$actual" != "$expected" ]]; then
  echo "wrong OAI378 checkout SHA: expected $expected, got $actual" >&2
  exit 4
fi
toolchain="$(cat "$dest/lean/lean-toolchain")"
if [[ "$toolchain" != "leanprover/lean4:v4.34.1" ]]; then
  echo "unexpected OAI378 Lean toolchain: $toolchain" >&2
  exit 5
fi
printf 'OAI378 separate source SHA: %s\nLean toolchain: %s\n' "$actual" "$toolchain"
