#!/usr/bin/env bash
set -euo pipefail

repo_url="https://github.com/openai/math.git"
expected_sha="1581d4cbdd69a0faf34b2089614fe2a814316a6a"
dest="${1:-vendor/openai-math}"

if [[ -e "$dest/.git" ]]; then
  git -C "$dest" remote set-url origin "$repo_url"
  git -C "$dest" fetch --tags --prune origin
elif [[ -e "$dest" ]]; then
  echo "refusing to overwrite non-git path: $dest" >&2
  exit 2
else
  git clone --no-checkout "$repo_url" "$dest"
fi

git -C "$dest" fetch origin "$expected_sha"
git -C "$dest" checkout --detach "$expected_sha"

actual_sha="$(git -C "$dest" rev-parse HEAD)"
if [[ "$actual_sha" != "$expected_sha" ]]; then
  echo "OpenAI math vendor pin mismatch: expected $expected_sha, got $actual_sha" >&2
  exit 3
fi

printf 'OpenAI math vendor ready at %s\n' "$actual_sha"
printf 'upstream Lean toolchain: %s\n' "$(cat "$dest/lean/lean-toolchain")"
