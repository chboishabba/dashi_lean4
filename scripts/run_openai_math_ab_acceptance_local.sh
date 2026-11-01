#!/usr/bin/env bash
# A+B exact-source local acceptance receipt. Intentionally not CI.
# Run from dashi_lean4, with dashi_agda alongside it. Failure is reported,
# never silently treated as theorem acceptance.
set -uo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
agda_root="${AGDA_ROOT:-$repo_root/../dashi_agda}"
upstream="${UPSTREAM_378_ROOT:-$repo_root/vendor/openai378-src}"
out="${1:-$repo_root/.build/openai-math-ab-receipts}"
mkdir -p "$out"
result="$out/status.tsv"
printf 'stage\texit_code\tcommand\n' > "$result"
failures=0
run() {
  local key="$1"; shift
  printf 'BEGIN %s\n' "$key"
  ("$@") > "$out/$key.log" 2>&1
  local rc=$?
  printf '%s\t%s\t%s\n' "$key" "$rc" "$*" >> "$result"
  printf 'END %s: %s (log %s)\n' "$key" "$rc" "$out/$key.log"
  if [[ "$rc" -ne 0 ]]; then failures=$((failures+1)); fi
}
if [[ ! -d "$agda_root/DASHI" ]]; then
  echo "DASHI Agda checkout not found: $agda_root" >&2
  exit 3
fi
git -C "$repo_root" rev-parse HEAD > "$out/lean_commit.txt"
git -C "$agda_root" rev-parse HEAD > "$out/agda_commit.txt"
if [[ -e "$upstream/.git" || -d "$upstream/.git" ]]; then
  git -C "$upstream" rev-parse HEAD > "$out/upstream_commit.txt"
fi
run python_frontend python "$repo_root/scripts/check_openai378_frontend_exact.py"
run python_graph python "$repo_root/scripts/check_openai378_27grid_maxcut_bridge.py"
run agda_original bash -c 'cd "$1" && agda DASHI/Research/OpenAIMath/Everything.agda' _ "$agda_root"
run agda_opt bash -c 'cd "$1" && agda DASHI/Research/OpenAIMath/OpenAIMathSharedTseitinOptimizedCNFExact.agda' _ "$agda_root"
run lean_428_generic bash -c 'cd "$1" && lake env lean Integration/OpenAIMath/ListFinsetCNFTransport.lean' _ "$repo_root"
run lean_434_adapter bash "$repo_root/scripts/check_openai378_staged_lean.sh" "$upstream"
run corpus_matrix python "$repo_root/scripts/build_openai_math_same_object_matrix.py" \
  --agda-root "$agda_root" --lean-root "$repo_root" --upstream-root "$upstream" \
  --out-dir "$out/corpus"
run corpus_catalogue python "$repo_root/scripts/audit_openai_main_result_catalogue.py" \
  --upstream "$upstream/lean/formalization.yaml" \
  --catalogue "$repo_root/Integration/OpenAIMath/FullUpstreamMainResultsCatalogue.lean" \
  --json-out "$out/catalogue_audit.json"
printf '\nSUMMARY failures=%s\n' "$failures"
printf 'Receipt manifest: %s\n' "$result"
if [[ "$failures" -ne 0 ]]; then
  echo "UNACCEPTED: one or more source/runner obligations failed" >&2
  exit 1
fi
echo "All scripted commands returned success. Separate transitive trust,"
echo "axiom and exact Agda↔Lean same-object M00-M05 proof checks STILL required."
