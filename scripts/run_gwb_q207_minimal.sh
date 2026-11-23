#!/usr/bin/env bash
# JMD EntityData source-field check: separate, bounded core compile and execution.
set -euo pipefail
if [[ $# -ne 1 || ! -f "$1" ]]; then
  echo "usage: bash scripts/run_gwb_q207_minimal.sh /path/to/Q207-EntityData.json" >&2
  exit 2
fi
input="$(realpath "$1")"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
src=DASHI/output-final_aristotle/RequestProject/Cli/EntityIdentityCore.lean
out=.lake/build/lib/lean/RequestProject/Cli/EntityIdentityCore.olean
mkdir -p "$(dirname "$out")" .dashi/gwb-q207
build_log=.dashi/gwb-q207/minimal-core-build.log
run_log=.dashi/gwb-q207/minimal-kernel.log
# Compiler only consumes JMD's exact two JSON field helpers. No JMD Engine import.
if [[ ! -f "$out" || "$src" -nt "$out" ]]; then
  set +e
  timeout 90s lake env lean -o "$out" "$src" > "$build_log" 2>&1
  status=$?
  set -e
  cat "$build_log"
  if [[ "$status" -ne 0 ]]; then
    echo "GWB_Q207_MINIMAL_CORE_UNVERIFIED exit=$status log=$build_log" >&2
    exit 1
  fi
  echo "GWB_Q207_MINIMAL_JMD_CORE_KERNEL_OK"
else
  echo "GWB_Q207_MINIMAL_JMD_CORE_CACHED"
fi
set +e
timeout 90s lake env lean --run tools/GwbQ207MinimalRunner.lean "$input" > "$run_log" 2>&1
status=$?
set -e
cat "$run_log"
if [[ "$status" -ne 0 ]] || ! grep -Fxq GWB_Q207_MINIMAL_KERNEL_OK "$run_log"; then
  echo "GWB_Q207_MINIMAL_UNVERIFIED exit=$status log=$run_log" >&2
  exit 1
fi
echo "GWB_Q207_MINIMAL_ACCEPTED status=$status log=$run_log"
