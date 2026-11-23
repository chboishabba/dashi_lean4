#!/usr/bin/env bash
# Targeted JMD theorem dependencies required by the GWB proof handoff.
# Build these existing, source-attributed modules ONLY; never invoke lake build wikidata.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
src="$root/DASHI/output-final_aristotle/RequestProject"
out="$root/.lake/build/lib/lean/RequestProject"
mkdir -p "$out/Cli"

compile_jmd() {
  local module="$1"
  local input="$src/${module}.lean"
  local artifact="$out/${module}.olean"
  [[ -f "$input" ]] || { echo "GWB_JMD_MISSING_SOURCE $input" >&2; exit 2; }
  mkdir -p "$(dirname "$artifact")"
  echo "GWB_JMD_TARGETED_BUILD_${module}"
  lake env lean -o "$artifact" "$input"
}

# Explicit transitive import closure (confirmed from original JMD sources):
# Core, Reachability ← Mathlib; Engine ← Core, Reachability;
# Merge ← Engine; Properties ← Core; PropertyEngine ← Engine, Properties;
# Cli.Import and Cli.Format ← Engine; Cli.Fetch ← Import, Format;
# Cli.Derive ← Engine, Merge.
compile_jmd Core
compile_jmd Reachability
compile_jmd Engine
compile_jmd Merge
compile_jmd Properties
compile_jmd PropertyEngine
compile_jmd Cli/EntityIdentityCore
compile_jmd Cli/Import
compile_jmd Cli/Format
compile_jmd Cli/Fetch
compile_jmd Cli/Derive

echo "GWB_JMD_TARGETED_IMPORT_CLOSURE_OK"
