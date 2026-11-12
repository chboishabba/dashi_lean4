#!/usr/bin/env bash
set -euo pipefail

# Source-verified, exact-head Lean 4.35 sidecar. Never use Docker or CI.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

command -v lake >/dev/null || {
  echo "lake unavailable; activate the pinned Lean 4.35 toolchain" >&2
  exit 2
}
command -v python3 >/dev/null || {
  echo "python3 unavailable for strict axiom-set parsing" >&2
  exit 2
}
grep -Fxq 'leanprover/lean4:v4.35.0' lean-toolchain
grep -Fq 'rev = "v1.0"' lakefile.toml

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
lake exe cache get
lake build BishopZ7Admission BishopZ7DirichletSameObject

receipt="${TMPDIR:-/tmp}/bishop-z7-admission-axioms.$$.txt"
trap 'rm -f "$receipt"' EXIT
{
  lake env lean BishopZ7Admission.lean
  lake env lean BishopZ7DirichletSameObject.lean
} 2>&1 | tee "$receipt"

python3 - "$receipt" <<'PY'
import re
import sys

receipt = open(sys.argv[1], encoding="utf-8").read()
targets = [
  "ZetaIrr.Z7.oneOfZeta7To21",
  "BishopZ7Admission.z7WitnessFin8",
  "BishopZ7Admission.z7WitnessComplexNotRational",
  "BishopZ7Admission.z7WitnessForSource",
  "BishopZ7DirichletSameObject.selectedDirichlet_eq_riemannZeta",
  "BishopZ7DirichletSameObject.selectedOddDirichlet_eq_riemannZeta",
  "BishopZ7DirichletSameObject.z7DirichletOddWindowIsIrrational",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
for theorem in targets:
    matching = [line for line in receipt.splitlines()
                if theorem in line and
                   ("depends on axioms" in line or "does not depend on any axioms" in line)]
    if len(matching) != 1:
        raise SystemExit(f"FAIL missing/ambiguous exact theorem axiom receipt: {theorem}")
    line = matching[0]
    if "does not depend on any axioms" in line:
        actual = set()
    else:
        match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", line)
        if not match:
            raise SystemExit(f"FAIL unparsed axiom receipt: {line}")
        actual = {word.strip() for word in match.group(1).split(",") if word.strip()}
    if not actual <= allowed:
        raise SystemExit(f"FAIL unexpected axioms for {theorem}: {sorted(actual - allowed)}")
    print(f"PASS {theorem}: axioms {sorted(actual)}")
if re.search(r"\bsorryAx\b|Lean\.ofReduceBool|unsafe axiom|unknown constant", receipt):
    raise SystemExit("FAIL kernel/admission escape detected")
print("PASS external Z7 + genuine Dirichlet sidecar, axiom-set checked")
PY
