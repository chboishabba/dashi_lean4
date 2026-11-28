#!/usr/bin/env bash
# Candidate evidence only. Called by the eventual integrated endpoint runner
# after the existing formal build; no workstation run requested in isolation.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
producer="$root/scripts/produce_native_pnf_workset.sh"
python3 - "$producer" <<'PY'
import copy
import json
import subprocess
import sys

producer = sys.argv[1]

def row(kind, key, *, event=0, refuted=False, evidence_key=0):
    return dict(target_kind=kind, target_id=key, refuted=refuted,
                event_kind=event, event_id=7 if event else 0,
                evidence_id=8 if event else 0,
                evidence_demand=11 if event else 0,
                evidence_target_kind=kind if event else 0,
                evidence_target_id=evidence_key if event else 0,
                evidence_ref="original-m086-evidence" if event else "")

large_id = 9007199254740993
base = dict(schema="slr-native-typed-evidence-input-v1",
            source_sha256="a"*64, source_revision_ref="fixture-revision",
            numeric_run_ref="fixture-run", snapshot_ref="fixture-snapshot",
            input_digest="b"*64, demand_id=11, source_object_id=12,
            outside_model_possible=True,
            candidates=[row(1, 9, event=1, refuted=True, evidence_key=9),
                        row(1, large_id), row(2, 9, event=2, evidence_key=9)],
            horizons=[dict(target_kind=1, target_id=large_id,
                           horizon=3, signed_residual=-9, execution_residual=True)])
def invoke(value):
    return subprocess.run(["bash", producer], input=json.dumps(value).encode(),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          timeout=90, check=False)
positive = invoke(base)
assert positive.returncode == 0, positive.stderr.decode(errors="replace")
got = json.loads(positive.stdout)
assert got["live"] == [{"target_kind":1,"target_id":large_id},
                       {"target_kind":2,"target_id":9}]
assert got["refuted"] == [{"target_kind":1,"target_id":9}]
assert got["outside_model_possible"] and not got["typed_coverage_paid"] and not got["identity_paid"]
assert got["kernel_receipt"]["kernel_checked"]
for mutant in ("foreign_target", "foreign_demand", "foreign_kind",
               "duplicate", "fake_refutation", "missing_evidence"):
    bad = copy.deepcopy(base)
    if mutant == "foreign_target": bad["candidates"][0]["evidence_target_id"] = 10
    if mutant == "foreign_demand": bad["candidates"][0]["evidence_demand"] = 99
    if mutant == "foreign_kind": bad["candidates"][0]["evidence_target_kind"] = 2
    if mutant == "duplicate": bad["candidates"].append(bad["candidates"][1])
    if mutant == "fake_refutation": bad["candidates"][1]["refuted"] = True
    if mutant == "missing_evidence": bad["candidates"][0]["evidence_id"] = 0
    failed = invoke(bad)
    assert failed.returncode != 0, mutant
print("NATIVE_TYPED_EVIDENCE_GOLDEN_OK")
PY
