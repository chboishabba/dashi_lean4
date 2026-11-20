#!/usr/bin/env python3
"""Atomic publication of original SLR/Lean evidence, never experimental Rust.

No archive, source modification, or untracked deletion. Writes the NEW
artifacts/gwb-original-slr-proof/ directory only after original checker markers
and adversarial rejects are verified. Rejects stale or substituted evidence.
"""
import argparse, hashlib, json, os, shutil, tempfile
from pathlib import Path
PIN="a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
REV="enwiki-revid:1385850169"
NEGATIVE=("missing-predicate","missing-direct-actor","false-year-index",
          "promoted-world-truth","forged-paragraph-boundary")
FILES=("lean-source-instances.json","lean-source-instances.log","canonical-source-regression.log","original-source-inventory.json","original-source-inventory.log",
       "article-source-proof.log","semantic-scope-proof.log",
       "original-scope-and-mention-audit.json","original-scope-and-mention.log")
def require(ok,why):
    if not ok:raise ValueError(why)
def publish(source,run,dest):
    article=(source/"article.txt").read_bytes()
    require(hashlib.sha256(article).hexdigest()==PIN,"source digest changed")
    data=json.loads((run/"original-source-inventory.json").read_bytes())
    require(data["schema"]=="gwb-original-slr-canonical-source-acceptance-v1" and
            data["source_revision"]==REV and data["source_utf8_sha256"]==PIN and
            data["experimental_sl_semantic_expansion_used"] is False and
            data["semantic_authority_created"] is False,
            "canonical producer evidence absent or promoted")
    for filename, field in (
        ("slr-record.json","original_slr_json_sha256"),
        ("article-candidates.json","original_projection_json_sha256"),
        ("gwb_sensiblaw_p0b_mention_licences.json","original_p0b_json_sha256"),
    ):
        document=json.loads((source/filename).read_bytes())
        digest=hashlib.sha256(json.dumps(document,sort_keys=True,separators=(",",":")).encode("utf-8")).hexdigest()
        require(data.get(field)==digest,"original producer input changed after validation: "+filename)
    counts=data["counts"]
    require(counts["sentences"]==643 and counts["parser_tokens"]==17547 and
            counts["original_predicates"]>0 and
            sum(data["original_dependency_histogram"].values())==17547,
            "lost actual parser tokens or original predicates")
    evidence=json.loads((run/"original-scope-and-mention-audit.json").read_bytes())
    require(evidence["source_revision"]==REV and
            evidence["source_utf8_sha256"]==PIN and
            evidence["scope_label_observer_collision"]["different_consumer_answers"] is True,
            "original source scope witness missing")
    for name,marker in {
      "article-source-proof.log":b"JMD_LEAN_SOURCE_PROOF_OK sha256="+PIN.encode(),
      "semantic-scope-proof.log":b"GWB_REAL_SOURCE_FLAT_SCOPE_NONFACTORABILITY_PROVED",
      "original-source-inventory.log":b"GWB_CANONICAL_SLR_SOURCE_VALIDATED",
      "original-scope-and-mention.log":b"GWB_SEMANTIC_OBSERVER_AUDIT_PASS"
    }.items():
        require(marker in (run/name).read_bytes(),"missing original proof "+name)
    regression=(run/"canonical-source-regression.log").read_text(encoding="utf-8")
    require("Ran 8 tests" in regression and "OK" in regression and
            "FAILED" not in regression and "ERROR" not in regression,
            "canonical original-SLR source regression suite did not pass")
    for label in NEGATIVE:
        raw=(run/("rejected-"+label+".log")).read_bytes()
        require(b"JMD Lean rejected a forged or unsupported source/PNF projection" in raw,
                "wrong negative reason "+label)
    instances=json.loads((run/"lean-source-instances.json").read_bytes())
    projection=json.loads((source/"article-candidates.json").read_bytes())
    require(instances["source_revision"]==REV and
            instances["source_unit_ref"]==data["source_unit_ref"] and
            [x["event"] for x in instances["instances"]]==projection["event_candidates"],
            "Lean population lost or changed original event rows")
    require("GWB_CANONICAL_LEAN_INSTANCES count="+str(counts["original_predicates"]) in
            (run/"lean-source-instances.log").read_text(),
            "missing Lean population execution")
    manifest={
      "schema":"gwb-original-slr-source-lean-proof-v1",
      "source_revision":REV, "source_utf8_sha256":PIN,
      "source_unit_ref":data["source_unit_ref"],
      "original_slr_json_sha256":data["original_slr_json_sha256"],
      "original_projection_json_sha256":data["original_projection_json_sha256"],
      "original_p0b_json_sha256":data["original_p0b_json_sha256"],
      "source_producer":"slr-source-unit-pnf-record-v1",
      "source_projection":"slr-jmd-wikipedia-article-candidates-v1",
      "original_semantic_predicate_count":counts["original_predicates"],
      "original_parser_token_count":counts["parser_tokens"],
      "original_dependency_label_count":counts["dependency_labels"],
      "source_lean_article_checker":"PASSED",
      "lean_source_instances":len(instances["instances"]),
      "original_scope_nonfactorability":"PASSED",
      "adversarial_source_controls_rejected":len(NEGATIVE),
      "canonical_regression_tests_passed":8,
      "experimental_rust_semantic_expansion_executed":False,
      "world_or_event_truth_promoted":False,
      "reviewed_identity_time_requires_original_owner_receipts":True,
      "canonical_source_output":True,
      "historical_experimental_output_role":"diagnostic only",
    }
    dest.parent.mkdir(parents=True,exist_ok=True)
    tmp=Path(tempfile.mkdtemp(prefix=".gwb-original-stage-",dir=dest.parent))
    try:
        for name in FILES:
            shutil.copyfile(run/name,tmp/name)
        for label in NEGATIVE:
            shutil.copyfile(run/("rejected-"+label+".log"),
                            tmp/("rejected-"+label+".log"))
        (tmp/"proof_run_manifest.json").write_text(
            json.dumps(manifest,indent=2,sort_keys=True)+"\n",encoding="utf-8")
        # Never delete the historical Rust results, other files, or any
        # pre-existing untracked output. Only replace explicitly generated
        # files; previously untracked files remain untouched.
        dest.mkdir(parents=True,exist_ok=True)
        for path in tmp.iterdir():
            os.replace(path,dest/path.name)
    finally:
        shutil.rmtree(tmp)
    print("GWB_CANONICAL_ORIGINAL_SLR_RECEIPTS_VERIFIED",dest)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,required=True)
    p.add_argument("--run",type=Path,required=True)
    p.add_argument("--destination",type=Path,required=True)
    a=p.parse_args();publish(a.source,a.run,a.destination)
if __name__=="__main__":main()
