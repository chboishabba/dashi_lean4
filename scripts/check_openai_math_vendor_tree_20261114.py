#!/usr/bin/env python3
"""Count ALL Git-pinned OpenAI math Lean source paths, not just 200 headlines.

Uses only pinned git tree metadata: no large generated source copies, no web,
no mathematically invalid theorem imports, no dependency on Mathlib build.
Produces optional streamed NDJSON source candidates for existing DASHI
world ingestion. A .lean file is NOT necessarily a proof or theorem.
"""
import argparse
from collections import Counter
import json
import re
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PIN = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
OAI_COUNTS = {
  "Algebra": 2081,
  "AlgebraicGeometry": 975,
  "AlgebraicTopology": 45,
  "Analysis": 26567,
  "CategoryTheory": 312,
  "Combinatorics": 16614,
  "Computability": 5213,
  "Dynamics": 664,
  "GameTheory": 303,
  "Geometry": 14057,
  "GroupTheory": 4192,
  "InformationTheory": 339,
  "LinearAlgebra": 954,
  "MathematicalPhysics": 6736,
  "MeasureTheory": 2950,
  "ModelTheory": 42,
  "NumberTheory": 23530,
  "Optimization": 2,
  "Probability": 12971,
  "RepresentationTheory": 1108,
  "RingTheory": 536,
  "SetTheory": 1018,
  "Topology": 1249
}
COMPARATOR_COUNT = 416
OAI_ROOT_FILES = 2
TOTAL_LEAN_FILES = 122876

def require(cond,why):
    if not cond:
        raise ValueError(why)

def run_git(root,*cmd):
    p=subprocess.run(["git","-C",str(root),*cmd],capture_output=True,
                     check=True)
    return p.stdout.decode("utf-8").strip()

def git_records(vendor):
    cmd=["git","-C",str(vendor),"ls-tree","-r","-z","HEAD","lean"]
    p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    buf=bytearray()
    while True:
        chunk=p.stdout.read(131072)
        if not chunk: break
        buf.extend(chunk)
        while True:
            i=buf.find(0)
            if i < 0: break
            raw=bytes(buf[:i])
            del buf[:i+1]
            require(b"\t" in raw,"malformed Git tree entry")
            prefix,path=raw.split(b"\t",1)
            mode,kind,blob=prefix.decode("ascii").split()
            require(mode=="100644" and kind=="blob" and
                    re.fullmatch(r"[0-9a-f]{40}",blob),
                    "unexpected type/mode of source tree blob")
            name=path.decode("utf-8")
            require(name.startswith("lean/") and
                    ".." not in Path(name).parts and "\x00" not in name,
                    "Git tree returned an invalid path")
            yield name,blob
    require(not buf,"unterminated Git tree record")
    err=p.stderr.read().decode("utf-8",errors="replace")
    require(p.wait()==0,"Git tree scan failed: "+err)

def group(path):
    if not path.endswith(".lean"): return None
    if path in ("lean/OAI.lean","lean/lakefile.lean"):
        return ("root",None)
    parts=path.split("/")
    if len(parts)>=4 and parts[:2]==["lean","OAI"]:
        require(parts[2] in OAI_COUNTS,"unknown OAI academic domain "+parts[2])
        return ("OAI",parts[2])
    if len(parts)>=3 and parts[1]=="ComparatorChallenges":
        return ("ComparatorChallenges",None)
    raise ValueError("unclassified .lean source "+path)

def audit(vendor, ndjson=None):
    by=Counter()
    total=0
    with (ndjson.open("w",encoding="utf-8") if ndjson else open("/dev/null","w")) as out:
        for path,blob in git_records(vendor):
            kind=group(path)
            if kind is None: continue
            total += 1
            by[kind] += 1
            if ndjson:
                out.write(json.dumps({
                  "repo":"openai/math",
                  "pin":PIN,
                  "git_blob":blob,
                  "path":path,
                  "type":"LEAN_SOURCE_MODULE",
                  "math_theorem_statement_compared":False,
                  "same_object_dashi_proved":False,
                  "kernel_imported_into_dashi":False
                },ensure_ascii=False,separators=(",",":"))+"\n")
    require(total==TOTAL_LEAN_FILES,
            f"source-tree size drift: {total} != {TOTAL_LEAN_FILES}")
    require(by[("root",None)]==OAI_ROOT_FILES,"wrong Lean umbrella/root file count")
    require(by[("ComparatorChallenges",None)]==COMPARATOR_COUNT,
            "wrong comparator module count")
    for academic_domain,n in OAI_COUNTS.items():
        require(by[("OAI",academic_domain)]==n,
                "domain source count drift: "+academic_domain)
    return {"status":"GIT_TREE_PINS_CONFIRMED","source_files":total,
            "oai_modules":sum(OAI_COUNTS.values()),
            "comparator_modules":COMPARATOR_COUNT,
            "root_modules":OAI_ROOT_FILES,
            "domains":dict(sorted(OAI_COUNTS.items())),
            "headline_main_result_references_at_this_pin":200,
            "source_files_are_not_theorem_count":True,
            "dashi_proof_ports_confirmed_by_inventory":0,
            "source_producer_acceptance":False}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--vendor",type=Path,default=ROOT/"vendor/openai-math-src")
    ap.add_argument("--json-out",type=Path)
    ap.add_argument("--emit-ndjson",type=Path,
                    help="Optional streamed module metadata; NOT theorem imports")
    args=ap.parse_args()
    vendor=args.vendor.resolve()
    require(vendor.is_dir() and (vendor/".git").exists(),
            "materialize the pinned submodule first with git submodule update --init")
    require(run_git(vendor,"rev-parse","HEAD")==PIN,
            "OpenAI math vendor revision drift")
    require(run_git(ROOT,"ls-tree","HEAD","vendor/openai-math-src").startswith(
            "160000 commit "+PIN+"\t"),"DASHI Lean parent gitlink differs")
    require((vendor/"lean/lean-toolchain").read_text().strip()==
            "leanprover/lean4:v4.34.1","unexpected upstream Lean toolchain")
    report=audit(vendor,args.emit_ndjson)
    if args.json_out:
        args.json_out.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))

if __name__=="__main__":
    try: main()
    except (ValueError,KeyError,OSError,subprocess.CalledProcessError) as e:
        print("BLOCKED:",e,file=sys.stderr)
        sys.exit(1)
