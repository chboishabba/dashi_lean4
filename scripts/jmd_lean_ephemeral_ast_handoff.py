#!/usr/bin/env python3
"""Fail-closed adapter: PR #1491 native v3 receipt -> existing PR #105 AST importer manifest.

Does not validate the full native expression DAG or certify a Lean proof.
"""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path
SHA40=re.compile(r"[0-9a-f]{40}\Z")
SHA256=re.compile(r"[0-9a-f]{64}\Z")
class HandoffError(ValueError): pass

def handoff(receipt:dict,github_id:int)->dict:
    if type(github_id) is not int or github_id<=0:
        raise HandoffError("invalid GitHub numeric ID")
    if receipt.get("status")!="lean-module-checked" or receipt.get("declaration_ast_exported") is not True:
        raise HandoffError("worker did not export AST")
    export=receipt.get("native_export")
    if not isinstance(export,dict) or export.get("status")!="native-v3-exported-unadmitted":
        raise HandoffError("native exporter receipt missing")
    repo,rev=receipt.get("repository"),receipt.get("revision")
    if not isinstance(repo,str) or len(repo.split("/"))!=2 or not isinstance(rev,str) or not SHA40.fullmatch(rev):
        raise HandoffError("unpinned source identity")
    if export.get("repository")!=repo or export.get("revision")!=rev:
        raise HandoffError("source and native export origins disagree")
    closure=receipt.get("source_closure")
    if not isinstance(closure,list) or not closure or export.get("source_closure")!=closure:
        raise HandoffError("source closure mismatch")
    if receipt.get("target") not in {r.get("path") for r in closure if isinstance(r,dict)}:
        raise HandoffError("target absent from pinned source closure")
    validation=export.get("validation")
    h=export.get("artifact_sha256")
    if not isinstance(validation,dict) or validation.get("syntax_v3_checked") is not True or not isinstance(h,str) or not SHA256.fullmatch(h) or validation.get("export_sha256")!=h:
        raise HandoffError("missing native v3 evidence or digest")
    artifact=Path(export.get("artifact_path","")).resolve()
    if not artifact.is_file() or artifact.name!=h+".ndjson":
        raise HandoffError("native content-addressed artifact unavailable")
    sha=hashlib.sha256()
    with artifact.open("rb") as stream:
        while block:=stream.read(65536): sha.update(block)
    if sha.hexdigest()!=h: raise HandoffError("native artifact bytes changed")
    module=export.get("module")
    if not isinstance(module,str) or not module: raise HandoffError("native module absent")
    return {"github_id":github_id,"full_name":repo,"commit":rev,
            "module":module,"path":str(artifact)}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--receipt",required=True,type=Path)
    p.add_argument("--github-id",required=True,type=int)
    p.add_argument("--manifest-out",required=True,type=Path)
    a=p.parse_args()
    item=handoff(json.loads(a.receipt.read_text(encoding="utf-8")),a.github_id)
    a.manifest_out.parent.mkdir(parents=True,exist_ok=True)
    with a.manifest_out.open("a",encoding="utf-8") as file:
        file.write(json.dumps(item,sort_keys=True)+"\n")
    print(json.dumps({"manifest":str(a.manifest_out),"entry":item,
        "authority":"native-artifact-handoff-only","full_dag_validated":False},sort_keys=True))
if __name__=="__main__": main()
