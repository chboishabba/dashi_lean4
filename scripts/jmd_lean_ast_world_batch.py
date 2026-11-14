#!/usr/bin/env python3
"""Batch all locally available Lean checkouts into the ONE native AST world.

Prerequisites: build_jmd_lean_ast_world.py --repositories (and optional stars).
Input: JSONL {github_id,repository,commit,checkout} for EXISTING local clones.

Default action inventories tracked source only; --capture opts into running
third-party Lean/Lake and lean4export (use credential-free Nix sandbox).
The output is per-checkout source/AST coverage with exact residuals.
No LLM, AO fleet, extra database, implicit clone, or proof promotion.
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
from pathlib import Path

import build_jmd_lean_ast_world as world
import jmd_lean_world_intake_queue as intake
import jmd_lean_ast_batch_capture as exporter

SHA=re.compile(r"[a-f0-9]{40}\Z")


def read_local_checkouts(path:Path,max_repos:int) -> list[dict]:
    if not 1<=max_repos<=10000:
        raise ValueError("Maximum repositories must be between 1 and 10000")
    out=[]
    seen=set()
    for line,text in enumerate(path.read_text(encoding="utf-8").splitlines(),1):
        if not text.strip():continue
        row=json.loads(text)
        if not isinstance(row,dict):
            raise ValueError(f"Non-object checkout at line {line}")
        keys={"github_id","repository","commit","checkout"}
        if not keys<=row.keys():
            raise ValueError(f"Missing checkout identity at line {line}")
        ident=int(row["github_id"])
        if ident<=0 or not isinstance(row["repository"],str) or \
             len(row["repository"].split("/"))!=2 or \
             not isinstance(row["commit"],str) or not SHA.fullmatch(row["commit"]) or \
             not isinstance(row["checkout"],str):
            raise ValueError(f"Invalid pinned checkout at line {line}")
        identity=(ident,row["commit"])
        if identity in seen:
            raise ValueError(f"Duplicate pinned checkout {identity}")
        seen.add(identity)
        out.append(row)
    if len(out)>max_repos:
        raise ValueError("Checkout manifest exceeds bounded batch; partition explicitly")
    return out


def run_batch(db:sqlite3.Connection,rows:list[dict],out:Path,*,capture:bool=False,
              max_modules:int=12,max_declarations:int=50,timeout:int=180)->dict:
    if not 1<=max_modules<=300 or not 1<=max_declarations<=500:
        raise ValueError("Module/declaration caps must be positive and bounded")
    out=out.resolve()
    out.mkdir(parents=True,exist_ok=True)
    statuses=[]
    for row in rows:
        ident=int(row["github_id"])
        commit=row["commit"]
        repo=row["repository"]
        checkout=Path(row["checkout"]).resolve()
        record={"github_id":ident,"repository":repo,"commit":commit,
                "source_files":0,"ast_exports_imported":0,
                "modules_attempted":0,"proofs_certified":0}
        try:
            # Per-repo savepoints: a malformed source/export cannot corrupt
            # prior successfully admitted repositories.
            with db:
                source=intake.scan(db,checkout,ident,commit)
                record["source_files"]=source["tracked_lean_sources"]
            record["status"]="source-inventoried"
            if capture:
                module_rows=intake.source_worklist(db,ident,commit)
                unique={}
                for r in module_rows:
                    if r["candidate_module"]:
                        unique.setdefault(r["candidate_module"],r["source_path"])
                for module,source_path in list(sorted(unique.items()))[:max_modules]:
                    record["modules_attempted"]+=1
                    export_root=out/str(ident)/commit/module.replace(".","_")
                    result=exporter.capture(checkout,github_id=ident,
                        repo=repo,commit=commit,module=module,
                        source=Path(source_path),out=export_root,
                        limit=max_declarations,timeout=timeout)
                    manifest=Path(result.get("manifest",""))
                    if manifest.is_file():
                        for line in manifest.read_text(encoding="utf-8").splitlines():
                            if not line.strip():continue
                            export=json.loads(line)
                            if (int(export["github_id"])!=ident or
                                export["full_name"]!=repo or
                                export["commit"]!=commit or
                                export["module"]!=module):
                                raise ValueError("AST export manifest attribution mismatch")
                            with db:
                                record["ast_exports_imported"]+=world.import_export(db,export)
                record["status"]=("some-native-ast-indexed" if record["ast_exports_imported"]
                                  else "no-native-ast-imported")
                record["modules_remaining"]=max(0,len(unique)-max_modules)
        except (OSError,ValueError,RuntimeError,sqlite3.Error,
                json.JSONDecodeError) as exc:
            record["status"]="blocked"
            record["residual"]={"kind":type(exc).__name__,
                                "message":str(exc)[:500]}
        statuses.append(record)
    file=out/"world_ingest_receipts.jsonl"
    file.write_text("".join(json.dumps(x,sort_keys=True)+"\n" for x in statuses),
                    encoding="utf-8")
    return {"schema":"jmd-native-lean-world-batch-v1",
        "repositories_attempted":len(rows),
        "repositories_blocked":sum(x["status"]=="blocked" for x in statuses),
        "source_files_inventoried":sum(x["source_files"] for x in statuses),
        "ast_exports_imported":sum(x["ast_exports_imported"] for x in statuses),
        "proofs_certified":0,"statuses":statuses,
        "receipt_path":str(file),"uses_single_dashi_database":True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--checkouts",required=True,type=Path)
    p.add_argument("--output",required=True,type=Path)
    p.add_argument("--capture",action="store_true",
                   help="Opt in to executing third-party Lake and Lean; use sandbox")
    p.add_argument("--max-repos",type=int,default=50)
    p.add_argument("--max-modules",type=int,default=12)
    p.add_argument("--max-declarations",type=int,default=50)
    p.add_argument("--timeout",type=int,default=180)
    args=p.parse_args()
    if not args.database.is_file():
        p.error("Canonical .dashi/repository.sqlite3 required")
    rows=read_local_checkouts(args.checkouts,args.max_repos)
    db=world.connect(args.database)
    try:
        result=run_batch(db,rows,args.output,capture=args.capture,
                         max_modules=args.max_modules,
                         max_declarations=args.max_declarations,
                         timeout=args.timeout)
        print(json.dumps({k:v for k,v in result.items() if k!="statuses"},
                         sort_keys=True,indent=2))
    finally:db.close()


if __name__=="__main__":
    main()
