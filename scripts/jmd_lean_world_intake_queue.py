#!/usr/bin/env python3
"""Populate source coverage and prioritize native AST export work.

Reads the *existing* jmd_lean_world tables in .dashi/repository.sqlite3.
No clone, network, LLM, scheduler, agent, repository edits or proof promotion.
A pinned checkout inventory is NOT an elaborated AST and not a theorem check.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sqlite3
import subprocess
from pathlib import Path

SHA=re.compile(r"[0-9a-f]{40}\Z")
MODULE=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
EXCLUDE={".git",".lake",".direnv","node_modules","vendor","build"}


def git(root:Path,*args:str)->str:
    return subprocess.run(["git",*args],cwd=root,check=True,
                          capture_output=True,text=True).stdout.strip()


def source_module_hint(path: str)->str:
    """A source-path SEARCH HINT only, not a checked Lean module owner."""
    parts=list(Path(path).with_suffix("").parts)
    if parts and parts[0] in {"src","lean","Lean","Mathlib"}:
        # Lean and Mathlib are actual module prefixes, not always source roots.
        if parts[0] in {"src","lean"}:parts=parts[1:]
    guess=".".join(parts)
    return guess if MODULE.fullmatch(guess) else ""


def pinned_origin(root:Path,expected:str)->str:
    if not (root/".git").exists():
        raise ValueError("Pinned local checkout required; no automatic clone")
    actual=git(root,"rev-parse","HEAD")
    if not SHA.fullmatch(actual) or actual!=expected:
        raise ValueError("Expected immutable full commit SHA")
    if git(root,"status","--porcelain","--untracked-files=no"):
        raise ValueError("Tracked checkout is dirty")
    origin=git(root,"remote","get-url","origin").removesuffix(".git")
    if origin.startswith("git@github.com:"):
        origin=origin[len("git@github.com:"):]
    elif origin.startswith("https://github.com/"):
        origin=origin[len("https://github.com/"):]
    else:
        raise ValueError("Unsupported Git source origin")
    return origin


def scan(db:sqlite3.Connection,root:Path,github_id:int,commit:str)->dict:
    root=root.resolve()
    origin=pinned_origin(root,commit)
    row=db.execute("""SELECT full_name,stage
       FROM jmd_lean_world_repositories WHERE github_id=?""",(github_id,)).fetchone()
    if row is None or row[0].casefold()!=origin.casefold():
        raise ValueError("Source checkout identity differs from corpus GitHub numeric ID")
    db.execute("""INSERT INTO jmd_lean_world_source_attestations
      (github_id,source_commit,origin,verification_method)
      VALUES(?,?,?,'pinned-clean-local-git')
      ON CONFLICT(github_id,source_commit) DO UPDATE SET origin=excluded.origin""",
      (github_id,commit,origin))
    tracked=subprocess.run(["git","ls-files","-z","--","*.lean"],
        cwd=root,capture_output=True,check=True).stdout
    paths=[p.decode("utf-8") for p in tracked.split(b"\0") if p]
    scanned=0
    skipped=0
    for rel in sorted(paths):
        path=Path(rel)
        if set(path.parts)&EXCLUDE or path.suffix!=".lean":
            skipped+=1
            continue
        actual=(root/path).resolve()
        if not actual.is_relative_to(root) or not actual.is_file():
            raise ValueError("Tracked Lean source missing or path escapes root")
        data=actual.read_bytes()
        sha=hashlib.sha256(data).hexdigest()
        blob=git(root,"hash-object","--",rel)
        if not SHA.fullmatch(blob):
            raise ValueError("Invalid Git tracked blob SHA")
        module=source_module_hint(rel)
        db.execute("""INSERT INTO jmd_lean_world_source_files
          (github_id,source_commit,source_path,git_blob_sha,sha256,bytes,
            module_hint,authority)
          VALUES(?,?,?,?,?,?,?,'git-tracked-source')
          ON CONFLICT(github_id,source_commit,source_path) DO UPDATE SET
            git_blob_sha=excluded.git_blob_sha,sha256=excluded.sha256,
            bytes=excluded.bytes,module_hint=excluded.module_hint""",
          (github_id,commit,rel,blob,sha,len(data),module))
        scanned+=1
    if row[1]=="metadata":
        db.execute("UPDATE jmd_lean_world_repositories SET stage='source-inventory' WHERE github_id=?",
                   (github_id,))
    return {"repository_id":github_id,"revision":commit,
            "tracked_lean_sources":scanned,"excluded_sources":skipped,
            "elaborated_ast_declarations":0,
            "source_module_names_are_hints":True}


def source_worklist(db:sqlite3.Connection,ident:int,commit:str)->list[dict]:
    """Return remaining *candidate* module names for external Lean kernel export.

    Does not invent declaration names or call lean4export with fabricated args.
    The selected Lean environment must supply real theorem names first.
    """
    rows=db.execute("""SELECT source_path,module_hint,sha256 FROM
      jmd_lean_world_source_files WHERE github_id=? AND source_commit=?
      ORDER BY source_path""",(ident,commit)).fetchall()
    exports={r[0] for r in db.execute("""SELECT module FROM jmd_lean_world_exports
           WHERE github_id=? AND source_commit=?""",(ident,commit))}
    return [{"source_path":p,"candidate_module":m,"source_sha256":s,
             "module_proven":False,"ast_exported":m in exports,
             "requires_environment_elaboration":True} for p,m,s in rows
             if m and m not in exports]


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    sub=p.add_subparsers(dest="action",required=True)
    scan_args=sub.add_parser("inventory")
    scan_args.add_argument("--checkout",required=True,type=Path)
    scan_args.add_argument("--github-id",type=int,required=True)
    scan_args.add_argument("--commit",required=True)
    w=sub.add_parser("modules")
    w.add_argument("--github-id",type=int,required=True)
    w.add_argument("--commit",required=True)
    args=p.parse_args(argv)
    if not args.database.is_file():p.error("Use the existing dashi-repo SQLite file")
    db=sqlite3.connect(args.database)
    try:
        if args.action=="inventory":
            with db:result=scan(db,args.checkout,args.github_id,args.commit)
        else:
            if not SHA.fullmatch(args.commit):p.error("Full pinned commit required")
            result={"modules":source_worklist(db,args.github_id,args.commit),
                    "authority":"module-hints-not-AST"}
        print(json.dumps(result,indent=2,sort_keys=True))
    finally:db.close()


if __name__=="__main__":
    main()
