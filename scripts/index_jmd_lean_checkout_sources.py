#!/usr/bin/env python3
"""Admit actual git-tracked Lean source inventories to JMD's ONE world DB.

Input is a JSONL of already-present pinned checkouts:
  {"github_id":123,"full_name":"owner/repo","checkout":"/path/to/repo"}

The Git index supplies blob identity and paths. No source code is executed,
no repository is downloaded, and a path inventory is NOT called an AST. The
native checked AST is ingested separately from lean4export NDJSON.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import sqlite3
import subprocess
from pathlib import Path

from build_jmd_lean_ast_world import connect, report

SHA = re.compile(r"[a-f0-9]{40}\Z")
MAX_FILE = 8_000_000

def git(root:Path,*args)->bytes:
    return subprocess.run(["git",*args],cwd=root,capture_output=True,check=True,
                          timeout=90).stdout

def normalize_origin(s:str)->str:
    s=s.strip().removesuffix(".git").removesuffix("/")
    for prefix in ("https://github.com/","ssh://git@github.com/","git@github.com:"):
        if s.startswith(prefix):
            return s[len(prefix):].lower()
    raise ValueError("Unsupported non-GitHub origin")

def index_one(conn:sqlite3.Connection, row:dict, *,max_files:int=0)->dict:
    ident=int(row["github_id"])
    full_name=str(row["full_name"])
    root=Path(row["checkout"]).resolve(strict=True)
    if not (root/".git").exists():
        raise ValueError("Not a Git checkout: "+str(root))
    source=conn.execute("SELECT full_name,stage FROM jmd_lean_world_repositories WHERE github_id=?",
                        (ident,)).fetchone()
    if source is None or source[0].casefold()!=full_name.casefold():
        raise ValueError("Source checkout not admitted by JMD repo ID")
    if normalize_origin(git(root,"remote","get-url","origin").decode())!=full_name.lower():
        raise ValueError("Checkout Git origin does not match numeric ID owner")
    revision=git(root,"rev-parse","HEAD").decode().strip()
    if not SHA.fullmatch(revision):
        raise ValueError("Cannot pin checkout revision")
    dirty=git(root,"status","--porcelain","--untracked-files=no","--",
              "*.lean","lakefile.lean","lakefile.toml","lean-toolchain","lake-manifest.json")
    if dirty:
        raise ValueError("Tracked Lean source modified; do not claim pinned source")
    raw=git(root,"ls-files","-s","-z","--","*.lean")
    entries=[part for part in raw.split(b"\x00") if part]
    if max_files and len(entries)>max_files:
        raise ValueError("Repository exceeds configured Lean source file count")
    indexed=0
    for entry in entries:
        try:
            head,p=entry.split(b"\t",1)
            mode,blob,stage=head.decode("ascii").split(" ")
            relative=p.decode("utf-8")
        except (ValueError,UnicodeDecodeError) as exc:
            raise ValueError("Unparseable Git index entry") from exc
        if mode not in ("100644","100755") or stage!="0" or not SHA.fullmatch(blob):
            raise ValueError("Unsupported Git index mode/blob/stage")
        path=(root/relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError("Git-tracked Lean path escapes checkout or is absent")
        if path.stat().st_size>MAX_FILE:
            raise ValueError("Lean source exceeds explicit file-size policy")
        content=path.read_bytes()
        digest=hashlib.sha256(content).hexdigest()
        hint=".".join(Path(relative).with_suffix("").parts)
        conn.execute("""INSERT INTO jmd_lean_world_source_files
         VALUES(?,?,?,?,?,?,?,'git-tracked-source')
         ON CONFLICT(github_id,source_commit,source_path) DO UPDATE SET
           git_blob_sha=excluded.git_blob_sha,sha256=excluded.sha256,
           bytes=excluded.bytes,module_hint=excluded.module_hint""",
           (ident,revision,relative,blob,digest,len(content),hint))
        indexed+=1
    if indexed and source[1]=="metadata":
        conn.execute("UPDATE jmd_lean_world_repositories SET stage='source-inventory' WHERE github_id=?",
                     (ident,))
    return {"github_id":ident,"source_commit":revision,
            "tracked_lean_files":indexed,"source_identity":"git-tracked-source",
            "elaborated_ast":False}

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--checkouts",type=Path,help="JSONL of local pinned repositories")
    p.add_argument("--mirrors-root",type=Path,help="Existing pinned checkouts named by numeric GitHub ID")
    p.add_argument("--max-files-per-repo",type=int,default=10000)
    p.add_argument("--max-repos",type=int,default=0,help="0 means all listed checkouts")
    args=p.parse_args(argv)
    if bool(args.checkouts)==bool(args.mirrors_root):
        p.error("Provide exactly one of --checkouts or --mirrors-root")
    if args.max_repos<0 or args.max_files_per_repo<0:
        p.error("Cannot configure negative limits")
    conn=connect(args.database)
    rows=[]
    try:
        absent=0
        if args.checkouts:
            with args.checkouts.open(encoding="utf-8") as stream:
                for line in stream:
                    if line.strip():
                        rows.append(json.loads(line))
        else:
            root=args.mirrors_root.resolve(strict=True)
            for ident,name in conn.execute("""SELECT github_id,full_name
                 FROM jmd_lean_world_repositories
                 ORDER BY starred DESC,github_id"""):
                checkout=root/str(ident)
                if not checkout.is_dir():
                    absent+=1
                    continue
                rows.append({"github_id":ident,"full_name":name,
                             "checkout":str(checkout)})
                if args.max_repos and len(rows)>=args.max_repos:
                    break
        if args.max_repos:
            rows=rows[:args.max_repos]
        result=[]
        for row in rows:
            with conn:
                result.append(index_one(conn,row,max_files=args.max_files_per_repo))
        print(json.dumps({"checkouts":result,"missing_local_mirrors":absent,
                          "world":report(conn)},sort_keys=True,indent=2))
    finally:
        conn.close()

if __name__=="__main__":
    main()
