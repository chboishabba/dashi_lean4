#!/usr/bin/env python3
"""Bounded, resumable GitHub Lean source acquisition (NO code execution).

Consumes query_jmd_lean_ast_world.py JSONL work queue, clones public Git
repositories into <mirror_root>/<numeric-github-id>, checks pinned HEAD and
origin, writes source-checkout JSONL for index_jmd_lean_checkout_sources.py.

Network use requires --allow-network. Cloning is a data operation only;
this script never runs Lake, Lean, package builds, arbitrary hooks or LLMs.
The caller should execute external compiler tools in a credential-free Nix
sandbox after independently auditing the repositories.
"""
from __future__ import annotations
import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path

SHA=re.compile(r"[0-9a-f]{40}\Z")
FULL=re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")

def run(args,cwd=None,timeout=240):
    env=os.environ.copy()
    env.update({"GIT_TERMINAL_PROMPT":"0","GIT_LFS_SKIP_SMUDGE":"1",
                "GIT_CONFIG_NOSYSTEM":"1","GIT_ASKPASS":"/bin/false"})
    return subprocess.run(args,cwd=cwd,env=env,capture_output=True,
                          text=True,timeout=timeout,check=False)

def pin(root,expected):
    if not (root/".git").exists():
        raise ValueError("Not a Git checkout")
    head=run(["git","rev-parse","HEAD"],cwd=root)
    origin=run(["git","remote","get-url","origin"],cwd=root)
    if head.returncode or origin.returncode:
        raise ValueError("Missing checkout HEAD or origin")
    revision=head.stdout.strip()
    if not SHA.fullmatch(revision):
        raise ValueError("Malformed HEAD")
    url=origin.stdout.strip().removesuffix(".git")
    if url not in ("https://github.com/"+expected,
                   "git@github.com:"+expected):
        raise ValueError("Mismatched source repository origin")
    status=run(["git","status","--porcelain","--untracked-files=no"],cwd=root)
    if status.returncode or status.stdout.strip():
        raise ValueError("Checkout has tracked source changes")
    return revision

def acquire(entries,root,*,allow_network=False,max_repos=20,sleep_seconds=2.25):
    if max_repos<1:
        raise ValueError("Batch must be explicitly bounded")
    root=root.resolve()
    root.mkdir(parents=True,exist_ok=True)
    success=[]
    failures=[]
    # Prioritised input order is maintained; retries are an explicit later run.
    for record in entries[:max_repos]:
        ident=int(record["github_id"])
        name=str(record["repository"])
        if ident<1 or not FULL.fullmatch(name):
            raise ValueError("Bad source repository numeric ID/name")
        directory=root/str(ident)
        if not directory.exists():
            if not allow_network:
                failures.append({"github_id":ident,"repository":name,
                                 "reason":"not-locally-mirrored","attempted_clone":False})
                continue
            result=run(["git","-c","protocol.version=2","clone",
                "--filter=blob:none","--depth=1","--no-tags",
                "https://github.com/"+name+".git",str(directory)])
            if result.returncode:
                failures.append({"github_id":ident,"repository":name,
                      "reason":"clone-failed","stderr_excerpt":result.stderr[-500:],
                      "attempted_clone":True})
                # Partial repos are never indexed as successful.
                continue
            time.sleep(sleep_seconds)
        try:
            sha=pin(directory,name)
        except ValueError as exc:
            failures.append({"github_id":ident,"repository":name,
                             "reason":"pin-failed","detail":str(exc),
                             "attempted_clone":False})
            continue
        success.append({"github_id":ident,"full_name":name,
                        "checkout":str(directory),"commit":sha,
                        "authority":"git-pinned-local-source",
                        "establishes_AST":False,"establishes_proof":False})
    return success,failures

def read_queue(path):
    records=[]
    seen=set()
    with path.open(encoding="utf-8") as f:
        for ln,line in enumerate(f,1):
            if not line.strip():
                continue
            try: obj=json.loads(line)
            except ValueError as exc:
                raise ValueError(f"Invalid JSONL at {ln}") from exc
            if not isinstance(obj,dict) or obj.get("authority")!="discovery-work-queue":
                raise ValueError("Only canonical JMD discovery queue entries allowed")
            ident=int(obj["github_id"])
            if ident in seen:
                raise ValueError("Duplicate GitHub ID in queue")
            seen.add(ident)
            if obj.get("next_action") not in (
                    "acquire-pinned-local-git-source","native-lean4export"):
                raise ValueError("Bad queued work stage")
            records.append(obj)
    return records

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--queue",type=Path,required=True)
    p.add_argument("--mirror-root",type=Path,required=True)
    p.add_argument("--out-checkouts",type=Path,required=True)
    p.add_argument("--out-failures",type=Path,required=True)
    p.add_argument("--max-repos",type=int,default=20)
    p.add_argument("--allow-network",action="store_true")
    p.add_argument("--sleep-seconds",type=float,default=2.25)
    args=p.parse_args(argv)
    if args.sleep_seconds<0:
        p.error("Negative sleep forbidden")
    jobs=read_queue(args.queue)
    success,failed=acquire(jobs,args.mirror_root,allow_network=args.allow_network,
                           max_repos=args.max_repos,sleep_seconds=args.sleep_seconds)
    for dest,records in ((args.out_checkouts,success),(args.out_failures,failed)):
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_text("".join(json.dumps(x,sort_keys=True)+"\n" for x in records))
    print(json.dumps({"jobs_considered":min(len(jobs),args.max_repos),
       "local_pinned_checkouts":len(success),"unacquired_or_failed":len(failed),
       "network_allowed":args.allow_network,
       "compiled":0,"ast_exports_generated":0,"proofs_verified":0},sort_keys=True))
if __name__=="__main__":
    main()
