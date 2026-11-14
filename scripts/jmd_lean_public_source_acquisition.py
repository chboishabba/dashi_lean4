#!/usr/bin/env python3
"""Bounded, resumable public Git source acquisition for the single Lean AST world.

Consumes JSONL produced by query_jmd_lean_ast_world.py --queue. Defaults to
dry-run; --acquire opts into git clone of public GitHub source, never execution
of third-party Lean/Lake code. Emits pinned-checkout JSONL consumed by
jmd_lean_ast_world_batch.py. No LLM, AO fleet, repo publication or CI.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path

REPO=re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")
SHA=re.compile(r"[0-9a-f]{40}\Z")


def safe_git(root:Path,args:list[str],timeout:int=120):
    env={**os.environ,"GIT_TERMINAL_PROMPT":"0","GIT_LFS_SKIP_SMUDGE":"1",
         "GIT_CONFIG_NOSYSTEM":"1","GIT_CONFIG_GLOBAL":os.devnull}
    return subprocess.run(["git","-c","core.hooksPath="+os.devnull,*args],
       cwd=root,env=env,capture_output=True,text=True,timeout=timeout,check=False)


def validate_existing(checkout:Path,repo:str)->str:
    if not (checkout/".git").exists():
        raise ValueError("Existing checkout lacks .git; refusing overwrite")
    remote=safe_git(checkout,["remote","get-url","origin"])
    if remote.returncode:
        raise ValueError("Missing source origin")
    url=remote.stdout.strip().removesuffix(".git")
    if url.startswith("git@github.com:"):
        origin=url[len("git@github.com:"):]
    elif url.startswith("https://github.com/"):
        origin=url[len("https://github.com/"):]
    else:
        raise ValueError("Not a GitHub source")
    if origin.casefold()!=repo.casefold():
        raise ValueError("Existing checkout belongs to another repository")
    head=safe_git(checkout,["rev-parse","HEAD"])
    if head.returncode or not SHA.fullmatch(head.stdout.strip()):
        raise ValueError("Cannot pin current checkout")
    dirty=safe_git(checkout,["status","--porcelain","--untracked-files=no"])
    if dirty.returncode or dirty.stdout.strip():
        raise ValueError("Existing checkout has tracked modifications")
    return head.stdout.strip()


def acquire_one(row:dict,root:Path,*,allow_network:bool=False,
                timeout:int=240)->dict:
    ident=row.get("github_id")
    repo=row.get("repository")
    if type(ident) is not int or ident<=0 or not isinstance(repo,str) or not REPO.fullmatch(repo):
        raise ValueError("Invalid numeric GitHub identity or repository name")
    target=(root/str(ident)).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError("Checkout path escape")
    result={"github_id":ident,"repository":repo,"checkout":str(target),
            "metadata_only_input":True,"proofs_certified":0}
    if target.exists():
        revision=validate_existing(target,repo)
        result.update({"status":"already-pinned","commit":revision})
        return result
    if not allow_network:
        result["status"]="dry-run-not-cloned"
        return result
    root.mkdir(parents=True,exist_ok=True)
    url=f"https://github.com/{repo}.git"
    cmd=["clone","--depth=1","--filter=blob:none","--no-tags",url,str(target)]
    try:
        p=safe_git(root,cmd,timeout=timeout)
    except subprocess.TimeoutExpired:
        return {**result,"status":"clone-timeout","residual":"network acquisition timed out"}
    if p.returncode:
        return {**result,"status":"clone-failed",
                "residual":(p.stderr or p.stdout)[-300:]}
    try:
        revision=validate_existing(target,repo)
    except ValueError as exc:
        return {**result,"status":"clone-identity-unverified",
                "residual":str(exc)}
    result.update({"status":"pinned-source-acquired","commit":revision})
    return result


def run(queue:list[dict],root:Path,*,limit:int,allow_network:bool=False,
        delay:float=1.5)->dict:
    if not 1<=limit<=500 or delay<0 or delay>60:
        raise ValueError("Bounded acquisition policy required")
    results=[]
    pinned=[]
    seen=set()
    for row in queue[:limit]:
        ident=row.get("github_id")
        if ident in seen:
            raise ValueError("Repeated GitHub repository identity")
        seen.add(ident)
        try:
            r=acquire_one(row,root,allow_network=allow_network)
        except (OSError,ValueError) as exc:
            r={"github_id":ident,"repository":row.get("repository"),
               "status":"invalid-or-inaccessible","residual":str(exc)[:300],
               "proofs_certified":0}
        results.append(r)
        if r["status"] in {"already-pinned","pinned-source-acquired"}:
            pinned.append({key:r[key] for key in ("github_id","repository","commit","checkout")})
        if allow_network and delay and r["status"]=="pinned-source-acquired":
            time.sleep(delay)
    return {"schema":"jmd-lean-public-acquisition-v1",
            "attempted":len(results),"pinned":len(pinned),
            "dry_run":not allow_network,"results":results,
            "pinned_checkouts":pinned,
            "statement_equivalences_proven":0}


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--queue",required=True,type=Path)
    p.add_argument("--checkout-root",required=True,type=Path)
    p.add_argument("--output",required=True,type=Path)
    p.add_argument("--limit",type=int,default=20)
    p.add_argument("--acquire",action="store_true",
                   help="Explicitly allow network git clone for public repositories")
    p.add_argument("--delay",type=float,default=1.5)
    args=p.parse_args(argv)
    queue=[json.loads(line) for line in args.queue.read_text(encoding="utf-8").splitlines()
           if line.strip()]
    result=run(queue,args.checkout_root.resolve(),limit=args.limit,
               allow_network=args.acquire,delay=args.delay)
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/"acquisition_receipts.jsonl").write_text("".join(
       json.dumps(r,sort_keys=True)+"\n" for r in result["results"]),encoding="utf-8")
    (args.output/"pinned_checkouts.jsonl").write_text("".join(
       json.dumps(r,sort_keys=True)+"\n" for r in result["pinned_checkouts"]),encoding="utf-8")
    print(json.dumps({"attempted":result["attempted"],"pinned":result["pinned"],
       "dry_run":result["dry_run"],"proofs_certified":0},sort_keys=True))


if __name__=="__main__":
    main()
