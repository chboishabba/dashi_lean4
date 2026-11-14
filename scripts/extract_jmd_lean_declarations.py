#!/usr/bin/env python3
"""Kernel-environment source extraction for selected Lean declarations.

Input is a JSONL shortlist containing repository_id, repository, commit,
module, declaration. Runs 'lake env lean' in an existing pinned checkout.
Output is JSONL records accepted by jmd_formal_world_reconcile.py. The
type is Lean's #check pretty-print, NOT an independently checked Agda type.
This never clones, fetches or writes to any third-party repository.
"""
import argparse
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")


def git(root, *args):
    return subprocess.run(["git",*args],cwd=root,text=True,
                          capture_output=True,check=True).stdout.strip()


def extract(root, shortlist, *, timeout=180):
    root=Path(root).resolve()
    if not (root/".git").exists():
        raise ValueError("Pinned Git checkout required")
    head=git(root,"rev-parse","HEAD")
    if not SHA.fullmatch(head):
        raise ValueError("Invalid HEAD SHA")
    remote=git(root,"remote","get-url","origin").removesuffix(".git")
    if remote.startswith("git@github.com:"):
        repo=remote[len("git@github.com:"):]
    elif remote.startswith("https://github.com/"):
        repo=remote[len("https://github.com/"):]
    else:
        raise ValueError("Unknown origin, refusing source identity")
    if not shutil.which("lake"):
        raise RuntimeError("lake not installed")
    output=[]
    for row in shortlist:
        for key in ("repository","repository_id","commit","module","declaration"):
            if key not in row: raise ValueError(f"Missing {key}")
        if row["repository"] != repo or row["commit"] != head:
            raise ValueError("Source owner/revision disagrees with checkout")
        module,decl=row["module"],row["declaration"]
        if not NAME.fullmatch(module) or not NAME.fullmatch(decl):
            raise ValueError("Invalid Lean module/declaration")
        # Separate runs prevent #print axioms diagnostic from contaminating type.
        checks=[]
        for command in (f"#check {decl}", f"#print axioms {decl}"):
            with tempfile.NamedTemporaryFile("w",suffix=".lean",prefix="JMDExtract_",dir=root,
                                             delete=False) as f:
                p=Path(f.name)
                f.write(f"import {module}\nset_option pp.width 100000\n"
                        f"set_option pp.fullNames true\n{command}\n")
            try:
                result=subprocess.run(["lake","env","lean",p.name],
                         cwd=root,text=True,capture_output=True,
                         timeout=timeout,check=False)
            finally:
                p.unlink(missing_ok=True)
            if result.returncode:
                raise ValueError(f"Lean rejected {decl}: {(result.stderr + result.stdout)[:600]}")
            checks.append(result.stdout.strip())
        printed=checks[0]
        match=re.match(r"^(.+?)\s*:\s*(.+)\Z",printed,re.DOTALL)
        if not match or match.group(1).strip().split(".")[-1] != decl.split(".")[-1]:
            raise ValueError(f"Ambiguous #check output for {decl}: {printed[:250]}")
        typ=match.group(2).strip()
        if not typ:
            raise ValueError("Empty type output")
        output.append({**row,"type":typ,"lean_axioms_printout":checks[1],
                       "source_observed_by":"lake env lean #check / #print axioms",
                       "source_revision_verified":True,
                       "kernel_proof_transport":False})
    return output


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout",required=True,type=Path)
    parser.add_argument("--shortlist",required=True,type=Path)
    parser.add_argument("--out",required=True,type=Path)
    args=parser.parse_args()
    rows=[json.loads(s) for s in args.shortlist.read_text(encoding="utf-8").splitlines() if s.strip()]
    result=extract(args.checkout,rows)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text("".join(json.dumps(r,sort_keys=True)+"\n" for r in result),
                        encoding="utf-8")
    print(json.dumps({"source_declarations":len(result),"output":str(args.out),
                      "same_object_proofs":0},sort_keys=True))


if __name__=="__main__":
    main()
