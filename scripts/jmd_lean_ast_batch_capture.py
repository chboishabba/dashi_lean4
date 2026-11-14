#!/usr/bin/env python3
"""Locally capture native lean4export ASTs for candidate source declarations.

Runs only in an explicitly provided clean, pinned Lean checkout and writes
outside it. Uses source names solely as candidates; the Lean environment and
lean4export adjudicate names and declarations. The result feeds
build_jmd_lean_ast_world.py --exports. No LLM, cloning or external publication.

WARNING: invoking Lean/Lake on third-party code executes untrusted build
hooks/metaprograms. Use a credential-free Nix sandbox; do not run as root.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

SHA=re.compile(r"[a-f0-9]{40}\Z")
IDENT=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
HEADER=re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b")
NS=re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*(?:--.*)?$")
END=re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*(?:--.*)?$")
SECTION=re.compile(r"^\s*section(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*(?:--.*)?$")


def git(root,*args):
    return subprocess.run(["git",*args],cwd=root,text=True,
                          capture_output=True,check=True).stdout.strip()


def source_candidates(content:str, *, module:str) -> list[str]:
    """Conservative discovery, with explicit incompleteness of source parsing."""
    scopes=[]
    names=set()
    for line in content.splitlines():
        ns=NS.fullmatch(line)
        if ns:
            scopes.append(("namespace",ns.group(1)))
            continue
        section=SECTION.fullmatch(line)
        if section:
            scopes.append(("section",section.group(1) or ""))
            continue
        close=END.fullmatch(line)
        if close and scopes:
            target=close.group(1)
            if target is None or target==scopes[-1][1]:
                scopes.pop()
            continue
        match=HEADER.match(line)
        if not match:
            continue
        name=match.group(1)
        if name=="_":
            continue
        # A file may include multiple namespaces, and module names need not
        # be prefixes of declaration names. Exporter resolves actual owners.
        prefix=".".join(x for role,x in scopes if role=="namespace" and x)
        qualified=prefix+"."+name if prefix else name
        if IDENT.fullmatch(qualified):
            names.add(qualified)
    return sorted(names)


def check_source(root:Path, *, expected_repo:str, revision:str):
    root=root.resolve()
    if not (root/".git").is_dir() or not SHA.fullmatch(revision):
        raise ValueError("Pinned local git checkout and full SHA required")
    if git(root,"rev-parse","HEAD")!=revision:
        raise ValueError("Pinned checkout revision mismatch")
    if git(root,"status","--porcelain","--untracked-files=no"):
        raise ValueError("Dirty tracked Lean checkout")
    remote=git(root,"remote","get-url","origin").removesuffix(".git")
    if remote.startswith("git@github.com:"):
        actual=remote.split("git@github.com:",1)[1]
    elif remote.startswith("https://github.com/"):
        actual=remote.split("https://github.com/",1)[1]
    else:
        raise ValueError("Non-GitHub source remote")
    if actual.casefold()!=expected_repo.casefold():
        raise ValueError("Origin differs from admitted source repository")
    if not shutil.which("lake"):
        raise RuntimeError("Lake not installed; no native Lean AST available")
    return root


def run_checked(root:Path,argv:list[str],timeout:int):
    try:
        p=subprocess.run(argv,cwd=root,capture_output=True,timeout=timeout,check=False)
        return p.returncode,p.stdout,p.stderr[:1200]
    except subprocess.TimeoutExpired:
        return -1,b"",b"timeout"


def capture(root:Path, *, github_id:int, repo:str, commit:str, module:str,
            source:Path, out:Path, limit:int=100, timeout:int=180):
    root=check_source(root,expected_repo=repo,revision=commit)
    if not IDENT.fullmatch(module) or not 1<=limit<=2000 or not 1<=timeout<=1200:
        raise ValueError("Invalid module or resource limits")
    candidate_path=(root/source).resolve()
    if not candidate_path.is_relative_to(root) or not candidate_path.is_file() or candidate_path.suffix!=".lean":
        raise ValueError("Lean source path escape, wrong extension or missing source")
    tracked=git(root,"ls-files","--",str(source))
    if str(source) not in tracked.splitlines():
        raise ValueError("Lean source file is not tracked")
    names=source_candidates(candidate_path.read_text(encoding="utf-8"),module=module)
    if not names:
        return {"source_repo":repo,"candidates":0,"accepted":0,"failures":[],
                "status":"no-recognised-source-headers",
                "coverage_complete":False}
    out=out.resolve()
    if out.is_relative_to(root):
        raise ValueError("Export observations must be written outside source checkout")
    out.mkdir(parents=True,exist_ok=True)
    receipts=[]
    manifest=[]
    for name in names[:limit]:
        # Validate source candidate first; never infer from the header.
        with tempfile.NamedTemporaryFile(mode="w",suffix=".lean",prefix="JMDCheck_",
                                         dir=root,delete=False) as stream:
            stream.write(f"import {module}\nset_option autoImplicit false\n"
                         f"#check {name}\n")
            proof_path=Path(stream.name)
        try:
            code,stdout,stderr=run_checked(root,["lake","env","lean",proof_path.name],timeout)
        finally:
            proof_path.unlink(missing_ok=True)
        if code:
            receipts.append({"declaration":name,"status":"not-elaborated",
                             "stderr_sha256":hashlib.sha256(stderr).hexdigest()})
            continue
        code,export,stderr=run_checked(root,
            ["lake","exe","lean4export",module,"--",name],timeout)
        if code or not export or len(export)>200_000_000:
            receipts.append({"declaration":name,"status":"export-failed",
                             "stderr_sha256":hashlib.sha256(stderr).hexdigest()})
            continue
        # Native v3 NDJSON is the AST; parse all rows before writing it.
        try:
            lines=[json.loads(line) for line in export.splitlines() if line.strip()]
        except (ValueError,UnicodeError):
            receipts.append({"declaration":name,"status":"invalid-export"})
            continue
        if not lines or not isinstance(lines[0],dict) or "meta" not in lines[0] or \
           not str(lines[0]["meta"].get("format",{}).get("version","")).startswith("3."):
            receipts.append({"declaration":name,"status":"unsupported-export-format"})
            continue
        sha=hashlib.sha256(export).hexdigest()
        archive=out/(sha+".ndjson")
        if not archive.exists():
            archive.write_bytes(export)
        manifest.append({"github_id":github_id,"full_name":repo,"commit":commit,
                         "module":module,"path":str(archive)})
        receipts.append({"declaration":name,"status":"native-ast-exported",
                         "ndjson_sha256":sha,"bytes":len(export)})
    # Re-run the canonical importer separately; this manifest remains an
    # observation until imported by the existing native AST world owner.
    manifest_path=out/"exports.jsonl"
    with manifest_path.open("a",encoding="utf-8") as f:
        for row in manifest:
            f.write(json.dumps(row,sort_keys=True)+"\n")
    receipt_path=out/"capture_receipts.jsonl"
    with receipt_path.open("a",encoding="utf-8") as f:
        for row in receipts:
            f.write(json.dumps({"repository":repo,"commit":commit,"module":module,
                                **row},sort_keys=True)+"\n")
    return {"repository":repo,"module":module,"candidate_headers":len(names),
            "attempted":len(receipts),"native_ast_exports":len(manifest),
            "unattempted_after_limit":max(0,len(names)-limit),
            "coverage_complete":False,"manifest":str(manifest_path),
            "receipt_path":str(receipt_path),"proofs_certified":0}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--checkout",required=True,type=Path)
    p.add_argument("--github-id",required=True,type=int)
    p.add_argument("--repo",required=True)
    p.add_argument("--commit",required=True)
    p.add_argument("--module",required=True)
    p.add_argument("--source",required=True,type=Path)
    p.add_argument("--out",required=True,type=Path)
    p.add_argument("--limit",type=int,default=100)
    p.add_argument("--timeout",type=int,default=180)
    args=p.parse_args()
    result=capture(args.checkout,github_id=args.github_id,repo=args.repo,
       commit=args.commit,module=args.module,source=args.source,
       out=args.out,limit=args.limit,timeout=args.timeout)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
