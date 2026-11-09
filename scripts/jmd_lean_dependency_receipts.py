#!/usr/bin/env python3
"""Run agda2lean's EXISTING Lean environment manifest on selected donors.

The manifest is Lean code (agda2lean/lean/Agda2Lean/Manifest.lean), executed
by the pinned SOURCE Lean checkout. It extracts actual direct constant
references and transitive axiom closure; this script is only a strict wrapper.
No new theorem index, no LLM, and no implicit proof promotion.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

NAME=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
SHA=re.compile(r"[a-f0-9]{40}\Z")
RELATIONS={"type-direct","value-direct","axiom-closure"}


def git(root: Path, *args) -> str:
    result=subprocess.run(["git",*args],cwd=root,text=True,capture_output=True,check=True)
    return result.stdout.strip()


def parse_manifest(content: str, requested: set[str]) -> dict[str,dict[str,list[str]]]:
    results={k:{kind:[] for kind in sorted(RELATIONS)} for k in requested}
    counts={(k,kind):0 for k in requested for kind in RELATIONS}
    for line in content.splitlines():
        cells=line.split("\t")
        if len(cells)!=3:
            raise ValueError("Unexpected Lean manifest output row")
        decl,kind,dependency=cells
        if decl not in requested or kind not in RELATIONS:
            raise ValueError("Unexpected source declaration or manifest relation")
        # The original manifest escapes special characters, so the consumer
        # deliberately accepts only simple Lean constant names.
        if dependency and not NAME.fullmatch(dependency):
            raise ValueError("Invalid or escaped dependency name")
        if not NAME.fullmatch(decl):
            raise ValueError("Invalid declaration name")
        counts[(decl,kind)]+=1
        if dependency:
            results[decl][kind].append(dependency)
    for key,n in counts.items():
        if n==0:
            raise ValueError(f"Missing Lean manifest relation {key}")
    for decl,relations in results.items():
        for kind,refs in relations.items():
            if refs!=sorted(set(refs)):
                raise ValueError("Manifest relation not ordered and unique")
    return results


def inspect(checkout: Path, manifest: Path, rows: list[dict]) -> list[dict]:
    checkout=checkout.resolve()
    manifest=manifest.resolve()
    if not (checkout/".git").exists() or not manifest.is_file():
        raise ValueError("Requires pinned source checkout and agda2lean manifest file")
    if not shutil.which("lake"):
        raise RuntimeError("Missing Lean/Lake checker")
    revision=git(checkout,"rev-parse","HEAD")
    if not SHA.fullmatch(revision):
        raise ValueError("Invalid Lean checkout revision")
    dirty=git(checkout,"status","--porcelain","--","*.lean","lakefile.lean","lakefile.toml")
    if dirty:
        raise ValueError("Source Lean checkout is dirty")
    requested=[]
    modules=set()
    seen=set()
    for row in rows:
        if row.get("commit")!=revision:
            raise ValueError("Donor revision mismatch")
        decl,module=row.get("declaration"),row.get("module")
        if not isinstance(decl,str) or not NAME.fullmatch(decl):
            raise ValueError("Unsafe Lean declaration")
        if not isinstance(module,str) or not NAME.fullmatch(module):
            raise ValueError("Unsafe Lean module")
        if decl in seen:
            raise ValueError("Duplicate source declaration")
        seen.add(decl)
        modules.add(module)
        requested.append(decl)
    if not requested:
        return []
    # Existing agda2lean Lean module *performs* dependency and axiom checks.
    command=["lake","env","lean","--run",str(manifest)]
    for mod in sorted(modules):
        command.extend(["--module",mod])
    command.extend(sorted(requested))
    result=subprocess.run(command,cwd=checkout,text=True,capture_output=True,timeout=300,check=False)
    if result.returncode:
        raise RuntimeError("Agda2Lean.Manifest failed: "+(result.stderr+"\n"+result.stdout)[:1000])
    parsed=parse_manifest(result.stdout,set(requested))
    output=[]
    for row in rows:
        deps=parsed[row["declaration"]]
        ax=deps["axiom-closure"]
        output.append({
            "repository_id":row.get("repository_id"),
            "repository":row.get("repository"),
            "source_revision":revision,
            "module":row["module"],
            "declaration":row["declaration"],
            "direct_type_dependencies":deps["type-direct"],
            "direct_value_dependencies":deps["value-direct"],
            "transitive_axioms":ax,
            "contains_sorryAx":any("sorryAx" in a for a in ax),
            "checker":"agda2lean/lean/Agda2Lean/Manifest.lean",
            "authority":"lean-environment-dependency-evidence",
            "establishes_cross_prover_proof":False
        })
    return output


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--checkout",type=Path,required=True)
    p.add_argument("--manifest",type=Path,required=True,
                   help="Existing agda2lean/lean/Agda2Lean/Manifest.lean")
    p.add_argument("--shortlist",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args(argv)
    rows=[json.loads(x) for x in args.shortlist.read_text(encoding="utf-8").splitlines() if x.strip()]
    results=inspect(args.checkout,args.manifest,rows)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text("".join(json.dumps(x,sort_keys=True)+"\n" for x in results),
                           encoding="utf-8")
    print(json.dumps({"inspected":len(results),
                      "axiom_or_sorry_risk":sum(bool(x["transitive_axioms"]) for x in results),
                      "cross_prover_proofs":0},indent=2))


if __name__=="__main__":
    main()
