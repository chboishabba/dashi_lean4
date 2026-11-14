#!/usr/bin/env python3
"""Drive native Lean .olean declaration enumeration and selected AST exports.

Reads already-pinned Git checkouts and module hints from the SAME DASHI
repository.sqlite3. Runs the checked Lean module enumerator in the original
project environment, then optionally lean4export on individual declarations.
No LLM, no agent, no second semantic DB.

This MAY execute third-party Lean macros/build scripts. Requires explicit
--allow-execute-lean and a credential-free, resource-limited Nix sandbox.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import sqlite3
import subprocess
from pathlib import Path

from build_jmd_lean_ast_world import connect
from mirror_jmd_lean_sources import pin

def digest(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()

def ensure_schema(conn):
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS jmd_lean_world_module_runs (
      github_id INTEGER NOT NULL, source_commit TEXT NOT NULL,
      module TEXT NOT NULL, enumerator_sha256 TEXT NOT NULL,
      status TEXT NOT NULL, stderr_excerpt TEXT NOT NULL,
      result_digest TEXT NOT NULL, declaration_count INTEGER NOT NULL,
      PRIMARY KEY(github_id,source_commit,module,enumerator_sha256)
    );
    CREATE TABLE IF NOT EXISTS jmd_lean_world_constant_inventory (
      github_id INTEGER NOT NULL,source_commit TEXT NOT NULL,
      module TEXT NOT NULL,declaration TEXT NOT NULL,kind TEXT NOT NULL,
      enumerator_sha256 TEXT NOT NULL,
      PRIMARY KEY(github_id,source_commit,module,declaration)
    );
    CREATE INDEX IF NOT EXISTS idx_jmd_lean_world_constants
      ON jmd_lean_world_constant_inventory(declaration);
    """)

def execute(cmd,root,timeout,output=None):
    env=os.environ.copy()
    env.update({"GIT_TERMINAL_PROMPT":"0","GIT_LFS_SKIP_SMUDGE":"1",
                "GIT_CONFIG_NOSYSTEM":"1","GIT_ASKPASS":"/bin/false"})
    if output:
        with output.open("wb") as out:
            p=subprocess.run(cmd,cwd=root,env=env,stdout=out,
                             stderr=subprocess.PIPE,timeout=timeout,check=False)
        return p.returncode,b"",p.stderr.decode("utf-8","replace")
    p=subprocess.run(cmd,cwd=root,env=env,capture_output=True,
                     timeout=timeout,check=False)
    return p.returncode,p.stdout,p.stderr.decode("utf-8","replace")

def parse_module_rows(blob,module):
    rows=[]
    seen=set()
    for line in blob.decode("utf-8").splitlines():
        bits=line.split("\t")
        if len(bits)!=3 or bits[0]!=module:
            raise ValueError("Lean enumerator returned an unbound module row")
        _,name,kind=bits
        if not name or "\x00" in name or name in seen:
            raise ValueError("Duplicate/bad native Lean declaration identity")
        if kind not in {"thm","def","axiom","inductive","ctor",
                        "rec","opaque","quot"}:
            raise ValueError("Unrecognised native Lean declaration kind")
        seen.add(name)
        rows.append((name,kind))
    return sorted(rows)

def enumerate_one(conn,checkout,en,m,*,timeout=240,refresh=False):
    ident=int(checkout["github_id"])
    name=checkout["full_name"]
    root=Path(checkout["checkout"]).resolve(strict=True)
    revision=pin(root,name)
    if checkout.get("commit") and revision!=checkout["commit"]:
        raise ValueError("Checkout changed since source-manifest emission")
    script=Path(en).resolve(strict=True)
    script_sha=hashlib.sha256(script.read_bytes()).hexdigest()
    if not refresh:
        state=conn.execute("""SELECT status FROM jmd_lean_world_module_runs
           WHERE github_id=? AND source_commit=? AND module=? AND enumerator_sha256=?""",
           (ident,revision,m,script_sha)).fetchone()
        if state and state[0]=="accepted":
            return [{"name":n,"kind":k} for n,k in conn.execute(
                """SELECT declaration,kind FROM jmd_lean_world_constant_inventory
                   WHERE github_id=? AND source_commit=? AND module=?
                   ORDER BY declaration""",(ident,revision,m))]
    try:
        code,out,err=execute(["lake","env","lean","--run",str(script),m],
                             root,timeout)
        status="accepted" if code==0 else "lean-environment-error"
        rows=parse_module_rows(out,m) if code==0 else []
        if code==0 and not rows:
            status="no-native-module-constants"
    except (OSError,subprocess.TimeoutExpired,ValueError) as exc:
        status="enumeration-error"
        err=str(exc)
        out=b""
        rows=[]
    conn.execute("""INSERT INTO jmd_lean_world_module_runs
       VALUES(?,?,?,?,?,?,?,?)
       ON CONFLICT(github_id,source_commit,module,enumerator_sha256)
       DO UPDATE SET status=excluded.status,
         stderr_excerpt=excluded.stderr_excerpt,
         result_digest=excluded.result_digest,
         declaration_count=excluded.declaration_count""",
       (ident,revision,m,script_sha,status,err[-1200:],
        hashlib.sha256(out).hexdigest(),len(rows)))
    conn.execute("""DELETE FROM jmd_lean_world_constant_inventory
         WHERE github_id=? AND source_commit=? AND module=?""",
         (ident,revision,m))
    conn.executemany("""INSERT INTO jmd_lean_world_constant_inventory
         VALUES(?,?,?,?,?,?)""",
         ((ident,revision,m,n,k,script_sha) for n,k in rows))
    return [{"name":n,"kind":k} for n,k in rows]

def run_batch(conn,checkouts,enumerator,*,max_modules=4,export_per_module=0,
              export_root=None,refresh=False):
    results=[]
    manifests=[]
    for checkout in checkouts:
        ident=int(checkout["github_id"])
        revision=str(checkout["commit"])
        modules=[r[0] for r in conn.execute(
            """SELECT DISTINCT module_hint FROM jmd_lean_world_source_files
               WHERE github_id=? AND source_commit=? AND module_hint != ''
               ORDER BY module_hint LIMIT ?""",
            (ident,revision,max_modules))]
        for module in modules:
            with conn:
                rows=enumerate_one(conn,checkout,enumerator,module,refresh=refresh)
            status=conn.execute("""SELECT status FROM jmd_lean_world_module_runs
                 WHERE github_id=? AND source_commit=? AND module=?
                 ORDER BY rowid DESC LIMIT 1""",
                 (ident,revision,module)).fetchone()[0]
            results.append({"github_id":ident,"module":module,
                            "status":status,"declarations":len(rows)})
            if status!="accepted" or export_per_module==0:
                continue
            selected=[x for x in rows if x["kind"] in ("thm","def","opaque")]
            for item in selected[:export_per_module]:
                if export_root is None:
                    raise ValueError("Export output root required")
                filename=digest("\x1f".join(
                    (str(ident),revision,module,item["name"])))+".ndjson"
                dest=export_root/str(ident)/revision/filename
                dest.parent.mkdir(parents=True,exist_ok=True)
                if not dest.exists() or refresh:
                    try:
                        code,_,err=execute(["lake","exe","lean4export",module,
                                           "--",item["name"]],
                                          Path(checkout["checkout"]),
                                          timeout=600,output=dest)
                        if code:
                            dest.unlink(missing_ok=True)
                            results.append({"github_id":ident,"module":module,
                                            "declaration":item["name"],
                                            "export":"failure",
                                            "stderr_excerpt":err[-600:]})
                            continue
                    except (OSError,subprocess.TimeoutExpired) as exc:
                        dest.unlink(missing_ok=True)
                        results.append({"github_id":ident,"module":module,
                                        "declaration":item["name"],
                                        "export":"failure","reason":str(exc)[:600]})
                        continue
                manifests.append({
                    "github_id":ident,"full_name":checkout["full_name"],
                    "commit":revision,"module":module,
                    "declaration":item["name"],"path":str(dest),
                    "checkout":checkout["checkout"],
                    "authority":"native-lean4export-unchecked-by-this-runner"})
    return results,manifests

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--checkouts",type=Path,required=True)
    p.add_argument("--enumerator",type=Path,default=Path("scripts/JMDWorldEnumerate.lean"))
    p.add_argument("--max-modules",type=int,default=4)
    p.add_argument("--export-per-module",type=int,default=0)
    p.add_argument("--export-root",type=Path)
    p.add_argument("--output-manifest",type=Path)
    p.add_argument("--allow-execute-lean",action="store_true")
    p.add_argument("--refresh",action="store_true")
    args=p.parse_args(argv)
    if not args.allow_execute_lean:
        p.error("Explicit --allow-execute-lean required; third-party code may execute")
    if args.max_modules<1 or args.export_per_module<0:
        p.error("Invalid batch limits")
    if args.export_per_module and (not args.export_root or not args.output_manifest):
        p.error("Export output root and manifest required when exporting")
    if not args.checkouts.is_file():
        p.error("Missing pinned checkout manifest")
    checkouts=[json.loads(line) for line in args.checkouts.read_text(
        encoding="utf-8").splitlines() if line.strip()]
    conn=connect(args.database)
    try:
        ensure_schema(conn)
        report,exports=run_batch(conn,checkouts,args.enumerator,
            max_modules=args.max_modules,export_per_module=args.export_per_module,
            export_root=args.export_root,refresh=args.refresh)
        if args.output_manifest:
            args.output_manifest.parent.mkdir(parents=True,exist_ok=True)
            args.output_manifest.write_text("".join(
                json.dumps(x,sort_keys=True)+"\n" for x in exports))
        print(json.dumps({"module_runs":report,
                          "native_export_manifest_records":len(exports),
                          "tool":"pinned Lean module data, not source regex",
                          "theorem_equivalences_proved":0},sort_keys=True,indent=2))
    finally:
        conn.close()

if __name__=="__main__":
    main()
