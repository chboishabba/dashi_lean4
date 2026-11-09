#!/usr/bin/env python3
"""Unify JMD's harvested Lean repositories and native lean4export ASTs.

One durable world in the existing .dashi/repository.sqlite3. This script
never compiles, clones, fetches, or publishes third-party code. Repository
inventory is NOT AST coverage; AST evidence requires pinned lean4export v3
NDJSON containing checked environment constants. No LLM is needed.

Exports JSONL manifest rows:
  {"github_id":123,"full_name":"owner/repo","commit":"40hex",
   "module":"Pkg.Algebra","path":"/absolute/pinned-export.ndjson"}
Run: python scripts/build_jmd_lean_ast_world.py --database ... --repositories
  docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv --exports exports.jsonl

Each AST node retains its exact exporter ID and raw serialized constructor,
with source, Git revision, Lean revision, module, declaration, type root and
value root. Structural fingerprints are only candidates, not theorem identity.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
import re
import sqlite3
from pathlib import Path

SHA = re.compile(r"[a-f0-9]{40}\Z")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
DECL_KINDS = ("thm", "def", "opaque", "axiom", "ind", "quot", "ctor", "rec")
ROOT_KEYS = ("type", "value")
MAX_EXPORT_BYTES = 200_000_000

def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

def digest(obj):
    return hashlib.sha256(canonical(obj).encode("utf-8")).hexdigest()

def connect(path: Path):
    if not path.is_file():
        raise FileNotFoundError("Run dashi-repo index to create the canonical SQLite world first")
    conn = sqlite3.connect(str(path))
    conn.execute("PRAGMA foreign_keys=ON")
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS jmd_lean_world_repositories (
        github_id INTEGER PRIMARY KEY, full_name TEXT NOT NULL,
        default_branch TEXT NOT NULL, primary_language TEXT NOT NULL,
        starred INTEGER NOT NULL DEFAULT 0 CHECK(starred IN (0,1)),
        global_discovered INTEGER NOT NULL DEFAULT 0 CHECK(global_discovered IN (0,1)),
        corpus_snapshot TEXT NOT NULL, stage TEXT NOT NULL DEFAULT 'metadata'
          CHECK(stage IN ('metadata','exported-ast'))
    );
    CREATE TABLE IF NOT EXISTS jmd_lean_world_exports (
        export_id INTEGER PRIMARY KEY,
        github_id INTEGER NOT NULL REFERENCES jmd_lean_world_repositories(github_id),
        source_commit TEXT NOT NULL, module TEXT NOT NULL,
        ndjson_sha256 TEXT NOT NULL, exporter_version TEXT NOT NULL,
        lean_revision TEXT NOT NULL,
        UNIQUE(github_id,source_commit,module,ndjson_sha256)
    );
    CREATE TABLE IF NOT EXISTS jmd_lean_world_names (
        export_id INTEGER NOT NULL REFERENCES jmd_lean_world_exports(export_id)
          ON DELETE CASCADE,
        name_id INTEGER NOT NULL, qualified TEXT NOT NULL,
        PRIMARY KEY(export_id,name_id)
    );
    CREATE TABLE IF NOT EXISTS jmd_lean_world_ast (
        export_id INTEGER NOT NULL REFERENCES jmd_lean_world_exports(export_id)
          ON DELETE CASCADE,
        expr_id INTEGER NOT NULL, node_json TEXT NOT NULL,
        PRIMARY KEY(export_id,expr_id)
    );
    CREATE TABLE IF NOT EXISTS jmd_lean_world_declarations (
        export_id INTEGER NOT NULL REFERENCES jmd_lean_world_exports(export_id)
          ON DELETE CASCADE,
        name TEXT NOT NULL, kind TEXT NOT NULL, type_expr INTEGER NOT NULL,
        value_expr INTEGER, type_fingerprint TEXT NOT NULL,
        source_authority TEXT NOT NULL CHECK(source_authority='exporter-ast'),
        PRIMARY KEY(export_id,name)
    );
    CREATE TABLE IF NOT EXISTS jmd_lean_world_refs (
        export_id INTEGER NOT NULL REFERENCES jmd_lean_world_exports(export_id)
          ON DELETE CASCADE,
        declaration TEXT NOT NULL, referenced_constant TEXT NOT NULL,
        relation TEXT NOT NULL CHECK(relation IN ('type','value')),
        PRIMARY KEY(export_id,declaration,referenced_constant,relation)
    );
    CREATE INDEX IF NOT EXISTS idx_jmd_lean_world_type
        ON jmd_lean_world_declarations(type_fingerprint);
    CREATE INDEX IF NOT EXISTS idx_jmd_lean_world_refs_target
        ON jmd_lean_world_refs(referenced_constant);
    """)
    return conn

def import_repositories(conn, csv_path, snapshot, starred_path=None):
    star_rows={}
    if starred_path:
        with Path(starred_path).open(newline="", encoding="utf8") as fh:
            reader=csv.DictReader(fh)
            if not reader.fieldnames or not {"github_id","full_name"} <= set(reader.fieldnames):
                raise ValueError("Star inventory must have GitHub numeric identity and name")
            for row in reader:
                ident=int(row["github_id"])
                name=row["full_name"].strip()
                if ident<=0 or ident in star_rows or len(name.split("/"))!=2:
                    raise ValueError("Duplicate/invalid starred repository")
                if row.get("language","Lean") != "Lean":
                    raise ValueError("Pass only the primary-language Lean starred export")
                star_rows[ident]=row
    count=0
    seen=set()
    with Path(csv_path).open(newline="", encoding="utf8") as fh:
        reader=csv.DictReader(fh)
        if not reader.fieldnames or not {"github_id","full_name","default_branch"} <= set(reader.fieldnames):
            raise ValueError("Missing canonical repository identity columns")
        for r in reader:
            ident=int(r["github_id"])
            name=r["full_name"].strip()
            if ident<=0 or ident in seen or len(name.split("/"))!=2:
                raise ValueError("Duplicate or invalid GitHub numeric repository identity")
            seen.add(ident)
            prior=conn.execute("SELECT full_name FROM jmd_lean_world_repositories WHERE github_id=?",
                               (ident,)).fetchone()
            if prior and prior[0].casefold()!=name.casefold():
                # Record renames only with a separate authenticated rename receipt.
                raise ValueError("Repository numeric identity has changed name: "+str(ident))
            conn.execute("""INSERT INTO jmd_lean_world_repositories
                (github_id,full_name,default_branch,primary_language,starred,global_discovered,corpus_snapshot)
                VALUES(?,?,?,?,?,?,?)
                ON CONFLICT(github_id) DO UPDATE SET
                  default_branch=excluded.default_branch,
                  primary_language=excluded.primary_language,
                  starred=excluded.starred,
                  global_discovered=1,corpus_snapshot=excluded.corpus_snapshot""",
                (ident,name,r["default_branch"],r.get("language",""),int(ident in star_rows),1,snapshot))
            count+=1
    # Preserve starred Lean repositories missed by GitHub's search snapshot.
    # Numeric ID is the primary key; conflicting names require review.
    for ident,row in sorted(star_rows.items()):
        if ident in seen:
            if row["full_name"].casefold()!=conn.execute(
                "SELECT full_name FROM jmd_lean_world_repositories WHERE github_id=?",
                (ident,)).fetchone()[0].casefold():
                raise ValueError("Star/global repository identity disagrees")
            continue
        conn.execute("""INSERT INTO jmd_lean_world_repositories
          (github_id,full_name,default_branch,primary_language,
           starred,global_discovered,corpus_snapshot)
          VALUES(?,?,?,?,1,0,?)
          ON CONFLICT(github_id) DO UPDATE SET starred=1""",
          (ident,row["full_name"],row.get("default_branch",""),"Lean",snapshot))
    return count

def nodes_from_export(path):
    path=Path(path)
    if path.stat().st_size>MAX_EXPORT_BYTES:
        raise ValueError("Export exceeds per-artifact memory/size policy")
    names={0:""}
    exprs={}
    decls=[]
    meta=None
    content_sha=hashlib.sha256()
    with path.open("rb") as stream:
        for n,line in enumerate(stream,1):
            content_sha.update(line)
            if len(line)>8_000_000:
                raise ValueError("Oversized individual export line")
            try:
                obj=json.loads(line)
            except (ValueError, UnicodeDecodeError) as exc:
                raise ValueError(f"Malformed lean4export NDJSON at {path}:{n}") from exc
            if not isinstance(obj,dict):
                raise ValueError("Export entry must be an object")
            if meta is None and n>1:
                raise ValueError("Exporter metadata must be first")
            if "meta" in obj:
                if meta is not None or n!=1:
                    raise ValueError("Duplicate or misplaced exporter metadata")
                meta=obj["meta"]
                if not isinstance(meta,dict) or not str(meta.get("format",{}).get("version","")).startswith("3."):
                    raise ValueError("Unsupported lean4export serialization version")
            elif "in" in obj:
                idx=int(obj["in"])
                info=obj.get("str",obj.get("num"))
                if idx<=0 or idx in names or not isinstance(info,dict):
                    raise ValueError("Invalid name-trie node")
                parent=int(info["pre"])
                if parent not in names:
                    raise ValueError("Unresolved name trie parent")
                segment=str(info.get("str",info.get("num","")))
                names[idx]=(names[parent]+"." if names[parent] else "")+segment
            elif "ie" in obj:
                idx=int(obj["ie"])
                if idx<0 or idx in exprs:
                    raise ValueError("Duplicate/negative expression index")
                exprs[idx]={k:v for k,v in obj.items() if k!="ie"}
            else:
                kinds=[k for k in DECL_KINDS if k in obj]
                if len(kinds)==1:
                    decls.append((kinds[0],obj[kinds[0]]))
                # Other Lean levels/metadata are retained by the export file
                # SHA but are not expression-index nodes.
    if meta is None:
        raise ValueError("No lean4export metadata")
    return {"names":names,"exprs":exprs,"decls":decls,"meta":meta,
            "sha":content_sha.hexdigest()}

def _expr_children(node):
    for kind,data in node.items():
        if not isinstance(data,dict):
            continue
        for field in ("type","body","fn","arg","value","expr","proof","motive"):
            if field in data and type(data[field]) is int:
                yield data[field]

def reachable(root, exprs, names):
    """Non-recursive walk over the native Lean expression DAG."""
    pending=[root]
    seen=set()
    consts=set()
    while pending:
        idx=pending.pop()
        if idx in seen:
            continue
        if idx not in exprs:
            raise ValueError("Expression reference not in exporter AST: "+str(idx))
        seen.add(idx)
        node=exprs[idx]
        for kind,data in node.items():
            if kind=="const" and isinstance(data,dict):
                name=int(data["name"])
                if name not in names:
                    raise ValueError("Unresolved Lean constant name")
                consts.add(names[name])
        pending.extend(_expr_children(node))
    return seen,consts

def expression_fingerprint(root, exprs, names):
    """Bottom-up bounded DAG digest, not an exponentially expanded tree.

    Node IDs and binder variable names are intentionally omitted; binder info,
    constants, universe arguments and constructor roles are preserved.
    This is a *candidate fingerprint*, never a verified equivalence.
    """
    todo=[(root,False)]
    memo={}
    active=set()
    while todo:
        idx,done=todo.pop()
        if idx in memo:
            continue
        if idx not in exprs:
            raise ValueError("Expression reference absent")
        if not done:
            if idx in active:
                raise ValueError("Cyclic native expression graph")
            active.add(idx)
            todo.append((idx,True))
            for child in _expr_children(exprs[idx]):
                if child not in memo:
                    todo.append((child,False))
            continue
        obj=exprs[idx]
        form={}
        for kind,data in sorted(obj.items()):
            if not isinstance(data,dict):
                form[kind]=data
                continue
            fields={}
            for key,value in sorted(data.items()):
                if key=="name" and kind=="const":
                    fields[key]=names[int(value)]
                elif key=="name" and kind in ("lam","forallE","letE"):
                    fields[key]="<bound>"
                elif key in ("type","body","fn","arg","value","expr","proof","motive") and type(value) is int:
                    fields[key]=memo[value]
                else:
                    fields[key]=value
            form[kind]=fields
        memo[idx]=digest(form)
        active.remove(idx)
    return memo[root]

def import_export(conn, row):
    repo_id=int(row["github_id"])
    existing=conn.execute("SELECT full_name FROM jmd_lean_world_repositories WHERE github_id=?",
                          (repo_id,)).fetchone()
    if not existing or existing[0].casefold()!=str(row["full_name"]).casefold():
        raise ValueError("Lean export owner not admitted by repository inventory")
    commit=str(row["commit"])
    module=str(row["module"])
    if not SHA.fullmatch(commit) or not IDENT.fullmatch(module):
        raise ValueError("Source commit/module must be pinned and unambiguous")
    ast=nodes_from_export(Path(row["path"]))
    source=ast["meta"].get("lean",{})
    exporter=ast["meta"].get("exporter",{})
    lean_rev=str(source.get("githash",""))
    if not SHA.fullmatch(lean_rev):
        raise ValueError("Missing pinned Lean compiler revision")
    prior=conn.execute("""SELECT export_id FROM jmd_lean_world_exports
       WHERE github_id=? AND source_commit=? AND module=? AND ndjson_sha256=?""",
       (repo_id,commit,module,ast["sha"])).fetchone()
    if prior:
        return 0
    conn.execute("""INSERT INTO jmd_lean_world_exports
       (github_id,source_commit,module,ndjson_sha256,exporter_version,lean_revision)
       VALUES(?,?,?,?,?,?)""",
       (repo_id,commit,module,ast["sha"],str(exporter.get("version","")),lean_rev))
    export_id=conn.execute("SELECT last_insert_rowid()").fetchone()[0]
    conn.executemany("INSERT INTO jmd_lean_world_names VALUES(?,?,?)",
        ((export_id,i,name) for i,name in ast["names"].items()))
    conn.executemany("INSERT INTO jmd_lean_world_ast VALUES(?,?,?)",
        ((export_id,i,canonical(node)) for i,node in ast["exprs"].items()))
    for kind,decl in ast["decls"]:
        if not isinstance(decl,dict) or "name" not in decl or "type" not in decl:
            continue
        nameid=int(decl["name"])
        if nameid not in ast["names"]:
            raise ValueError("Declaration name not defined by native exporter")
        name=ast["names"][nameid]
        root=int(decl["type"])
        _,type_refs=reachable(root,ast["exprs"],ast["names"])
        value_root=decl.get("value")
        value_refs=set()
        if isinstance(value_root,int):
            _,value_refs=reachable(value_root,ast["exprs"],ast["names"])
        # Checked-environment AST fingerprint; candidate-only.
        conn.execute("""INSERT INTO jmd_lean_world_declarations
          VALUES(?,?,?,?,?,?,'exporter-ast')""",
          (export_id,name,kind,root,value_root,expression_fingerprint(root,ast["exprs"],ast["names"])))
        conn.executemany("INSERT OR IGNORE INTO jmd_lean_world_refs VALUES(?,?,?,?)",
          ((export_id,name,ref,"type") for ref in sorted(type_refs)))
        conn.executemany("INSERT OR IGNORE INTO jmd_lean_world_refs VALUES(?,?,?,?)",
          ((export_id,name,ref,"value") for ref in sorted(value_refs)))
    conn.execute("""UPDATE jmd_lean_world_repositories SET stage='exported-ast'
                    WHERE github_id=?""",(repo_id,))
    return 1

def report(conn):
    tables={"repositories":"jmd_lean_world_repositories",
            "native_ast_exports":"jmd_lean_world_exports",
            "native_ast_nodes":"jmd_lean_world_ast",
            "declarations":"jmd_lean_world_declarations",
            "dependency_edges":"jmd_lean_world_refs"}
    out={k:conn.execute("SELECT count(*) FROM "+v).fetchone()[0] for k,v in tables.items()}
    out["global_discovered"]=conn.execute(
        "SELECT count(*) FROM jmd_lean_world_repositories WHERE global_discovered=1").fetchone()[0]
    out["starred_lean"]=conn.execute(
        "SELECT count(*) FROM jmd_lean_world_repositories WHERE starred=1").fetchone()[0]
    out["starred_only"]=conn.execute(
        "SELECT count(*) FROM jmd_lean_world_repositories WHERE starred=1 AND global_discovered=0").fetchone()[0]
    out["metadata_only_repositories"]=conn.execute(
        "SELECT count(*) FROM jmd_lean_world_repositories WHERE stage='metadata'").fetchone()[0]
    out["authority"]="native Lean AST candidate index; no theorem equivalence or kernel proof inferred"
    out["llm_required"]=False
    return out

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--repositories",type=Path,required=True)
    p.add_argument("--stars",type=Path)
    p.add_argument("--exports",type=Path)
    p.add_argument("--snapshot",default="jmd-lean-global-2026-11-09")
    args=p.parse_args(argv)
    conn=connect(args.database)
    try:
        with conn:
            import_repositories(conn,args.repositories,args.snapshot,args.stars)
        if args.exports:
            with args.exports.open(encoding="utf8") as fh:
                for n,line in enumerate(fh,1):
                    if not line.strip():continue
                    row=json.loads(line)
                    with conn:
                        import_export(conn,row)
        print(json.dumps(report(conn),indent=2,sort_keys=True))
    finally:
        conn.close()
if __name__=="__main__":
    main()
