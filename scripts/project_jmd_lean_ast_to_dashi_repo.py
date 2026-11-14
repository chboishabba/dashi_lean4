#!/usr/bin/env python3
"""Project native Lean AST declarations onto EXISTING dashi-repo discovery.

No shadow index. Source of truth remains jmd_lean_world_declarations plus
lean4export expression nodes in SAME SQLite database. This only enables
existing symbol, discover, and related-symbol queries.

A repo_files path prefixed jmd-lean-export:// is a VIRTUAL URI, never an
actual Agda source file or real line. All resulting relations are candidates.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from build_jmd_lean_ast_world import connect

MANDATORY={"repo_files","repo_symbols","repo_symbol_signatures","repo_refs",
           "repo_symbol_tags","jmd_lean_world_exports","jmd_lean_world_declarations"}
VIRTUAL="jmd-lean-export://"

def require_native(conn):
    tables={r[0] for r in conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table'")}
    missing=MANDATORY-tables
    if missing:
        raise ValueError("Canonical dashi-repo inventory missing: "+",".join(sorted(missing)))

def projection(conn,limit=0):
    require_native(conn)
    sql="""SELECT e.export_id,e.github_id,e.source_commit,e.module,
              e.ndjson_sha256,e.lean_revision,d.name,d.kind,
              d.type_fingerprint
      FROM jmd_lean_world_declarations d
      JOIN jmd_lean_world_exports e ON e.export_id=d.export_id
      ORDER BY e.github_id,e.source_commit,e.module,d.name"""
    if limit:
        sql+=" LIMIT "+str(limit)
    count=0
    for exp,ident,commit,module,blob,lean_rev,name,kind,fingerprint in conn.execute(sql):
        path=f"{VIRTUAL}{ident}/{commit}/{blob}/{module}"
        symbol=f"lean-export:{ident}:{commit}:{blob}:{name}"
        refs=sorted({r[0] for r in conn.execute(
          """SELECT referenced_constant FROM jmd_lean_world_refs
             WHERE export_id=? AND declaration=? AND relation='type'""",
          (exp,name))})
        # Discovery text is not a printed theorem type; the full native
        # AST is retained separately with exact source/exporter provenance.
        signature="lean-native-ast-fingerprint "+fingerprint+" refs ["+", ".join(refs)+"]"
        normalized=signature.lower()
        signature_sha=hashlib.sha256(normalized.encode("utf-8")).hexdigest()
        conn.execute("""INSERT INTO repo_files
           (path,language,module,mtime_ns,size,sha256,indexed_at)
           VALUES(?, 'lean-ast-export', ?, 0, 0, ?, 0)
           ON CONFLICT(path) DO UPDATE SET
             language=excluded.language,module=excluded.module,
             sha256=excluded.sha256""",(path,module,blob))
        conn.execute("""INSERT INTO repo_symbols(
            symbol_id,name,kind,language,module,file,line_start,line_end,
            promotion,authority,truth,source)
           VALUES(?,?,?,'lean',?,?,0,0,'candidate-only',
                  'lean4export-ast-candidate','unknown','external-lean-export')
           ON CONFLICT(symbol_id) DO UPDATE SET
             name=excluded.name,kind=excluded.kind,
             module=excluded.module,file=excluded.file,
             promotion='candidate-only',authority='lean4export-ast-candidate',
             truth='unknown',source='external-lean-export'""",
           (symbol,name.split(".")[-1],kind,module,path))
        # Structural fingerprint is only a candidate hash, not a kernel
        # definitional equality witness and not a string hash.
        conn.execute("""INSERT INTO repo_symbol_signatures
            (symbol_id,signature,normalized_signature,signature_sha256,body_sha256)
            VALUES(?,?,?,?,?)
            ON CONFLICT(symbol_id) DO UPDATE SET
              signature=excluded.signature,
              normalized_signature=excluded.normalized_signature,
              signature_sha256=excluded.signature_sha256,
              body_sha256=excluded.body_sha256""",
            (symbol,signature,normalized,signature_sha,""))
        conn.execute("DELETE FROM repo_refs WHERE from_symbol=? AND ref_kind='lean-export-type-ref'",
                     (symbol,))
        conn.executemany("""INSERT INTO repo_refs
             (from_symbol,to_symbol,ref_kind,file,line,snippet)
             VALUES(?,?,'lean-export-type-ref',?,0,?)""",
             ((symbol,"lean-name:"+ref,path,ref) for ref in refs))
        for tag in ("jmd-lean-world","external-lean-ast","candidate-only",
                    f"github-id:{ident}",f"lean-revision:{lean_rev}"):
            conn.execute("INSERT OR IGNORE INTO repo_symbol_tags VALUES(?,?)",
                         (symbol,tag))
        count+=1
    return count

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--limit",type=int,default=0)
    args=p.parse_args(argv)
    if args.limit<0:
        p.error("Negative limit")
    conn=connect(args.database)
    try:
        with conn:
            count=projection(conn,limit=args.limit)
        print(json.dumps({"projected_lean_declarations":count,
          "authority":"candidate-only; no theorem/Agda promotion",
          "source_tables":"jmd_lean_world_declarations/ast",
          "discovery_tables":"repo_symbols/repo_symbol_signatures/repo_refs"},
          sort_keys=True,indent=2))
    finally:
        conn.close()
if __name__=="__main__":
    main()
