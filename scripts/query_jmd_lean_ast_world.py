#!/usr/bin/env python3
"""Deterministic intake queue and structural query over one Lean AST world.

This reads the existing .dashi/repository.sqlite3 tables created by
build_jmd_lean_ast_world.py. A structural hash or dependency neighbour is
a *candidate* only. There is no LLM, network call, agent, or proof promotion.

Queue order: JMD-starred projects first, then projects with source ready,
then global-corpus metadata. Explicit failures remain residuals.
"""
from __future__ import annotations
import argparse
import json
import sqlite3
from pathlib import Path

from build_jmd_lean_ast_world import connect, report

def queue(conn,limit=0):
    sql="""SELECT github_id,full_name,default_branch,starred,global_discovered,stage
       FROM jmd_lean_world_repositories
       ORDER BY starred DESC,
         CASE stage WHEN 'source-inventory' THEN 0
                    WHEN 'exported-ast' THEN 1 ELSE 2 END,
         github_id"""
    result=[]
    for ident,name,branch,star,global_seen,stage in conn.execute(sql):
        result.append({
            "github_id":ident,"repository":name,
            "default_branch_at_harvest":branch,
            "jmd_starred":bool(star),"global_corpus":bool(global_seen),
            "stage":stage,
            "next_action":("expand-native-lean4export-coverage" if stage=="exported-ast"
                           else "native-lean4export" if stage=="source-inventory"
                           else "acquire-pinned-local-git-source"),
            "establishes_proof":False,
            "authority":"discovery-work-queue",
        })
        if limit and len(result)>=limit:
            break
    return result

def equivalent_type_candidates(conn,limit=30):
    """Exact AST fingerprint is not necessarily definitional equality."""
    hashes=conn.execute("""SELECT d.type_fingerprint,e.lean_revision,
            COUNT(DISTINCT e.github_id) AS repositories,
            COUNT(*) AS declarations
       FROM jmd_lean_world_declarations d
       JOIN jmd_lean_world_exports e ON e.export_id=d.export_id
       GROUP BY d.type_fingerprint,e.lean_revision
       HAVING COUNT(DISTINCT e.github_id)>1
       ORDER BY repositories DESC,declarations DESC,d.type_fingerprint LIMIT ?""",
       (limit,)).fetchall()
    return [{
        "type_fingerprint":h,"lean_revision":lean_revision,
        "distinct_repositories":n,"declarations":count,
        "candidates":[{
            "repository":repo,"source_commit":rev,"module":module,
            "declaration":name,"kind":kind,"source_export":sha,
        } for repo,rev,module,name,kind,sha in conn.execute(
          """SELECT r.full_name,e.source_commit,e.module,d.name,d.kind,e.ndjson_sha256
             FROM jmd_lean_world_declarations d
             JOIN jmd_lean_world_exports e ON e.export_id=d.export_id
             JOIN jmd_lean_world_repositories r ON r.github_id=e.github_id
             WHERE d.type_fingerprint=? AND e.lean_revision=?
             ORDER BY e.github_id,e.source_commit,e.module,d.name LIMIT 100""",
             (h,lean_revision))
        ],"authority":"structural-candidate-only",
        "establishes_equivalence":False
    } for h,lean_revision,n,count in hashes]

def related_constants(conn,constant,limit=50):
    sql="""SELECT r.full_name,e.source_commit,e.module,ref.declaration,
             ref.relation,ref.referenced_constant
        FROM jmd_lean_world_refs ref
        JOIN jmd_lean_world_exports e ON e.export_id=ref.export_id
        JOIN jmd_lean_world_repositories r ON r.github_id=e.github_id
        WHERE ref.referenced_constant=? OR ref.declaration=?
        ORDER BY r.full_name,e.source_commit,e.module,ref.declaration LIMIT ?"""
    return [
        {"repository":repo,"source_commit":rev,"module":module,
         "declaration":decl,"relation":kind,"reference":ref,
         "authority":"dependency-neighbour-only","establishes_proof":False}
        for repo,rev,module,decl,kind,ref in conn.execute(sql,
            (constant,constant,limit))
    ]

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--queue",type=Path,help="Write pending repository tasks as JSONL")
    p.add_argument("--same-type-candidates",type=Path)
    p.add_argument("--related",type=str,help="Native constant name to find reference neighbours")
    p.add_argument("--limit",type=int,default=100)
    args=p.parse_args(argv)
    if args.limit<0:
        p.error("Cannot use a negative limit")
    conn=connect(args.database)
    try:
        info=report(conn)
        if args.queue:
            tasks=queue(conn,args.limit)
            args.queue.parent.mkdir(parents=True,exist_ok=True)
            args.queue.write_text("".join(json.dumps(x,sort_keys=True)+"\n" for x in tasks))
            info["queue_written"]=len(tasks)
            info["queue_path"]=str(args.queue)
        if args.same_type_candidates:
            matches=equivalent_type_candidates(conn,args.limit or 100)
            args.same_type_candidates.parent.mkdir(parents=True,exist_ok=True)
            args.same_type_candidates.write_text(
                json.dumps(matches,indent=2,sort_keys=True)+"\n")
            info["same_type_candidate_groups"]=len(matches)
        if args.related:
            info["dependency_neighbours"]=related_constants(conn,args.related,
                                                           args.limit or 100)
        print(json.dumps(info,indent=2,sort_keys=True))
    finally:
        conn.close()

if __name__=="__main__":
    main()
