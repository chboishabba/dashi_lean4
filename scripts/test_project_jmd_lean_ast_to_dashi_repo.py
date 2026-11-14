"""Offline original-schema projection tests: no Agda owner overwritten."""
import importlib.util
import json
import pathlib
import sqlite3
import sys
import tempfile
import unittest
import hashlib

DIR=pathlib.Path(__file__).parent
sys.path.insert(0,str(DIR))
import build_jmd_lean_ast_world as world
import project_jmd_lean_ast_to_dashi_repo as project

class ProjectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=pathlib.Path(self.tmp.name)
        path=self.root/"canonical.sqlite3"
        sqlite3.connect(path).close()
        self.conn=world.connect(path)
        self.addCleanup(self.conn.close)
        self.conn.executescript("""
        CREATE TABLE repo_files(
          path TEXT PRIMARY KEY,language TEXT NOT NULL,module TEXT,
          mtime_ns INTEGER NOT NULL,size INTEGER NOT NULL,
          sha256 TEXT NOT NULL,indexed_at INTEGER NOT NULL);
        CREATE TABLE repo_symbols(
          symbol_id TEXT PRIMARY KEY,name TEXT NOT NULL,kind TEXT NOT NULL,
          language TEXT NOT NULL,module TEXT,
          file TEXT NOT NULL REFERENCES repo_files(path),
          line_start INTEGER NOT NULL,line_end INTEGER NOT NULL,
          promotion TEXT NOT NULL,authority TEXT NOT NULL,
          truth TEXT NOT NULL,source TEXT NOT NULL);
        CREATE TABLE repo_symbol_signatures(
          symbol_id TEXT PRIMARY KEY REFERENCES repo_symbols(symbol_id),
          signature TEXT NOT NULL, normalized_signature TEXT NOT NULL,
          signature_sha256 TEXT NOT NULL,body_sha256 TEXT NOT NULL);
        CREATE TABLE repo_refs(
          from_symbol TEXT NOT NULL,to_symbol TEXT NOT NULL,
          ref_kind TEXT NOT NULL,file TEXT NOT NULL,
          line INTEGER NOT NULL,snippet TEXT NOT NULL);
        CREATE TABLE repo_symbol_tags(
          symbol_id TEXT NOT NULL REFERENCES repo_symbols(symbol_id),
          tag TEXT NOT NULL,PRIMARY KEY(symbol_id,tag));
        INSERT INTO repo_files VALUES ('DASHI/Original.agda','agda','DASHI.Original',
                                      0,0,'hash',0);
        INSERT INTO repo_symbols VALUES ('DASHI.Original.foo','foo','function',
          'agda','DASHI.Original','DASHI/Original.agda',1,2,
          'golden','agda-kernel','source-checked','agda');
        """)
        self.csv=self.root/"repos.csv"
        self.csv.write_text(
            "github_id,full_name,default_branch,language\n"
            "17,donor/lean-lib,main,Lean\n")
        self.export=self.root/"one.ndjson"
        entries=[
          {"meta":{"format":{"version":"3.1.0"},
                   "lean":{"version":"4.33.1","githash":"b"*40},
                   "exporter":{"version":"3.1.0"}}},
          {"in":1,"str":{"pre":0,"str":"External"}},
          {"in":2,"str":{"pre":1,"str":"foo"}},
          {"ie":0,"sort":0},
          {"ie":1,"const":{"name":2,"us":[]}},
          {"ie":2,"forallE":{"name":2,"binderInfo":"default","type":1,"body":0}},
          {"thm":{"name":2,"type":2,"value":0}}
        ]
        self.export.write_text("".join(json.dumps(x)+"\n" for x in entries))
        with self.conn:
            world.import_repositories(self.conn,self.csv,"test")
            world.import_export(self.conn,{"github_id":17,"full_name":"donor/lean-lib",
                "commit":"a"*40,"module":"External","path":str(self.export)})

    def test_native_symbol_projection_candidate_only(self):
        with self.conn:
            self.assertEqual(project.projection(self.conn),1)
        row=self.conn.execute("""SELECT language,promotion,authority,truth,file
           FROM repo_symbols WHERE symbol_id LIKE 'lean-export:%'""").fetchone()
        self.assertEqual(row[:4],
            ("lean","candidate-only","lean4export-ast-candidate","unknown"))
        self.assertTrue(row[4].startswith("jmd-lean-export://"))
        self.assertEqual(self.conn.execute(
            "SELECT authority FROM repo_symbols WHERE symbol_id='DASHI.Original.foo'"
        ).fetchone()[0],"agda-kernel")

    def test_idempotent_projection_and_source_hash(self):
        with self.conn:
            project.projection(self.conn)
            project.projection(self.conn)
        self.assertEqual(self.conn.execute(
            "SELECT COUNT(*) FROM repo_refs WHERE ref_kind='lean-export-type-ref'"
        ).fetchone()[0],1)
        row=self.conn.execute("""SELECT normalized_signature,signature_sha256
          FROM repo_symbol_signatures WHERE symbol_id LIKE 'lean-export:%'""").fetchone()
        self.assertEqual(hashlib.sha256(row[0].encode()).hexdigest(),row[1])

    def test_no_canonical_schema_no_projection(self):
        self.conn.execute("DROP TABLE repo_symbol_tags")
        with self.assertRaisesRegex(ValueError,"Canonical"):
            project.projection(self.conn)

if __name__=="__main__":
    unittest.main()
