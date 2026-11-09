"""Executable offline regressions for the unified Lean AST world."""
import importlib.util
import json
import pathlib
import sqlite3
import tempfile
import unittest

SCRIPT=pathlib.Path(__file__).with_name("build_jmd_lean_ast_world.py")
spec=importlib.util.spec_from_file_location("jmd_ast_world", SCRIPT)
world=importlib.util.module_from_spec(spec)
spec.loader.exec_module(world)

SHA="a"*40
LEAN="b"*40

def native_export(theorem="Pkg.foo", extra=False):
    name_parts=theorem.split(".")
    rows=[{"meta":{"format":{"version":"3.1.0"},
                   "exporter":{"version":"3.1.0"},
                   "lean":{"githash":LEAN,"version":"4.33.1"}}}]
    parent=0
    for i,part in enumerate(name_parts,1):
        rows.append({"in":i,"str":{"pre":parent,"str":part}})
        parent=i
    rows.extend([
        {"ie":0,"sort":0},
        {"ie":1,"const":{"name":parent,"us":[]}},
        {"ie":2,"forallE":{"binderInfo":"default","body":0,
                          "name":parent,"type":1}},
        {"thm":{"name":parent,"type":2,"value":0,"all":[parent],
                "levelParams":[]}},
    ])
    if extra:
        rows.append({"ie":3,"app":{"fn":1,"arg":0}})
    return rows

class WorldTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root=pathlib.Path(self.tmp.name)
        self.db=root/"existing-dashi.sqlite3"
        sqlite3.connect(self.db).close()
        self.con=world.connect(self.db)
        self.addCleanup(self.con.close)
        self.csv=root/"repos.csv"
        self.csv.write_text(
            "github_id,full_name,default_branch,language\n"
            "9,owner/repository,main,Lean\n"
            "10,other/repository,main,Lean\n",encoding="utf-8")
        self.export=root/"source.ndjson"
        self.export.write_text(
            "".join(json.dumps(x)+"\n" for x in native_export()),
            encoding="utf-8")

    def row(self):
        return {"github_id":9,"full_name":"owner/repository",
                "commit":SHA,"module":"Pkg","path":str(self.export)}

    def setup_repos(self):
        with self.con:
            self.assertEqual(world.import_repositories(self.con,self.csv,"unit-test"),2)

    def test_metadata_is_not_ast(self):
        self.setup_repos()
        r=world.report(self.con)
        self.assertEqual(r["repositories"],2)
        self.assertEqual(r["metadata_only_repositories"],2)
        self.assertEqual(r["declarations"],0)

    def test_global_and_starred_union_by_numeric_identity(self):
        self.stars=pathlib.Path(self.tmp.name)/"stars.csv"
        self.stars.write_text(
            "github_id,full_name,default_branch,language\n"
            "9,owner/repository,main,Lean\n"
            "11,starred/only,main,Lean\n")
        with self.con:
            self.assertEqual(world.import_repositories(self.con,self.csv,
                         "unit-test",self.stars),2)
        result=world.report(self.con)
        self.assertEqual(result["repositories"],3)
        self.assertEqual(result["global_discovered"],2)
        self.assertEqual(result["starred_lean"],2)
        self.assertEqual(result["starred_only"],1)
        # Repeat without the optional star file; provenance must not vanish.
        with self.con: world.import_repositories(self.con,self.csv,"unit-test")
        self.assertEqual(world.report(self.con)["starred_lean"],2)

    def test_native_ast_ingest_is_idempotent(self):
        self.setup_repos()
        with self.con:
            self.assertEqual(world.import_export(self.con,self.row()),1)
            self.assertEqual(world.import_export(self.con,self.row()),0)
        r=world.report(self.con)
        self.assertEqual(r["native_ast_exports"],1)
        self.assertEqual(r["native_ast_nodes"],3)
        self.assertEqual(r["declarations"],1)
        self.assertEqual(r["metadata_only_repositories"],1)
        self.assertGreaterEqual(r["dependency_edges"],1)

    def test_source_identity_must_match_manifest(self):
        self.setup_repos()
        r=self.row()
        r["full_name"]="impostor/repository"
        with self.assertRaisesRegex(ValueError,"not admitted"):
            world.import_export(self.con,r)

    def test_absent_source_commit_rejected(self):
        self.setup_repos()
        r=self.row()
        r["commit"]="main"
        with self.assertRaisesRegex(ValueError,"pinned"):
            world.import_export(self.con,r)

    def test_broken_expression_reference_rejected(self):
        self.setup_repos()
        obj=native_export()
        obj[-1]["thm"]["type"]=999
        self.export.write_text("".join(json.dumps(x)+"\n" for x in obj))
        with self.assertRaisesRegex(ValueError,"not in exporter AST"):
            with self.con: world.import_export(self.con,self.row())

    def test_structural_digest_ignores_allocation_index(self):
        a={0:{"sort":0},1:{"app":{"fn":0,"arg":0}}}
        b={7:{"sort":0},9:{"app":{"fn":7,"arg":7}}}
        self.assertEqual(world.expression_fingerprint(1,a,{}),
                         world.expression_fingerprint(9,b,{}))

    def test_no_unsupported_export_revision(self):
        self.setup_repos()
        obj=native_export()
        obj[0]["meta"]["format"]["version"]="2.0"
        self.export.write_text("".join(json.dumps(x)+"\n" for x in obj))
        with self.assertRaisesRegex(ValueError,"Unsupported"):
            world.import_export(self.con,self.row())

    def test_no_theorem_authority_from_matching_hash(self):
        self.setup_repos()
        with self.con: world.import_export(self.con,self.row())
        r=world.report(self.con)
        self.assertIn("no theorem equivalence",r["authority"])
        self.assertEqual(self.con.execute(
            "SELECT count(*) FROM jmd_lean_world_declarations").fetchone()[0],1)

    def test_reject_duplicate_repo_identity(self):
        self.csv.write_text(
            "github_id,full_name,default_branch,language\n"
            "9,owner/repository,main,Lean\n9,owner/repository,main,Lean\n")
        with self.assertRaisesRegex(ValueError,"Duplicate"):
            with self.con: world.import_repositories(self.con,self.csv,"unit-test")

if __name__=="__main__":
    unittest.main()
