"""Single AST world scheduler and structural candidate search regressions."""
import json
import pathlib
import sqlite3
import sys
import tempfile
import unittest
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import build_jmd_lean_ast_world as world
import query_jmd_lean_ast_world as query

def export_content():
    rows=[
     {"meta":{"format":{"version":"3.1.0"},"lean":{"githash":"c"*40},
              "exporter":{"version":"3.1.0"}}},
     {"in":1,"str":{"pre":0,"str":"Nat"}},
     {"in":2,"str":{"pre":1,"str":"succ"}},
     {"in":3,"str":{"pre":0,"str":"Donor"}},
     {"in":4,"str":{"pre":3,"str":"f"}},
     {"ie":0,"sort":0},
     {"ie":1,"const":{"name":2,"us":[]}},
     {"ie":2,"forallE":{"name":4,"type":1,"body":0,
                        "binderInfo":"default"}},
     {"thm":{"name":4,"type":2,"value":1}}
    ]
    return "".join(json.dumps(x)+"\n" for x in rows)

class QueryWorldTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=pathlib.Path(self.temp.name)
        path=self.root/"world.sqlite3"
        sqlite3.connect(path).close()
        self.conn=world.connect(path)
        self.addCleanup(self.conn.close)
        self.csv=self.root/"repositories.csv"
        self.csv.write_text("github_id,full_name,default_branch,language\n"
           "3,lean/alfa,main,Lean\n4,lean/beta,main,Lean\n")
        self.star=self.root/"star.csv"
        self.star.write_text("github_id,full_name,language\n4,lean/beta,Lean\n")
        with self.conn: world.import_repositories(self.conn,self.csv,"unit",self.star)
        self.data=self.root/"native.ndjson"
        self.data.write_text(export_content())

    def test_starred_first_and_existing_ast_skipped(self):
        rows=query.queue(self.conn)
        self.assertEqual([r["github_id"] for r in rows],[4,3])
        self.assertTrue(all(r["next_action"]=="acquire-pinned-local-git-source"
                            for r in rows))
        self.assertTrue(all(not r["establishes_proof"] for r in rows))
        with self.conn:
            world.import_export(self.conn,{"github_id":4,"full_name":"lean/beta",
                                 "commit":"a"*40,"module":"Donor",
                                 "path":str(self.data)})
        rows=query.queue(self.conn)
        self.assertEqual([r["github_id"] for r in rows],[4,3])
        self.assertEqual(rows[0]["next_action"],
                         "expand-native-lean4export-coverage")

    def test_shared_native_ast_fingerprint_is_only_candidate(self):
        with self.conn:
            for ident,name in ((3,"lean/alfa"),(4,"lean/beta")):
                world.import_export(self.conn,{"github_id":ident,"full_name":name,
                     "commit":"a"*40,"module":"Donor","path":str(self.data)})
        groups=query.equivalent_type_candidates(self.conn)
        self.assertEqual(len(groups),1)
        self.assertEqual(len(groups[0]["candidates"]),2)
        self.assertFalse(groups[0]["establishes_equivalence"])

    def test_reference_relatedness_is_nonproof(self):
        with self.conn:
            world.import_export(self.conn,{"github_id":3,"full_name":"lean/alfa",
                                 "commit":"a"*40,"module":"Donor",
                                 "path":str(self.data)})
        rows=query.related_constants(self.conn,"Nat.succ")
        self.assertTrue(rows)
        self.assertTrue(all(r["establishes_proof"] is False for r in rows))

if __name__=="__main__":
    unittest.main()
