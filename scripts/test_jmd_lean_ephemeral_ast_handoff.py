"""Offline native AST handoff regression and false-proof controls."""
import copy,hashlib,importlib.util
from pathlib import Path
import tempfile,unittest
MODULE=Path(__file__).with_name("jmd_lean_ephemeral_ast_handoff.py")
spec=importlib.util.spec_from_file_location("jmd_handoff",MODULE)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class TestBridge(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.payload=b'{"meta":{"format":{"version":"3.1.0"}}}\n{"thm":{"type":1}}\n'
        digest=hashlib.sha256(self.payload).hexdigest()
        self.path=self.root/(digest+".ndjson")
        self.path.write_bytes(self.payload)
        self.sources=[{"path":"Target.lean","sha256":"b"*64}]
        native={"status":"native-v3-exported-unadmitted",
            "repository":"u/r","revision":"a"*40,"module":"Target",
            "source_closure":self.sources,"artifact_sha256":digest,
            "artifact_path":str(self.path),
            "validation":{"syntax_v3_checked":True,"export_sha256":digest}}
        self.row={"status":"lean-module-checked","declaration_ast_exported":True,
            "repository":"u/r","revision":"a"*40,"target":"Target.lean",
            "source_closure":self.sources,"native_export":native}

    def test_handoff_only(self):
        row=m.handoff(self.row,17)
        self.assertEqual(row["github_id"],17)
        self.assertNotIn("kernel_proof_certified",row)

    def test_failed_worker(self):
        row=copy.deepcopy(self.row)
        row["status"]="incomplete"
        with self.assertRaises(m.HandoffError):m.handoff(row,17)

    def test_mismatched_origin(self):
        row=copy.deepcopy(self.row)
        row["native_export"]["revision"]="c"*40
        with self.assertRaises(m.HandoffError):m.handoff(row,17)

    def test_mismatched_source(self):
        row=copy.deepcopy(self.row)
        row["native_export"]["source_closure"]=[]
        with self.assertRaises(m.HandoffError):m.handoff(row,17)

    def test_changed_artifact(self):
        self.path.write_bytes(b"tampered")
        with self.assertRaises(m.HandoffError):m.handoff(self.row,17)

    def test_invalid_repo_id(self):
        with self.assertRaises(m.HandoffError):m.handoff(self.row,0)

if __name__=="__main__":unittest.main()
