"""Regression and negative-control fixtures for the public corpus ingress audit."""
import importlib.util
import pathlib
import unittest

SCRIPT = pathlib.Path(__file__).with_name("audit_jmd_formal_corpus.py")
spec = importlib.util.spec_from_file_location("audit_jmd_formal_corpus", SCRIPT)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

def row(i, lang="Lean"):
    return {"github_id": str(i), "full_name": f"user/repo{i}",
            "html_url": f"https://github.com/user/repo{i}", "language": lang}

class FormalIngressTests(unittest.TestCase):
    def setUp(self):
        self.global_rows = {1: row(1), 3: row(3)}
        self.stars = {1: row(1), 2: row(2, "Python")}
        self.lean = {1: row(1)}
        self.gs = {"repository_count": 2, "partitions": 1, "query": "language:Lean"}
        self.ss = {"github_user": "jmikedupont2", "total_public_starred": 2,
                   "primary_language_lean": 1}
        self.cp = {"partitions": {"2026-01-01_2026-01-01":
                  {"start": "2026-01-01", "end": "2026-01-01", "count": 2, "pages": 1}},
                  "repos": {"1": row(1), "3": row(3)}}

    def check(self):
        return audit.verify(self.global_rows, self.stars, self.lean,
                            self.gs, self.ss, self.cp)

    def test_overlap_is_not_proof(self):
        result, both = self.check()
        self.assertEqual(both, {1})
        self.assertEqual(result["jmd_stars_in_global_lean_snapshot"], 1)
        self.assertFalse(result["establishes_theorem"])
        self.assertFalse(result["establishes_same_object"])

    def test_wrong_global_count_rejected(self):
        self.gs["repository_count"] = 3
        with self.assertRaises(audit.AuditError): self.check()

    def test_bad_subset_rejected(self):
        self.lean = {2: row(2)}
        with self.assertRaises(audit.AuditError): self.check()

    def test_missing_checkpoint_repo_rejected(self):
        self.cp["repos"].pop("3")
        with self.assertRaises(audit.AuditError): self.check()

    def test_incomplete_partition_rejected(self):
        self.cp["partitions"]["2026-01-01_2026-01-01"]["pages"] = 0
        with self.assertRaises(audit.AuditError): self.check()

    def test_duplicate_repo_id_rejected(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as folder:
            p = Path(folder) / "dupe.csv"
            p.write_text("github_id,full_name,html_url\n1,user/repo1,https://github.com/user/repo1\n1,user/repo1,https://github.com/user/repo1\n")
            with self.assertRaises(audit.AuditError):
                audit.load_rows(p, {"github_id", "full_name", "html_url"})

    def test_partition_gap_rejected(self):
        self.cp["partitions"]["2026-01-03_2026-01-03"] = {
            "start": "2026-01-03", "end": "2026-01-03", "count": 0, "pages": 0}
        self.gs["partitions"] = 2
        with self.assertRaises(audit.AuditError): self.check()

if __name__ == "__main__":
    unittest.main()
