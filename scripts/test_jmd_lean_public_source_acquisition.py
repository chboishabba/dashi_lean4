"""Offline tests: opt-in public clone acquisition is a separate source step."""
import importlib.util
import pathlib
import subprocess
import tempfile
import unittest
from unittest.mock import patch

PATH=pathlib.Path(__file__).with_name("jmd_lean_public_source_acquisition.py")
spec=importlib.util.spec_from_file_location("jmd_lean_acquisition",PATH)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def git(root,*args):
    return subprocess.run(["git",*args],cwd=root,capture_output=True,
                          text=True,check=True).stdout.strip()

class AcquisitionTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=pathlib.Path(self.tmp.name)
        self.repo=self.root/"clones"/"7"
        self.repo.mkdir(parents=True)
        git(self.repo,"init")
        git(self.repo,"config","user.email","fixture@example.invalid")
        git(self.repo,"config","user.name","Fixture")
        git(self.repo,"remote","add","origin","https://github.com/owner/repo.git")
        (self.repo/"README").write_text("source")
        git(self.repo,"add","README")
        git(self.repo,"commit","-m","fixture")
        self.head=git(self.repo,"rev-parse","HEAD")

    def test_existing_clone_is_bound_to_git_revision(self):
        result=m.acquire_one({"github_id":7,"repository":"owner/repo"},
            self.root/"clones",allow_network=False)
        self.assertEqual(result["status"],"already-pinned")
        self.assertEqual(result["commit"],self.head)
        self.assertEqual(result["proofs_certified"],0)

    def test_default_missing_repo_is_dry_run(self):
        with patch.object(m,"safe_git",side_effect=AssertionError("no git")):
            result=m.acquire_one({"github_id":8,"repository":"owner/other"},
                                 self.root/"clones")
        self.assertEqual(result["status"],"dry-run-not-cloned")
        self.assertFalse((self.root/"clones"/"8").exists())

    def test_invalid_remote_refuses_reuse(self):
        git(self.repo,"remote","set-url","origin","https://github.com/other/repo.git")
        with self.assertRaisesRegex(ValueError,"another repository"):
            m.acquire_one({"github_id":7,"repository":"owner/repo"},self.root/"clones")

    def test_dirty_tracked_checkout_is_rejected(self):
        (self.repo/"README").write_text("modified")
        with self.assertRaisesRegex(ValueError,"tracked modifications"):
            m.acquire_one({"github_id":7,"repository":"owner/repo"},self.root/"clones")

    def test_no_shell_injection_from_repo_name(self):
        with self.assertRaisesRegex(ValueError,"Invalid numeric"):
            m.acquire_one({"github_id":8,"repository":"owner/evil;touch /tmp/bad"},
                          self.root/"clones",allow_network=False)

    def test_bounded_batch_does_not_exceed_limit(self):
        queue=[{"github_id":7,"repository":"owner/repo"},
               {"github_id":8,"repository":"owner/other"}]
        result=m.run(queue,self.root/"clones",limit=1)
        self.assertEqual(result["attempted"],1)
        self.assertEqual(result["pinned"],1)
        self.assertTrue(result["dry_run"])

    def test_repeated_repo_id_rejected(self):
        row={"github_id":7,"repository":"owner/repo"}
        with self.assertRaisesRegex(ValueError,"Repeated"):
            m.run([row,row],self.root/"clones",limit=2)

if __name__=="__main__":
    unittest.main()
