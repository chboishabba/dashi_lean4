#!/usr/bin/env python3
"""Synthetic Git fixtures test the real checkout wrapper; no network or Lean."""
import copy
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

WRAPPER = pathlib.Path(__file__).with_name("checkout_fork_source.sh")


class SourcePinTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        self.sidecar = self.root / "dashi/proofs/alpoge-lean433"
        self.sidecar.mkdir(parents=True)
        shutil.copyfile(WRAPPER, self.sidecar / WRAPPER.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.git("init", "-q")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "Fixture")
        self.git("remote", "add", "origin", "https://example.invalid/fixture.git")
        for project in ("", "grh-compact", "grh"):
            p = self.source / project
            (p / "src").mkdir(parents=True)
            (p / "src/Statements.lean").write_text("synthetic identical statement\n")
            (p / "src/Main.lean").write_text(f"synthetic {project}\n")
            (p / "lean-toolchain").write_text("fixture-toolchain\n")
            (p / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": "fixture"}]}))
        (self.source / "LICENSE").write_text("fixture only\n")
        self.git("add", ".")
        self.git("commit", "-qm", "pin")
        self.rev = self.git("rev-parse", "HEAD")
        self.original = {"url": "https://example.invalid/fixture.git", "revision": self.rev,
                         "toolchain": "fixture-toolchain", "mathlib_revision": "fixture",
                         "git_blobs": {p: self.blob(p) for p in ("src/Main.lean", "src/Statements.lean")}}
        self.licensed = {**self.original, "root_git_blobs": {"LICENSE": self.blob("LICENSE")}, "editions": {}}
        for name, p in (("compact", "grh-compact"), ("readable", "grh")):
            self.licensed["editions"][name] = {"project": p, "tree": self.blob(p),
                "git_blobs": {f: self.blob(f"{p}/{f}") for f in ("src/Main.lean", "src/Statements.lean")}}
        self.write_pins()

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.source), *args], text=True).strip()

    def blob(self, p):
        return self.git("rev-parse", "HEAD:" + p)

    def write_pins(self):
        for name, obj in (("fork_pin.json", self.original), ("licensed_rewrite_pin.json", self.licensed)):
            (self.sidecar / name).write_text(json.dumps(obj))

    def run_pin(self, mode, verify_only=False):
        return subprocess.run(["bash", str(self.sidecar / WRAPPER.name), str(self.source)],
            env={**os.environ, "GRH_P0_SOURCE": mode, "GRH_P0_VERIFY_ONLY": str(int(verify_only))},
            text=True, capture_output=True)

    def test_all_profiles(self):
        for mode in ("original", "compact", "readable"):
            with self.subTest(mode=mode):
                p = self.run_pin(mode)
                self.assertEqual(p.returncode, 0, p.stderr)
                self.assertIn("SOURCE PROVENANCE ONLY", p.stdout)

    def test_pin_mutations(self):
        base = copy.deepcopy(self.licensed)
        for change in ("tree", "statement", "blob", "toolchain", "mathlib", "origin"):
            with self.subTest(change=change):
                self.licensed = copy.deepcopy(base)
                if change == "tree": self.licensed["editions"]["compact"]["tree"] = "0" * 40
                if change == "statement": self.licensed["editions"]["compact"]["git_blobs"]["src/Statements.lean"] = "0" * 40
                if change == "blob": self.licensed["editions"]["compact"]["git_blobs"]["src/Main.lean"] = "0" * 40
                if change == "toolchain": self.licensed["toolchain"] = "wrong"
                if change == "mathlib": self.licensed["mathlib_revision"] = "wrong"
                if change == "origin": self.licensed["url"] = "https://example.invalid/wrong.git"
                self.write_pins()
                self.assertNotEqual(self.run_pin("compact").returncode, 0)

    def test_dirty_and_hidden_paths(self):
        p = self.source / "grh-compact/src/Main.lean"
        p.write_text("changed\n")
        self.assertNotEqual(self.run_pin("compact").returncode, 0)
        self.assertEqual(p.read_text(), "changed\n")
        self.git("restore", "grh-compact/src/Main.lean")
        self.git("update-index", "--assume-unchanged", "grh-compact/src/Main.lean")
        self.assertNotEqual(self.run_pin("compact").returncode, 0)

    def test_verify_only_preserves_changed_head(self):
        self.git("commit", "--allow-empty", "-qm", "changed head")
        changed = self.git("rev-parse", "HEAD")
        self.assertNotEqual(self.run_pin("compact", verify_only=True).returncode, 0)
        self.assertEqual(self.git("rev-parse", "HEAD"), changed)
        self.assertEqual(self.run_pin("compact").returncode, 0)
        self.assertEqual(self.git("rev-parse", "HEAD"), self.rev)


if __name__ == "__main__":
    unittest.main()
