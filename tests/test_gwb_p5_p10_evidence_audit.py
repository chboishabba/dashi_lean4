#!/usr/bin/env python3
"""Negative controls for the P5–P10 audit boundary; no user fixtures needed."""
import importlib.util
from pathlib import Path
import tempfile
import json
import unittest

spec = importlib.util.spec_from_file_location(
    "gwb_p5_p10_evidence_audit",
    Path(__file__).resolve().parents[1] / "tools/gwb_p5_p10_evidence_audit.py",
)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

M = {
    "schema": "gwb-committed-rust-lean-proof-v1",
    "source_revision": "enwiki-revid:1385850169",
    "lean_source_fibre_receipt": "PASSED",
}


class EvidenceAudit(unittest.TestCase):
    def test_original_manifest_gates_not_falsely_closed(self):
        gates = audit.classify(M)
        self.assertEqual(set(gates), {f"P{i}" for i in range(5, 11)})
        self.assertTrue(all(g["state"] == "OPEN" for g in gates.values()))

    def test_revision_spoof_rejected(self):
        with self.assertRaises(ValueError):
            audit.classify({**M, "source_revision": "enwiki-revid:9999"})

    def test_unverified_native_receipt_rejected(self):
        with self.assertRaises(ValueError):
            audit.classify({**M, "lean_source_fibre_receipt": "NOT_TESTED"})

    def test_topic_review_stays_topic(self):
        result = audit.classify(M, {
            "rows": 10, "topic_only": 8,
            "exact_source_work": 1, "semantic_actor_identity_admitted": False,
        })
        self.assertEqual(result["P5"]["state"], "OPEN")

    def test_candidate_s28_never_pays_event_time(self):
        s28 = {
            "schema": "slr-s28-event-chronology-candidates-v1",
            "candidate_only": True,
            "semantic_promotion": False,
            "event_occurrence_paid": False,
        }
        result = audit.classify(M, s28=s28)
        self.assertEqual(result["P6"]["state"], "OPEN")
        self.assertEqual(result["P7"]["state"], "OPEN")

    def test_promoted_s28_rejected(self):
        with self.assertRaises(ValueError):
            audit.classify(M, s28={
                "schema": "slr-s28-event-chronology-candidates-v1",
                "candidate_only": True,
                "semantic_promotion": True,
                "event_occurrence_paid": False,
            })

    def test_kb_graph_not_article_alignment(self):
        result = audit.classify(M, world={
            "article_semantic_alignment_paid": False,
        })
        self.assertEqual(result["P9"]["state"], "OPEN")
        self.assertEqual(result["P10"]["state"], "OPEN")

    def test_forged_kb_alignment_rejected(self):
        with self.assertRaises(ValueError):
            audit.classify(M, world={"article_semantic_alignment_paid": True})

    def test_seed_overlay_requires_candidate_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "overlay.jsonl"
            path.write_text(json.dumps({
                "schema": audit.OVERLAY_SCHEMA,
                "candidate_only": False,
                "semantic_promotion": True,
            }) + "\n")
            with self.assertRaises(ValueError):
                audit.audited_overlay(path)


if __name__ == "__main__":
    unittest.main()
