#!/usr/bin/env python3
"""Strict negative controls for original-source unsupported-dependency audit.

Small fixtures test the checker implementation, NEVER semantic GWB quality.
Real evidence requires ignored .dashi/gwb-source/slr-record.json.
"""
import importlib.util
from pathlib import Path
from copy import deepcopy
import unittest

spec = importlib.util.spec_from_file_location(
    "fine_audit", Path(__file__).resolve().parents[1] /
    "tools/audit_gwb_original_dependency_fibre.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

def fixture():
    source = {"revision_ref": audit.EXPECTED_SOURCE_REV,
              "pnf_candidates": [
                  {"sentence_index": 0, "dependency_rows": [
                      {"idx": 0, "text": "Bush", "dep": "nsubj"},
                      {"idx": 5, "text": "married", "dep": "ROOT"},
                      {"idx": 13, "text": "Laura", "dep": "compound"},
                      {"idx": 19, "text": "and", "dep": "cc"},
                      {"idx": 23, "text": "she", "dep": "nsubj"},
                      {"idx": 27, "text": "said", "dep": "advmod"},
                  ]}
              ]}
    native = {
        "source_revision": audit.EXPECTED_SOURCE_REV,
        "source_text_sha256": audit.EXPECTED_SOURCE_HASH,
        "engine_certification": "EXPERIMENTAL_CANDIDATE_ONLY_OUTSIDE_CERTIFIED_DIRECT_PATH",
        "source_sentences": 1, "source_tokens": 6,
        "native_candidate_count": 2, "alternative_fibre_count": 0,
        "typed_residual_count": 4,
        "sentence_observations": [
            {"sentence_index": 0, "projection_failures": [],
             "candidates": [
                 {"token_ordinal": 0}, {"token_ordinal": 4},
             ],
             "alternative_fibres": [],
             "residuals": [
                 {"token_ordinal": i, "sentence_index": 0,
                  "kind": "UnsupportedDependency", "consumer_closed": False}
                 for i in (1, 2, 3, 5)
             ]}
        ]
    }
    return native, source

class FineAuditTest(unittest.TestCase):
    def test_exact_routes_and_prior_art_taxonomy_gap(self):
        native, slr = fixture()
        result = audit.inspect(native, slr)
        self.assertEqual(result["unsupported_dependency_count"], 4)
        self.assertEqual(result["work_routes"]["predicateAction"], 1)
        self.assertEqual(result["work_routes"]["nominalStructure"], 1)
        self.assertEqual(result["work_routes"]["coordination"], 1)
        self.assertEqual(result["labels_outside_historical_v04"], {"advmod": 1})
        self.assertTrue(result["exact_parser_token_partition"])

    def test_wrong_revision_rejected(self):
        n, s = fixture()
        s["revision_ref"] = "wrong"
        with self.assertRaisesRegex(ValueError, "revision"):
            audit.inspect(n, s)

    def test_unsupported_row_reassigned_to_other_sentence_rejected(self):
        n, s = fixture()
        n["sentence_observations"][0]["residuals"][0]["sentence_index"] = 1
        with self.assertRaisesRegex(ValueError, "wrong-source"):
            audit.inspect(n, s)

    def test_unknown_token_ordinal_rejected(self):
        n, s = fixture()
        n["sentence_observations"][0]["residuals"][0]["token_ordinal"] = 999
        with self.assertRaisesRegex(ValueError, "ordinal"):
            audit.inspect(n, s)

    def test_overlapping_semantic_site_rejected(self):
        n, s = fixture()
        n["sentence_observations"][0]["candidates"][0]["token_ordinal"] = 1
        with self.assertRaisesRegex(ValueError, "overlap"):
            audit.inspect(n, s)

    def test_missing_structural_site_rejected(self):
        n, s = fixture()
        n["sentence_observations"][0]["residuals"].pop()
        n["typed_residual_count"] = 3
        with self.assertRaisesRegex(ValueError, "partition"):
            audit.inspect(n, s)

    def test_duplicate_residual_site_rejected(self):
        n, s = fixture()
        n["sentence_observations"][0]["residuals"][1]["token_ordinal"] = 1
        with self.assertRaisesRegex(ValueError, "duplicated"):
            audit.inspect(n, s)

    def test_missing_original_sentence_rejected(self):
        n, s = fixture()
        s["pnf_candidates"].append({"sentence_index": 1, "dependency_rows": []})
        with self.assertRaisesRegex(ValueError, "incomplete"):
            audit.inspect(n, s)

    def test_promoted_residual_rejected(self):
        n, s = fixture()
        n["sentence_observations"][0]["residuals"][0]["consumer_closed"] = True
        with self.assertRaisesRegex(ValueError, "promoted"):
            audit.inspect(n, s)

if __name__ == "__main__":
    unittest.main()
