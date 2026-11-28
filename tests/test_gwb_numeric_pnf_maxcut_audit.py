"""Read-only P0-C/D numeric owner audit: no inferred IDs/admissions.

Actual operator run requires original SensibLaw PostgreSQL with an explicitly
selected numeric run; no synthetic test asserts payment of a source-book identity.
"""
from __future__ import annotations
import copy
import unittest
from unittest.mock import patch
from tools import gwb_numeric_pnf_maxcut_audit as audit

def source_receipt():
    return {
      "schema":"slr-native-source-local-consumer-v1",
      "source_content_sha256":audit.BOOK_SHA,
      "source_document_ref":"document:original-book",
      "source_revision_ref":"revision:book-1",
      "original_parser_run_ref":"parser:original",
      "original_candidate_set_ref":"candidate:original",
      "answer_receipt_ref":"source-relative-answer:real",
      "original_policy_ref":"slr:policy:source-local-repeated-person-topic:v1",
      "original_focus_span":[4534,4536],
      "original_selected_antecedent_span":[4310,4314],
      "original_focus_surface":"he",
      "original_selected_antecedent_surface":"Bush",
      "answer_kind":"DERIVED_UNDER_NAMED_TOPIC_POLICY",
      "answer_value":"Bush",
      "source_local_policy_inference_paid":True,
      "typed_unique_identity_witness_paid":False,
      "governed_semantic_identity_paid":False,
      "level_three_substitution_paid":False,
      "external_qid_paid":False,
      "historical_truth_paid":False,
    }

class NumericEndpointReadOnlyContract(unittest.TestCase):
    def test_original_source_policy_is_valid_upstream_only(self):
        audit.source_gate(source_receipt())
    def test_foreign_book_sha_refused(self):
        c=source_receipt()
        c["source_content_sha256"]="0"*64
        with self.assertRaisesRegex(ValueError,"source_content_sha256"):
            audit.source_gate(c)
    def test_q207_or_wrong_antecedent_refused(self):
        c=source_receipt()
        c["answer_value"]="Q207"
        with self.assertRaisesRegex(ValueError,"answer_value"):
            audit.source_gate(c)
    def test_forged_document_identity_refused(self):
        c=source_receipt()
        c["governed_semantic_identity_paid"]=True
        with self.assertRaisesRegex(ValueError,"governed_semantic"):
            audit.source_gate(c)
    def test_forged_level3_refused(self):
        c=source_receipt()
        c["level_three_substitution_paid"]=True
        with self.assertRaisesRegex(ValueError,"level_three"):
            audit.source_gate(c)
    def test_forged_qid_refused(self):
        c=source_receipt()
        c["external_qid_paid"]=True
        with self.assertRaisesRegex(ValueError,"external_qid"):
            audit.source_gate(c)
    def test_missing_numeric_run_document_is_not_invented(self):
        with patch.object(audit,"query",return_value=[]):
            out=audit.inspect(object(),source_receipt(),"numeric-run","document:original-book")
        self.assertEqual(out["registered_numeric_scope"],[])
        self.assertEqual(out["first_blocker"],
                         "ORIGINAL_NUMERIC_RUN_OR_DOCUMENT_UNAVAILABLE")
    def test_forged_source_local_policy_not_numeric_evidence(self):
        c=source_receipt()
        c["answer_kind"]="ADMITTED_DOCUMENT_IDENTITY"
        with self.assertRaisesRegex(ValueError,"answer_kind"):
            audit.source_gate(c)

if __name__=="__main__": unittest.main()
