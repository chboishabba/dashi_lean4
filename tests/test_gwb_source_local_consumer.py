"""P0 real-source consumer contract, not repeated parser/S29 acceptance.

Synthetic fixtures exercise the invariant; the operator delta runner checks
the current original PostgreSQL-generated consumer against the previously
accepted, *real* local run-q5AjcB6o evidence.
"""
from __future__ import annotations

import copy
import unittest

from test_gwb_native_named_topic_policy import actor_fixture
from tools.gwb_native_maxcut_ledger import EvidenceRejected, make_ledger


def fixture():
    i, f, p=actor_fixture()
    selected=i["candidate_antecedent"]
    focus=i["focus"]
    consumer={
        "schema":"slr-native-source-local-consumer-v1",
        "consumer_scope_ref":
            "source-local-antecedent-query:declared-named-topic-policy-v1",
        "answer_receipt_ref":"source-relative-answer:sha256:"+"a"*64,
        "source_document_ref":i["document_ref"],
        "source_revision_ref":i["source_revision_ref"],
        "source_content_sha256":i["canonical_content_sha256"],
        "original_focus_mention_ref":focus["mention_ref"],
        "original_focus_statement_ref":focus["statement_ref"],
        "original_focus_region_ref":focus["region_ref"],
        "original_focus_span":[4534,4536],
        "original_focus_surface":"he",
        "original_selected_antecedent_statement_ref":selected["statement_ref"],
        "original_selected_antecedent_region_ref":selected["region_ref"],
        "original_selected_antecedent_span":[4310,4314],
        "original_selected_antecedent_surface":"Bush",
        "original_parser_run_ref":f["parser_run_ref"],
        "original_candidate_set_ref":f["candidate_set_ref"],
        "original_review_item_ref":i["review_item_ref"],
        "original_s29_status":i["s29_review_status"],
        "original_policy_ref":p["policy_ref"],
        "original_derivation_ref":p["derivation_ref"],
        "original_person_support":p["supporting_person_mentions"],
        "answer_kind":"DERIVED_UNDER_NAMED_TOPIC_POLICY",
        "answer_value":"Bush",
        "source_local_policy_inference_paid":True,
        "typed_unique_identity_witness_paid":False,
        "governed_semantic_identity_paid":False,
        "level_three_substitution_paid":False,
        "external_qid_paid":False,
        "historical_truth_paid":False,
    }
    replay={
        "schema":"slr-native-source-local-answer-replay-v1",
        "result":"CURRENT",
        "current":copy.deepcopy(consumer),
        "prior_receipt_ref":consumer["answer_receipt_ref"],
        "original_level_one_source_preserved":True,
        "previous_interpretation_usable":True,
        "original_level_three_retracted_here":False,
        "external_identity_inferred":False,
    }
    return i,f,p,consumer,replay

class OriginalSourceConsumerTests(unittest.TestCase):
    def evaluate(self, mutate=None):
        i,f,p,c,r=fixture()
        if mutate:mutate(i,f,p,c,r)
        return make_ledger(i,f,named_topic_inference=p,
                           source_consumer=c,source_consumer_replay=r)
    def rejected(self,mutate):
        with self.assertRaises(EvidenceRejected):self.evaluate(mutate)
    def test_positive_original_source_replay_and_bounded_answer(self):
        ledger,_=self.evaluate()
        b=ledger["book_lane"]
        self.assertEqual(b["answer_value"],"Bush")
        self.assertTrue(b["source_local_interpretation_paid_under_declared_policy"])
        self.assertTrue(b["original_source_consumer_certificate_checked"])
        self.assertTrue(b["original_source_consumer_replay_current"])
        self.assertFalse(b["source_relative_identity_paid"])
        self.assertFalse(b["world_q23505_paid"])
        self.assertFalse(b["claim_truth_paid"])
    def test_old_source_revision_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(source_revision_ref="foreign"))
    def test_wrong_original_focus_statement_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(
            original_focus_statement_ref="statement:foreign"))
    def test_wrong_original_antecedent_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(
            original_selected_antecedent_surface="Reagan"))
    def test_wrong_parser_run_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(original_parser_run_ref="run:fake"))
    def test_wrong_candidate_set_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(original_candidate_set_ref="frontier:fake"))
    def test_changed_policy_derivation_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(original_derivation_ref="derivation:fake"))
    def test_forged_governed_identity_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(governed_semantic_identity_paid=True))
    def test_forged_level_three_substitution_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(level_three_substitution_paid=True))
    def test_forged_world_qid_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(external_qid_paid=True))
    def test_forged_historical_truth_rejected(self):
        self.rejected(lambda i,f,p,c,r: c.update(historical_truth_paid=True))
    def test_wrong_supporting_evidence_rejected(self):
        self.rejected(lambda i,f,p,c,r: c["original_person_support"].pop())
    def test_stale_replay_rejected(self):
        self.rejected(lambda i,f,p,c,r: r.update(result="INVALIDATED"))
    def test_replay_does_not_claim_level_three_retraction(self):
        self.rejected(lambda i,f,p,c,r: r.update(original_level_three_retracted_here=True))
    def test_replay_does_not_claim_world_identity(self):
        self.rejected(lambda i,f,p,c,r: r.update(external_identity_inferred=True))
    def test_replay_current_must_match_real_answer(self):
        self.rejected(lambda i,f,p,c,r: r["current"].update(answer_value="Reagan"))
    def test_replay_can_run_as_unpaid_old_snapshot(self):
        i,f,p,c,r=fixture()
        ledger,_=make_ledger(i,f,named_topic_inference=p,source_consumer=c)
        self.assertTrue(ledger["book_lane"]["original_source_consumer_certificate_checked"])
        self.assertFalse(ledger["book_lane"]["original_source_consumer_replay_current"])

if __name__=="__main__":
    unittest.main()
