"""Real-source-equivalent M2 positive named-topic policy + adversarial tests.

These unit fixtures do not impersonate the original PostgreSQL run. The
one-command acceptance also checks the actual native Rust derivation and
original book source against Python and Lean.
"""
from __future__ import annotations
import copy
import json
import unittest

from test_gwb_native_maxcut_ledger import fixture
from tools.gwb_native_maxcut_ledger import (
    make_ledger, EvidenceRejected, validate_named_topic_inference,
)

def actor_fixture():
    i,f=fixture()
    # Source string of sentence 19 must agree with additional PERSON label.
    s=i["before"][0]
    offset=4005-s["start_char"]
    s["literal"]=s["literal"][:offset]+"Bush"+s["literal"][offset+4:]
    original=f["nominations"][0]
    person0={
        **original,
        "nomination_ref":"native-parser-nomination:sha256:"+("1"*64),
        "parser_observation_ref":"comp:19:entity:0",
        "original_statement_ref":"stmt:19",
        "original_region_ref":"reg:19",
        "original_start_char":4005,
        "original_end_char":4009,
        "surface":"Bush",
        "observation_kind":"parser_entity",
        "parser_pos_or_label":"PERSON",
        "parser_lemma":None,
        "parser_morph_json":None,
        "parser_dependency_ref":None,
    }
    person1={
        **person0,
        "nomination_ref":"native-parser-nomination:sha256:"+("2"*64),
        "parser_observation_ref":"comp:22:entity:0",
        "original_statement_ref":"stmt:22",
        "original_region_ref":"reg:22",
        "original_start_char":4310,
        "original_end_char":4314,
    }
    f["nominations"].extend([person0,person1])
    f["parser_nomination_count"]=len(f["nominations"])
    f["focus_parser_pos"]="PRON"
    f["focus_parser_morph_json"]=json.dumps(
        {"Person":"3","Number":"Sing","Gender":"Masc"})
    f["focus_parser_dependency_ref"]="nsubj"
    supporting=[
        {
            "name":p["surface"],
            "statement_ref":p["original_statement_ref"],
            "region_ref":p["original_region_ref"],
            "start_char":p["original_start_char"],
            "end_char":p["original_end_char"],
            "original_observation_ref":p["parser_observation_ref"]
        }
        for p in (person0,person1)
    ]
    policy={
        "schema":"slr-native-named-topic-inference-v1",
        "policy_ref":"slr:policy:source-local-repeated-person-topic:v1",
        "derivation_ref":"source-local-topic-inference:sha256:"+("f"*64),
        "original_document_ref":i["document_ref"],
        "original_source_revision_ref":i["source_revision_ref"],
        "canonical_content_sha256":i["canonical_content_sha256"],
        "parser_run_ref":f["parser_run_ref"],
        "review_item_ref":i["review_item_ref"],
        "focus_mention_ref":f["focus_mention_ref"],
        "focus_span":[4534,4536],
        "focus_surface":"he",
        "raw_parser_observation_count":len(f["nominations"]),
        "named_person_observation_count":2,
        "distinct_named_person_groups":1,
        "supporting_person_mentions":supporting,
        "distinct_supporting_original_sentences":2,
        "named_person_groups":["bush"],
        "status":"DERIVED_SOURCE_LOCAL_NAMED_TOPIC",
        "reason":"unique repeatedly named PERSON across original scope; no competing PERSON or quote boundary",
        "source_local_answer":"Bush",
        "source_local_inference_derived":True,
        "s29_status_at_derivation":"Pending",
        "requires_human_s29_to_form_policy_inference":False,
        "governed_source_local_admission_paid":False,
        "complete_all_live_referents_proven":False,
        "external_qid_paid":False,
        "historical_claim_truth_paid":False,
    }
    return i,f,policy


class SourceLocalNamedTopicPolicyTests(unittest.TestCase):
    def test_real_policy_pays_source_local_interpretation_not_qid(self):
        i,f,p=actor_fixture()
        m,w=make_ledger(i,f,named_topic_inference=p)
        self.assertEqual(m["book_lane"]["answer_value"],"Bush")
        self.assertEqual(m["book_lane"]["answer_kind"],
                         "DETERMINISTIC_POLICY_SOURCE_LOCAL")
        self.assertTrue(m["book_lane"]["named_topic_source_inference_derived"])
        self.assertFalse(m["book_lane"]["source_relative_identity_paid"])
        self.assertFalse(m["book_lane"]["world_q23505_paid"])
        self.assertFalse(m["wikipedia_lane"]["book_local_identity_from_Q207"])
        self.assertFalse(w["review_complete"])
    def test_pending_s29_does_not_block_scoped_inference(self):
        i,f,p=actor_fixture()
        self.assertEqual(p["s29_status_at_derivation"],"Pending")
        self.assertTrue(validate_named_topic_inference(
            i,f,p,i["before"]+[i["focus_statement"]]+i["after"]))
    def test_wrong_actor_string_is_rejected(self):
        i,f,p=actor_fixture()
        p["source_local_answer"]="Reagan"
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_a_second_preceding_person_breaks_uniqueness(self):
        i,f,p=actor_fixture()
        s=i["before"][1]
        s["literal"]="Reagan"+s["literal"][6:]
        new=copy.deepcopy(f["nominations"][-1])
        new["nomination_ref"]="native-parser-nomination:sha256:"+("3"*64)
        new["surface"]="Reagan"
        new["parser_observation_ref"]="comp:20:entity:0"
        new["original_statement_ref"]="stmt:20"
        new["original_region_ref"]="reg:20"
        new["original_start_char"]=4100
        new["original_end_char"]=4106
        # Original 20 fixture is [4100,4200). Preserve valid length and text.
        f["nominations"].append(new)
        f["parser_nomination_count"]=len(f["nominations"])
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_quote_boundary_disallows_unreviewed_scoped_topic(self):
        i,f,p=actor_fixture()
        s=i["before"][1]
        s["literal"]='"'+s["literal"][1:]
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_morphological_conflict_blocks_inference(self):
        i,f,p=actor_fixture()
        f["focus_parser_morph_json"]='{"Person":"1","Number":"Plur"}'
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_forged_governed_admission_rejected(self):
        i,f,p=actor_fixture()
        p["governed_source_local_admission_paid"]=True
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_q23505_is_never_attached_by_policy(self):
        i,f,p=actor_fixture()
        p["external_qid_paid"]=True
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_no_repeated_named_person_is_insufficient(self):
        i,f,p=actor_fixture()
        f["nominations"].pop(1)
        f["parser_nomination_count"]=len(f["nominations"])
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)
    def test_foreign_source_revision_fails(self):
        i,f,p=actor_fixture()
        p["original_source_revision_ref"]="foreign"
        with self.assertRaises(EvidenceRejected):
            make_ledger(i,f,named_topic_inference=p)

if __name__=="__main__":
    unittest.main()
