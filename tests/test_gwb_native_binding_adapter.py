#!/usr/bin/env python3
"""C4.09a native binding carrier: synthetic, fail-closed contract controls."""
import copy
import unittest
from types import SimpleNamespace
from tools.gwb_native_binding_adapter import capture, verify_owner_carrier

RUN="parser-run:test"
REV="source-revision:test"
DOC="document:test"
REG="document-region:test"
MENTION="entity-mention:test"
LITERAL="Bush said he."
TOKEN=[
    {"compilation_key":"compile:test","token_ordinal":0,"start_char":100,"end_char":104,
     "surface":"Bush","lemma":"Bush","pos":"PROPN","morph_json":"{}",
     "head_ordinal":1,"dependency_ref":"nsubj"},
    {"compilation_key":"compile:test","token_ordinal":1,"start_char":105,"end_char":109,
     "surface":"said","lemma":"say","pos":"VERB","morph_json":"{}",
     "head_ordinal":1,"dependency_ref":"ROOT"},
    {"compilation_key":"compile:test","token_ordinal":2,"start_char":110,"end_char":112,
     "surface":"he","lemma":"he","pos":"PRON","morph_json":"{\"Number\":\"Sing\"}",
     "head_ordinal":1,"dependency_ref":"dobj"},
    {"compilation_key":"compile:test","token_ordinal":3,"start_char":112,"end_char":113,
     "surface":".","lemma":".","pos":"PUNCT","morph_json":"{}",
     "head_ordinal":1,"dependency_ref":"punct"},
]
CAND=f"candidate-pnf-db:{RUN}:{REG}:2:110:112"
SCOPE={
    "mention_ref":MENTION,"candidate_ref":CAND,"statement_ref":"statement:test",
    "surface":"he","lemma":"he","role_ref":"patient",
    "entity_fingerprint_ref":"entity-fingerprint:test",
    "source_start_char":110,"source_end_char":112,
    "candidate_only":True,"creates_entity_identity":False,
    "creates_semantic_authority":False,"claim_truth_promoted":False,
    "exact_span_ref":REG,"literal_text":LITERAL,"source_revision_ref":REV,
    "document_ref":DOC,"compilation_key":"compile:test","parser_run_ref":RUN,
    "region_start_char":100,"region_end_char":113,
    "parser_product_key":"parser-product:test","job_status":"succeeded",
    "batch_ref":"batch:test","candidate_product_ref":"pnf-product:test",
}
ENTITIES=[{"entity_ordinal":0,"compilation_key":"compile:test",
           "start_char":100,"end_char":104,"surface":"Bush","label_ref":"PERSON"}]
FACTORS=[{"product_ref":"pnf-product:test","factor_ordinal":2,
          "start_offset":10,"end_offset":12,"surface":"he"}]
L2=[{"product_ref":"pnf-product:test","factor_ordinal":2}]
DATA=[ [SCOPE],TOKEN,ENTITIES,FACTORS,L2 ]


class Cursor:
    def __init__(self,data):
        self.data=data
        self.index=0
        self.description=[]
        self.answer=[]
    def __enter__(self):return self
    def __exit__(self,*args):return False
    def execute(self,sql,params=None):
        if sql.strip().startswith("SET"):return
        result=self.data[self.index]
        self.index+=1
        self.description=[SimpleNamespace(name=k) for k in result[0]] if result else []
        self.answer=[tuple(r.values()) for r in result]
    def fetchall(self):return self.answer

class Connection:
    def __init__(self,data):self.data=data
    def cursor(self):return Cursor(self.data)


def source(data=None):
    return capture(Connection(copy.deepcopy(data if data is not None else DATA)),
                   run=RUN,revision=REV,mention=MENTION)

def owner(native):
    return {
        "canonical_text":LITERAL,
        "pnf_graph":{"document_ref":DOC,"graph_ref":"pnf:test",
                     "factors":[{"factor_ref":"factor:owner",
                                 "factor_type":"semantic.argument.subject",
                                 "metadata":{"parser_pos":"PRON"}}]},
        "semantic_annotation_layer":{
            "span_annotations":[
                {"annotation_type":"parser_token","start_token":i,
                 "end_token":i+1,
                 "value":{"start_char":t["start_char"]-100,
                          "end_char":t["end_char"]-100,
                          "surface":t["surface"]}}
                for i,t in enumerate(native["parser_tokens"])
            ]}
    }


class NativeBindingContract(unittest.TestCase):
    def test_exact_capture_and_owner_alignment(self):
        native=source()
        self.assertEqual(len(native["parser_tokens"]),4)
        self.assertEqual(native["source"]["document_ref"],DOC)
        self.assertEqual(verify_owner_carrier(native,owner(native))
                         ["matched_parser_tokens"],4)
    def test_wrong_parser_run_is_rejected(self):
        altered=copy.deepcopy(DATA)
        altered[0][0]["parser_run_ref"]="parser-run:foreign"
        with self.assertRaisesRegex(ValueError,"candidate reference"):
            source(altered)
    def test_foreign_dependency_head_is_rejected(self):
        altered=copy.deepcopy(DATA)
        altered[1][2]["head_ordinal"]=99
        with self.assertRaisesRegex(ValueError,"dependency head"):
            source(altered)
    def test_fake_entity_surface_is_rejected(self):
        altered=copy.deepcopy(DATA)
        altered[2][0]["surface"]="Bosh"
        with self.assertRaisesRegex(ValueError,"entity surface"):
            source(altered)
    def test_missing_token_is_rejected(self):
        altered=copy.deepcopy(DATA)
        altered[1].pop(1)
        with self.assertRaisesRegex(ValueError,"uncovered non-whitespace"):
            source(altered)
    def test_promoted_mention_is_rejected(self):
        altered=copy.deepcopy(DATA)
        altered[0][0]["creates_entity_identity"]=True
        with self.assertRaisesRegex(ValueError,"promoted"):
            source(altered)
    def test_legacy_null_product_key_fails_strict_binding(self):
        native=source()
        native["source"]["parser_product_key"]=None
        with self.assertRaisesRegex(ValueError,"parser_product_key"):
            verify_owner_carrier(native,owner(native))
    def test_different_document_is_rejected(self):
        native=source()
        evidence=owner(native)
        evidence["pnf_graph"]["document_ref"]="document:foreign"
        with self.assertRaisesRegex(ValueError,"revision mismatch"):
            verify_owner_carrier(native,evidence)
    def test_owner_token_shift_is_rejected(self):
        native=source()
        evidence=owner(native)
        evidence["semantic_annotation_layer"]["span_annotations"][2]["value"]["start_char"]=11
        with self.assertRaisesRegex(ValueError,"coordinate mismatch"):
            verify_owner_carrier(native,evidence)
    def test_semantic_factor_must_be_original_owner_kind(self):
        native=source()
        evidence=owner(native)
        evidence["pnf_graph"]["factors"][0]["factor_type"]="actor"
        with self.assertRaisesRegex(ValueError,"semantic reduction"):
            verify_owner_carrier(native,evidence)


if __name__=="__main__":
    unittest.main()
