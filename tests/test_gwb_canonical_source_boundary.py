#!/usr/bin/env python3
"""Canonical SLR observer negative controls; synthetic shapes ONLY for checker tests."""
import hashlib, importlib.util, json
from pathlib import Path
from unittest import TestCase, main
from unittest.mock import patch

p=Path(__file__).resolve().parents[1]/"tools/gwb_canonical_slr_acceptance.py"
spec=importlib.util.spec_from_file_location("original_slr",p)
source=importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)

def fixtures():
    article="X"
    digest=hashlib.sha256(article.encode("utf-8")).hexdigest()
    ref="source:test"
    token={"dep":"ROOT","head_i":0,"idx":0,"i":0,"text":"X"}
    slr={"schema":"slr-source-unit-pnf-record-v1",
         "revision_ref":source.REV,
         "source_unit_ref":ref,"candidate_only":True,"semantic_promotion":False,
         "manifestation":{"source_text_sha256":digest},
         "pnf_candidates":[
           {"sentence_index":i,"candidate_only":True,"semantic_promotion":False,
            "dependency_rows":[dict(token)]} for i in range(643)]}
    projection={"schema":"slr-jmd-wikipedia-article-candidates-v1",
         "source_revision_ref":source.REV,"source_unit_ref":ref,
         "source_text_sha256":digest,
         "source_assertion_is_world_truth":False,
         "parser_carries_semantic_licence":False,
         "cross_sentence_identity_paid":False,
         "text_order_is_event_chronology":False,
         "event_candidates":[{"sentence_index":0,"candidate_only":True,
           "semantic_licence_paid":False,"world_event_occurrence_paid":False,
           "predicate":{"i":0,"start_char":0,"surface":"X"},
           "actors":[],"patients":[]}],
         "timeline_candidates":[],"sections":[],"proper_noun_tokens":[]}
    p0b={"source_ref":ref,"mentions":[],"licenses":[]}
    return article,slr,projection,p0b,digest

class CanonicalSourceTest(TestCase):
    def inspect(self,args):
        with patch.object(source,"SHA",args[4]):
            return source.inspect(*args[:4])

    def test_complete_original_source_only(self):
        a=fixtures()
        r=self.inspect(a)
        self.assertEqual(r["counts"]["sentences"],643)
        self.assertEqual(r["counts"]["parser_tokens"],643)
        self.assertEqual(r["counts"]["original_predicates"],1)
        self.assertEqual(r["original_dependency_histogram"],{"ROOT":643})
        self.assertFalse(r["experimental_sl_semantic_expansion_used"])
        self.assertFalse(r["semantic_authority_created"])

    def test_cross_source_id_rejected(self):
        a=list(fixtures())
        a[3]["source_ref"]="wrong"
        with self.assertRaisesRegex(ValueError,"source refs"):self.inspect(a)

    def test_source_revision_rejected(self):
        a=list(fixtures())
        a[1]["revision_ref"]="wrong"
        with self.assertRaisesRegex(ValueError,"revision"):self.inspect(a)

    def test_missing_event_predicate_rejected(self):
        a=list(fixtures())
        a[2]["event_candidates"][0]["predicate"]["surface"]="fabricated"
        with self.assertRaisesRegex(ValueError,"predicate"):self.inspect(a)

    def test_parser_head_missing_rejected(self):
        a=list(fixtures())
        del a[1]["pnf_candidates"][0]["dependency_rows"][0]["head_i"]
        with self.assertRaisesRegex(ValueError,"head"):self.inspect(a)

    def test_unreviewed_event_promotion_rejected(self):
        a=list(fixtures())
        a[2]["event_candidates"][0]["world_event_occurrence_paid"]=True
        with self.assertRaisesRegex(ValueError,"promotion"):self.inspect(a)

    def test_source_scope_authority_rejected(self):
        a=list(fixtures())
        a[2]["cross_sentence_identity_paid"]=True
        with self.assertRaisesRegex(ValueError,"promoted"):self.inspect(a)

    def test_duplicate_sentence_rejected(self):
        a=list(fixtures())
        a[1]["pnf_candidates"][1]["sentence_index"]=0
        with self.assertRaisesRegex(ValueError,"duplicate"):self.inspect(a)

if __name__=="__main__":main()
