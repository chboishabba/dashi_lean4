"""M1–M3 exact negative controls; no fabricated S29 human review."""
from __future__ import annotations
import copy
import unittest

from tools.gwb_native_maxcut_ledger import (
    BOOK_SHA, REVIEW_ITEM, WIKI_SHA, LEAN_MARKER, Q207_MARKER,
    make_ledger, EvidenceRejected,
)

def source_sentence(start: int, end: int, statement: str, region: str,
                    replacement: tuple[int,int,str] | None = None) -> dict:
    s = list("x" * (end-start))
    if replacement:
        a,b,value = replacement
        assert len(value)==b-a
        s[a-start:b-start]=list(value)
    return {
        "start_char":start,"end_char":end,"literal":"".join(s),
        "statement_ref":statement,"region_ref":region
    }

def fixture() -> tuple[dict,dict]:
    before=[
        source_sentence(4000,4100,"stmt:19","reg:19"),
        source_sentence(4100,4200,"stmt:20","reg:20"),
        source_sentence(4200,4300,"stmt:21","reg:21"),
        source_sentence(4300,4526,"stmt:22","reg:22",(4310,4314,"Bush"))
    ]
    at=source_sentence(4526,4693,"stmt:23","reg:23",(4534,4536,"he"))
    after=[
        source_sentence(4693,4800,"stmt:24","reg:24"),
        source_sentence(4800,4900,"stmt:25","reg:25")
    ]
    focus={
        "mention_ref":"mention:he","candidate_ref":"candidate:he",
        "statement_ref":"stmt:23","region_ref":"reg:23",
        "start_char":4534,"end_char":4536,"surface":"he"
    }
    antecedent={
        "statement_ref":"stmt:22","region_ref":"reg:22",
        "start_char":4310,"end_char":4314,"surface":"Bush"
    }
    inspect={
        "schema":"slr-native-antecedent-s29-inspection-v1",
        "review_item_ref":REVIEW_ITEM,
        "proposal_ref":REVIEW_ITEM.removeprefix("review-item:"),
        "original_source_ref":"source:book",
        "source_revision_ref":"source-revision:sha256:example",
        "canonical_content_sha256":BOOK_SHA,
        "document_ref":"document:sha256:"+BOOK_SHA,
        "original_context_sha256":"a"*64,
        "focus":focus,"candidate_antecedent":antecedent,
        "before":before,"focus_statement":at,"after":after,
        "s29_review_status":"Pending",
        "s29_receipt_commands":[],
        "candidate_only":True,
        "antecedent_resolution":"REVIEW_REQUIRED",
        "identity_admission_paid":False,
        "external_qid_paid":False,
        "claim_truth_paid":False,
    }
    nominations=[
        {
            "nomination_ref":"native-parser-nomination:sha256:"+("f"*64),
            "original_statement_ref":"stmt:22","original_region_ref":"reg:22",
            "parser_compilation_key":"comp:22",
            "original_start_char":4310,"original_end_char":4314,
            "surface":"Bush","observation_kind":"parser_token",
            "parser_observation_ref":"comp:22:token:9",
            "parser_pos_or_label":"PROPN","parser_lemma":"Bush",
            "parser_morph_json":None,"parser_dependency_ref":"nsubj",
            "in_preceding_source":True,
            "same_original_statement_as_focus":False,
            "source_verified":True,"morphological_resolution":"UNASSESSED",
            "quotation_scope":"UNASSESSED","semantic_admission_paid":False
        }
    ]
    frontier={
        "schema":"slr-native-antecedent-bounded-frontier-v1",
        "original_source_ref":inspect["original_source_ref"],
        "source_revision_ref":inspect["source_revision_ref"],
        "canonical_content_sha256":BOOK_SHA,
        "document_ref":inspect["document_ref"],
        "review_item_ref":REVIEW_ITEM,
        "s29_review_status":"Pending",
        "parser_run_ref":"parser-run:original",
        "focus_mention_ref":"mention:he",
        "focus_start_char":4534,"focus_end_char":4536,
        "focus_surface":"he",
        "nominated_source_anchor_ref":"stmt:22",
        "nominated_source_anchor_start_char":4310,
        "nominated_source_anchor_end_char":4314,
        "candidate_set_ref":"native-antecedent-bounded-frontier:sha256:"+("e"*64),
        "parser_nomination_count":len(nominations),
        "original_regions_covered":5,
        "structural_region_coverage_complete":True,
        "semantic_candidate_exhaustiveness_paid":False,
        "nominations":nominations,
        "source_relative_answer":"UNRESOLVED_REVIEW_REQUIRED",
        "local_antecedent_admission_paid":False,
        "external_qid_paid":False,
        "claim_truth_paid":False
    }
    return inspect,frontier


class OriginalSemanticMaxCutTests(unittest.TestCase):
    def gate(self,mutator=None,**kwargs):
        inspect,frontier=fixture()
        if mutator:mutator(inspect,frontier)
        return make_ledger(inspect,frontier,**kwargs)
    def rejected(self,mutator):
        with self.assertRaises(EvidenceRejected):
            self.gate(mutator)
    def test_positive_is_unresolved_book_not_q207(self):
        manifest,review=self.gate()
        self.assertEqual(manifest["book_lane"]["answer_kind"],"EXPLICIT_UNRESOLVED")
        self.assertIsNone(manifest["book_lane"]["answer_value"])
        self.assertEqual(manifest["wikipedia_lane"]["root_qid"],"Q207")
        self.assertFalse(manifest["book_lane"]["world_q207_book_attachment_paid"])
        self.assertFalse(review["review_complete"])
    def test_s29_accept_without_semantic_witness_remains_unpaid(self):
        def mutate(i,f):
            i["s29_review_status"]=f["s29_review_status"]="Accepted"
            i["s29_receipt_commands"]=["review-command:actual-but-not-semantic"]
        manifest,review=self.gate(mutate)
        self.assertEqual(manifest["book_lane"]["s29_workflow_status"],"Accepted")
        self.assertFalse(manifest["book_lane"]["source_relative_identity_paid"])
        self.assertFalse(review["identity_admission_paid"])
    def test_kernel_markers_are_explicit_and_scope_limited(self):
        m,_=self.gate(lean_log=LEAN_MARKER+"\n",q207_log=Q207_MARKER+"\n")
        self.assertTrue(m["book_lane"]["lean_bounded_frontier_boundary_checked"])
        self.assertTrue(m["wikipedia_lane"]["minimum_source_field_kernel_checked_in_this_packet"])
        self.assertFalse(m["wikipedia_lane"]["independently_reviewed_article_kb_property_paid"])
    def test_missing_lean_marker_not_assumed(self):
        with self.assertRaises(EvidenceRejected):
            self.gate(lean_log="theorem compilation returned zero")
    def test_missing_jmd_kernel_marker_not_assumed(self):
        with self.assertRaises(EvidenceRejected):
            self.gate(q207_log="GWB_Q207_MINIMAL_ACCEPTED")
    def test_book_wikipedia_source_hashes_stay_distinct(self):
        self.assertNotEqual(BOOK_SHA,WIKI_SHA)
        self.rejected(lambda i,f:f.update(canonical_content_sha256=WIKI_SHA))
    def test_wrong_inspection_source_hash_rejected(self):
        self.rejected(lambda i,f:i.update(canonical_content_sha256=WIKI_SHA))
    def test_foreign_revision_rejected(self):
        self.rejected(lambda i,f:f.update(source_revision_ref="revision:foreign"))
    def test_foreign_original_review_item_rejected(self):
        self.rejected(lambda i,f:i.update(review_item_ref="review-item:fake"))
    def test_wrong_original_he_case_rejected(self):
        self.rejected(lambda i,f:i["focus"].update(surface="He"))
    def test_wrong_bush_substring_rejected(self):
        def mutate(i,f):
            s=i["before"][3]
            s["literal"]=s["literal"][:10]+"Rush"+s["literal"][14:]
        self.rejected(mutate)
    def test_wrong_candidate_span_rejected(self):
        self.rejected(lambda i,f:i["candidate_antecedent"].update(start_char=4311))
    def test_future_nomination_rejected(self):
        def mutate(i,f):
            n=f["nominations"][0]
            n.update(original_start_char=4800,original_end_char=4804,
                     original_statement_ref="stmt:25",original_region_ref="reg:25")
        self.rejected(mutate)
    def test_foreign_parser_nomination_rejected(self):
        self.rejected(lambda i,f:f["nominations"][0].update(
            original_region_ref="reg:unrelated"))
    def test_unsupported_semantic_promotion_rejected(self):
        self.rejected(lambda i,f:f.update(local_antecedent_admission_paid=True))
    def test_missing_candidate_exhaustiveness_never_promoted(self):
        self.rejected(lambda i,f:f.update(semantic_candidate_exhaustiveness_paid=True))
    def test_unsupported_external_qid_rejected(self):
        self.rejected(lambda i,f:f.update(external_qid_paid=True))
    def test_claim_truth_promotion_rejected(self):
        self.rejected(lambda i,f:i.update(claim_truth_paid=True))
    def test_duplicate_nomination_rejected(self):
        def mutate(i,f):
            f["nominations"].append(copy.deepcopy(f["nominations"][0]))
            f["parser_nomination_count"]=2
        self.rejected(mutate)
    def test_missing_review_alternatives_not_silent_unique(self):
        def mutate(i,f):
            n=copy.deepcopy(f["nominations"][0])
            n["nomination_ref"]="native-parser-nomination:sha256:"+("d"*64)
            n["original_start_char"]=4300
            n["original_end_char"]=4304
            n["surface"]="xxxx"
            f["nominations"].append(n)
            f["parser_nomination_count"]=2
        manifest,worksheet=self.gate(mutate)
        self.assertEqual(worksheet["candidate_count_bounded_parser_observations"],2)
        self.assertEqual(manifest["book_lane"]["answer_kind"],"EXPLICIT_UNRESOLVED")
        self.assertTrue(all(n["reviewer_disposition"]=="UNREVIEWED"
                            for n in worksheet["nominees"]))
    def test_nonoriginal_statement_rejected(self):
        self.rejected(lambda i,f:f["nominations"][0].update(
            original_statement_ref="stmt:19"))
    def test_parser_run_required(self):
        self.rejected(lambda i,f:f.update(parser_run_ref=""))
    def test_original_sentence_count_required(self):
        self.rejected(lambda i,f:i["before"].pop(0))
    def test_invalid_unicode_original_length_rejected(self):
        self.rejected(lambda i,f:i["before"][3].update(literal="Bush"))

if __name__=="__main__":
    unittest.main()
