"""Original SensibLaw binding compilation interop: exact source, no QID."""
import copy
import unittest
from tools.gwb_native_maxcut_ledger import BOOK_SHA, EvidenceRejected
from tools.gwb_original_binding_interop import factor_anchor_spans, weld_original_binding
from test_gwb_native_maxcut_ledger import fixture


def binder_fixture():
    i,f=fixture()
    # Original *synthetic test-only* canonical source, with the precise
    # same book source SHA impossible to reproduce from these short fixtures.
    # Tests below exercise rejection and mapping helpers, not live welding.
    text="hello Bush ... he"
    artifacts={
        "canonical_text":text,
        "pnf_graph":{"document_ref":i["document_ref"]},
        "semantic_annotation_layer":{
            "span_annotations":[
                {"annotation_type":"parser_token","start_token":1,
                 "end_token":2,"value":{"start_char":6,"end_char":10}},
                {"annotation_type":"parser_token","start_token":3,
                 "end_token":4,"value":{"start_char":15,"end_char":17}},
            ]
        }
    }
    compiled={
        "factor_anchors":[
            {"factor_ref":"factor:bush","factor_revision_ref":"revision:bush",
             "document_ref":i["document_ref"],"start_token":1,"end_token":2},
            {"factor_ref":"factor:he","factor_revision_ref":"revision:he",
             "document_ref":i["document_ref"],"start_token":3,"end_token":4},
        ],
        "binding_compaction_summary":{
            "generation_mode":"direct_observation_graph_index",
            "authority":"diagnostic_only"
        },
        "binding_accessibility_declaration":{"authority":"configuration_only"},
        "binding_compatibility_declaration":{"authority":"configuration_only"},
        "binding_candidate_sets":[]
    }
    return i,f,artifacts,compiled


class OriginalProducerBindingInteropTests(unittest.TestCase):
    def test_original_factor_token_coordinates_reconstructed(self):
        i,f,a,c=binder_fixture()
        rows=factor_anchor_spans(a,c,i["document_ref"])
        self.assertEqual(rows["factor:bush"]["surface"],"Bush")
        self.assertEqual(rows["factor:bush"]["start_char"],6)
        self.assertEqual(rows["factor:bush"]["end_char"],10)
        self.assertEqual(rows["factor:he"]["surface"],"he")
    def test_changed_original_token_offset_rejected(self):
        i,f,a,c=binder_fixture()
        a["semantic_annotation_layer"]["span_annotations"].append({
            "annotation_type":"parser_token","start_token":1,
            "end_token":2,"value":{"start_char":7,"end_char":10}
        })
        with self.assertRaises(EvidenceRejected):
            factor_anchor_spans(a,c,i["document_ref"])
    def test_foreign_original_factor_document_rejected(self):
        i,f,a,c=binder_fixture()
        c["factor_anchors"][0]["document_ref"]="document:foreign"
        with self.assertRaises(EvidenceRejected):
            factor_anchor_spans(a,c,i["document_ref"])
    def test_factor_duplicate_mapped_to_different_span_rejected(self):
        i,f,a,c=binder_fixture()
        r=copy.deepcopy(c["factor_anchors"][0])
        r["start_token"]=3
        r["end_token"]=4
        c["factor_anchors"].append(r)
        with self.assertRaises(EvidenceRejected):
            factor_anchor_spans(a,c,i["document_ref"])
    def test_full_book_sha_not_forged_by_small_test_text(self):
        i,f,a,c=binder_fixture()
        with self.assertRaisesRegex(EvidenceRejected,"exact native SLR book"):
            weld_original_binding(i,f,a,c)
    def test_cross_work_document_rejected_before_compiler_semantics(self):
        i,f,a,c=binder_fixture()
        a["pnf_graph"]["document_ref"]="document:another-work"
        with self.assertRaises(EvidenceRejected):
            weld_original_binding(i,f,a,c)
    def test_no_original_parser_annotation_graph_rejected(self):
        i,f,a,c=binder_fixture()
        del a["semantic_annotation_layer"]["span_annotations"]
        with self.assertRaises(EvidenceRejected):
            factor_anchor_spans(a,c,i["document_ref"])
    def test_no_original_factor_span_rejected(self):
        i,f,a,c=binder_fixture()
        c["factor_anchors"][0]["start_token"]=200
        rows=factor_anchor_spans(a,c,i["document_ref"])
        self.assertNotIn("factor:bush",rows)
    def test_book_and_wikipedia_shas_are_distinct(self):
        from tools.gwb_native_maxcut_ledger import WIKI_SHA
        self.assertNotEqual(BOOK_SHA,WIKI_SHA)

if __name__=="__main__": unittest.main()
