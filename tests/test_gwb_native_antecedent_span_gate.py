"""C4.10: native SLR source-span geometry does not constitute identity."""
import copy
import unittest
from tools.gwb_native_antecedent_span_gate import check_candidate

PREFIX = "Café: Mr Bush arrived."
CENTRE = "Then he spoke."
AFTER = " He departed."
CENTER_START = len(PREFIX)
AFTER_START = CENTER_START + len(CENTRE)
HASH = "f" * 64
CTX = {
  "schema": "slr-native-original-discourse-context-v1",
  "original_source_ref": "source:foo",
  "source_revision_ref": "source-revision:foo",
  "document_ref": "document:sha256:" + HASH,
  "canonical_content_sha256": HASH,
  "focus": {"mention_ref": "mention:he", "candidate_ref": "candidate:he",
            "statement_ref": "stmt:centre", "region_ref": "region:centre",
            "start_char": CENTER_START+5, "end_char": CENTER_START+7,
            "surface": "he"},
  "before": [{"region_ref":"region:before", "statement_ref":"stmt:before",
              "start_char":0, "end_char":len(PREFIX),
              "literal":PREFIX, "candidate_only":True}],
  "at": {"region_ref":"region:centre", "statement_ref":"stmt:centre",
         "start_char":CENTER_START,"end_char":AFTER_START,
         "literal":CENTRE,"candidate_only":True},
  "after": [{"region_ref":"region:after","statement_ref":"stmt:after",
             "start_char":AFTER_START,"end_char":AFTER_START+len(AFTER),
             "literal":AFTER,"candidate_only":True}],
  "antecedent_resolution":"UNRESOLVED_REVIEW_REQUIRED",
  "resolved_referent":None,"external_qid":"NOT_TESTED",
  "semantic_authority_promoted":False,
}
A = PREFIX.index("Bush")
CAND = {"statement_ref":"stmt:before", "region_ref":"region:before",
        "start_char":A,"end_char":A+4,"surface":"Bush"}

class SourceSpanAcceptance(unittest.TestCase):
  def gate(self,ctx=CTX,cand=CAND):
    return check_candidate(copy.deepcopy(ctx),copy.deepcopy(cand))
  def test_positive_candidate_only(self):
    r=self.gate()
    self.assertEqual(r["antecedent_source_span"]["surface"],"Bush")
    self.assertTrue(r["same_source_span_geometry_checked"])
    self.assertEqual(r["identity_admission"],"NOT_PAID")
    self.assertEqual(r["antecedent_resolution"],"REVIEW_REQUIRED")
    self.assertEqual(r["external_qid"],"NOT_TESTED")
  def test_unicode_absolute_char_spans(self):
    self.assertEqual(PREFIX[A:A+4],"Bush")
    self.gate()
  def test_future_candidate_rejected(self):
    c={"statement_ref":"stmt:after", "region_ref":"region:after",
       "start_char":AFTER_START+1,"end_char":AFTER_START+3,"surface":"He"}
    with self.assertRaisesRegex(ValueError,"preceding discourse"):self.gate(cand=c)
  def test_candidate_span_outside_statement_rejected(self):
    c=copy.deepcopy(CAND);c["end_char"]=AFTER_START+1
    with self.assertRaisesRegex(ValueError,"outside selected"):self.gate(cand=c)
  def test_forged_candidate_surface_rejected(self):
    c=copy.deepcopy(CAND);c["surface"]="Reagan"
    with self.assertRaisesRegex(ValueError,"exact surface mismatch"):self.gate(cand=c)
  def test_unresolved_context_required(self):
    x=copy.deepcopy(CTX);x["antecedent_resolution"]="RESOLVED"
    with self.assertRaisesRegex(ValueError,"boundaries changed"):self.gate(ctx=x)
  def test_zero_position_allowed(self):
    c={"statement_ref":"stmt:before", "region_ref":"region:before",
       "start_char":0,"end_char":4,"surface":"Café"}
    self.gate(cand=c)
  def test_foreign_statement_rejected(self):
    c=copy.deepcopy(CAND);c["statement_ref"]="stmt:other"
    with self.assertRaisesRegex(ValueError,"preceding discourse"):self.gate(cand=c)
  def test_overlapping_original_regions_rejected(self):
    x=copy.deepcopy(CTX);x["at"]["start_char"]-=1;x["at"]["end_char"]-=1
    with self.assertRaisesRegex(ValueError,"unordered or overlapping"):self.gate(ctx=x)
  def test_promoted_original_statement_rejected(self):
    x=copy.deepcopy(CTX);x["before"][0]["candidate_only"]=False
    with self.assertRaisesRegex(ValueError,"context entry promoted"):self.gate(ctx=x)
  def test_duplicate_original_statement_rejected(self):
    x=copy.deepcopy(CTX);x["before"].append(copy.deepcopy(x["before"][0]))
    with self.assertRaisesRegex(ValueError,"duplicate source statement"):self.gate(ctx=x)
  def test_self_pronoun_rejected(self):
    c={"statement_ref":"stmt:centre", "region_ref":"region:centre",
       "start_char":CENTER_START+5,"end_char":CENTER_START+7,"surface":"he"}
    with self.assertRaisesRegex(ValueError,"not before the pronoun"):self.gate(cand=c)
  def test_wrong_focus_surface_rejected(self):
    x=copy.deepcopy(CTX);x["focus"]["surface"]="He"
    with self.assertRaisesRegex(ValueError,"focus original-surface mismatch"):self.gate(ctx=x)
  def test_document_digest_mismatch_rejected(self):
    x=copy.deepcopy(CTX);x["document_ref"]="document:sha256:" + ("1"*64)
    with self.assertRaisesRegex(ValueError,"canonical source/document mismatch"):self.gate(ctx=x)

if __name__=='__main__':unittest.main()
