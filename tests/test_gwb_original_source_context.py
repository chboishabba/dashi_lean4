"""C4.09 original SLR discourse reopening: no new NLP and no identity promotion."""
import copy
import hashlib
import unittest
from unittest.mock import patch

from tools.gwb_original_source_context import reopen

TEXT = "Café. George H. W. Bush was considered. Perhaps he was chosen. Afterward."
BEFORE = "Café. George H. W. Bush was considered. "
FOCUS_SENTENCE = "Perhaps he was chosen."
AFTER = " Afterward."
START = len(BEFORE)
END = START + len(FOCUS_SENTENCE)
HE_START = START + len("Perhaps ")
HE_END = HE_START + 2
DIGEST = hashlib.sha256(TEXT.encode("utf-8")).hexdigest()
DOC = "document:sha256:" + DIGEST
REV = "source-revision:original"
NATIVE = {
  "schema":"gwb-native-parser-binding-carrier-v1",
  "authority":"candidate_only","semantic_authority_promoted":False,
  "source":{"source_revision_ref":REV,"document_ref":DOC,
            "statement_ref":"stmt:focus","region_ref":"region:focus",
            "region_start_char":START,"region_end_char":END,
            "document_literal":FOCUS_SENTENCE,
            "region_literal_sha256":hashlib.sha256(FOCUS_SENTENCE.encode()).hexdigest()},
  "focus_mention":{"mention_ref":"mention:he","candidate_ref":"candidate:he",
                   "source_start_char":HE_START,"source_end_char":HE_END,
                   "surface":"he"},
  "parser_tokens":[],"parser_entities":[],"pnf_product_factors":[],"l2_entity_factors":[]
}
SOURCE = [("source:original",DOC,"sha256:"+DIGEST,True,False,False,False,TEXT.encode())]
def row(region, start, end, stmt, literal):
    return (region,start,end,"sentence",stmt,literal,
            True,False,False,False,True,False,False)
STATEMENTS = [
 row("region:before",0,START,"stmt:before",BEFORE),
 row("region:focus",START,END,"stmt:focus",FOCUS_SENTENCE),
 row("region:after",END,len(TEXT),"stmt:after",AFTER)
]

class Cursor:
    def __init__(self,source,statements):self.source=source;self.statements=statements
    def __enter__(self):return self
    def __exit__(self,*_):return False
    def execute(self, sql, params):
        if "FROM ingest.generic_source_revision" in sql:self.output=self.source
        elif "FROM ingest.long_document_region" in sql:self.output=self.statements
        else:raise AssertionError("unknown original source SQL")
    def fetchall(self):return self.output
class DB:
    def __init__(self,source=SOURCE,statements=STATEMENTS):
        self.source=source;self.statements=statements
    def cursor(self):return Cursor(self.source,self.statements)

class NativeContextTests(unittest.TestCase):
    def reopened(self,native=NATIVE,source=SOURCE,statements=STATEMENTS):
        with patch("tools.gwb_original_source_context.validate_region"):
            return reopen(copy.deepcopy(native),DB(copy.deepcopy(source),copy.deepcopy(statements)))
    def test_original_context_keeps_provenance_and_nonpromotion(self):
        a=self.reopened()
        self.assertEqual([x["statement_ref"] for x in a["before"]],["stmt:before"])
        self.assertEqual(a["focus"]["surface"],"he")
        self.assertEqual(a["canonical_content_sha256"],DIGEST)
        self.assertEqual(a["antecedent_resolution"],"UNRESOLVED_REVIEW_REQUIRED")
        self.assertIsNone(a["resolved_referent"])
        self.assertEqual(a["external_qid"],"NOT_TESTED")
    def test_unicode_offsets_are_characters(self):
        self.assertEqual(TEXT[:5],"Café.")
        self.assertEqual(TEXT[HE_START:HE_END],"he")
        self.reopened()
    def test_wrong_original_revision_rejected(self):
        with self.assertRaisesRegex(ValueError,"missing/ambiguous canonical source"):
            self.reopened(source=[])
    def test_wrong_document_rejected(self):
        bad=copy.deepcopy(SOURCE);x=list(bad[0]);x[1]="document:other";bad=[tuple(x)]
        with self.assertRaisesRegex(ValueError,"foreign document"):self.reopened(source=bad)
    def test_promoted_original_source_rejected(self):
        bad=copy.deepcopy(SOURCE);x=list(bad[0]);x[4]=True;bad=[tuple(x)]
        with self.assertRaisesRegex(ValueError,"source revision promoted"):self.reopened(source=bad)
    def test_modified_original_payload_rejected(self):
        bad=copy.deepcopy(SOURCE);x=list(bad[0]);x[-1]=b"forged";bad=[tuple(x)]
        with self.assertRaisesRegex(ValueError,"stored canonical digest mismatch"):self.reopened(source=bad)
    def test_forged_native_literal_rejected(self):
        bad=copy.deepcopy(NATIVE);bad["source"]["document_literal"]="Perhaps she was chosen."
        with self.assertRaisesRegex(ValueError,"archived region checksum mismatch"):self.reopened(native=bad)
    def test_modified_neighbour_rejected(self):
        bad=list(STATEMENTS);x=list(bad[0]);x[5]="Forged!";bad[0]=tuple(x)
        with self.assertRaisesRegex(ValueError,"neighbor original-source mismatch"):self.reopened(statements=bad)
    def test_duplicate_region_rejected(self):
        with self.assertRaisesRegex(ValueError,"ambiguous same-revision"):
            self.reopened(statements=STATEMENTS+[STATEMENTS[1]])
    def test_missing_focus_rejected(self):
        with self.assertRaisesRegex(ValueError,"focus not one persisted"):
            self.reopened(statements=[STATEMENTS[0],STATEMENTS[2]])
    def test_candidate_only_neighbour_required(self):
        bad=list(STATEMENTS);x=list(bad[0]);x[6]=False;bad[0]=tuple(x)
        with self.assertRaisesRegex(ValueError,"neighbor source/region promoted"):self.reopened(statements=bad)
    def test_bounds_rejected(self):
        with self.assertRaisesRegex(ValueError,"context bounds"):
            self.reopened(native=NATIVE, statements=STATEMENTS) if False else reopen(NATIVE,DB(),before=21)

if __name__=="__main__":unittest.main()
