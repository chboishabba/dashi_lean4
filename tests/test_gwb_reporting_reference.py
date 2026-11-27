import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from publish_gwb_original_slr_receipts import reporting_reference

class ReportingReferenceTest(unittest.TestCase):
    def test_coordination_and_signed_scope(self):
        def event(i, head, dep, lemma, sentence=1, claim="c"):
            return {"sentence_index":sentence, "slr_claim_candidate_id":claim,
                    "predicate":{"i":i, "head_i":head, "dep":dep, "lemma":lemma}}
        events = [event(1,1,"ROOT","state"), event(3,1,"ccomp","stimulate"),
                  event(4,3,"conj","create"), event(6,1,"ccomp","fall",2,"d")]
        raw = {"pnf_candidates":[
            {"sentence_index":1,"claim_candidate_id":"c","dependency_rows":[
                {"i":2,"head_i":1,"dep":"neg","text":"not","idx":0},
                {"i":5,"head_i":4,"dep":"neg","text":"not","idx":4}]},
            {"sentence_index":2,"claim_candidate_id":"d","dependency_rows":[]}]}
        rows = reporting_reference("not not",raw,{"event_candidates":events},"state")
        self.assertEqual([r["content"]["predicate"]["i"] for r in rows],[3,4])
        self.assertEqual([t["i"] for t in rows[0]["report_negation_tokens"]],[2])
        self.assertEqual(rows[0]["content_negation_tokens"],[])
        self.assertEqual([t["i"] for t in rows[1]["content_negation_tokens"]],[5])
        self.assertEqual(rows[1]["complement_negation_tokens"],[])
        self.assertEqual(reporting_reference("not not",raw,{"event_candidates":events},"say"),[])
        altered = reporting_reference("bad not",raw,{"event_candidates":events},"state")
        self.assertEqual(altered[0]["report_negation_tokens"],[])

if __name__ == "__main__":
    unittest.main()
