"""Independent source-work match is never an actor/QID admission."""
import copy
import hashlib
import json
import unittest
from tools.gwb_source_work_crosscheck import verify, git_blob_sha

DOC="Perhaps he was chosen."
NATIVE={
 "authority":"candidate_only","semantic_authority_promoted":False,
 "source":{"source_revision_ref":"rev:a","document_ref":"doc:a","statement_ref":"stmt:a",
           "region_ref":"region:a","region_start_char":100,
           "document_literal":DOC,
           "region_literal_sha256":hashlib.sha256(DOC.encode()).hexdigest()},
 "focus_mention":{"mention_ref":"mention:a","source_start_char":108,
                  "source_end_char":110,"surface":"he"}
}
TIMELINE={"events":[
 {"event_id":"prev","path":"same:book","text":"Bush was discussed."},
 {"event_id":"current","path":"same:book","text":"Perhaps he was chosen. Then ..."}]}
RAW=json.dumps(TIMELINE).encode()
RECEIPT={
 "authority":"candidate_only",
 "native":{"source_revision_ref":"rev:a","document_ref":"doc:a",
           "statement_ref":"stmt:a","region_ref":"region:a",
           "focus_mention_ref":"mention:a","focus_start_char":108,
           "focus_end_char":110},
 "independent_timeline":{"git_blob_sha1":git_blob_sha(RAW),
        "matching_event_id":"current","prior_same_work_event_id":"prev",
        "source_path_original":"same:book","shared_source_path":True},
 "comparison":{"native_folded_length":len(DOC),
         "exact_native_manifestation_equality":"NOT_PROVED",
         "reviewed_antecedent":"NOT_PROVED",
         "external_person_qid":"NOT_PROVED",
         "world_truth_promoted":False}
}
class SourceWorkProofTests(unittest.TestCase):
 def check(self,native=NATIVE,timeline=TIMELINE,receipt=RECEIPT,raw=RAW):
  return verify(copy.deepcopy(native),copy.deepcopy(timeline),
                copy.deepcopy(receipt),raw)
 def test_positive_is_work_candidate_only(self):
  a=self.check()
  self.assertEqual(a["source_work_candidate"],"MATCHED_INDEPENDENT_EXCERPT")
  self.assertEqual(a["identity_admission"],"NOT_TESTED")
  self.assertEqual(a["canonical_source_equality"],"NOT_PROVED")
 def test_wrong_native_revision(self):
  a=copy.deepcopy(NATIVE);a["source"]["source_revision_ref"]="rev:foreign"
  with self.assertRaisesRegex(ValueError,"native source mismatch"):self.check(native=a)
 def test_wrong_prior_work(self):
  a=copy.deepcopy(TIMELINE);a["events"][0]["path"]="other:book"
  with self.assertRaisesRegex(ValueError,"same-work"):self.check(timeline=a)
 def test_tampered_timeline_bytes(self):
  with self.assertRaisesRegex(ValueError,"Git blob mismatch"):
   self.check(raw=RAW+b"tampered")
 def test_wrong_excerpt(self):
  a=copy.deepcopy(TIMELINE);a["events"][1]["text"]="She was chosen."
  with self.assertRaisesRegex(ValueError,"excerpt mismatch"):self.check(timeline=a)
 def test_unlicensed_identity_admission(self):
  a=copy.deepcopy(RECEIPT);a["comparison"]["reviewed_antecedent"]="RESOLVED"
  with self.assertRaisesRegex(ValueError,"illegally promoted"):self.check(receipt=a)
 def test_wrong_focus_span(self):
  a=copy.deepcopy(NATIVE);a["focus_mention"]["source_start_char"]=109
  with self.assertRaisesRegex(ValueError,"focus mismatch"):self.check(native=a)
 def test_missing_prior_actor_context(self):
  a=copy.deepcopy(TIMELINE);a["events"][0]["text"]="No actor named."
  with self.assertRaisesRegex(ValueError,"preceding same-work"):self.check(timeline=a)

if __name__=="__main__":unittest.main()
