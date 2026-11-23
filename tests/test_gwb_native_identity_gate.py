"""Fail-closed C4.09b numeric DB proof gate (isolated fake read-only rows)."""
import copy
import sys
import types
import unittest

# Unit tests isolate native↔owner verification (adapter's own 12 controls)
# from the original SensibLaw proof-table join.
shim = types.ModuleType("tools.gwb_native_binding_adapter")
def require(condition, reason):
    if not condition:
        raise ValueError(reason)
shim.require = require
shim.verify_owner_carrier = lambda native, owner: {"source_alignment": "EXACT"}
sys.modules["tools.gwb_native_binding_adapter"] = shim
from tools.gwb_native_identity_gate import audit

SOURCE = {"source_revision_ref":"rev:A", "parser_run_ref":"run:A",
          "region_ref":"region:A", "document_ref":"doc:A",
          "region_start_char":100, "region_end_char":113}
FOCUS = {"mention_ref":"mention:he", "source_start_char":110,
         "source_end_char":112, "surface":"he", "candidate_ref":"candidate:A"}
NATIVE = {"authority":"candidate_only", "semantic_authority_promoted":False,
          "source":SOURCE, "focus_mention":FOCUS,
          "parser_tokens":[{"start_char":110,"end_char":112,"pos":"PRON"}]}
OWNER = {"pnf_graph":{"graph_ref":"graph:A", "factors":[{"factor_ref":"factor:he",
          "metadata":{"parser_pos":"PRON", "atom_span_ref":"span:he"}}]},
         "semantic_annotation_layer":{"span_annotations":[
             {"span_ref":"span:he", "annotation_type":"semantic_atom",
              "start_token":0,"end_token":1}]}}
CROSS = {**{key:SOURCE[key] for key in ("source_revision_ref","parser_run_ref","region_ref")},
         **{key:FOCUS[key] for key in ("source_start_char","source_end_char","surface","candidate_ref")},
         "owner_document_ref":"doc:A", "owner_run_ref":"owner-run:A",
         "coordinate_frame":"region_local", "factor_ref":"factor:he",
         "owner_graph_ref":"graph:A",
         "source_object_id":6,"premise_factor_id":11,"demand_id":22}
BASE = {"object": [("owner-run:A","doc:A",0,13)],
        "hyperedge": [(1,)],
        "anchor": [("token:he",0,10,12,"he","PRON")],
        "frontier": [(1,99,2,1)],
        "projection": [(88,99,2,[444])],
        "witness": [(444,5,1,2,2)],
        "derivation": [(777,88,[444])]}

class Cursor:
    def __init__(self, data): self.data = data
    def __enter__(self): return self
    def __exit__(self,*args): return False
    def execute(self, sql, args):
        for clue, name in (("semantic_pnf_parser_object_anchor", "anchor"),
                            ("semantic_pnf_hyperedge", "hyperedge"),
                            ("semantic_pnf_frontier_resolution", "frontier"),
                            ("semantic_pnf_identity_projection", "projection"),
                            ("semantic_pnf_identity_witness_admission", "witness"),
                            ("semantic_pnf_factor_derivation", "derivation"),
                            ("semantic_pnf_object o", "object")):
            if clue in sql:
                self.result = self.data[name]
                return
        raise AssertionError("unexpected SQL query")
    def fetchall(self): return self.result

class Conn:
    def __init__(self, data): self.data=data
    def cursor(self): return Cursor(self.data)

class IdentityGateTests(unittest.TestCase):
    def run_gate(self, *, native=NATIVE, owner=OWNER, cross=CROSS, data=BASE):
        return audit(copy.deepcopy(native),copy.deepcopy(owner),copy.deepcopy(cross),
                     Conn(copy.deepcopy(data)))
    def test_valid_original_db_chain_is_document_local_only(self):
        result = self.run_gate()
        self.assertEqual(result["identity_admission"],"ORIGINAL_DB_ADMITTED_RESOLVED_UNIQUE")
        self.assertEqual(result["external_qid"],"NOT_TESTED")
        self.assertEqual(result["derivation_ids"],[777])
    def test_wrong_revision(self):
        x=copy.deepcopy(CROSS);x["source_revision_ref"]="rev:B"
        with self.assertRaisesRegex(ValueError,"wrong source_revision_ref"):self.run_gate(cross=x)
    def test_foreign_document(self):
        x=copy.deepcopy(BASE);x["object"]=[("owner-run:A","doc:B",0,13)]
        with self.assertRaisesRegex(ValueError,"numeric source scope mismatch"):self.run_gate(data=x)
    def test_crosswalk_not_owned_by_factor(self):
        x=copy.deepcopy(OWNER);x["pnf_graph"]["graph_ref"]="graph:other"
        with self.assertRaisesRegex(ValueError,"crosswalk does not name"):self.run_gate(owner=x)
    def test_ambiguous_demand(self):
        x=copy.deepcopy(BASE);x["frontier"]=[(1,None,3,2)]
        with self.assertRaisesRegex(ValueError,"not resolved_unique"):self.run_gate(data=x)
    def test_unadmitted_witness(self):
        x=copy.deepcopy(BASE);x["witness"]=[(444,5,1,2,3)]
        with self.assertRaisesRegex(ValueError,"missing admitted anaphor"):self.run_gate(data=x)
    def test_wrong_witness_kind(self):
        x=copy.deepcopy(BASE);x["witness"]=[(444,3,1,2,2)]
        with self.assertRaisesRegex(ValueError,"missing admitted anaphor"):self.run_gate(data=x)
    def test_missing_substitution(self):
        x=copy.deepcopy(BASE);x["derivation"]=[]
        with self.assertRaisesRegex(ValueError,"no Level-3"):self.run_gate(data=x)
    def test_substitution_drops_witness(self):
        x=copy.deepcopy(BASE);x["derivation"]=[(777,88,[999])]
        with self.assertRaisesRegex(ValueError,"does not retain"):self.run_gate(data=x)
    def test_wrong_span(self):
        x=copy.deepcopy(CROSS);x["source_start_char"]=109
        with self.assertRaisesRegex(ValueError,"crosswalk wrong source_start_char"):self.run_gate(cross=x)
    def test_missing_projection(self):
        x=copy.deepcopy(BASE);x["projection"]=[]
        with self.assertRaisesRegex(ValueError,"expected exactly one persisted row"):self.run_gate(data=x)
    def test_promoted_native(self):
        x=copy.deepcopy(NATIVE);x["semantic_authority_promoted"]=True
        with self.assertRaisesRegex(ValueError,"promoted native authority"):self.run_gate(native=x)
    def test_nonpronoun_factor(self):
        x=copy.deepcopy(OWNER);x["pnf_graph"]["factors"][0]["metadata"]["parser_pos"]="PROPN"
        with self.assertRaisesRegex(ValueError,"owner focus factor"):self.run_gate(owner=x)
    def test_unanchored_numeric_object(self):
        x=copy.deepcopy(BASE);x["anchor"]=[]
        with self.assertRaisesRegex(ValueError,"original unique parser-token/object anchor"):
            self.run_gate(data=x)
    def test_ambiguous_numeric_anchor(self):
        x=copy.deepcopy(BASE);x["anchor"]*=2
        with self.assertRaisesRegex(ValueError,"expected exactly one persisted row"):
            self.run_gate(data=x)
    def test_mismatched_native_anchor_surface(self):
        x=copy.deepcopy(BASE);x["anchor"]=[("token:he",0,10,12,"she","PRON")]
        with self.assertRaisesRegex(ValueError,"anchor disagrees with native"):
            self.run_gate(data=x)
    def test_missing_source_premise(self):
        x=copy.deepcopy(BASE);x["hyperedge"]=[(0,)]
        with self.assertRaisesRegex(ValueError,"missing original Level-1"):self.run_gate(data=x)
    def test_wrong_region_coordinates(self):
        x=copy.deepcopy(BASE);x["object"]=[("owner-run:A","doc:A",0,9)]
        with self.assertRaisesRegex(ValueError,"excludes focus"):self.run_gate(data=x)

if __name__=="__main__": unittest.main()
