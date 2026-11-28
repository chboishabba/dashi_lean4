import RequestProject.Slr.WikipediaArticleProof
import RequestProject.Slr.GwbArticleIdentity
import RequestProject.Slr.GwbWorldGraphProof

/-! Generic source inspection. Reuses original JMD import/checkers
(meta-introspector) and SLR source projection. A sitelink is navigation,
not semantic identity of claims. No special QID or predicate vocabulary. -/
namespace Wikidata.Slr.IndexedWorldFibreInspection

open Lean

def arr (j : Json) (key : String) : List Json :=
  ((j.getObjValAs? (Array Json) key).toOption.getD #[]).toList

def str (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

def checkRoot (qid title article : String) (source projection entity : Json) : Bool :=
  let revision := str source "revision_ref"
  Wikidata.Slr.ArticleProof.checkProjectionFor qid article source projection &&
  Wikidata.Slr.GwbArticleIdentity.checkSitelink qid title entity &&
  Wikidata.Slr.GwbWorldGraph.jsonEntityMatchesQid qid entity &&
  revision.startsWith "enwiki-revid:" &&
  (match (revision.drop "enwiki-revid:".length).toString.toNat? with
   | some n => decide (n > 0) && str source "source_unit_ref" ==
       ("wikipedia:en:" ++ title.replace " " "_" ++ ":" ++ toString n)
   | none => false)

structure CheckedRoot (qid title article : String) (source projection entity : Json) where
  checked : checkRoot qid title article source projection entity = true

/-- All recorded rows in each declared chart; unknown lanes have no answer. -/
def articleMembers (source projection : Json) (lane : String) : Option (List Json) :=
  if lane == "pnf_candidates" || lane == "named_entities" then
    (source.getObjValAs? (Array Json) lane).toOption.map Array.toList
  else if ["sections","event_candidates","people_mentions","time_mentions",
      "proper_noun_tokens","literal_year_mentions","timeline_candidates",
      "text_order_edges"].contains lane then
    (projection.getObjValAs? (Array Json) lane).toOption.map Array.toList
  else none

def membersMatching (rows : List Json) (test : Json → Bool) : List Json :=
  rows.filter test

theorem membersMatchingExact (rows : List Json) (test : Json → Bool) (row : Json) :
    row ∈ membersMatching rows test ↔ row ∈ rows ∧ test row = true := by
  simp only [membersMatching, List.mem_filter]

def propertyMembers (entity : Json) (qid property : String) : List Json :=
  Wikidata.Slr.GwbWorldGraph.originalPropertyRows entity qid property

theorem propertyMembersExact (entity : Json) (qid property : String) (row : Json) :
    row ∈ propertyMembers entity qid property ↔
    row ∈ Wikidata.Slr.GwbWorldGraph.originalPropertyRows entity qid property := Iff.rfl

/-- Each source retains its own row membership. No cross-source proposition
alignment follows from sharing a root or matching a property string. -/
theorem independentlyCheckedMembers
    {qid title article : String} {source projection entity : Json}
    (root : CheckedRoot qid title article source projection entity)
    (lane property : String) (rows : List Json) (a b : Json)
    (selected : articleMembers source projection lane = some rows)
    (ha : a ∈ rows) (hb : b ∈ propertyMembers entity qid property) :
    checkRoot qid title article source projection entity = true ∧
    articleMembers source projection lane = some rows ∧ a ∈ rows ∧
    b ∈ Wikidata.Slr.GwbWorldGraph.originalPropertyRows entity qid property :=
  ⟨root.checked, selected, ha, hb⟩

def inventory (qid title : String) (source projection entity : Json)
    (properties : List String) : Json :=
  Json.mkObj [
    ("schema", toJson ("slr.jmd-indexed-world-fibre.v1" : String)),
    ("qid", toJson qid), ("title", toJson title),
    ("article_revision", toJson (str source "revision_ref")),
    ("article_lanes", Json.mkObj
      ((["pnf_candidates","named_entities","sections","event_candidates","people_mentions",
        "time_mentions","proper_noun_tokens","literal_year_mentions","timeline_candidates",
        "text_order_edges"] : List String).map (fun k =>
        (k, toJson (articleMembers source projection k))))),
    ("wikidata_lanes", Json.mkObj (properties.map (fun p =>
      (p, toJson (propertyMembers entity qid p))))),
    ("semantic_coverage_paid", toJson false),
    ("cross_source_alignment_paid", toJson false),
    ("world_truth_paid", toJson false)]

end Wikidata.Slr.IndexedWorldFibreInspection

#print axioms Wikidata.Slr.IndexedWorldFibreInspection.membersMatchingExact
#print axioms Wikidata.Slr.IndexedWorldFibreInspection.independentlyCheckedMembers
