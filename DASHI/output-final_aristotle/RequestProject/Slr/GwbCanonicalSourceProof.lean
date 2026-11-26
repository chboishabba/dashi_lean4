import RequestProject.Slr.WikipediaArticleProof
import RequestProject.Slr.DocumentQuerySound

/-! Canonical source proof population. SLR is production; Lean/Agda golden.
No experimental semantic-expansion input. These are source observations,
not admitted identities or historical occurrences. -/
namespace Wikidata.Slr.GwbCanonicalSource
open Lean

def rows (j : Json) (key : String) : List Json :=
  ((j.getObjValAs? (Array Json) key).toOption.getD #[]).toList

def field (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

def events (projection : Json) : List Json := rows projection "event_candidates"

structure SourceAnchor (article : String) (slr projection : Json) where
  checked : ArticleProof.CheckedArticleExtraction article slr projection
  event : Json
  present : event ∈ events projection

theorem anchorRetainsOriginal {article : String} {slr projection : Json}
    (a : SourceAnchor article slr projection) :
    ArticleProof.checkProjection article slr projection = true ∧
    a.event ∈ events projection :=
  ⟨a.checked.checked, a.present⟩

/-- Instantiate a proof for every original event, retaining the complete JSON
    rather than collapsing subject/object spans into an alternative vocabulary. -/
def populate {article : String} {slr projection : Json}
    (checked : ArticleProof.CheckedArticleExtraction article slr projection) :
    List (SourceAnchor article slr projection) :=
  (events projection).attach.map fun e => ⟨checked, e.val, e.property⟩

def predicateSurface (event : Json) : String :=
  field ((event.getObjVal? "predicate").toOption.getD Json.null) "surface"

def predicateQuery (projection : Json) (surface : String) : List Json :=
  (events projection).filter (fun e => predicateSurface e == surface)

/-- Concrete source-only query, not a semantic identity answer. -/
theorem predicateQuerySound (projection : Json) (surface : String) (e : Json)
    (h : e ∈ predicateQuery projection surface) :
    e ∈ events projection ∧ predicateSurface e = surface := by
  have hh := List.mem_filter.mp h
  exact ⟨hh.1, beq_iff_eq.mp hh.2⟩

/-- Exact source-observation consumer. The observation is the complete
    original checked event array, not a semantic interpretation. -/
def sourceModel : DocumentQueryModel Json Json Json String (List Json) where
  observe := id
  live := fun observation reading => reading = observation
  documentAnswer := predicateQuery
  readingAnswer := predicateQuery

/-- Source-only predicate query licence: the observation is the original
    projection itself. No semantic completeness or reviewed identity follows. -/
def sourcePredicateLicence (projection : Json) (surface : String) :
    SourceQueryLicence sourceModel projection surface where
  observation := projection
  sameProducedObservation := rfl
  chosenReading := projection
  chosenIsLive := rfl
  consumerFactorises := by
    intro other h
    exact congrArg (fun j => predicateQuery j surface) h
  consumerClosed := by
    intro reading h
    exact congrArg (fun j => predicateQuery j surface) h

theorem licensedPredicateQuerySound (projection : Json) (surface : String) :
    sourceModel.documentAnswer projection surface = predicateQuery projection surface :=
  slrJmdDocumentQuerySound (sourcePredicateLicence projection surface)
    (predicateQuery projection surface) rfl

/-- A source-bound evaluated query with both directions of membership.
    No arbitrary evidence proposition or external identity premise. -/
theorem predicateQueryComplete (projection : Json) (surface : String) (e : Json) :
    e ∈ predicateQuery projection surface ↔
      e ∈ events projection ∧ predicateSurface e = surface := by
  constructor
  · exact predicateQuerySound projection surface e
  · intro h
    exact List.mem_filter.mpr ⟨h.1, beq_iff_eq.mpr h.2⟩

def run (articlePath sourcePath projectionPath outputPath : String) : IO UInt32 := do
  let ok ← ArticleProof.verifyFiles articlePath sourcePath projectionPath
  if !ok then return 1
  let article ← IO.FS.readFile articlePath
  match Json.parse (← IO.FS.readFile sourcePath), Json.parse (← IO.FS.readFile projectionPath) with
  | .ok slr, .ok projection =>
    if h : ArticleProof.checkProjection article slr projection = true then
      let checked : ArticleProof.CheckedArticleExtraction article slr projection := ⟨h⟩
      let anchors := populate checked
      let output := anchors.map fun a =>
        let _ := anchorRetainsOriginal a
        Json.mkObj [("event", a.event), ("predicate_surface", toJson (predicateSurface a.event))]
      let surfaces := (events projection).map predicateSurface
      let queries := surfaces.eraseDups.map fun surface =>
        let answer := predicateQuery projection surface
        let _ := licensedPredicateQuerySound projection surface
        Json.mkObj [("query", toJson surface), ("answer", toJson answer),
          ("scope", toJson ("original-predicate-surface-only" : String))]
      IO.FS.writeFile outputPath ((Json.mkObj [
        ("schema", toJson ("gwb-canonical-lean-source-instances-v1" : String)),
        ("source_revision", toJson (field slr "revision_ref")),
        ("source_unit_ref", toJson (field slr "source_unit_ref")),
        ("instances", toJson output), ("predicate_queries", toJson queries)]).pretty ++ "\n")
      IO.println s!"GWB_CANONICAL_LEAN_INSTANCES count={anchors.length}"
      return 0
    else return 1
  | _, _ => return 1

end Wikidata.Slr.GwbCanonicalSource
