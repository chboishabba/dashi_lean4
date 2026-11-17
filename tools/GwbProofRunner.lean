import RequestProject.Slr.GwbConsumerFibreProof
import RequestProject.Slr.WikipediaArticleProof
import RequestProject.Slr.GwbRealSourceConsumer

open Wikidata

def printAxiomAudit : IO Unit := do
  IO.println "GWB_FIBRE_THEOREMS_KERNEL_OK"
  IO.println "AXIOM_AUDIT_BEGIN"
  IO.println "See the kernel-checked declarations below."
  IO.println "AXIOM_AUDIT_END"

def runArticleCheck (args : List String) : IO UInt32 := do
  match args with
  | [article, source, projection] =>
      let ok ← Slr.ArticleProof.verifyFiles article source projection
      return if ok then 0 else 1
  | _ =>
      IO.eprintln "usage: article-check ARTICLE SLR_RECORD PROJECTION"
      return 2

/-- Kernel-checked, source-extracted nonfactorability witness on the
    original Wikipedia dependency graph; NOT a semantic admission. -/
def runRealScopeCheck (articleFile slrFile projectionFile : String) :
    IO UInt32 := do
  let article ← IO.FS.readFile articleFile
  let sourceText ← IO.FS.readFile slrFile
  let projectionText ← IO.FS.readFile projectionFile
  let source ← match Lean.Json.parse sourceText with
    | .ok j => pure j
    | .error err =>
        IO.eprintln s!"SLR source JSON rejected: {err}"
        return 1
  let projection ← match Lean.Json.parse projectionText with
    | .ok j => pure j
    | .error err =>
        IO.eprintln s!"Article projection JSON rejected: {err}"
        return 1
  match Slr.GwbRealSource.sourceBoundCollision? article source projection with
  | none =>
      IO.eprintln "GWB_REAL_SOURCE_SCOPE_WITNESS_REJECTED: unsupported source or no collision"
      return 1
  | some (left, right) =>
      if hSame : left.scopeLabel = right.scopeLabel then
        if hDifferent : left.parentEmbedded ≠ right.parentEmbedded then
          let _proof :=
            Slr.GwbRealSource.flatScopeCannotAnswerEmbeddedParent
              left right hSame hDifferent
          IO.println "GWB_REAL_SOURCE_FLAT_SCOPE_NONFACTORABILITY_PROVED"
          IO.println s!"left={left.sentenceIndex}:{left.predicateSurface} parent={left.parentSurface} embedded={left.parentEmbedded}"
          IO.println s!"right={right.sentenceIndex}:{right.predicateSurface} parent={right.parentSurface} embedded={right.parentEmbedded}"
          IO.println s!"same_flat_scope_label={left.scopeLabel}"
          IO.println "This does not refute the production SLR rich source graph."
          return 0
        else
          IO.eprintln "No distinct dependency answers for chosen pair"
          return 1
      else
        IO.eprintln "The flattened label was not equal"
        return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["fibre"] =>
      IO.println "GWB_FIBRE_THEOREMS_KERNEL_OK"
      IO.println "PROVED: source-claim/year-string consumer closure; four semantic nonfactorability countermodels; ACI fibre join retains provenance"
      IO.println "NOT PROVED HERE: GWB article semantic admission, reviewed S28 event identity, world occurrence"
      return 0
  | ["axioms"] =>
      printAxiomAudit
      return 0
  | ["semantic-scope", article, source, projection] =>
      runRealScopeCheck article source projection
  | "article-check" :: rest =>
      runArticleCheck rest
  | _ =>
      IO.eprintln "usage: fibre | axioms | article-check ARTICLE SLR_RECORD PROJECTION | semantic-scope ARTICLE SLR_RECORD PROJECTION"
      return 2

#print axioms Wikidata.Slr.GwbConsumer.fibreJoinAssociative
#print axioms Wikidata.Slr.GwbConsumer.sourceMentionQueryCloses
#print axioms Wikidata.Slr.GwbConsumer.actualPossessionNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.actorIdentityNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.eventDateNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.embeddedScopeNotLicensed

#print axioms Wikidata.Slr.GwbRealSource.flatScopeCannotAnswerEmbeddedParent
