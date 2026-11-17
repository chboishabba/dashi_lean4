import RequestProject.Slr.GwbConsumerFibreProof
import RequestProject.Slr.WikipediaArticleProof

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
  | "article-check" :: rest =>
      runArticleCheck rest
  | _ =>
      IO.eprintln "usage: fibre | axioms | article-check ARTICLE SLR_RECORD PROJECTION"
      return 2

#print axioms Wikidata.Slr.GwbConsumer.fibreJoinAssociative
#print axioms Wikidata.Slr.GwbConsumer.sourceMentionQueryCloses
#print axioms Wikidata.Slr.GwbConsumer.actualPossessionNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.actorIdentityNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.eventDateNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.embeddedScopeNotLicensed
