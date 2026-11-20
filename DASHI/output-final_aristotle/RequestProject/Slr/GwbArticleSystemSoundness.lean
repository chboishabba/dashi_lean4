import RequestProject.Slr.GwbArticleIdentity
import RequestProject.Slr.GwbHyperfabricTransport
import RequestProject.Slr.GwbProofComposition
import RequestProject.Slr.GwbWorldGraphProof

/-!
GWB article-local end-to-end proof-composition theorem.

It depends on:
  * the original exact Q207 article/SLR parser and JMD sitelink checker;
  * the same original source-checked native Rust semantic receipt;
  * a fragment that is provably drawn from that checked source;
  * a query-specific SourceQueryLicence over the ACTUAL typed row list;
  * an independently JMD-checked KB property statement.

A successful theorem proves the stated properties of those checked inputs.
It does NOT manufacture the externally missing semantic coverage,
cross-sentence referent identity, event occurrence or statement-to-prose
alignment. Those are not implicit in the source, graph or checker flags.
-/

namespace Wikidata
namespace Slr
namespace GwbArticleSystem

open Lean
open GwbTypedFibre

/-- This is the exact dependency interface the automatic GWB elaborator
must inhabit. A semantic consumer may use only a source observation
that is explicitly the typed list from the original checked receipt. -/
theorem checkedArticleLocalSystemSound
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native)
    (fragment : GwbHyperfabric.Fragment source)
    {Observation Reading Query Answer : Type}
    (model : DocumentQueryModel
      (List SentenceObservation) Observation Reading Query Answer)
    (query : Query)
    (licence : SourceQueryLicence model source.rows.toList query)
    (answerValue : Answer)
    (evaluation :
      model.readingAnswer licence.chosenReading query = answerValue) :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    model.documentAnswer source.rows.toList query = answerValue := by
  exact ⟨GwbArticleIdentity.checkedGwbRootSourceAndSitelink root,
    GwbHyperfabric.anyFragmentRetainsOriginalReceipt fragment,
    slrJmdDocumentQuerySound licence answerValue evaluation⟩

/-- Explicitly compose the article-relative theorem with ONE separately
reimported JMD property, requiring its QID subject to be the same Q207
root. This does not assert the historical truth of the property or
automatically identify a source sentence with the KB statement. -/
theorem checkedArticleAndRootKBPropertySound
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native)
    (fragment : GwbHyperfabric.Fragment source)
    {Observation Reading Query Answer : Type}
    (model : DocumentQueryModel
      (List SentenceObservation) Observation Reading Query Answer)
    (query : Query)
    (licence : SourceQueryLicence model source.rows.toList query)
    (answerValue : Answer)
    (evaluation :
      model.readingAnswer licence.chosenReading query = answerValue)
    (property : GwbWorldGraph.CheckedWorldProperty)
    (sameQid : property.subject = Qid.wd "Q207") :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    model.documentAnswer source.rows.toList query = answerValue ∧
    (∃ p, (p, Qid.wd "Q207", property.object) ∈
      property.pkb.stmts ∧
      property.pkb.isSubPropertyOf p property.property = true) := by
  have articleProof :=
    checkedArticleLocalSystemSound root source fragment
      model query licence answerValue evaluation
  have kbProof := GwbWorldGraph.checkedWorldPropertySound property
  rcases articleProof with ⟨hIdentity, hSource, hAnswer⟩
  rw [sameQid] at kbProof
  exact ⟨hIdentity, hSource, hAnswer, kbProof⟩

end GwbArticleSystem
end Slr
end Wikidata
