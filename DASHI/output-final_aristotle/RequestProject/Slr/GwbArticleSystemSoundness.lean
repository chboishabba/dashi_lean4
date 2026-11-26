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

/- The canonical article lead is a bounded controlled-language specimen,
not an unrestricted English-to-Wikidata translator. The exact source
sentence explicitly attributes the office to the named article subject.
The JMD sitelink binds that subject to Q207; independent EntityData must
support P39/Q11696. The article's date and ordinal are NOT mapped to
Wikidata qualifiers by this rule. -/

def officeLead : String :=
  "George Walker Bush (born July 6, 1946) is an American retired politician and businessman who served as the 43rd president of the United States from 2001 to 2009."

def officeClaim (article : String) : Bool :=
  article.startsWith officeLead

private def entityRecord (json : Json) (qid : String) : Json :=
  (((json.getObjVal? "entities").toOption.getD Json.null).getObjVal? qid).toOption.getD Json.null

def entityRevision (json : Json) (qid : String) : Option Nat :=
  ((entityRecord json qid).getObjValAs? Nat "lastrevid").toOption

def officeLabelChecked (office : Json) : Bool :=
  GwbWorldGraph.jsonEntityMatchesQid "Q11696" office &&
  Cli.entityLabelIn (entityRecord office "Q11696") "en" ==
    some "President of the United States"

def officePKB (root office : Json) : PKB :=
  GwbWorldGraph.pkbFromImportedEntities
    (Cli.entitiesOfJson root ++ Cli.entitiesOfJson office)

def officePropertySupported (root office : Json) : Bool :=
  (officePKB root office).supportsB (Pid.wd "P39")
    (Qid.wd "Q207") (Qid.wd "Q11696")

/-- The source rule and independent KB support are retained as distinct
    premises. This is an article-claim/KB agreement under the named bounded
    rule, not general semantic identity, qualifier agreement or world truth. -/
theorem checkedOfficeClaimAndKB
    {article : String} {slr projection root office : Json}
    (source : GwbArticleIdentity.CheckedGwbRootIdentity article slr projection root)
    (claim : officeClaim article = true)
    (label : officeLabelChecked office = true)
    (support : officePropertySupported root office = true) :
    GwbArticleIdentity.checkGwbRootIdentity article slr projection root = true ∧
    officeClaim article = true ∧ officeLabelChecked office = true ∧
    (∃ p, (p, Qid.wd "Q207", Qid.wd "Q11696") ∈ (officePKB root office).stmts ∧
      (officePKB root office).isSubPropertyOf p (Pid.wd "P39") = true) := by
  exact ⟨source.checked, claim, label, PKB.supportsB_iff.mp support⟩

/-- Extend the EXISTING exact bounded lead rule, not a generic parser.
Its selected consumer is the office interval at year granularity. Each
matched native statement carries its complete GUID, rank and qualifiers;
other qualifier semantics remain outside this consumer. -/
theorem checkedOfficeClaimAndQualifiedYears
    {article : String} {slr projection root office statement : Json}
    (source : GwbArticleIdentity.CheckedGwbRootIdentity article slr projection root)
    (claim : officeClaim article = true)
    (label : officeLabelChecked office = true)
    (support : officePropertySupported root office = true)
    (years : statement ∈ GwbWorldGraph.qualifiedYearRows root "Q207" "P39" "Q11696" 2001 2009) :
    officeClaim article = true ∧
    (∃ p, (p, Qid.wd "Q207", Qid.wd "Q11696") ∈ (officePKB root office).stmts ∧
      (officePKB root office).isSubPropertyOf p (Pid.wd "P39") = true) ∧
    statement ∈ GwbWorldGraph.originalPropertyRows root "Q207" "P39" ∧
    GwbWorldGraph.yearIntervalStatementMatches "P39" "Q11696" 2001 2009 statement = true := by
  have base := checkedOfficeClaimAndKB source claim label support
  have native := (GwbWorldGraph.qualifiedYearRowsExact root "Q207" "P39" "Q11696" 2001 2009 statement).mp years
  exact ⟨claim, base.2.2.2, native.1, native.2⟩

end GwbArticleSystem
end Slr
end Wikidata
