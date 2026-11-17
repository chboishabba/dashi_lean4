import RequestProject.Slr.GwbP4SourceLicence
import RequestProject.Slr.GwbArticleSystemSoundness

/-!
P4 end-to-end original-source article-local proof.

Previously GwbArticleSystem.checkedArticleLocalSystemSound demanded an
unconstructed SourceQueryLicence. This module constructs it on the actual
GWB source-checked Rust typed rows for source-observable queries, then
instantiates the existing article system theorem with the original Q207
Wikidata sitelink witness.

Real inputs required by the command:
  article.txt, slr-record.json, article-candidates.json,
  original slr-rust-semantic-expansion.json, original Q207 EntityData.

No one of these external inputs alone asserts actor/event/temporal/world
semantics. The proof is positive *only* for the source-query family.
-/

namespace Wikidata
namespace Slr
namespace GwbP4Article

open Lean
open GwbTypedFibre

/-- No hand-authored factorisation premise: P4 computes the original
    source observation, derives the universal source-only licence and
    applies the existing article-local theorem. -/
theorem originalGwbArticlePositiveSourceQuery
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native)
    (query : GwbP4.SourceQuery) :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    GwbP4.sourceModel.documentAnswer source.rows.toList query =
      GwbP4.sourceAnswer source.rows.toList query := by
  exact GwbArticleSystem.checkedArticleLocalSystemSound
    root source (GwbHyperfabric.whole source)
    GwbP4.sourceModel query
    (GwbP4.checkedSourceLicence source query)
    (GwbP4.sourceAnswer source.rows.toList query) rfl

/-- The same theorem holds for source-syntactic actor-role candidates and
    typed unresolved reference residuals. Neither count is a person-QID
    resolution or a proof of actual historical events. -/
theorem sourceActorCandidatesAndReferenceResiduals
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native) :
    GwbP4.sourceModel.documentAnswer source.rows.toList
      (.candidateKind "Role(Actor)") =
        GwbP4.sourceAnswer source.rows.toList
          (.candidateKind "Role(Actor)") ∧
    GwbP4.sourceModel.documentAnswer source.rows.toList
      (.residualKind "ReferenceAttachmentUnresolved") =
        GwbP4.sourceAnswer source.rows.toList
          (.residualKind "ReferenceAttachmentUnresolved") := by
  exact ⟨(originalGwbArticlePositiveSourceQuery root source
    (.candidateKind "Role(Actor)")).2.2,
    (originalGwbArticlePositiveSourceQuery root source
    (.residualKind "ReferenceAttachmentUnresolved")).2.2⟩

end GwbP4Article
end Slr
end Wikidata
