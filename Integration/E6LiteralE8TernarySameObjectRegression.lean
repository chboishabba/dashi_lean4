import Integration.E6LiteralE8TernarySameObject

namespace Integration.E6LiteralE8TernarySameObjectRegression

open Integration.E6Mod3QuadraticBridge
open Integration.E8LiteralE6A2Branching
open Integration.E6LiteralE8TernarySameObject
open Integration.T5QuadraticOrbitAudit

example : simpleE8GramMatchesE6Cartan := simple_e8_gram_matches_e6

example : ∀ root : E6Root,
    ∃! target : LiteralE6Sector,
      ∀ k, e8Coord target.1 k = embeddedE6Vector root k :=
  embedded_root_vector_matches_unique_literal_e8

example : E6Root ≃ LiteralE6Sector := e6RootEquivLiteralE6Sector

example : LiteralE6Sector ≃ QTwoShell := literalE6SectorEquivQTwoShell

example : canonicalBoundary.explicitE6SimpleSystemInsideE8Paid = true := rfl
example : canonicalBoundary.e6RootToLiteralE8SectorBijectionPaid = true := rfl
example : canonicalBoundary.literalE6ToTernaryQTwoSameObjectPaid = true := rfl
example : canonicalBoundary.e6SectorRecognitionCreatesWholeE8Recognition = false := rfl

end Integration.E6LiteralE8TernarySameObjectRegression
