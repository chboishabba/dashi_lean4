import Integration.E8ExceptionalLiftCapstone

namespace Integration.E8ExceptionalLiftCapstoneRegression

open Integration.E8ExceptionalLiftCapstone
open Integration.E6F3GeneratedGroupClosure

example : 240 = 72 + 6 + 6 * 27 := by norm_num
example : literalE8OrbitLedger.total = 240 := by rfl
example : literalE8OrbitLedger.e6RootOrbit = 72 := by rfl
example : literalE8OrbitLedger.a2FixedRoots = 6 := by rfl
example : literalE8OrbitLedger.mixedWeightFibres = 6 := by rfl
example : literalE8OrbitLedger.eachMixedFibre = 27 := by rfl
example :
    literalE8OrbitLedger.total =
      literalE8OrbitLedger.e6RootOrbit +
      literalE8OrbitLedger.a2FixedRoots +
      literalE8OrbitLedger.mixedWeightFibres * literalE8OrbitLedger.eachMixedFibre :=
  literal_e8_orbit_ledger_closes
example : generatedMatrixSet.card = 51840 := e6_generated_image_order_paid
example : canonicalBoundary.e6GeneratedImageOrder51840Paid = true := rfl
example : canonicalBoundary.e6SectorLiteralActionPaid = true := rfl
example : canonicalBoundary.sixMixed27FibresTyped = true := rfl
example : canonicalBoundary.sixMixed27FibresTransitivePaid = true := rfl
example : canonicalBoundary.schlafli27RelationPaid = true := rfl
example : canonicalBoundary.minuscule27WeightOrbitRecognitionPaid = true := rfl
example : canonicalBoundary.minuscule27RelationRecognitionPaid = true := rfl
example : canonicalBoundary.bareTernaryTranslationSchlafliBlocked = true := rfl
example : canonicalBoundary.countMatchedTernaryBranchingActionObstructionPaid = true := rfl
example : canonicalBoundary.fullTernary240SameActionRecognitionPaid = false := rfl
example : canonicalBoundary.albert27AlgebraRecognitionPaid = false := rfl
example : canonicalBoundary.cardinalityAloneCreatesExceptionalRecognition = false := rfl

end Integration.E8ExceptionalLiftCapstoneRegression
