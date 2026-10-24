import Integration.E6Mod3QuadraticBridge

namespace Integration.E6Mod3QuadraticBridgeRegression

open Integration.E6Mod3QuadraticBridge
open Integration.T5QuadraticOrbitAudit

example : Fintype.card E6Root = 72 := e6_root_card
example : Fintype.card QTwoShell = 72 := qtwo_shell_card

example : ∀ x : F3Six, ∀ a : ZMod 3,
    e6Mod3Quadratic (radicalTranslate a x) = e6Mod3Quadratic x :=
  radical_translation_preserves_quadratic

example : ∀ x : F3Six,
    e6Mod3Quadratic x = quotientQuadratic (quotientCoordinates x) :=
  quotient_coordinates_preserve_quadratic

example : ∀ y : F3Five,
    quotientQuadratic y = standardQuadratic (quotientToStandard y) :=
  quotient_to_standard_isometry

example (root : E6Root) : qT5 (rootToT5 root) = 2 := root_to_t5_has_qtwo

example : Function.Injective rootToQTwoShell := root_to_qtwo_injective
example : Function.Surjective rootToQTwoShell := root_to_qtwo_surjective

example : E6Root ≃ QTwoShell := e6RootEquivQTwoShell

example : canonicalBoundary.e6RootCount72Paid = true := rfl
example : canonicalBoundary.mod3RadicalInvariancePaid = true := rfl
example : canonicalBoundary.quotientQuadraticEqualityPaid = true := rfl
example : canonicalBoundary.explicitFiveDimensionalIsometryPaid = true := rfl
example : canonicalBoundary.explicitQuadraticShellBijectionPaid = true := rfl
example : canonicalBoundary.bijectionAloneCreatesE8Recognition = false := rfl
example : canonicalBoundary.bijectionAloneCreatesPhysicalMechanism = false := rfl

end Integration.E6Mod3QuadraticBridgeRegression
