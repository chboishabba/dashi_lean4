import Integration.E6Mod3QuadraticBridge

namespace Integration.E6Mod3QuadraticBridgeRegression

open Integration.E6Mod3QuadraticBridge
open Integration.T5QuadraticOrbitAudit

example : Fintype.card E6Root = 72 := e6_root_card
example : Fintype.card QTwoShell = 72 := qtwo_shell_card

example (root : E6Root) : qT5 (rootToT5 root) = 2 := root_to_t5_has_qtwo

example : Function.Injective rootToQTwoShell := root_to_qtwo_injective
example : Function.Surjective rootToQTwoShell := root_to_qtwo_surjective

example : E6Root ≃ QTwoShell := e6RootEquivQTwoShell

example : canonicalBoundary.e6RootCount72Paid = true := rfl
example : canonicalBoundary.mod3RadicalQuotientTyped = true := rfl
example : canonicalBoundary.explicitQuadraticShellBijectionPaid = true := rfl
example : canonicalBoundary.bijectionAloneCreatesE8Recognition = false := rfl
example : canonicalBoundary.bijectionAloneCreatesPhysicalMechanism = false := rfl

end Integration.E6Mod3QuadraticBridgeRegression
