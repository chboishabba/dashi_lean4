import Integration.E6Mod3WeylAction

namespace Integration.E6Mod3WeylActionRegression

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction

example : ∀ s x, reflectStandard s (reflectStandard s x) = x :=
  simple_reflections_are_involutions

example : ∀ s x,
    standardQuadratic (reflectStandard s x) = standardQuadratic x :=
  simple_reflections_preserve_quadratic

example : ∀ i j,
    coxeterAdjacent i j = true →
    ∀ x, reflectStandard i (reflectStandard j (reflectStandard i x)) =
      reflectStandard j (reflectStandard i (reflectStandard j x)) :=
  adjacent_generators_satisfy_braid

example : ∀ i j,
    i ≠ j → coxeterAdjacent i j = false →
    ∀ x, reflectStandard i (reflectStandard j x) =
      reflectStandard j (reflectStandard i x) :=
  nonadjacent_generators_commute

example : canonicalBoundary.simpleReflectionsPreserveQuadratic = true := rfl
example : canonicalBoundary.e6CoxeterRelationsPaid = true := rfl
example : canonicalBoundary.generatedGroupOrder51840KernelProvedHere = false := rfl

end Integration.E6Mod3WeylActionRegression
