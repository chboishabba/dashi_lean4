import Mathlib
import YangMills.LiteralSU2FourDimensionalLattice

/-!
# CMP119 regular-component to periodic-polymer dictionary

Block C needs the published regular contribution to be populated component by
component on the same literal finite lattice carrier.  This file records the
exact `c ↦ X_c` seam without choosing a surrogate polymer or evaluator.

A concrete source implementation supplies a finite component family, the
periodic link support of each component, its evaluator on the literal link
field, and additive source semantics.  The support field is data here: proving
that it is the support selected by CMP119 remains a source-identification task.
-/

namespace RequestProject.YangMills

structure CMP119RegularComponentPolymerDictionary
    (L : ℕ) where
  Component : Type
  components : Finset Component
  polymerSupport : Component → Finset (FourDimensionalLinkIndex L)
  evaluate : Component → SU2TorusLinks L → ℝ
  sourceRegular : SU2TorusLinks L → ℝ
  additiveSourceSemantics :
    sourceRegular = fun links =>
      ∑ c in components, evaluate c links

namespace CMP119RegularComponentPolymerDictionary

/-- The source regular term is literally the sum of its selected components. -/
theorem source_regular_eq_component_sum
    {L : ℕ}
    (dict : CMP119RegularComponentPolymerDictionary L)
    (links : SU2TorusLinks L) :
    dict.sourceRegular links =
      ∑ c in dict.components, dict.evaluate c links := by
  exact congrFun dict.additiveSourceSemantics links

/-- Explicit selected periodic support `X_c` for one regular component. -/
def componentPolymer
    {L : ℕ}
    (dict : CMP119RegularComponentPolymerDictionary L)
    (c : dict.Component) : Finset (FourDimensionalLinkIndex L) :=
  dict.polymerSupport c

end CMP119RegularComponentPolymerDictionary

end RequestProject.YangMills
