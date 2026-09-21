import Gap
import NavierStokes.ComparatorSolution

/-!
# End-to-end adapter

This file is deliberately separate from the independent Clay specification and
semantic bridge. It is the only audit file that imports the OpenAI proof.
-/

namespace SemanticGapAdapter

theorem openAIComparatorOptionC : SemanticGap.ComparatorOptionC := by
  intro ν hν
  exact NavierStokes.Comparator.navier_stokes_breakdown_R3 ν hν

theorem openAIComparatorOptionD : SemanticGap.ComparatorOptionD := by
  intro ν hν
  exact NavierStokes.Comparator.navier_stokes_breakdown_periodic ν hν

theorem openAI_to_ClayOptionC : ClaySpec.ClayOptionC :=
  SemanticGap.ComparatorOptionC_to_ClayOptionC openAIComparatorOptionC

theorem openAI_to_ClayOptionD : ClaySpec.ClayOptionD :=
  SemanticGap.ComparatorOptionD_to_ClayOptionD openAIComparatorOptionD

#print axioms openAI_to_ClayOptionC
#print axioms openAI_to_ClayOptionD

end SemanticGapAdapter
