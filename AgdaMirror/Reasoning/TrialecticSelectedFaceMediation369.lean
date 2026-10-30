/-!
# Selected finite graph/attached-face mediation (golden Agda downstream)

The golden Agda owner is
`DASHI.Reasoning.TrialecticWeightedGraphFaceMediationSelectedExact`.
The next-depth cell is selected by an explicit synthetic three-case chart,
*not* inferred from the weighted graph nor from experimental evidence.
This mirror proves the selected output fails factorisation through the
matrix projection, in addition to the existing face non-descent result.

No general face-mediation law, Grothendieck higher-stack, smooth pants or
physical/social result is claimed. Kernel verification is still pending.
-/
import Mathlib
import AgdaMirror.Base369
import AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369

namespace AgdaMirror.Reasoning.TrialecticSelectedFaceMediation369

open AgdaMirror.Base369
open AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369

abbrev SelectedCell := TriTruth × TriTruth × TriTruth

def selectedOutput : AttachedFace → SelectedCell
  | .reciprocal => (.high,.high,.high)
  | .coercive => (.low,.low,.low)
  | .underdetermined => (.mid,.mid,.mid)

/-- An explicit output assignment is a chart, not a graph-decoding law. -/
def selectedConsumer (s : GraphWithFace) : SelectedCell :=
  selectedOutput s.face

theorem same_matrix_distinct_selected_output :
    observe leftState = observe rightState ∧
    selectedConsumer leftState ≠ selectedConsumer rightState := by
  constructor
  · rfl
  · decide

theorem selected_output_not_graph_only :
    ¬ FactorsThrough observe selectedConsumer := by
  rintro ⟨decode, hd⟩
  have hl := hd leftState
  have hr := hd rightState
  have impossible : selectedConsumer leftState = selectedConsumer rightState := by
    calc
      selectedConsumer leftState = decode (observe leftState) := hl
      _ = decode (observe rightState) := by
        rw [same_matrix_distinct_selected_output.1]
      _ = selectedConsumer rightState := hr.symm
  exact same_matrix_distinct_selected_output.2 impossible

end AgdaMirror.Reasoning.TrialecticSelectedFaceMediation369
