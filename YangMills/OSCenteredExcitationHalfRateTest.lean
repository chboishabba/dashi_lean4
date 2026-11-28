import Mathlib
import YangMills.OSCenteredExcitationHalfRate

open Filter MeasureTheory

namespace RequestProject.YangMills

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.excitationTransfer
      (weld.centeredExcitationVector left)
      (weld.centeredExcitationVector right) :=
  weld.centered_excitation_pair_half_rate left right

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense
      (Submodule.span ℝ (Set.range weld.centeredExcitationVector) :
        Set (vacuumOrthogonalSubmodule weld.vacuum)) :=
  weld.dense_centered_excitation_span

end RequestProject.YangMills
