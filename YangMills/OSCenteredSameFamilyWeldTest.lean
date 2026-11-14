import Mathlib
import YangMills.OSCenteredSameFamilyWeld

open Filter MeasureTheory

namespace RequestProject.YangMills

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.transfer
      (weld.centeredVector left) (weld.centeredVector right) :=
  weld.centered_pair_half_rate left right

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense
      (Submodule.span ℝ
        (Set.range (weld.data.centeredRawVector
          weld.vacuum weld.vacuumNormalized)) :
        Set (vacuumOrthogonalSubmodule weld.vacuum)) :=
  weld.dense_centered_span

end RequestProject.YangMills
