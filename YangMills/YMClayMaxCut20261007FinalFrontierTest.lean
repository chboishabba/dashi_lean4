import Mathlib
import YangMills.YMClayMaxCut20261007FinalFrontier

open MeasureTheory

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n] {X : Type*}
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  ym20261007BCExactCompiler cut

example
    {Ω Obs : Type*} [MeasurableSpace Ω]
    (rep : PhysicalCylinderObservableRepresentation Ω Obs) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      rep.source rep.reflectedProduct :=
  ym20261007PhysicalCylinderOSPositiveFromRepresentation rep

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense
      (Submodule.span ℝ
        (Set.range (weld.data.centeredRawVector
          weld.vacuum weld.vacuumNormalized)) :
        Set (vacuumOrthogonalSubmodule weld.vacuum)) :=
  ym20261007PreferredCenteredSameFamilyDenseSector weld

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.transfer
      (weld.centeredVector left) (weld.centeredVector right) :=
  ym20261007PreferredCenteredPairHalfRate weld left right

example (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E :=
  ym20261007HalfRatePhysicalEnergyFloor a E ha hDecay

end RequestProject.YangMills
