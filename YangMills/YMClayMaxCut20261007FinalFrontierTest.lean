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
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    SameHDenseWilsonMixedHalfRateWeld State V weld.data.Hilbert :=
  ym20261007PreferredSameFamilyDenseWeld weld

example (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E :=
  ym20261007HalfRatePhysicalEnergyFloor a E ha hDecay

end RequestProject.YangMills
