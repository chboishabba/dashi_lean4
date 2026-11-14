import Mathlib
import YangMills.ProjectiveCylinderPhysicalReflectionRepresentation

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω Obs : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (reflectObservable : Obs → Obs)
    (multiplyObservable : Obs → Obs → Obs)
    (represent : ∀ m, Obs → BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (hcutoff :
      ∀ (m r : ℕ) (tests : Fin r → Obs) (coeff : Fin r → ℝ) (k : ℕ),
        0 ≤ ∫ x,
          (∑ i : Fin r, ∑ j : Fin r,
            (coeff i * coeff j) •
              represent m (multiplyObservable (reflectObservable (tests i)) (tests j))) x
          ∂(((source.family.marginal m (source.diagonal.subsequence k) :
            ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      source
      (physicalCylinderReflectedProduct reflectObservable multiplyObservable represent) :=
  physical_cylinder_os_positive_from_representation
    source reflectObservable multiplyObservable represent hcutoff

end RequestProject.YangMills
