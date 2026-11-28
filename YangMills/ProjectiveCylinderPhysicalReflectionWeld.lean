import Mathlib
import YangMills.ProjectiveCylinderOSContinuum

open MeasureTheory

/-!
# Physical reflected-product weld for projective cylinder OS positivity

`ProjectiveCylinderOSContinuum` transports any supplied bounded continuous
finite-prefix reflected Gram observable.  This owner keeps the remaining E1
same-object obligation explicit: the physical reflected Wilson product used at
finite cutoff must be literally the same cylinder function transported through
the weak marginal limit.
-/

namespace RequestProject.YangMills

structure PhysicalCylinderReflectionWeld
    (Ω Test : Type*) [MeasurableSpace Ω] where
  source : RealCountableObservableNormMomentSource Ω
  physicalReflectedProduct : ∀ m, Test → Test →
    BoundedContinuousFunction (Fin m → ℝ) ℝ
  cylinderReflectedProduct : ∀ m, Test → Test →
    BoundedContinuousFunction (Fin m → ℝ) ℝ
  sameReflectedProduct :
    cylinderReflectedProduct = physicalReflectedProduct
  cutoffPhysicalOS2 :
    ∀ (m r : ℕ) (tests : Fin r → Test) (coeff : Fin r → ℝ) (k : ℕ),
      0 ≤ ∫ x,
        (∑ i : Fin r, ∑ j : Fin r,
          (coeff i * coeff j) •
            physicalReflectedProduct m (tests i) (tests j)) x
        ∂(((source.family.marginal m (source.diagonal.subsequence k) :
          ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))

/--
Once the physical and cylinder reflected products are the same object, finite
physical OS2 is exactly the hypothesis consumed by the projective continuum
transport theorem.
-/
theorem physical_cylinder_os_positive
    {Ω Test : Type*} [MeasurableSpace Ω]
    (weld : PhysicalCylinderReflectionWeld Ω Test) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      weld.source weld.cylinderReflectedProduct := by
  rw [weld.sameReflectedProduct]
  exact weld.source.projective_cylinder_os_positive_of_cutoff
    weld.physicalReflectedProduct weld.cutoffPhysicalOS2

/-- Exact remaining E1 physical same-object producer. -/
def PhysicalCylinderReflectionWeldExists
    (Ω Test : Type*) [MeasurableSpace Ω] : Prop :=
  Nonempty (PhysicalCylinderReflectionWeld Ω Test)

end RequestProject.YangMills
