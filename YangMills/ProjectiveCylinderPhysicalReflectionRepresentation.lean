import Mathlib
import YangMills.ProjectiveCylinderOSContinuum

open MeasureTheory

/-!
# Representation-first physical cylinder reflection weld

The earlier E1 weld stored two reflected-product functions and an equality
between them.  That equality is an avoidable interface artifact.  The physical
OS algebra already supplies reflection and multiplication on observables; the
continuum cylinder route only needs a bounded continuous realization of each
physical observable on every selected finite coordinate prefix.

This file therefore defines the reflected cylinder product from ONE physical
observable representation.  The genuine remaining same-object input is the
representation itself: callers must show that the selected bounded cylinder
function really represents the intended physical Wilson/cylinder observable.
-/

namespace RequestProject.YangMills

/--
The bounded finite-prefix realization of the physical reflected product is
computed definitionally from physical reflection, multiplication and the ONE
selected physical observable representation.
-/
def physicalCylinderReflectedProduct
    {Obs : Type*}
    (reflectObservable : Obs → Obs)
    (multiplyObservable : Obs → Obs → Obs)
    (represent : ∀ m, Obs → BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    ∀ m, Obs → Obs → BoundedContinuousFunction (Fin m → ℝ) ℝ :=
  fun m left right =>
    represent m (multiplyObservable (reflectObservable left) right)

/--
Representation-first E1 package.  There is no second arbitrary cylinder
product and hence no artificial equality field.  The source obligation is to
supply the intended physical observable representation `represent`.
-/
structure PhysicalCylinderObservableRepresentation
    (Ω Obs : Type*) [MeasurableSpace Ω] where
  source : RealCountableObservableNormMomentSource Ω
  reflectObservable : Obs → Obs
  multiplyObservable : Obs → Obs → Obs
  represent : ∀ m, Obs → BoundedContinuousFunction (Fin m → ℝ) ℝ
  cutoffPhysicalOS2 :
    ∀ (m r : ℕ) (tests : Fin r → Obs) (coeff : Fin r → ℝ) (k : ℕ),
      0 ≤ ∫ x,
        (∑ i : Fin r, ∑ j : Fin r,
          (coeff i * coeff j) •
            represent m
              (multiplyObservable (reflectObservable (tests i)) (tests j))) x
        ∂(((source.family.marginal m (source.diagonal.subsequence k) :
          ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))

namespace PhysicalCylinderObservableRepresentation

/-- The reflected product consumed by the projective continuum theorem. -/
def reflectedProduct
    {Ω Obs : Type*} [MeasurableSpace Ω]
    (rep : PhysicalCylinderObservableRepresentation Ω Obs) :
    ∀ m, Obs → Obs → BoundedContinuousFunction (Fin m → ℝ) ℝ :=
  physicalCylinderReflectedProduct
    rep.reflectObservable rep.multiplyObservable rep.represent

/--
Finite physical OS2 now feeds the continuum theorem definitionally; no
physical-vs-cylinder function equality remains to be proved.
-/
theorem projectiveOSPositive
    {Ω Obs : Type*} [MeasurableSpace Ω]
    (rep : PhysicalCylinderObservableRepresentation Ω Obs) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      rep.source rep.reflectedProduct := by
  exact rep.source.projective_cylinder_os_positive_of_cutoff
    rep.reflectedProduct (by
      intro m r tests coeff k
      simpa [reflectedProduct, physicalCylinderReflectedProduct] using
        rep.cutoffPhysicalOS2 m r tests coeff k)

end PhysicalCylinderObservableRepresentation

/-- Direct constructor theorem used by frontier integrations. -/
theorem physical_cylinder_os_positive_from_representation
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
              represent m
                (multiplyObservable (reflectObservable (tests i)) (tests j))) x
          ∂(((source.family.marginal m (source.diagonal.subsequence k) :
            ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      source
      (physicalCylinderReflectedProduct
        reflectObservable multiplyObservable represent) := by
  let rep : PhysicalCylinderObservableRepresentation Ω Obs :=
    { source := source
      reflectObservable := reflectObservable
      multiplyObservable := multiplyObservable
      represent := represent
      cutoffPhysicalOS2 := hcutoff }
  exact rep.projectiveOSPositive

/-- Exact E1 source producer after removing the duplicate reflected-product field. -/
def PhysicalCylinderObservableRepresentationExists
    (Ω Obs : Type*) [MeasurableSpace Ω] : Prop :=
  Nonempty (PhysicalCylinderObservableRepresentation Ω Obs)

end RequestProject.YangMills
