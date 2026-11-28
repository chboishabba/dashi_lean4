import Mathlib
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-!
# Carathéodory construction of a projective continuum measure

Mathlib already supplies the exact additive cylinder content attached to a
projective family and the generic Carathéodory extension theorem.  Therefore
the remaining analytic wall for a probability-valued projective family can be
stated sharply: prove sigma-subadditivity of that cylinder content.

Once this one property is supplied, the global product-space measure is
constructed, it realizes every finite marginal exactly, it is automatically a
probability measure, and projective-limit uniqueness is inherited from
`IsProjectiveLimit.unique`.

This turns the former opaque `RealProjectiveLimitExistenceObligation` into a
specific cylinder-content theorem rather than postulating the continuum law.
-/

open Set MeasureTheory

namespace RequestProject.YangMills

/-- A finite-dimensional probability family on all finite coordinate sets. -/
structure ProbabilityProjectiveFamily
    {ι : Type*} (α : ι → Type*)
    [(i : ι) → MeasurableSpace (α i)] where
  marginal : (I : Finset ι) → ProbabilityMeasure (∀ i : I, α i)
  projective :
    IsProjectiveMeasureFamily
      (fun I => ((marginal I : ProbabilityMeasure (∀ i : I, α i)) :
        Measure (∀ i : I, α i)))

namespace ProbabilityProjectiveFamily

/-- The underlying measure family consumed by mathlib's projective machinery. -/
def measureFamily
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (family : ProbabilityProjectiveFamily α) :
    (I : Finset ι) → Measure (∀ i : I, α i) :=
  fun I => family.marginal I

/-- Every finite member is a probability measure by construction. -/
instance marginalIsProbabilityMeasure
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (family : ProbabilityProjectiveFamily α)
    (I : Finset ι) :
    IsProbabilityMeasure (family.measureFamily I) :=
  (family.marginal I).prop

end ProbabilityProjectiveFamily

/--
The one analytic producer still needed after finite projective consistency:
sigma-subadditivity of mathlib's canonical cylinder content.
-/
structure ProbabilityProjectiveCylinderExtensionProducer
    {ι : Type*} (α : ι → Type*)
    [(i : ι) → MeasurableSpace (α i)] where
  family : ProbabilityProjectiveFamily α
  sigmaSubadditive :
    (projectiveFamilyContent family.projective).IsSigmaSubadditive

namespace ProbabilityProjectiveCylinderExtensionProducer

/--
Carathéodory extension of the canonical projective cylinder content to the full
product measurable space.
-/
noncomputable def globalMeasure
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (producer : ProbabilityProjectiveCylinderExtensionProducer α) :
    Measure (∀ i, α i) :=
  (projectiveFamilyContent producer.family.projective).measure
    isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    producer.sigmaSubadditive

/-- The constructed measure has exactly the requested finite marginals. -/
theorem isProjectiveLimit_globalMeasure
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (producer : ProbabilityProjectiveCylinderExtensionProducer α) :
    IsProjectiveLimit producer.globalMeasure producer.family.measureFamily := by
  intro I
  ext s hs
  rw [Measure.map_apply (measurable_restrict I) hs,
    globalMeasure, AddContent.measure_eq,
    projectiveFamilyContent_cylinder producer.family.projective hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

/-- The Carathéodory extension is automatically a probability law. -/
instance globalMeasureIsProbability
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (producer : ProbabilityProjectiveCylinderExtensionProducer α) :
    IsProbabilityMeasure producer.globalMeasure :=
  producer.isProjectiveLimit_globalMeasure.isProbabilityMeasure

/-- Package the global measure as an actual probability measure. -/
noncomputable def globalProbabilityMeasure
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (producer : ProbabilityProjectiveCylinderExtensionProducer α) :
    ProbabilityMeasure (∀ i, α i) :=
  ⟨producer.globalMeasure, inferInstance⟩

/--
D3.6 uniqueness: two global measures realizing the same finite probability
family coincide.  No extra determining-class hypothesis is needed beyond the
full cylinder family.
-/
theorem globalMeasure_unique
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (producer : ProbabilityProjectiveCylinderExtensionProducer α)
    (ν : Measure (∀ i, α i))
    (hν : IsProjectiveLimit ν producer.family.measureFamily) :
    ν = producer.globalMeasure := by
  exact hν.unique producer.isProjectiveLimit_globalMeasure

end ProbabilityProjectiveCylinderExtensionProducer

end RequestProject.YangMills
