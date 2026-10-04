import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import YangMills.ProjectiveCylinderMeasure

/-!
# Sequential projective continuum measure compiler

For a countable real coordinate family, mathlib provides `inducedFamily`: a
consistent sequence of prefix laws on `Iic n` induces a projective family on
all finite subsets of `ℕ`.  Combining that theorem with the cylinder-content
Carathéodory compiler turns D3.5 into one explicit analytic producer:
sigma-subadditivity of the induced projective-family content.

The resulting global probability measure has exactly the selected finite prefix
laws.  This is a genuine continuum measure construction, conditional only on
that one cylinder-content theorem; it does not postulate a projective limit.
-/

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

/-- A consistent sequence of finite-prefix probability laws. -/
structure RealSequentialProjectiveFamily where
  marginal : (n : ℕ) → ProbabilityMeasure ((i : Set.Iic n) → ℝ)
  consistent :
    ∀ (a b : ℕ) (hab : a ≤ b),
      ((marginal b : ProbabilityMeasure ((i : Set.Iic b) → ℝ)) :
        Measure ((i : Set.Iic b) → ℝ)).map (frestrictLe₂ hab) =
      ((marginal a : ProbabilityMeasure ((i : Set.Iic a) → ℝ)) :
        Measure ((i : Set.Iic a) → ℝ))

namespace RealSequentialProjectiveFamily

/-- Underlying prefix measure family in mathlib's native shape. -/
def measureSequence
    (sequence : RealSequentialProjectiveFamily) :
    (n : ℕ) → Measure ((i : Set.Iic n) → ℝ) :=
  fun n => sequence.marginal n

/-- Every prefix member is a probability measure. -/
instance prefixIsProbabilityMeasure
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) : IsProbabilityMeasure (sequence.measureSequence n) :=
  (sequence.marginal n).prop

/-- Mathlib's induced family on arbitrary finite coordinate subsets. -/
noncomputable def inducedMeasureFamily
    (sequence : RealSequentialProjectiveFamily) :
    (I : Finset ℕ) → Measure ((i : I) → ℝ) :=
  inducedFamily sequence.measureSequence

/-- The induced all-finset family is projective by finite-prefix consistency. -/
theorem inducedMeasureFamily_projective
    (sequence : RealSequentialProjectiveFamily) :
    IsProjectiveMeasureFamily sequence.inducedMeasureFamily := by
  exact isProjectiveMeasureFamily_inducedFamily
    sequence.measureSequence sequence.consistent

/-- Every induced finite marginal remains a probability measure. -/
instance inducedIsProbabilityMeasure
    (sequence : RealSequentialProjectiveFamily)
    (I : Finset ℕ) :
    IsProbabilityMeasure (sequence.inducedMeasureFamily I) := by
  unfold inducedMeasureFamily
  infer_instance

/-- Package the induced all-finset family into the generic probability API. -/
noncomputable def toProbabilityProjectiveFamily
    (sequence : RealSequentialProjectiveFamily) :
    ProbabilityProjectiveFamily (fun _ : ℕ => ℝ) where
  marginal := fun I =>
    ⟨sequence.inducedMeasureFamily I, inferInstance⟩
  projective := by
    simpa [ProbabilityProjectiveFamily.measureFamily] using
      sequence.inducedMeasureFamily_projective

end RealSequentialProjectiveFamily

/--
The exact remaining D3.5 analytic producer for a sequential projective family.
-/
structure RealSequentialCylinderExtensionProducer where
  sequence : RealSequentialProjectiveFamily
  sigmaSubadditive :
    (projectiveFamilyContent
      sequence.toProbabilityProjectiveFamily.projective).IsSigmaSubadditive

namespace RealSequentialCylinderExtensionProducer

/-- Reuse the generic Carathéodory cylinder extension. -/
noncomputable def cylinderProducer
    (producer : RealSequentialCylinderExtensionProducer) :
    ProbabilityProjectiveCylinderExtensionProducer (fun _ : ℕ => ℝ) where
  family := producer.sequence.toProbabilityProjectiveFamily
  sigmaSubadditive := producer.sigmaSubadditive

/-- The constructed continuum probability measure on the full real sequence space. -/
noncomputable def globalProbabilityMeasure
    (producer : RealSequentialCylinderExtensionProducer) :
    ProbabilityMeasure (ℕ → ℝ) :=
  producer.cylinderProducer.globalProbabilityMeasure

/-- Underlying continuum measure. -/
noncomputable def globalMeasure
    (producer : RealSequentialCylinderExtensionProducer) :
    Measure (ℕ → ℝ) :=
  producer.globalProbabilityMeasure

instance globalMeasureIsProbability
    (producer : RealSequentialCylinderExtensionProducer) :
    IsProbabilityMeasure producer.globalMeasure :=
  (producer.globalProbabilityMeasure).prop

/-- The global measure is the projective limit of the induced all-finset family. -/
theorem globalMeasure_projective
    (producer : RealSequentialCylinderExtensionProducer) :
    IsProjectiveLimit producer.globalMeasure
      producer.sequence.inducedMeasureFamily := by
  simpa [globalMeasure, globalProbabilityMeasure, cylinderProducer,
    RealSequentialProjectiveFamily.toProbabilityProjectiveFamily,
    ProbabilityProjectiveFamily.measureFamily] using
    producer.cylinderProducer.isProjectiveLimit_globalMeasure

/--
Every original prefix law is recovered exactly from the constructed continuum
measure.  This is the literal D3.5 conclusion for the selected sequence.
-/
theorem globalMeasure_prefix
    (producer : RealSequentialCylinderExtensionProducer)
    (n : ℕ) :
    producer.globalMeasure.map (frestrictLe n) =
      (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) := by
  have hProj := producer.globalMeasure_projective
  have hIic := hProj (Set.Iic n)
  rw [inducedFamily_Iic producer.sequence.measureSequence n] at hIic
  exact hIic

/-- D3.6 uniqueness for the sequential continuum law. -/
theorem globalMeasure_unique
    (producer : RealSequentialCylinderExtensionProducer)
    (ν : Measure (ℕ → ℝ))
    (hν :
      ∀ n : ℕ,
        ν.map (frestrictLe n) =
          (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ))) :
    ν = producer.globalMeasure := by
  apply (producer.globalMeasure_projective.unique ?_).symm
  rw [isProjectiveLimit_nat_iff
    producer.sequence.inducedMeasureFamily_projective]
  intro n
  rw [inducedFamily_Iic producer.sequence.measureSequence n]
  exact hν n

end RealSequentialCylinderExtensionProducer

end RequestProject.YangMills
