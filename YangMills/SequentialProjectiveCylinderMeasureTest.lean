import Mathlib
import YangMills.SequentialProjectiveCylinderMeasure

open MeasureTheory Preorder

namespace RequestProject.YangMills

example
    (producer : RealSequentialCylinderExtensionProducer) :
    IsProbabilityMeasure producer.globalMeasure := by
  infer_instance

example
    (producer : RealSequentialCylinderExtensionProducer)
    (n : ℕ) :
    producer.globalMeasure.map (frestrictLe n) =
      (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) :=
  producer.globalMeasure_prefix n

end RequestProject.YangMills
