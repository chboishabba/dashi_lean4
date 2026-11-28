import Mathlib
import YangMills.SequentialProjectiveKernelMeasure

open Set MeasureTheory Preorder ProbabilityTheory

namespace RequestProject.YangMills

example
    (producer : RealSequentialKernelExtensionProducer)
    (n : ℕ) :
    producer.globalMeasure.map (frestrictLe n) =
      (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) :=
  producer.globalMeasure_prefix n

example
    (producer : RealSequentialKernelExtensionProducer) :
    IsProbabilityMeasure producer.globalMeasure := by
  infer_instance

end RequestProject.YangMills
