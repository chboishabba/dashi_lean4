import Mathlib
import YangMills.SequentialProjectiveConditionalKernel

open Set MeasureTheory Preorder ProbabilityTheory

namespace RequestProject.YangMills

example
    (sequence : RealSequentialProjectiveFamily) :
    RealSequentialKernelExtensionProducer :=
  sequence.toConditionalKernelExtensionProducer

example
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) :
    sequence.conditionalGlobalMeasure.map (frestrictLe n) =
      (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) :=
  sequence.conditionalGlobalMeasure_prefix n

end RequestProject.YangMills
