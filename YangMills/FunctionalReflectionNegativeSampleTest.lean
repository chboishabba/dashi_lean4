import Mathlib
import YangMills.FunctionalReflectionNegativeSample

namespace RequestProject.YangMills

example
    {X : Type*} (K : X → X → ℝ)
    (sample : CMP119FunctionalNegativeSample K) :
    ¬ ReflectionPositiveKernel K :=
  sample.not_reflectionPositive

end RequestProject.YangMills
