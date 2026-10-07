import Mathlib
import YangMills.FunctionalReflectionPositiveKernel

/-!
# Finite negative witnesses falsify functional reflection positivity

A functional RP kernel must be PSD on every finite sample.  Therefore one
explicit sampled negative quadratic form is a mathematically complete
counterexample.  Conversely, a positive result on one sample is not promoted to
functional RP.
-/

namespace RequestProject.YangMills

/-- One negative finite sampled Gram form rules out functional RP. -/
theorem negative_sample_rules_out_reflectionPositiveKernel
    {X ι : Type*} [Fintype ι]
    (K : X → X → ℝ)
    (sample : ι → X)
    (test : ι → ℝ)
    (hneg : indexedReflectionQuadratic
      (fun i j => K (sample i) (sample j)) test < 0) :
    ¬ ReflectionPositiveKernel K := by
  intro hRP
  have hnonneg := hRP sample test
  linarith

end RequestProject.YangMills
