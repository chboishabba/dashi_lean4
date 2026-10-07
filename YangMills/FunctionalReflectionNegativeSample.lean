import Mathlib
import YangMills.FunctionalReflectionPositiveKernel

/-!
# Finite negative samples falsify functional reflection positivity

Functional RP quantifies over every finite sampled boundary family.  Therefore
one explicit finite sample with a negative quadratic form is a complete
counterexample to that functional kernel claim.  This is the fail-closed audit
surface for the selected CMP119 E/R/B component kernels.
-/

namespace RequestProject.YangMills

structure CMP119FunctionalNegativeSample
    {X : Type*} (K : X → X → ℝ) where
  size : ℕ
  sample : Fin size → X
  test : Fin size → ℝ
  negative :
    indexedReflectionQuadratic
      (fun i j => K (sample i) (sample j)) test < 0

namespace CMP119FunctionalNegativeSample

/-- One finite negative Gram sample disproves functional RP. -/
theorem not_reflectionPositive
    {X : Type*} {K : X → X → ℝ}
    (counterexample : CMP119FunctionalNegativeSample K) :
    ¬ ReflectionPositiveKernel K := by
  intro hRP
  have hnonneg := hRP counterexample.sample counterexample.test
  linarith [counterexample.negative]

end CMP119FunctionalNegativeSample

/-- RP or an explicit supplied negative sample cannot both hold. -/
theorem reflectionPositiveKernel_excludes_negative_sample
    {X : Type*} {K : X → X → ℝ}
    (hRP : ReflectionPositiveKernel K)
    (counterexample : CMP119FunctionalNegativeSample K) : False :=
  counterexample.not_reflectionPositive hRP

end RequestProject.YangMills
