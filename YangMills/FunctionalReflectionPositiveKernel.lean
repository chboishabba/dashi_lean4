import Mathlib
import YangMills.FiniteReflectionSchurProduct

/-!
# Functional reflection-positive kernels

OS positivity of a kernel on a continuous boundary carrier means positivity on
every finite sampled family of boundary configurations.  A certificate for one
fixed finite matrix is only a diagnostic slice.  This file lifts the existing
finite Schur-product machinery to the correct function-kernel statement.
-/

namespace RequestProject.YangMills

/-- Symmetry of a real kernel on an arbitrary carrier. -/
def SymmetricKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ x y, K x y = K y x

/--
Reflection positivity of a real kernel: every finite sampled Gram matrix is
positive semidefinite in quadratic-form form.
-/
def ReflectionPositiveKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ {ι : Type*} [Fintype ι] (sample : ι → X) (test : ι → ℝ),
    0 ≤ indexedReflectionQuadratic
      (fun i j => K (sample i) (sample j)) test

/-- Any reflected-half rank-one factor is reflection positive on every sample. -/
theorem reflectionPositiveKernel_halfFactor
    {X : Type*} (h : X → ℝ) :
    ReflectionPositiveKernel (fun x y => h x * h y) := by
  intro ι _ sample test
  classical
  unfold indexedReflectionQuadratic
  have hsquare :
      (∑ i, ∑ j, test i * (h (sample i) * h (sample j)) * test j) =
        (∑ i, test i * h (sample i)) ^ 2 := by
    calc
      _ = (∑ i, test i * h (sample i)) *
          (∑ j, test j * h (sample j)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = _ := by ring
  rw [hsquare]
  exact sq_nonneg _

/-- Pointwise Schur product preserves functional reflection positivity. -/
theorem reflectionPositiveKernel_mul
    {X : Type*}
    (K H : X → X → ℝ)
    (hKSymm : SymmetricKernel K)
    (hHSymm : SymmetricKernel H)
    (hK : ReflectionPositiveKernel K)
    (hH : ReflectionPositiveKernel H) :
    ReflectionPositiveKernel (fun x y => K x y * H x y) := by
  intro ι _ sample test
  exact indexed_reflection_positive_mul
    (fun i j => K (sample i) (sample j))
    (fun i j => H (sample i) (sample j))
    (fun i j => hKSymm (sample i) (sample j))
    (fun i j => hHSymm (sample i) (sample j))
    (fun f => hK sample f)
    (fun f => hH sample f)
    test

/-- Finite products of functional RP kernels remain functional RP. -/
theorem reflectionPositiveKernel_finset_product
    {X A : Type*}
    (terms : Finset A)
    (K : A → X → X → ℝ)
    (hSymm : ∀ a ∈ terms, SymmetricKernel (K a))
    (hRP : ∀ a ∈ terms, ReflectionPositiveKernel (K a)) :
    ReflectionPositiveKernel
      (fun x y => ∏ a ∈ terms, K a x y) := by
  intro ι _ sample test
  classical
  exact indexed_reflection_positive_finset_product
    terms
    (fun a i j => K a (sample i) (sample j))
    (fun a ha i j => hSymm a ha (sample i) (sample j))
    (fun a ha f => hRP a ha sample f)
    test

end RequestProject.YangMills
