import Mathlib
import Mathlib.Analysis.Matrix.Order

/-!
# Schur closure for finite real reflection kernels

OS2 is a finite-family positive-semidefinite statement.  If two
independently supplied reflection kernels are PSD on the SAME finite
positive-time family, their pointwise product is PSD by the Schur
product theorem.

This matters physically because the complete finite Yang--Mills
cross-plane factor may be proved positive by an argument different
from the Wilson character/quaternion expansion.  Once both kernels
are identified on the same boundary variables, no common feature
factorization is required.

This file deliberately works with a finite Fintype index, matching
the matrix formulation of OS2.
-/

namespace RequestProject.YangMills

def indexedReflectionQuadratic
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (test : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, test i * K i j * test j

def indexedKernelMatrix
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => K i j

theorem indexed_quadratic_eq_matrix
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (test : ι → ℝ) :
    indexedReflectionQuadratic K test =
      star test ⬝ᵥ
        (indexedKernelMatrix K *ᵥ test) := by
  classical
  simp [indexedReflectionQuadratic, indexedKernelMatrix,
    Matrix.dotProduct, Matrix.mulVec, mul_assoc]

theorem indexed_kernel_posSemidef
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ)
    (hSymm : ∀ i j, K i j = K j i)
    (hRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic K test) :
    (indexedKernelMatrix K).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext i j
    simp [indexedKernelMatrix, hSymm]
  · intro test
    rw [← indexed_quadratic_eq_matrix]
    exact hRP test

/--
Real finite Schur closure:
if K and H are independently reflection-positive on the same family,
then their pointwise product is reflection-positive.
-/
theorem indexed_reflection_positive_mul
    {ι : Type*} [Fintype ι]
    (K H : ι → ι → ℝ)
    (hKSymm : ∀ i j, K i j = K j i)
    (hHSymm : ∀ i j, H i j = H j i)
    (hK : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic K test)
    (hH : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic H test) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j => K i j * H i j) test := by
  classical
  have hKM := indexed_kernel_posSemidef K hKSymm hK
  have hHM := indexed_kernel_posSemidef H hHSymm hH
  have hProd := Matrix.PosSemidef.hadamard hKM hHM
  intro test
  rw [indexed_quadratic_eq_matrix]
  simpa [indexedKernelMatrix, Matrix.hadamard] using
    hProd.dotProduct_mulVec_nonneg test

/--
Any finite product of mutually symmetric reflection-positive kernels
remains reflection-positive.  This allows Wilson, gauge-fixing-neutral
half factors and independently verified cross-plane effective sectors
to be assembled one physical kernel at a time.
-/
theorem indexed_reflection_positive_finset_product
    {ι A : Type*} [Fintype ι]
    (terms : Finset A)
    (K : A → ι → ι → ℝ)
    (hSymm : ∀ a ∈ terms, ∀ i j, K a i j = K a j i)
    (hRP : ∀ a ∈ terms, ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic (K a) test) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j => ∏ a ∈ terms, K a i j) test := by
  classical
  induction terms using Finset.induction_on with
  | empty =>
      intro test
      simp [indexedReflectionQuadratic]
      positivity
  | @insert a terms ha ih =>
      intro test
      have hHeadSymm : ∀ i j, K a i j = K a j i :=
        hSymm a (Finset.mem_insert_self _ _) 
      have hTailSymm :
          ∀ i j,
            (∏ b ∈ terms, K b i j) =
              (∏ b ∈ terms, K b j i) := by
        intro i j
        apply Finset.prod_congr rfl
        intro b hb
        exact hSymm b (Finset.mem_insert_of_mem hb) i j
      have hHead :
          ∀ f : ι → ℝ,
            0 ≤ indexedReflectionQuadratic (K a) f :=
        hRP a (Finset.mem_insert_self _ _)
      have hTail :
          ∀ f : ι → ℝ,
            0 ≤ indexedReflectionQuadratic
              (fun i j => ∏ b ∈ terms, K b i j) f := by
        intro f
        exact ih
          (fun b hb => hSymm b (Finset.mem_insert_of_mem hb))
          (fun b hb => hRP b (Finset.mem_insert_of_mem hb))
          f
      have hMul := indexed_reflection_positive_mul
        (K a)
        (fun i j => ∏ b ∈ terms, K b i j)
        hHeadSymm hTailSymm hHead hTail test
      simpa [Finset.prod_insert ha, mul_assoc] using hMul

end RequestProject.YangMills
