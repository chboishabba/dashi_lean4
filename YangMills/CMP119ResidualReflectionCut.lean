import Mathlib
import YangMills.FiniteReflectionSchurProduct
import YangMills.LiteralSU2WilsonReflectionPlane

/-!
# Source-facing CMP119 residual reflection cut

The selected finite effective action carries four non-Wilson sectors:
regular E, R-operation, boundary B, and vacuum V. Reflection positivity
cannot be inferred from their smallness.

For each sector on one finite positive-time boundary family, the source must
provide either a reflected-half factor h(left) h(right), or an independently
symmetric positive-semidefinite cross-plane kernel.

The four sector kernels are multiplied pointwise. The Schur product theorem
then proves reflection positivity of the complete residual kernel. Combining
that kernel with the already-proved Wilson crossing kernel gives finite
complete-action RP on the SAME boundary family.

This does not claim CMP119 actually supplies these certificates. Failure to
construct one for an actual source sector is a concrete obstruction/falsifier.
-/

namespace RequestProject.YangMills

inductive CMP119ResidualSector
  | regularE
  | rOperation
  | boundaryB
  | vacuumV
  deriving DecidableEq, Fintype

inductive CMP119ReflectionPlacement
  | reflectedHalf
  | crossPlane
  deriving DecidableEq

inductive CMP119SectorReflectionCertificate
    (ι : Type*) [Fintype ι] where
  | halfFactor (halfWeight : ι → ℝ)
  | crossKernel
      (kernel : ι → ι → ℝ)
      (symmetric : ∀ i j, kernel i j = kernel j i)
      (rp : ∀ test : ι → ℝ,
        0 ≤ indexedReflectionQuadratic kernel test)

namespace CMP119SectorReflectionCertificate

def placement
    {ι : Type*} [Fintype ι] :
    CMP119SectorReflectionCertificate ι → CMP119ReflectionPlacement
  | .halfFactor _ => .reflectedHalf
  | .crossKernel _ _ _ => .crossPlane

def kernel
    {ι : Type*} [Fintype ι] :
    CMP119SectorReflectionCertificate ι → ι → ι → ℝ
  | .halfFactor h => fun i j => h i * h j
  | .crossKernel K _ _ => K

theorem symmetric
    {ι : Type*} [Fintype ι]
    (cert : CMP119SectorReflectionCertificate ι) :
    ∀ i j, cert.kernel i j = cert.kernel j i := by
  cases cert with
  | halfFactor h =>
      intro i j
      dsimp [kernel]
      ring
  | crossKernel K hSymm hRP =>
      exact hSymm

theorem reflectionPositive
    {ι : Type*} [Fintype ι]
    (cert : CMP119SectorReflectionCertificate ι) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic cert.kernel test := by
  cases cert with
  | halfFactor h =>
      intro test
      unfold indexedReflectionQuadratic kernel
      have hsquare :
          (∑ i, ∑ j, test i * (h i * h j) * test j) =
            (∑ i, test i * h i) ^ 2 := by
        calc
          _ = (∑ i, test i * h i) *
              (∑ j, test j * h j) := by
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
  | crossKernel K hSymm hRP =>
      exact hRP

end CMP119SectorReflectionCertificate

structure CMP119ResidualReflectionCut
    (ι : Type*) [Fintype ι] where
  certificate :
    CMP119ResidualSector → CMP119SectorReflectionCertificate ι
  sourceKernel : ι → ι → ℝ
  sourceKernelEquation :
    sourceKernel =
      fun i j =>
        ∏ sector : CMP119ResidualSector,
          (certificate sector).kernel i j

def CMP119ResidualReflectionCut.sectorPlacement
    {ι : Type*} [Fintype ι]
    (cut : CMP119ResidualReflectionCut ι)
    (sector : CMP119ResidualSector) : CMP119ReflectionPlacement :=
  (cut.certificate sector).placement

theorem cmp119_residual_source_kernel_symmetric
    {ι : Type*} [Fintype ι]
    (cut : CMP119ResidualReflectionCut ι) :
    ∀ i j, cut.sourceKernel i j = cut.sourceKernel j i := by
  intro i j
  rw [cut.sourceKernelEquation]
  apply Finset.prod_congr rfl
  intro sector hsector
  exact (cut.certificate sector).symmetric i j

theorem cmp119_complete_residual_kernel_rp
    {ι : Type*} [Fintype ι]
    (cut : CMP119ResidualReflectionCut ι) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic cut.sourceKernel test := by
  rw [cut.sourceKernelEquation]
  exact indexed_reflection_positive_finset_product
    (Finset.univ : Finset CMP119ResidualSector)
    (fun sector => (cut.certificate sector).kernel)
    (by
      intro sector hsector i j
      exact (cut.certificate sector).symmetric i j)
    (by
      intro sector hsector test
      exact (cut.certificate sector).reflectionPositive test)

theorem cmp119_wilson_mul_complete_residual_rp
    {ι : Type*} [Fintype ι]
    (wilsonKernel : ι → ι → ℝ)
    (hWilsonSymm : ∀ i j, wilsonKernel i j = wilsonKernel j i)
    (hWilsonRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic wilsonKernel test)
    (cut : CMP119ResidualReflectionCut ι) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j => wilsonKernel i j * cut.sourceKernel i j) test := by
  exact indexed_reflection_positive_mul
    wilsonKernel cut.sourceKernel
    hWilsonSymm
    (cmp119_residual_source_kernel_symmetric cut)
    hWilsonRP
    (cmp119_complete_residual_kernel_rp cut)

def CMP119ResidualReflectionCut.crossPlaneSectors
    {ι : Type*} [Fintype ι]
    (cut : CMP119ResidualReflectionCut ι) :
    Finset CMP119ResidualSector :=
  Finset.univ.filter
    (fun sector => cut.sectorPlacement sector = .crossPlane)

theorem cmp119_sector_not_silently_dropped
    {ι : Type*} [Fintype ι]
    (cut : CMP119ResidualReflectionCut ι)
    (sector : CMP119ResidualSector) :
    sector ∈ (Finset.univ : Finset CMP119ResidualSector) := by
  simp

end RequestProject.YangMills
