import Mathlib
import YangMills.CMP119SelectedComponentReflectionAssembly
import YangMills.FunctionalReflectionNegativeSample

/-!
# Exact selected-component functional reflection weld

The earlier component compiler permitted an arbitrary certificate family whose
product was identified with the source residual kernel.  For source auditing we
need a stricter same-object surface: every E/R/B component has a designated
actual reflection kernel and its certificate must certify exactly that kernel.

This file adds that fail-closed refinement.  It also makes finite negative
samples decisive at component level.
-/

namespace RequestProject.YangMills

structure CMP119SelectedSectorExactFunctionalRealization
    {n : ℕ} [NeZero n]
    (sector : CMP119SelectedSectorComponents n)
    (X : Type*) where
  actualKernel : sector.Component → X → X → ℝ
  certificate :
    sector.Component → CMP119FunctionalSectorReflectionCertificate X
  certificateSameKernel :
    ∀ c, (certificate c).kernel = actualKernel c

namespace CMP119SelectedSectorExactFunctionalRealization

/-- Every literal component kernel in an exact realization is functionally RP. -/
theorem actual_component_rp
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (realization : CMP119SelectedSectorExactFunctionalRealization sector X)
    (c : sector.Component) :
    ReflectionPositiveKernel (realization.actualKernel c) := by
  rw [← realization.certificateSameKernel c]
  exact (realization.certificate c).reflectionPositive

/-- One finite negative sample rules out an exact RP realization of that component kernel. -/
theorem negative_sample_impossible
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (realization : CMP119SelectedSectorExactFunctionalRealization sector X)
    (c : sector.Component)
    (counterexample : CMP119FunctionalNegativeSample (realization.actualKernel c)) : False :=
  counterexample.not_reflectionPositive (realization.actual_component_rp c)

/-- Product of the actual selected component kernels. -/
def actualAssembledKernel
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (realization : CMP119SelectedSectorExactFunctionalRealization sector X) :
    X → X → ℝ :=
  fun x y =>
    ∏ c in sector.components, realization.actualKernel c x y

/-- The actual component product is functionally RP. -/
theorem actual_assembled_kernel_rp
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (realization : CMP119SelectedSectorExactFunctionalRealization sector X) :
    ReflectionPositiveKernel realization.actualAssembledKernel := by
  unfold actualAssembledKernel
  exact reflectionPositiveKernel_finset_product
    sector.components realization.actualKernel
    (by
      intro c hc
      rw [← realization.certificateSameKernel c]
      exact (realization.certificate c).symmetric)
    (by
      intro c hc
      exact realization.actual_component_rp c)

/-- The actual component product is symmetric. -/
theorem actual_assembled_kernel_symmetric
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (realization : CMP119SelectedSectorExactFunctionalRealization sector X) :
    SymmetricKernel realization.actualAssembledKernel := by
  intro x y
  unfold actualAssembledKernel
  apply Finset.prod_congr rfl
  intro c hc
  rw [← realization.certificateSameKernel c]
  exact (realization.certificate c).symmetric x y

end CMP119SelectedSectorExactFunctionalRealization

/--
Strict selected-source BC cut: every actual E/R/B component kernel is fixed
before its certificate is supplied, and the full source kernel is the product
of those actual sector kernels and the source-constant vacuum factor.
-/
structure CMP119SelectedSourceExactFunctionalReflectionCut
    (n : ℕ) [NeZero n] (X : Type*) where
  selectedSource : CMP119SelectedSourceInstantiation n
  regular :
    CMP119SelectedSectorExactFunctionalRealization selectedSource.regularE X
  rOperation :
    CMP119SelectedSectorExactFunctionalRealization selectedSource.rOperation X
  boundary :
    CMP119SelectedSectorExactFunctionalRealization selectedSource.boundaryB X
  vacuumEnergy : ℝ
  sourceKernel : X → X → ℝ
  sourceKernelEquation :
    sourceKernel = fun x y =>
      regular.actualAssembledKernel x y *
      rOperation.actualAssembledKernel x y *
      boundary.actualAssembledKernel x y *
      (cmp119FunctionalConstantVacuumCertificate
        (X := X) vacuumEnergy).kernel x y

namespace CMP119SelectedSourceExactFunctionalReflectionCut

/-- The exact actual E/R/B/vacuum source kernel is functionally RP. -/
theorem source_kernel_rp
    {n : ℕ} [NeZero n] {X : Type*}
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n X) :
    ReflectionPositiveKernel cut.sourceKernel := by
  rw [cut.sourceKernelEquation]
  have hER : ReflectionPositiveKernel
      (fun x y => cut.regular.actualAssembledKernel x y *
        cut.rOperation.actualAssembledKernel x y) :=
    reflectionPositiveKernel_mul
      cut.regular.actualAssembledKernel
      cut.rOperation.actualAssembledKernel
      cut.regular.actual_assembled_kernel_symmetric
      cut.rOperation.actual_assembled_kernel_symmetric
      cut.regular.actual_assembled_kernel_rp
      cut.rOperation.actual_assembled_kernel_rp
  have hERB : ReflectionPositiveKernel
      (fun x y =>
        (cut.regular.actualAssembledKernel x y *
          cut.rOperation.actualAssembledKernel x y) *
        cut.boundary.actualAssembledKernel x y) :=
    reflectionPositiveKernel_mul
      (fun x y => cut.regular.actualAssembledKernel x y *
        cut.rOperation.actualAssembledKernel x y)
      cut.boundary.actualAssembledKernel
      (by
        intro x y
        rw [cut.regular.actual_assembled_kernel_symmetric x y,
          cut.rOperation.actual_assembled_kernel_symmetric x y])
      cut.boundary.actual_assembled_kernel_symmetric
      hER
      cut.boundary.actual_assembled_kernel_rp
  have hVacuum :=
    (cmp119FunctionalConstantVacuumCertificate
      (X := X) cut.vacuumEnergy).reflectionPositive
  exact reflectionPositiveKernel_mul
    (fun x y =>
      (cut.regular.actualAssembledKernel x y *
        cut.rOperation.actualAssembledKernel x y) *
      cut.boundary.actualAssembledKernel x y)
    (cmp119FunctionalConstantVacuumCertificate
      (X := X) cut.vacuumEnergy).kernel
    (by
      intro x y
      rw [cut.regular.actual_assembled_kernel_symmetric x y,
        cut.rOperation.actual_assembled_kernel_symmetric x y,
        cut.boundary.actual_assembled_kernel_symmetric x y])
    (cmp119FunctionalConstantVacuumCertificate
      (X := X) cut.vacuumEnergy).symmetric
    hERB hVacuum

end CMP119SelectedSourceExactFunctionalReflectionCut

/-- Exact BC producer after source extraction; deliberately uninhabited locally. -/
def CMP119SelectedSourceExactFunctionalReflectionCutExists
    (n : ℕ) [NeZero n] (X : Type*) : Prop :=
  Nonempty (CMP119SelectedSourceExactFunctionalReflectionCut n X)

end RequestProject.YangMills
