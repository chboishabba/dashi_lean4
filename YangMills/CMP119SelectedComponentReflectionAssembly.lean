import Mathlib
import YangMills.CMP119SelectedSourceInstantiation
import YangMills.CMP119FunctionalResidualReflectionCut

/-!
# Componentwise selected CMP119 functional reflection assembly

The source-side max-cut already decomposes E/R/B into selected localized
components with literal periodic supports.  Reflection positivity should be
proved or falsified at that granularity rather than hidden behind an opaque
whole-sector certificate.

This file is pure compiler machinery: if each actual selected source component
has a functional reflection certificate on the SAME boundary carrier, their
finite product is functionally RP.  The three assembled sectors plus the
constant vacuum then compile to the full residual cut.
-/

namespace RequestProject.YangMills

/-- Functional reflection certificates for every selected component of one source sector. -/
structure CMP119SelectedSectorFunctionalCertificates
    {n : ℕ} [NeZero n]
    (sector : CMP119SelectedSectorComponents n)
    (X : Type*) where
  certificate :
    sector.Component → CMP119FunctionalSectorReflectionCertificate X

/-- Product kernel of all selected components in one E/R/B source sector. -/
def selectedSectorAssembledKernel
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (certs : CMP119SelectedSectorFunctionalCertificates sector X) :
    X → X → ℝ :=
  fun x y =>
    ∏ c in sector.components, (certs.certificate c).kernel x y

/-- The assembled selected-sector kernel is symmetric. -/
theorem selected_sector_assembled_kernel_symmetric
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (certs : CMP119SelectedSectorFunctionalCertificates sector X) :
    SymmetricKernel (selectedSectorAssembledKernel certs) := by
  intro x y
  unfold selectedSectorAssembledKernel
  apply Finset.prod_congr rfl
  intro c hc
  exact (certs.certificate c).symmetric x y

/-- The assembled selected-sector kernel is functionally reflection positive. -/
theorem selected_sector_assembled_kernel_rp
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (certs : CMP119SelectedSectorFunctionalCertificates sector X) :
    ReflectionPositiveKernel (selectedSectorAssembledKernel certs) := by
  unfold selectedSectorAssembledKernel
  exact reflectionPositiveKernel_finset_product
    sector.components
    (fun c => (certs.certificate c).kernel)
    (by
      intro c hc
      exact (certs.certificate c).symmetric)
    (by
      intro c hc
      exact (certs.certificate c).reflectionPositive)

/-- Package the finite component product as one source-sector cross kernel. -/
def selectedSectorAssembledCertificate
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (certs : CMP119SelectedSectorFunctionalCertificates sector X) :
    CMP119FunctionalSectorReflectionCertificate X :=
  .crossKernel
    (selectedSectorAssembledKernel certs)
    (selected_sector_assembled_kernel_symmetric certs)
    (selected_sector_assembled_kernel_rp certs)

/--
Sharp BC source package: literal selected E/R/B provenance is already fixed by
`CMP119SelectedSourceInstantiation`; only functional certificates for those
actual selected components and the same-object residual-kernel equation remain.
-/
structure CMP119SelectedSourceFunctionalReflectionCut
    (n : ℕ) [NeZero n] (X : Type*) where
  selectedSource : CMP119SelectedSourceInstantiation n
  regularCertificates :
    CMP119SelectedSectorFunctionalCertificates selectedSource.regularE X
  rOperationCertificates :
    CMP119SelectedSectorFunctionalCertificates selectedSource.rOperation X
  boundaryCertificates :
    CMP119SelectedSectorFunctionalCertificates selectedSource.boundaryB X
  vacuumEnergy : ℝ
  sourceKernel : X → X → ℝ
  sourceKernelEquation :
    sourceKernel = fun x y =>
      (selectedSectorAssembledKernel regularCertificates x y) *
      (selectedSectorAssembledKernel rOperationCertificates x y) *
      (selectedSectorAssembledKernel boundaryCertificates x y) *
      (cmp119FunctionalConstantVacuumCertificate
        (X := X) vacuumEnergy).kernel x y

namespace CMP119SelectedSourceFunctionalReflectionCut

/-- Convert the componentwise selected-source package into the generic functional residual cut. -/
def toFunctionalResidualReflectionCut
    {n : ℕ} [NeZero n] {X : Type*}
    (source : CMP119SelectedSourceFunctionalReflectionCut n X) :
    CMP119FunctionalResidualReflectionCut X where
  certificate
    | .regularE => selectedSectorAssembledCertificate source.regularCertificates
    | .rOperation => selectedSectorAssembledCertificate source.rOperationCertificates
    | .boundaryB => selectedSectorAssembledCertificate source.boundaryCertificates
    | .vacuumV => cmp119FunctionalConstantVacuumCertificate source.vacuumEnergy
  sourceKernel := source.sourceKernel
  sourceKernelEquation := by
    rw [source.sourceKernelEquation]
    funext x y
    simp [selectedSectorAssembledCertificate]
    ring

/-- The actual selected-source residual kernel is functionally RP once all component receipts exist. -/
theorem source_kernel_rp
    {n : ℕ} [NeZero n] {X : Type*}
    (source : CMP119SelectedSourceFunctionalReflectionCut n X) :
    ReflectionPositiveKernel source.sourceKernel :=
  cmp119_functional_complete_residual_kernel_rp
    source.toFunctionalResidualReflectionCut

end CMP119SelectedSourceFunctionalReflectionCut

/-- Convenient top-level theorem name used by the frontier board. -/
theorem cmp119_selected_source_functional_kernel_rp
    {n : ℕ} [NeZero n] {X : Type*}
    (source : CMP119SelectedSourceFunctionalReflectionCut n X) :
    ReflectionPositiveKernel source.sourceKernel :=
  source.source_kernel_rp

end RequestProject.YangMills
