import Mathlib
import YangMills.CMP119ResidualReflectionCut
import YangMills.FunctionalReflectionPositiveKernel

/-!
# Functional CMP119 residual reflection cut

This is the physically correct Block-B interface on an arbitrary boundary
configuration carrier.  Each sector certificate is a genuine function kernel
whose every finite sampled Gram matrix is PSD.  The previous fixed-`Fintype`
cut remains useful for diagnostics and explicit negative witnesses, but it is
not by itself the full OS theorem on a continuous SU(2) boundary space.
-/

namespace RequestProject.YangMills

inductive CMP119FunctionalSectorReflectionCertificate (X : Type*) where
  | halfFactor (halfWeight : X → ℝ)
  | crossKernel
      (kernel : X → X → ℝ)
      (symmetric : SymmetricKernel kernel)
      (rp : ReflectionPositiveKernel kernel)

namespace CMP119FunctionalSectorReflectionCertificate

/-- Kernel represented by a functional sector certificate. -/
def kernel {X : Type*} :
    CMP119FunctionalSectorReflectionCertificate X → X → X → ℝ
  | .halfFactor h => fun x y => h x * h y
  | .crossKernel K _ _ => K

/-- Every functional sector certificate is symmetric. -/
theorem symmetric
    {X : Type*}
    (cert : CMP119FunctionalSectorReflectionCertificate X) :
    SymmetricKernel cert.kernel := by
  cases cert with
  | halfFactor h =>
      intro x y
      dsimp [kernel]
      ring
  | crossKernel K hSymm hRP =>
      exact hSymm

/-- Every functional sector certificate is reflection positive. -/
theorem reflectionPositive
    {X : Type*}
    (cert : CMP119FunctionalSectorReflectionCertificate X) :
    ReflectionPositiveKernel cert.kernel := by
  cases cert with
  | halfFactor h =>
      exact reflectionPositiveKernel_halfFactor h
  | crossKernel K hSymm hRP =>
      exact hRP

end CMP119FunctionalSectorReflectionCertificate

/--
Complete source-facing residual cut on the actual boundary carrier.  The source
kernel is exactly the pointwise product of E/R/B/V sector kernels.
-/
structure CMP119FunctionalResidualReflectionCut (X : Type*) where
  certificate :
    CMP119ResidualSector → CMP119FunctionalSectorReflectionCertificate X
  sourceKernel : X → X → ℝ
  sourceKernelEquation :
    sourceKernel = fun x y =>
      ∏ sector : CMP119ResidualSector,
        (certificate sector).kernel x y

/-- The full functional residual kernel is symmetric. -/
theorem cmp119_functional_residual_source_kernel_symmetric
    {X : Type*}
    (cut : CMP119FunctionalResidualReflectionCut X) :
    SymmetricKernel cut.sourceKernel := by
  intro x y
  rw [cut.sourceKernelEquation]
  apply Finset.prod_congr rfl
  intro sector hsector
  exact (cut.certificate sector).symmetric x y

/-- The full functional residual kernel is reflection positive. -/
theorem cmp119_functional_complete_residual_kernel_rp
    {X : Type*}
    (cut : CMP119FunctionalResidualReflectionCut X) :
    ReflectionPositiveKernel cut.sourceKernel := by
  rw [cut.sourceKernelEquation]
  exact reflectionPositiveKernel_finset_product
    (Finset.univ : Finset CMP119ResidualSector)
    (fun sector => (cut.certificate sector).kernel)
    (by
      intro sector hsector
      exact (cut.certificate sector).symmetric)
    (by
      intro sector hsector
      exact (cut.certificate sector).reflectionPositive)

/--
The source-native constant vacuum term is a functional rank-one half factor.
-/
def cmp119FunctionalConstantVacuumCertificate
    {X : Type*}
    (vacuumEnergy : ℝ) :
    CMP119FunctionalSectorReflectionCertificate X :=
  .halfFactor (fun _ => Real.exp (-(vacuumEnergy / 2)))

/-- Its kernel is exactly the constant Gibbs factor `exp (-V)`. -/
theorem cmp119_functional_constant_vacuum_kernel_eq
    {X : Type*}
    (vacuumEnergy : ℝ) :
    (cmp119FunctionalConstantVacuumCertificate
      (X := X) vacuumEnergy).kernel =
      fun _ _ => Real.exp (-vacuumEnergy) := by
  funext x y
  dsimp [cmp119FunctionalConstantVacuumCertificate,
    CMP119FunctionalSectorReflectionCertificate.kernel]
  rw [← Real.exp_add]
  congr 1
  ring

/--
Once the selected Wilson kernel and the actual CMP119 residual cut are both
functional RP kernels on the same carrier, the complete finite action is RP.
-/
theorem cmp119_wilson_mul_functional_complete_residual_rp
    {X : Type*}
    (wilsonKernel : X → X → ℝ)
    (hWilsonSymm : SymmetricKernel wilsonKernel)
    (hWilsonRP : ReflectionPositiveKernel wilsonKernel)
    (cut : CMP119FunctionalResidualReflectionCut X) :
    ReflectionPositiveKernel
      (fun x y => wilsonKernel x y * cut.sourceKernel x y) :=
  reflectionPositiveKernel_mul
    wilsonKernel cut.sourceKernel
    hWilsonSymm
    (cmp119_functional_residual_source_kernel_symmetric cut)
    hWilsonRP
    (cmp119_functional_complete_residual_kernel_rp cut)

/-- Exact corrected Block-B source producer. -/
def FunctionalProducerExists (X : Type*) : Prop :=
  Nonempty (CMP119FunctionalResidualReflectionCut X)

end RequestProject.YangMills
