import Mathlib
import YangMills.CMP119SelectedExactComponentReflection
import YangMills.LiteralSU2WilsonReflectionPlane

/-!
# Functional complete Wilson × selected CMP119 crossing RP

The literal SU(2) crossing-plane theorem is stated as positivity of every finite
Gram family.  This is exactly the definition of functional reflection
positivity once arbitrary samples are pulled back to their finite image.  The
strict selected E/R/B/V cut already supplies a functional RP residual kernel.
Their Schur product therefore gives the complete selected crossing kernel on one
and the same boundary carrier.
-/

namespace RequestProject.YangMills

/-- The literal complete Wilson crossing kernel is functionally reflection-positive. -/
theorem su2_wilson_crossing_plane_functional_rp
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β) :
    ReflectionPositiveKernel
      (su2WilsonCrossingPlaneKernel crossings β) := by
  intro ι _ sample test
  classical
  let sites : Finset (SU2CrossingBoundary P) :=
    Finset.univ.image sample
  have hBase :
      0 ≤ finiteReflectionGram sites
        (su2WilsonCrossingPlaneKernel crossings β)
        (fun b => ∑ i : ι, if sample i = b then test i else 0) :=
    su2_wilson_crossing_plane_rp
      crossings β hβ sites _
  have hPullback :
      indexedReflectionQuadratic
        (fun i j =>
          su2WilsonCrossingPlaneKernel crossings β
            (sample i) (sample j)) test =
      finiteReflectionGram sites
        (su2WilsonCrossingPlaneKernel crossings β)
        (fun b => ∑ i : ι, if sample i = b then test i else 0) := by
    unfold indexedReflectionQuadratic finiteReflectionGram
    simp [sites]
  rw [hPullback]
  exact hBase

/-- Symmetry of the functional Wilson crossing kernel. -/
theorem su2_wilson_crossing_plane_functional_symmetric
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) (β : ℝ) :
    SymmetricKernel (su2WilsonCrossingPlaneKernel crossings β) := by
  intro left right
  exact su2_wilson_crossing_plane_kernel_symmetric
    crossings β left right

/-- The strict selected E/R/B/V kernel is symmetric as well as RP. -/
theorem CMP119SelectedSourceExactFunctionalReflectionCut.source_kernel_symmetric
    {n : ℕ} [NeZero n] {X : Type*}
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n X) :
    SymmetricKernel cut.sourceKernel := by
  rw [cut.sourceKernelEquation]
  intro x y
  rw [cut.regular.actual_assembled_kernel_symmetric x y,
    cut.rOperation.actual_assembled_kernel_symmetric x y,
    cut.boundary.actual_assembled_kernel_symmetric x y,
    (cmp119FunctionalConstantVacuumCertificate
      (X := X) cut.vacuumEnergy).symmetric x y]

/--
Successful BC source extraction terminates directly at the complete literal
Wilson × selected E/R/B/V crossing kernel on the same boundary carrier.
-/
theorem cmp119_selected_complete_crossing_functional_rp
    {n : ℕ} [NeZero n]
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n
      (SU2CrossingBoundary P)) :
    ReflectionPositiveKernel
      (fun left right =>
        su2WilsonCrossingPlaneKernel crossings β left right *
          cut.sourceKernel left right) :=
  reflectionPositiveKernel_mul
    (su2WilsonCrossingPlaneKernel crossings β)
    cut.sourceKernel
    (su2_wilson_crossing_plane_functional_symmetric crossings β)
    cut.source_kernel_symmetric
    (su2_wilson_crossing_plane_functional_rp crossings β hβ)
    cut.source_kernel_rp

end RequestProject.YangMills
