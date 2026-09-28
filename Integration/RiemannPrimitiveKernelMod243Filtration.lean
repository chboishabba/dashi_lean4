import Mathlib
import Integration.RiemannPrimitiveKernelUnimodularBasis

/-!
# Basis-invariant replacement for the RH depth-five coordinate pattern

The raw coefficient-depth tuple is not GL₄(ℤ)-invariant.  The intrinsic object
at depth five is instead the kernel of the coefficient covector modulo 3^5.

Original basis:
  r = (80,243,1215,972)
so modulo 243:
  r̄(x) = 80*x₀.

After the explicit unimodular change:
  r' = (1,-3,1215,972)
so modulo 243:
  r̄'(y) = y₀ - 3*y₁.

The visible coordinate tail changes, but the two kernels are transported
exactly by the basis equivalence.
-/

namespace Integration.RiemannPrimitiveKernelMod243Filtration

open Integration.RiemannPrimitiveKernelUnimodularBasis

abbrev R243 := ZMod 243

structure Coord4 where
  x0 : R243
  x1 : R243
  x2 : R243
  x3 : R243
  deriving DecidableEq, Repr

def changeToOld : Coord4 → Coord4
  | ⟨y0,y1,y2,y3⟩ =>
      ⟨-82*y0 + 3*y1, 27*y0 - y1, y2, y3⟩

def changeToNew : Coord4 → Coord4
  | ⟨x0,x1,x2,x3⟩ =>
      ⟨-x0 - 27*x1, -3*x0 - 82*x1, x2, x3⟩

theorem change_to_old_after_new (x : Coord4) :
    changeToOld (changeToNew x) = x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  ext <;> simp [changeToOld, changeToNew] <;> ring

theorem change_to_new_after_old (y : Coord4) :
    changeToNew (changeToOld y) = y := by
  rcases y with ⟨y0,y1,y2,y3⟩
  ext <;> simp [changeToOld, changeToNew] <;> ring

def coordinateEquiv : Coord4 ≃ Coord4 where
  toFun := changeToOld
  invFun := changeToNew
  left_inv := change_to_new_after_old
  right_inv := change_to_old_after_new

def originalFunctional (x : Coord4) : R243 :=
  80*x.x0 + 243*x.x1 + 1215*x.x2 + 972*x.x3

def transformedFunctional (y : Coord4) : R243 :=
  y.x0 - 3*y.x1 + 1215*y.x2 + 972*y.x3

theorem original_mod243_depends_only_on_first (x : Coord4) :
    originalFunctional x = 80*x.x0 := by
  simp [originalFunctional]
  ring

theorem transformed_mod243_depends_on_first_two (y : Coord4) :
    transformedFunctional y = y.x0 - 3*y.x1 := by
  simp [transformedFunctional]

theorem functional_transport (y : Coord4) :
    originalFunctional (changeToOld y) = transformedFunctional y := by
  rcases y with ⟨y0,y1,y2,y3⟩
  simp [originalFunctional, transformedFunctional, changeToOld]
  ring

def originalKernel (x : Coord4) : Prop :=
  originalFunctional x = 0

def transformedKernel (y : Coord4) : Prop :=
  transformedFunctional y = 0

theorem kernel_transport (y : Coord4) :
    originalKernel (changeToOld y) ↔ transformedKernel y := by
  simp [originalKernel, transformedKernel, functional_transport]

def secondBasis : Coord4 := ⟨0,1,0,0⟩

theorem second_basis_is_originally_annihilated :
    originalKernel secondBasis := by
  native_decide

theorem second_basis_is_not_transformed_annihilated :
    ¬ transformedKernel secondBasis := by
  native_decide

def thirdBasis : Coord4 := ⟨0,0,1,0⟩
def fourthBasis : Coord4 := ⟨0,0,0,1⟩

theorem third_basis_in_both_kernels :
    originalKernel thirdBasis ∧ transformedKernel thirdBasis := by
  native_decide

theorem fourth_basis_in_both_kernels :
    originalKernel fourthBasis ∧ transformedKernel fourthBasis := by
  native_decide

/-- The original coordinate statement "the last three basis vectors lie in the
depth-five kernel" is presentation-dependent. -/
theorem coordinate_tail_flag_changes :
    originalKernel secondBasis ∧ ¬ transformedKernel secondBasis :=
  ⟨second_basis_is_originally_annihilated,
   second_basis_is_not_transformed_annihilated⟩

/-- What survives is the kernel itself transported through the coordinate
equivalence, not the list of coordinate axes used to display it. -/
theorem intrinsic_kernel_is_transport_invariant (y : Coord4) :
    originalKernel (coordinateEquiv y) ↔ transformedKernel y :=
  kernel_transport y

inductive FiltrationStatus
  | coordinatePresentation
  | transportedKernelInvariant
  deriving DecidableEq, Repr

def rawDepthTupleStatus : FiltrationStatus := .coordinatePresentation
def mod243KernelStatus : FiltrationStatus := .transportedKernelInvariant

structure Boundary where
  reductionModuloThreePowerFiveOwned : Bool
  originalFunctionalOnlyFirstCoordinateVisible : Bool
  transformedFunctionalFirstTwoCoordinatesVisible : Bool
  coordinateTailFlagBasisInvariant : Bool
  kernelTransportExact : Bool
  intrinsicFilteredObjectIdentifiedAsKernel : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  reductionModuloThreePowerFiveOwned := true
  originalFunctionalOnlyFirstCoordinateVisible := true
  transformedFunctionalFirstTwoCoordinatesVisible := true
  coordinateTailFlagBasisInvariant := false
  kernelTransportExact := true
  intrinsicFilteredObjectIdentifiedAsKernel := true

end Integration.RiemannPrimitiveKernelMod243Filtration
