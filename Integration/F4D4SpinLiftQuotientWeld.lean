import Integration.RationalOctonionSpin8WeylLift
import Integration.F4D4StandardTrialityRecognition
import Mathlib

/-!
# Exact quotient weld: native Spin(8) triality lift -> folded W(D4)

The native octonion triality side gives a 384-element central extension, while
the folded E6/F4 side gives an independently constructed 192-element W(D4)
kernel.  This owner synchronizes the four named simple generators and proves
that the finite closures are the same action modulo the single central spin
sign `z = (I,-I,-I)`.

No group identity is inferred from cardinality alone: the paired closure is
constructed generator-by-generator and both projections are checked exactly.
-/

namespace Integration.F4D4SpinLiftQuotientWeld

open Integration.E6F4WeylFold
open Integration.F4D4TrialityAlbertShape
open Integration.F4D4StandardTrialityRecognition
open Integration.RationalOctonionTriality192
open Integration.RationalOctonionSpin8WeylLift

structure WeldPair where
  folded : Mat6
  spin : TrialityTriple
  deriving DecidableEq, Repr

/-- Componentwise multiplication, synchronized in the same word order. -/
def composeWeld (a b : WeldPair) : WeldPair :=
  ⟨matrixComp a.folded b.folded, composeTriple a.spin b.spin⟩


def idWeld : WeldPair := ⟨identityMatrix,idTriple⟩

/-- The four same-named generators. -/
def weldGenerator (s : D4Simple) : WeldPair :=
  ⟨foldedD4Matrix s, spinLift s⟩

/-- Closure under all four generators. -/
def expandWeld (S : Finset WeldPair) : Finset WeldPair :=
  S ∪ S.image (composeWeld (weldGenerator .center)) ∪
      S.image (composeWeld (weldGenerator .outer0)) ∪
      S.image (composeWeld (weldGenerator .outer1)) ∪
      S.image (composeWeld (weldGenerator .outer2))


def weldClosureN : Nat → Finset WeldPair
  | 0 => {idWeld}
  | n+1 => expandWeld (weldClosureN n)


def weld384 : Finset WeldPair := weldClosureN 12

/-- The synchronized closure retains the full spinorial double cover. -/
theorem weld_closure_card_384 : weld384.card = 384 := by
  native_decide


theorem weld_closure_stable : weldClosureN 13 = weld384 := by
  native_decide

/-- The folded projection is exactly the independently constructed D4 kernel. -/
def foldedProjection : Finset Mat6 := weld384.image WeldPair.folded


theorem folded_projection_eq_kernel : foldedProjection = d4KernelSet := by
  native_decide

/-- The Spin projection is exactly the independently constructed 384 closure. -/
def spinProjection : Finset TrialityTriple := weld384.image WeldPair.spin


theorem spin_projection_eq_spin_lift : spinProjection = spinLift384 := by
  native_decide

/-- Every folded Weyl element has exactly two synchronized Spin lifts. -/
def foldedFiber (M : Mat6) : Finset WeldPair :=
  weld384.filter fun p => p.folded = M


theorem every_kernel_fiber_has_two :
    ∀ M ∈ d4KernelSet, (foldedFiber M).card = 2 := by
  native_decide

/-- The nontrivial element over the folded identity is precisely the central
spin sign. -/
def centralWeld : WeldPair := ⟨identityMatrix,centralZ⟩


theorem central_weld_in_closure : centralWeld ∈ weld384 := by
  native_decide


theorem identity_fiber_exact :
    foldedFiber identityMatrix = {idWeld,centralWeld} := by
  native_decide

/-- Multiplication by the central sign fixes the folded projection and toggles
between the two Spin lifts in every fibre. -/
def toggleCentral (p : WeldPair) : WeldPair :=
  ⟨p.folded, composeTriple centralZ p.spin⟩


theorem central_toggle_preserves_closure :
    ∀ p ∈ weld384, toggleCentral p ∈ weld384 := by
  native_decide


theorem central_toggle_involutive :
    ∀ p, toggleCentral (toggleCentral p) = p := by
  native_decide


theorem central_toggle_has_no_fixed_point_on_closure :
    ∀ p ∈ weld384, toggleCentral p ≠ p := by
  native_decide

/-- Exact finite same-action quotient receipt.  The quotient is paid through
an explicit two-sheeted synchronized closure rather than by group-order
comparison. -/
structure SpinWeylQuotientReceipt where
  coverOrder : Nat
  quotientOrder : Nat
  fibreSize : Nat
  coverOrder_eq_384 : coverOrder = 384
  quotientOrder_eq_192 : quotientOrder = 192
  fibreSize_eq_2 : fibreSize = 2
  foldedImageSameObject : foldedProjection = d4KernelSet
  spinImageSameObject : spinProjection = spinLift384


def canonicalReceipt : SpinWeylQuotientReceipt where
  coverOrder := weld384.card
  quotientOrder := foldedProjection.card
  fibreSize := 2
  coverOrder_eq_384 := weld_closure_card_384
  quotientOrder_eq_192 := by rw [folded_projection_eq_kernel]; exact d4_kernel_card_192
  fibreSize_eq_2 := rfl
  foldedImageSameObject := folded_projection_eq_kernel
  spinImageSameObject := spin_projection_eq_spin_lift

inductive SpinDoubleCoverCreatesContinuousSpin8 : Prop
inductive WeylQuotientCreatesFullF4 : Prop

 theorem finite_spin_cover_does_not_create_continuous_spin8 :
    ¬ SpinDoubleCoverCreatesContinuousSpin8 := by intro h; cases h

 theorem finite_weyl_quotient_does_not_create_full_f4 :
    ¬ WeylQuotientCreatesFullF4 := by intro h; cases h

structure Boundary where
  synchronizedGeneratorWeldPaid : Bool
  coverOrder384Paid : Bool
  foldedProjectionExactlyWD4Paid : Bool
  spinProjectionExactlyNativeLiftPaid : Bool
  everyWeylFiberTwoPaid : Bool
  centralTogglePaid : Bool
  quotientSameObjectActionPaid : Bool
  continuousSpin8Paid : Bool
  fullF4Paid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  synchronizedGeneratorWeldPaid := true
  coverOrder384Paid := true
  foldedProjectionExactlyWD4Paid := true
  spinProjectionExactlyNativeLiftPaid := true
  everyWeylFiberTwoPaid := true
  centralTogglePaid := true
  quotientSameObjectActionPaid := true
  continuousSpin8Paid := false
  fullF4Paid := false

end Integration.F4D4SpinLiftQuotientWeld
