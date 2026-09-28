import Mathlib
import Integration.TriadicPAdicKernel
import Integration.OggSSPP2BalancedTernaryPuncturedPlane

/-!
# p=2 conjugate fibre <-> punctured canonical Kernel 2

The paid eight-state p=2 conjugate fibre is exactly the nonzero subtype of the
canonical two-trit kernel.

No arithmetic CM meaning follows from this finite carrier equivalence.
-/

namespace Integration.OggSSPP2PuncturedKernel2Bidi

open Integration.BalancedTernaryAntipodal369OrbitHierarchy
open Integration.TriadicPAdicKernel
open Integration.OggSSPP2BalancedTernaryPuncturedPlane

def pairKernel (a b : Trit) : Kernel2 :=
  ![a,b]

def planeToPuncturedKernel2 : PuncturedNineSheet → PuncturedKernel2
  | .negativeFirstAxis =>
      ⟨pairKernel .neg .zero, by native_decide⟩
  | .positiveFirstAxis =>
      ⟨pairKernel .pos .zero, by native_decide⟩
  | .negativeSecondAxis =>
      ⟨pairKernel .zero .neg, by native_decide⟩
  | .positiveSecondAxis =>
      ⟨pairKernel .zero .pos, by native_decide⟩
  | .negativeEqualDiagonal =>
      ⟨pairKernel .neg .neg, by native_decide⟩
  | .positiveEqualDiagonal =>
      ⟨pairKernel .pos .pos, by native_decide⟩
  | .negativeOppositeDiagonal =>
      ⟨pairKernel .neg .pos, by native_decide⟩
  | .positiveOppositeDiagonal =>
      ⟨pairKernel .pos .neg, by native_decide⟩

def puncturedKernel2ToPlane (x : PuncturedKernel2) : PuncturedNineSheet := by
  let a := x.1 0
  let b := x.1 1
  cases ha : a <;> cases hb : b
  · exact .negativeEqualDiagonal
  · exact .negativeFirstAxis
  · exact .negativeOppositeDiagonal
  · exact .negativeSecondAxis
  · exfalso
    apply x.2
    funext i
    fin_cases i <;> simp [origin, a, b, ha, hb]
  · exact .positiveSecondAxis
  · exact .positiveOppositeDiagonal
  · exact .positiveFirstAxis
  · exact .positiveEqualDiagonal

theorem plane_kernel2_roundtrip (p : PuncturedNineSheet) :
    puncturedKernel2ToPlane (planeToPuncturedKernel2 p) = p := by
  cases p <;> rfl

theorem kernel2_plane_roundtrip (x : PuncturedKernel2) :
    planeToPuncturedKernel2 (puncturedKernel2ToPlane x) = x := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    rcases x with ⟨x,hx⟩ <;>
    simp only [puncturedKernel2ToPlane] at * <;>
    native_decide

noncomputable def puncturedPlaneEquivKernel2 :
    PuncturedNineSheet ≃ PuncturedKernel2 where
  toFun := planeToPuncturedKernel2
  invFun := puncturedKernel2ToPlane
  left_inv := plane_kernel2_roundtrip
  right_inv := kernel2_plane_roundtrip

structure Boundary where
  canonicalKernel2Reused : Bool
  literalNonzeroSubtypeUsed : Bool
  twoSidedRoundTripsProved : Bool
  arithmeticCMMeaningClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  canonicalKernel2Reused := true
  literalNonzeroSubtypeUsed := true
  twoSidedRoundTripsProved := true
  arithmeticCMMeaningClaimed := false

end Integration.OggSSPP2PuncturedKernel2Bidi
