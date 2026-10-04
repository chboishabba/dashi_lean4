import Synthesis.MillenniumBSDCMRationalToGeometricKummerExact
import Synthesis.MillenniumBSDActualE2AdditiveEquiv

/-!
# BSD max-cut: make the x-T / geometric E[2] coordinate orientation explicit

The literal geometric E[2] basis used by the continuous-cohomology lane is

  (1,0) ↦ (0,0),    (0,1) ↦ (1,0).

The explicit x-T descent target is conventionally written as the ordered pair

  ([x], [x-1]).

Those are distinct choices of coordinates until one proves which quadratic
root-sign character is detected by each geometric torsion basis vector.  This
owner prevents a silent basis-order assumption: it records the actual basis
labels and packages the unique coordinate swap needed if the half-point sign
calculation returns the opposite order.

No arithmetic comparison theorem is assumed here.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- Coordinate swap on the literal square-class pair. -/
def ratSquareClassPairSwap :
    (RatSquareClass × RatSquareClass) ≃*
      (RatSquareClass × RatSquareClass) where
  toFun c := (c.2, c.1)
  invFun c := (c.2, c.1)
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl
  map_mul' a b := by rfl

@[simp] theorem ratSquareClassPairSwap_apply
    (c : RatSquareClass × RatSquareClass) :
    ratSquareClassPairSwap c = (c.2, c.1) := rfl

@[simp] theorem ratSquareClassPairSwap_involutive
    (c : RatSquareClass × RatSquareClass) :
    ratSquareClassPairSwap (ratSquareClassPairSwap c) = c := by
  cases c
  rfl

/-- The geometric two-torsion basis is literally oriented by the points
`(0,0)` and `(1,0)` in this order. -/
theorem cmGeometricE2_basis_orientation :
    (cmAlgClosureTwoTorsionEquiv (1, 0) = actualZeroTorsionSubgroupPoint) ∧
    (cmAlgClosureTwoTorsionEquiv (0, 1) = actualOneTorsionSubgroupPoint) := by
  constructor <;> simp [cmAlgClosureTwoTorsionEquiv]

/-- An x-T-oriented version of the already-paid geometric H¹/square-class
comparison.  This is not asserted to be the correct arithmetic orientation
until the half-point root-sign theorem below is paid; it is the explicit
candidate obtained by swapping the two existing coordinates. -/
noncomputable def cmGenericKummerE2H1MulEquivXTOrder :
    Multiplicative
      (ContinuousCohomology.continuousCohomology 1 CMGenericKummerE2TopRep) ≃*
      (RatSquareClass × RatSquareClass) :=
  cmGenericKummerE2H1MulEquivRatSquareClasses.trans ratSquareClassPairSwap

/-- Geometric Kummer class on a rational point, displayed in the explicit
x-T candidate order. -/
noncomputable def cmRationalCohomologicalKummerXTSquareClass
    (P : RationalProjectivePoint) : RatSquareClass × RatSquareClass :=
  cmGenericKummerE2H1MulEquivXTOrder
    (Multiplicative.ofAdd (cmRationalGeometricKummerH1 P))

/-- The desired x-T equality is exactly equivalent to saying that the raw
geometric coordinates equal the swap of the explicit pair.  This theorem is
pure orientation bookkeeping and introduces no arithmetic assumption. -/
theorem cmRationalCohomologicalKummerXT_eq_iff_raw_eq_swap
    (P : RationalProjectivePoint) :
    cmRationalCohomologicalKummerXTSquareClass P = totalGlobalKummer P ↔
      cmRationalCohomologicalKummerSquareClass P =
        ratSquareClassPairSwap (totalGlobalKummer P) := by
  change
    ratSquareClassPairSwap (cmRationalCohomologicalKummerSquareClass P) =
        totalGlobalKummer P ↔
      cmRationalCohomologicalKummerSquareClass P =
        ratSquareClassPairSwap (totalGlobalKummer P)
  constructor
  · intro h
    have := congrArg ratSquareClassPairSwap h
    simpa using this
  · intro h
    have := congrArg ratSquareClassPairSwap h
    simpa using this

/-- Named arithmetic target after the orientation audit.  The intended proof
must identify the two geometric cocycle coordinates with the Galois sign
characters of the chosen square roots in the explicit half construction. -/
def CMGeometricXTKummerOrientationTheorem : Prop :=
  ∀ P : RationalProjectivePoint,
    cmRationalCohomologicalKummerSquareClass P =
      ratSquareClassPairSwap (totalGlobalKummer P)

/-- Once the root-sign calculation pays the raw orientation theorem, the
same-object geometric Kummer map agrees literally with explicit x-T descent in
x-T order. -/
theorem cmRationalCohomologicalKummerXT_eq_totalGlobalKummer
    (h : CMGeometricXTKummerOrientationTheorem)
    (P : RationalProjectivePoint) :
    cmRationalCohomologicalKummerXTSquareClass P = totalGlobalKummer P :=
  (cmRationalCohomologicalKummerXT_eq_iff_raw_eq_swap P).2 (h P)

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* the actual geometric E[2] basis orientation is recorded on literal points;
* the x-T coordinate swap is an explicit multiplicative equivalence;
* the desired geometric/explicit equality is reduced without ambiguity to one
  root-sign arithmetic theorem.

DECISIVE REMAINING ARITHMETIC THEOREM:
For the explicit half using a²=x, b²=x-1, c²=x+1, prove on the actual elliptic
group law that the two coordinates of σQ-Q are exactly the quadratic sign
characters corresponding to b and a in the geometric basis above (including
the exceptional torsion points).  That theorem decides the orientation rather
than assuming it.
-/

end

end Synthesis.Millennium.BSD
