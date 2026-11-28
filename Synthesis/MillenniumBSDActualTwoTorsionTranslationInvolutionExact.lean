import Synthesis.MillenniumBSDSplitActualPointTorsionActionExact

/-! Section 21f. The existing split-root two-torsion action really
is an involution of the ORIGINAL Mathlib elliptic point group.
This does not identify an intrinsic divisor-defined Weil pairing. -/
namespace DASHI.BSD.SplitTangent
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]
variable (e0 e1 e2 : F)

/-- Root-point translation twice is the identity on actual points,
including the identity and exceptional charts. -/
theorem splitRoot_translation_involution
    (h : SplitCoefficients W e0 e1 e2)
    (P : W.toAffine.Point) :
    (P + splitRootPoint W e0 e1 e2 h) +
      splitRootPoint W e0 e1 e2 h = P := by
  rw [← add_assoc]
  have ht := splitRootPoint_two W e0 e1 e2 h
  rw [two_nsmul] at ht
  rw [ht, add_zero]

end
end DASHI.BSD.SplitTangent
