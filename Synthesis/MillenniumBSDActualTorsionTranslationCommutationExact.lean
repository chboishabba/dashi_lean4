import Synthesis.MillenniumBSDActualTwoTorsionTranslationInvolutionExact

/-! Actual split elliptic point-group translation relations. Classical
abelian-group identities, no substituted finite Heisenberg carrier. -/
namespace DASHI.BSD.SplitTangent
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]
variable (e0 e1 e2 : F)

/-- Translation by the original root-point torsion commutes with every
point translation, rather than merely with sign coordinates. -/
theorem splitRoot_translation_commutes
    (h : SplitCoefficients W e0 e1 e2)
    (P Q : W.toAffine.Point) :
    (P + splitRootPoint W e0 e1 e2 h) + Q =
      (P + Q) + splitRootPoint W e0 e1 e2 h := by
  abel

/-- Two successive root-point translations are identity on the
original affine point group, not only the nonexceptional open chart. -/
theorem splitRoot_translation_twice
    (h : SplitCoefficients W e0 e1 e2)
    (P : W.toAffine.Point) :
    P + splitRootPoint W e0 e1 e2 h +
        splitRootPoint W e0 e1 e2 h = P :=
  splitRoot_translation_involution W e0 e1 e2 h P

end
end DASHI.BSD.SplitTangent
