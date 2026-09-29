import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

/-!
# Discriminant and nonsingularity of Banerjee's F₄ special fibre

This pays the special-fibre Weierstrass nonsingularity theorem directly from
Mathlib's characteristic-two discriminant identity.  This is NOT a proof of
supersingularity or of an elliptic scheme over Spf W(F₄)[[a₁]].
-/

namespace Integration.OggSSPP2BanerjeeSpecialFibreElliptic

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

open WeierstrassCurve

/-- In characteristic two, the discriminant of y² + y = x³ is exactly one. -/
theorem special_fibre_discriminant_is_one :
    B.specialCurve.Δ = 1 := by
  rw [WeierstrassCurve.Δ_of_char_two]
  simp [B.specialCurve, WeierstrassCurve.b₈]

/-- The explicit F₄ special fibre has invertible discriminant. -/
theorem special_fibre_discriminant_is_unit :
    IsUnit B.specialCurve.Δ := by
  rw [special_fibre_discriminant_is_one]
  exact isUnit_one

/-- The source curve satisfies Mathlib's Weierstrass elliptic criterion. -/
noncomputable instance specialFibreIsElliptic :
    B.specialCurve.IsElliptic where
  isUnit := special_fibre_discriminant_is_unit

/-- The characteristic-two c₄ invariant vanishes on the special fibre. -/
theorem special_fibre_c4_is_zero :
    B.specialCurve.c₄ = 0 := by
  rw [WeierstrassCurve.c₄_of_char_two]
  simp [B.specialCurve]

/-- The j-invariant of the special elliptic curve is zero. -/
theorem special_fibre_j_is_zero :
    B.specialCurve.j = 0 := by
  simp [WeierstrassCurve.j, special_fibre_c4_is_zero]

structure Boundary where
  concreteSpecialFibreDiscriminantOne : Bool
  concreteSpecialFibreIsElliptic : Bool
  concreteSpecialFibreC4Zero : Bool
  concreteSpecialFibreJZero : Bool
  geometricSupersingularityProved : Bool
  formalEllipticGroupSchemeConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  concreteSpecialFibreDiscriminantOne := true
  concreteSpecialFibreIsElliptic := true
  concreteSpecialFibreC4Zero := true
  concreteSpecialFibreJZero := true
  geometricSupersingularityProved := false
  formalEllipticGroupSchemeConstructed := false

end Integration.OggSSPP2BanerjeeSpecialFibreElliptic
