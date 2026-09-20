import Synthesis.MillenniumBSDFrobeniusPointCount
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Tactic

/-!
# Literal mathlib elliptic L-function for E : y² = x³ - x

The previous tranche defined the prime coefficient directly by counting
E(F_p). Mathlib now supplies the global formal L-function machinery for a
literal Weierstrass curve over Q.

This file instantiates that machinery at E : y² = x³ - x and therefore obtains
an actual Weierstrass curve, its elliptic instance, coefficients for every n,
and the associated complex L-series expression.

The remaining same-object theorem is to identify the prime coefficients of
this generic minimal-reduction L-function with the explicit finite-field
point-count coefficient already proved in the previous tranche.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

def cmWeierstrass : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -1, 0⟩

theorem cmWeierstrass_discriminant :
    cmWeierstrass.Δ = 64 := by
  rw [cmWeierstrass, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num1

instance cmWeierstrass_isElliptic :
    cmWeierstrass.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff,
    cmWeierstrass_discriminant]
  norm_num

theorem cmWeierstrass_equation_iff
    (x y : ℚ) :
    cmWeierstrass.toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [cmWeierstrass]
  ring_nf

noncomputable def cmFormalLFunction :
    ArithmeticFunction ℤ :=
  cmWeierstrass.LFunction

noncomputable def cmAllNCoefficient (n : ℕ) : ℤ :=
  cmFormalLFunction n

@[simp] theorem cmAllNCoefficient_zero :
    cmAllNCoefficient 0 = 0 := by
  simp [cmAllNCoefficient, cmFormalLFunction]

noncomputable def cmLSeries (s : ℂ) : ℂ :=
  cmWeierstrass.LSeries s

theorem cmFormalLFunction_is_literal_mathlib_LFunction :
    cmFormalLFunction = cmWeierstrass.LFunction :=
  rfl

theorem cmAllNCoefficient_is_global_LFunction_coefficient
    (n : ℕ) :
    cmAllNCoefficient n = cmWeierstrass.LFunction n :=
  rfl

theorem cmLSeries_is_literal_mathlib_LSeries
    (s : ℂ) :
    cmLSeries s = cmWeierstrass.LSeries s :=
  rfl

end Synthesis.Millennium.BSD
