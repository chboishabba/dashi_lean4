import Synthesis.MillenniumBSDFrobeniusPointCount
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.FieldTheory.Cardinality
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

theorem localEulerFactor_isMultiplicative
    (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K]
    [Finite (IsLocalRing.ResidueField R)]
    (W : WeierstrassCurve K) :
    ArithmeticFunction.IsMultiplicative
      (W.localEulerFactor R) := by
  letI : Fintype (IsLocalRing.ResidueField R) :=
    Fintype.ofFinite (IsLocalRing.ResidueField R)
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · simpa [Nat.card_eq_fintype_card] using
      (Fintype.isPrimePow_card_of_field
        (α := IsLocalRing.ResidueField R))
  · simp [WeierstrassCurve.localPowerSeries]

noncomputable def cmFormalLFunction :
    ArithmeticFunction ℤ :=
  cmWeierstrass.LFunction

theorem cmFormalLFunction_isMultiplicative :
    ArithmeticFunction.IsMultiplicative cmFormalLFunction := by
  unfold cmFormalLFunction WeierstrassCurve.LFunction
  apply ArithmeticFunction.isMultiplicative_eulerProduct
  intro p
  exact localEulerFactor_isMultiplicative
    (p.adicCompletionIntegers ℚ)
    (cmWeierstrass.baseChange (p.adicCompletion ℚ))

noncomputable def cmAllNCoefficient (n : ℕ) : ℤ :=
  cmFormalLFunction n

@[simp] theorem cmAllNCoefficient_zero :
    cmAllNCoefficient 0 = 0 := by
  simp [cmAllNCoefficient, cmFormalLFunction]

theorem cmAllNCoefficient_one :
    cmAllNCoefficient 1 = 1 := by
  exact cmFormalLFunction_isMultiplicative.map_one

theorem cmAllNCoefficient_coprime_mul
    {m n : ℕ} (h : m.Coprime n) :
    cmAllNCoefficient (m * n) =
      cmAllNCoefficient m * cmAllNCoefficient n := by
  exact cmFormalLFunction_isMultiplicative.map_mul_of_coprime h

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
