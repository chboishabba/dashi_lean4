import Synthesis.MillenniumBSDCMClayPointKummerExact
import Synthesis.MillenniumBSDTwoDescentFinitePrerequisitesExact
import Mathlib.Tactic

/-!
# Concrete CM instance of the exact finite two-descent consequences

The preceding source constructs a genuine point-level Kummer homomorphism on
the Clay-facing curve y²=x³-x, identifies its kernel with rational doubles,
and attaches the existing explicit two-Selmer residual cokernel.

Here the generic exact-sequence arithmetic is applied to that SPECIFIC object.
The result is not a universal BSD theorem and is not a stable-rank equality.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

private noncomputable instance : cmRationalEllipticCurve.1.IsElliptic :=
  cmRationalEllipticCurve.2

theorem cmClayTwoDescentCardinality :
    Nat.card explicitTwoSelmerSubgroup =
      Nat.card
        (Multiplicative CMClayRationalPoint ⧸
          rationalDoubleSubgroup cmRationalEllipticCurve)
        * Nat.card ExplicitTwoSelmerCokernel := by
  exact cmClayTwoDescentResidual.selmerCard_eq_mordellWeilModuloTwo_mul_residualCard

theorem cmClayResidualFinite_of_selmerFinite
    [Finite explicitTwoSelmerSubgroup] :
    Finite ExplicitTwoSelmerCokernel :=
  cmClayTwoDescentResidual.residual_finite_of_selmer_finite

theorem cmClayModuloTwoFinite_of_selmerFinite
    [Finite explicitTwoSelmerSubgroup] :
    Finite
      (Multiplicative CMClayRationalPoint ⧸
        rationalDoubleSubgroup cmRationalEllipticCurve) :=
  cmClayTwoDescentResidual.mordellWeilModuloTwo_finite_of_selmer_finite

/-- The explicit Selmer subgroup inherits exponent two from the ACTUAL
rational square-class group, not from an additional supplied Selmer premise. -/
theorem cmClaySelmerExponentTwo
    (s : explicitTwoSelmerSubgroup) :
    s * s = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · change (s.1.1 * s.1.1 : RatSquareClass) = 1
    exact ratSquareClass_sq_eq_one s.1.1
  · change (s.1.2 * s.1.2 : RatSquareClass) = 1
    exact ratSquareClass_sq_eq_one s.1.2

/-- Unconditional exponent-two law for the literal worked CM residual. -/
theorem cmClayResidualExponentTwo_actual :
    ∀ r : ExplicitTwoSelmerCokernel, r * r = 1 :=
  cmClayTwoDescentResidual.residual_exponent_two_of_selmer_exponent_two
    cmClaySelmerExponentTwo

/-- Unconditional exponent-two law for the literal CM Mordell--Weil mod-2
quotient, derived through the actual Kummer injection. -/
theorem cmClayMordellWeilModuloTwoExponentTwo_actual :
    ∀ q :
      Multiplicative CMClayRationalPoint ⧸
        rationalDoubleSubgroup cmRationalEllipticCurve,
      q * q = 1 :=
  cmClayTwoDescentResidual.mordellWeilModuloTwo_exponent_two_of_selmer_exponent_two
    cmClaySelmerExponentTwo

theorem cmClayResidualExponentTwo
    (hSelmer :
      ∀ s : explicitTwoSelmerSubgroup, s * s = 1) :
    ∀ r : ExplicitTwoSelmerCokernel, r * r = 1 :=
  cmClayTwoDescentResidual.residual_exponent_two_of_selmer_exponent_two
    hSelmer

theorem cmClayMordellWeilModuloTwoExponentTwo
    (hSelmer :
      ∀ s : explicitTwoSelmerSubgroup, s * s = 1) :
    ∀ q :
      Multiplicative CMClayRationalPoint ⧸
        rationalDoubleSubgroup cmRationalEllipticCurve,
      q * q = 1 :=
  cmClayTwoDescentResidual.mordellWeilModuloTwo_exponent_two_of_selmer_exponent_two
    hSelmer

/-!
Finiteness and exponent-two conditions remain explicit when not yet proved
from the real CM Selmer arithmetic. An all-curve extension needs construction
of all-place Selmer and residual objects, higher 2-power compatibility, and
independent analytic rank comparison on the same curve.
-/

end

end Synthesis.Millennium.BSD
