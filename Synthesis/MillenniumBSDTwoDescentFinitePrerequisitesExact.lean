import Synthesis.MillenniumBSDTwoDescentResidualCardinalityExact
import Mathlib.Tactic

/-!
# BSD: finite two-descent and elementary-two prerequisites

The previously proved Nat.card identity is a cardinality consequence of
an exact-sequence object. It is NOT automatically an F₂ dimension formula.

This owner derives what follows from explicit hypotheses on the literal
same-curve Selmer carrier:

* finite Selmer implies finite residual via surjectivity;
* finite Selmer implies finite MW/2 via injectivity;
* exponent-two Selmer implies exponent-two residual via the quotient map.

No universal Selmer finiteness, Sha identification or rank/2-torsion
dimension equation is assumed or inferred.
-/

namespace Synthesis.Millennium.BSD

namespace UniversalTwoDescentResidualOn

variable {E : RationalEllipticCurve}
variable (d : UniversalTwoDescentResidualOn E)

noncomputable local instance : CommGroup d.Selmer := d.selmerGroup
noncomputable local instance : CommGroup d.Residual := d.residualGroup

/-- Finiteness of the residual comes from an actual surjective group map. -/
theorem residual_finite_of_selmer_finite
    [Finite d.Selmer] : Finite d.Residual :=
  Finite.of_surjective d.residualMap d.residualSurjective

/-- Finiteness of MW/2 comes from the exact Kummer quotient injection. -/
theorem mordellWeilModuloTwo_finite_of_selmer_finite
    [Finite d.Selmer] :
    letI : E.1.IsElliptic := E.2
    Finite
      (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E) := by
  letI : E.1.IsElliptic := E.2
  exact Finite.of_injective
    d.quotientKummerToSelmer
    d.quotientKummerToSelmer_injective

/-- The residual of a group of exponent two also has exponent two. -/
theorem residual_exponent_two_of_selmer_exponent_two
    (hSelmer : ∀ s : d.Selmer, s * s = 1) :
    ∀ r : d.Residual, r * r = 1 := by
  intro r
  obtain ⟨s, rfl⟩ := d.residualSurjective r
  rw [← map_mul, hSelmer s, map_one]

/-- Same-curve finite-cardinality factorization, now with finiteness explicitly
available for both factors. This is still not an F₂ dimension statement. -/
theorem finite_selmer_two_descent_cardinality
    [Finite d.Selmer] :
    letI : E.1.IsElliptic := E.2
    Nat.card d.Selmer =
      Nat.card
        (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E) *
      Nat.card d.Residual := by
  letI : E.1.IsElliptic := E.2
  letI : Finite d.Residual :=
    d.residual_finite_of_selmer_finite
  letI : Finite
      (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E) :=
    d.mordellWeilModuloTwo_finite_of_selmer_finite
  exact d.selmerCard_eq_mordellWeilModuloTwo_mul_residualCard

end UniversalTwoDescentResidualOn

/-!
Next actual arithmetic obligations:

1. construct the Selmer carrier on every literal elliptic curve;
2. prove its finiteness and elementary-two structure using arithmetic,
   not a declaration in this file;
3. identify the exact residual with Sha(E)[2];
4. prove the full finite-dimensional formula with the rational 2-torsion term;
5. construct compatible higher Selmer levels for stable rank control.

The single two-descent quotient is not yet the universal BSD rank defect.
-/

end Synthesis.Millennium.BSD
