import Integration.OggSSPP2F4WeilMillerFixedPhase

/-!
# Curve-specific Miller divisor geometry: triple tangent and triple infinity cuts

This file pays the algebraic intersection calculation behind the fixed-phase
Miller functions for the genuine special fibre

  E : Y^2 Z + Y Z^2 = X^3

over F4.

For P=(0,0) and Q=(1,zeta), the tangent lines cut the affine cubic with
multiplicity three at their base point.  The projective line Z=0 cuts the
homogeneous cubic with equation -X^3, hence with multiplicity three at the
unique projective infinity point [0:1:0].

These are exactly the numerator/denominator intersection multiplicities needed
for div(f_P)=3[P]-3[O] and div(f_Q)=3[Q]-3[O].  This owner proves the
curve-specific polynomial identities.  Packaging those intersection
multiplicities as Mathlib divisors/rational functions remains a library-facing
representation step; no phase is assumed here.
-/

namespace Integration.OggSSPP2F4MillerDivisorGeometry

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace T := Integration.OggSSPP2F4CurveTangentFlex

/-- P=(0,0) is on the affine curve. -/
theorem P_on_curve :
    (0 : B.F4)^2 + 0 = (0 : B.F4)^3 := by
  norm_num

/-- Q=(1,zeta) is on the affine curve. -/
theorem Q_on_curve :
    Z.zeta^2 + Z.zeta = (1 : B.F4)^3 := by
  simpa using Z.zeta_trace_one

/-- The P tangent is y=0 and its substitution into the affine cubic is X^3:
a triple intersection at x=0. -/
theorem tangent_at_P_cuts_as_cube (X : B.F4) :
    (T.tangentY 0 0 X)^2 + T.tangentY 0 0 X + X^3 = X^3 := by
  simpa using T.tangent_meets_cubic_as_triple_root
    (0 : B.F4) (0 : B.F4) P_on_curve X

/-- The Q tangent is y=zeta+X+1 and its substitution is (X+1)^3:
a triple intersection at x=1. -/
theorem tangent_at_Q_cuts_as_cube (X : B.F4) :
    (T.tangentY 1 Z.zeta X)^2 + T.tangentY 1 Z.zeta X + X^3
      = (X+1)^3 := by
  simpa using T.tangent_meets_cubic_as_triple_root
    (1 : B.F4) Z.zeta Q_on_curve X

/-- The explicit tangent used by the Miller phase owner is exactly the
geometric tangent at Q. -/
theorem tangentFunctionAtQ_is_geometric_tangent_difference
    (X Y : B.F4) :
    Integration.OggSSPP2F4WeilMillerFixedPhase.tangentFunctionAtQ X Y
      = Y + T.tangentY 1 Z.zeta X := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  simp [Integration.OggSSPP2F4WeilMillerFixedPhase.tangentFunctionAtQ,
    T.tangentY]
  linear_combination Z.zeta * htwo

/-- Likewise f_P=y is the difference from the tangent y=0. -/
theorem tangentFunctionAtP_is_geometric_tangent_difference
    (X Y : B.F4) :
    Integration.OggSSPP2F4WeilMillerFixedPhase.tangentFunctionAtP X Y
      = Y + T.tangentY 0 0 X := by
  simp [Integration.OggSSPP2F4WeilMillerFixedPhase.tangentFunctionAtP,
    T.tangentY]

/-- Restriction of the homogeneous cubic to the line at infinity Z=0.
The cube shows triple intersection at X=0. -/
theorem infinity_line_cuts_as_cube (X Y : B.F4) :
    Z.specialHomogeneousCubic X Y 0 = -(X^3) := by
  simp [Z.specialHomogeneousCubic]

/-- On the projective cubic, every point with Z=0 necessarily has X=0;
therefore the only projective infinity point is represented by [0:1:0]. -/
theorem projective_infinity_forces_X_zero
    (X Y : B.F4)
    (hcurve : Z.specialHomogeneousCubic X Y 0 = 0) :
    X = 0 := by
  have hx3 : X^3 = 0 := by
    simpa [Z.specialHomogeneousCubic] using hcurve
  exact (pow_eq_zero hx3)

theorem numerator_denominator_triple_cut_certificate :
    (∀ X : B.F4,
      (T.tangentY 0 0 X)^2 + T.tangentY 0 0 X + X^3 = X^3)
    ∧
    (∀ X : B.F4,
      (T.tangentY 1 Z.zeta X)^2 + T.tangentY 1 Z.zeta X + X^3
        = (X+1)^3)
    ∧
    (∀ X Y : B.F4,
      Z.specialHomogeneousCubic X Y 0 = -(X^3)) := by
  exact ⟨tangent_at_P_cuts_as_cube,
    tangent_at_Q_cuts_as_cube,
    infinity_line_cuts_as_cube⟩

end Integration.OggSSPP2F4MillerDivisorGeometry
