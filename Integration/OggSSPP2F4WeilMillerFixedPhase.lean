import Integration.OggSSPP2F4CurveTangentFlex

/-!
# Fixed-phase Miller function evaluation on the genuine F4 curve

For E: y^2+y=x^3, P=(0,0), Q=(1,zeta), the tangent flex
functions are f_P=y and f_Q=y+x+1+zeta.
Their off-divisor evaluations are f_P(Q)=zeta and
f_Q(P)=1+zeta=zeta^2.

The standard monic Miller/Weil formula is
e_3(P,Q)=(-1)^3*f_P(Q)/f_Q(P).
In characteristic two this candidate is zeta^2, NOT zeta.

This file proves the actual finite field computation without *defining*
the intrinsic geometric Weil pairing by the desired value. The remaining
external geometry is construction of rational functions with these precise
divisors, monic normalization at infinity, and identification with the
independent Weil-pairing implementation.
-/

namespace Integration.OggSSPP2F4WeilMillerFixedPhase

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates

def tangentFunctionAtP (x y : B.F4) : B.F4 := y
def tangentFunctionAtQ (x y : B.F4) : B.F4 := y + x + 1 + Z.zeta

theorem tangent_P_at_Q :
    tangentFunctionAtP 1 Z.zeta = Z.zeta := by
  rfl

theorem tangent_Q_at_P :
    tangentFunctionAtQ 0 0 = Z.zeta ^ 2 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  dsimp [tangentFunctionAtQ]
  linear_combination -(Z.zeta_trace_one) + Z.zeta * htwo

theorem normalized_flex_ratio :
    tangentFunctionAtP 1 Z.zeta /
        tangentFunctionAtQ 0 0 = Z.zeta ^ 2 := by
  rw [tangent_P_at_Q, tangent_Q_at_P]
  apply (div_eq_iff (pow_ne_zero 2 Z.zeta_ne_zero)).2
  calc
    Z.zeta = Z.zeta ^ 4 := Z.zeta_fourth_is_zeta.symm
    _ = Z.zeta ^ 2 * Z.zeta ^ 2 := by ring

theorem signed_normalized_flex_ratio :
    ((-1 : B.F4) ^ 3) *
      (tangentFunctionAtP 1 Z.zeta /
       tangentFunctionAtQ 0 0) = Z.zeta ^ 2 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hmone : (-1 : B.F4) = 1 := by
    linear_combination -htwo
  rw [hmone, one_pow, one_mul, normalized_flex_ratio]

/-- A *conditional* fixed-phase conclusion. The missing hypothesis is
the independent geometric Weil-pairing/Miller divisor theorem, not the
finite field arithmetic in this file. -/
theorem intrinsic_phase_of_geometric_miller_identification
    (geometricWeilOnPQ : B.F4)
    (hMiller :
      geometricWeilOnPQ =
        ((-1 : B.F4) ^ 3) *
          (tangentFunctionAtP 1 Z.zeta /
           tangentFunctionAtQ 0 0)) :
    geometricWeilOnPQ = Z.zeta ^ 2 := by
  rw [hMiller, signed_normalized_flex_ratio]

end Integration.OggSSPP2F4WeilMillerFixedPhase
