import Integration.OggSSPP2F4MillerDivisorGeometry
import Integration.OggSSPP2F4WeilMillerPhaseToNative

/-!
# Curve-specific Weil/Miller certificate for E : y²+y=x³ over F4

This is the finite geometric payload needed by the intrinsic Weil-pairing lane,
assembled without defining the phase by the existing Heisenberg pairing.

Owned here:
* P=(0,0), Q=(1,zeta) lie on the genuine special fibre;
* tangent numerators cut the cubic triply at P and Q;
* the denominator line Z=0 cuts the projective cubic triply at O;
* the off-divisor Miller evaluations are nonzero;
* the normalized Miller ratio is zeta²;
* the existing native pairing has exactly that concrete phase.

What remains external is the generic algebraic-geometry theorem packaging these
line-intersection identities into rational-function divisors and the standard
Miller definition of the Weil pairing.  No curve-specific arithmetic remains
undetermined after this certificate.
-/

namespace Integration.OggSSPP2F4WeilCurveSpecificCertificate

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace D := Integration.OggSSPP2F4MillerDivisorGeometry
namespace M := Integration.OggSSPP2F4WeilMillerFixedPhase
namespace N := Integration.OggSSPP2F4WeilMillerPhaseToNative
namespace Native := Integration.OggSSPP2F4EllipticHeisenbergPairing
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace C := Integration.OggSSPP2F4ConcreteCubicPhase

theorem tangent_P_at_Q_nonzero :
    M.tangentFunctionAtP 1 Z.zeta ≠ 0 := by
  rw [M.tangent_P_at_Q]
  exact Z.zeta_ne_zero

theorem tangent_Q_at_P_nonzero :
    M.tangentFunctionAtQ 0 0 ≠ 0 := by
  rw [M.tangent_Q_at_P]
  exact pow_ne_zero 2 Z.zeta_ne_zero

theorem miller_ratio_exact :
    ((-1 : B.F4)^3) *
      (M.tangentFunctionAtP 1 Z.zeta /
       M.tangentFunctionAtQ 0 0)
      = Z.zeta^2 := by
  exact M.signed_normalized_flex_ratio

theorem native_PQ_phase_exact :
    C.phase (Native.pairing G.P G.Q) = Z.zeta^2 := by
  rw [N.existing_native_PQ_concrete_phase_is_miller_ratio,
      M.signed_normalized_flex_ratio]

structure CurveSpecificMillerCertificate where
  P_on_curve :
    (0 : B.F4)^2 + 0 = (0 : B.F4)^3
  Q_on_curve :
    Z.zeta^2 + Z.zeta = (1 : B.F4)^3
  tangentPTriple :
    ∀ X : B.F4,
      (Integration.OggSSPP2F4CurveTangentFlex.tangentY 0 0 X)^2
        + Integration.OggSSPP2F4CurveTangentFlex.tangentY 0 0 X
        + X^3 = X^3
  tangentQTriple :
    ∀ X : B.F4,
      (Integration.OggSSPP2F4CurveTangentFlex.tangentY 1 Z.zeta X)^2
        + Integration.OggSSPP2F4CurveTangentFlex.tangentY 1 Z.zeta X
        + X^3 = (X+1)^3
  infinityTriple :
    ∀ X Y : B.F4,
      Z.specialHomogeneousCubic X Y 0 = -(X^3)
  numeratorAtQNonzero :
    M.tangentFunctionAtP 1 Z.zeta ≠ 0
  denominatorAtPNonzero :
    M.tangentFunctionAtQ 0 0 ≠ 0
  normalizedMillerRatio :
    ((-1 : B.F4)^3) *
      (M.tangentFunctionAtP 1 Z.zeta /
       M.tangentFunctionAtQ 0 0)
      = Z.zeta^2
  nativeConcretePhase :
    C.phase (Native.pairing G.P G.Q) = Z.zeta^2

def canonicalCurveSpecificMillerCertificate :
    CurveSpecificMillerCertificate where
  P_on_curve := D.P_on_curve
  Q_on_curve := D.Q_on_curve
  tangentPTriple := D.tangent_at_P_cuts_as_cube
  tangentQTriple := D.tangent_at_Q_cuts_as_cube
  infinityTriple := D.infinity_line_cuts_as_cube
  numeratorAtQNonzero := tangent_P_at_Q_nonzero
  denominatorAtPNonzero := tangent_Q_at_P_nonzero
  normalizedMillerRatio := miller_ratio_exact
  nativeConcretePhase := native_PQ_phase_exact

/-- Any intrinsic geometric pairing satisfying the standard additive laws and
the standard Miller evaluation on P,Q is therefore forced to the existing
native Heisenberg pairing everywhere. -/
theorem intrinsic_pairing_forced_to_native
    (β :
      Integration.OggSSPP2F4ActualEllipticGroup.ActualCurveGroup →+
        (Integration.OggSSPP2F4ActualEllipticGroup.ActualCurveGroup →+ ZMod 3))
    (hAlt :
      ∀ p : Integration.OggSSPP2F4ActualEllipticGroup.ActualCurveGroup,
        β p p = 0)
    (hMiller :
      C.phase (β G.P G.Q) =
        ((-1 : B.F4)^3) *
          (M.tangentFunctionAtP 1 Z.zeta /
           M.tangentFunctionAtQ 0 0)) :
    ∀ p q, β p q = Native.pairing p q :=
  N.miller_normalized_pairing_equals_existing_native β hAlt hMiller

end Integration.OggSSPP2F4WeilCurveSpecificCertificate
