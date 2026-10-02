import Integration.OggSSPP2F4WeilMillerFixedPhase
import Integration.OggSSPP2F4ConcreteCubicPhase

/-!
# Fixed Miller phase -> existing native elliptic/Heisenberg pairing orientation

The independently computed tangent-Miller ratio at P,Q is zeta^2.
The repository's concrete cubic phase map sends the F3 exponent -1 to zeta^2.
This file proves that the Miller normalization therefore selects the *negative*
orientation of ellipticOmega, which is exactly the orientation already used by
OggSSPP2F4EllipticHeisenbergPairing.

No second pairing is introduced.  The only remaining geometric input is the
upstream theorem that an independently constructed intrinsic Weil pairing is
alternating/biadditive and that its P,Q value is represented by the verified
Miller ratio.  Mathlib currently has division-polynomial/Weierstrass support but
no native general Weil-pairing implementation, so this owner closes the
curve-specific orientation/transport seam rather than postulating that library.
-/

namespace Integration.OggSSPP2F4WeilMillerPhaseToNative

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace M := Integration.OggSSPP2F4WeilMillerFixedPhase
namespace C := Integration.OggSSPP2F4ConcreteCubicPhase
namespace P := Integration.OggSSPP2F4ActualPairingNormalization
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace Native := Integration.OggSSPP2F4EllipticHeisenbergPairing

theorem miller_ratio_is_negative_concrete_phase :
    ((-1 : B.F4) ^ 3) *
      (M.tangentFunctionAtP 1 Z.zeta /
       M.tangentFunctionAtQ 0 0)
      = C.phase (-1) := by
  rw [M.signed_normalized_flex_ratio, C.phase_neg_one]

private theorem zeta_sq_ne_one : Z.zeta ^ 2 ≠ (1 : B.F4) := by
  intro h
  have hz0 : Z.zeta = 0 := by
    linear_combination Z.zeta_trace_one - h
  exact Z.zeta_ne_zero hz0

private theorem zeta_ne_zeta_sq : Z.zeta ≠ Z.zeta ^ 2 := by
  intro h
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hsum : Z.zeta ^ 2 + Z.zeta = 0 := by
    rw [← h]
    linear_combination Z.zeta * htwo
  have honezero : (1 : B.F4) = 0 := by
    linear_combination Z.zeta_trace_one - hsum
  norm_num at honezero

theorem concrete_phase_eq_zeta_sq_implies_neg_one
    (a : ZMod 3)
    (h : C.phase a = Z.zeta ^ 2) :
    a = -1 := by
  fin_cases a
  · exfalso
    apply zeta_sq_ne_one
    simpa using h.symm
  · exfalso
    apply zeta_ne_zeta_sq
    simpa using h
  · decide

/-- The Miller ratio fixes the F3 exponent orientation uniquely. -/
theorem concrete_phase_eq_miller_ratio_implies_neg_one
    (a : ZMod 3)
    (h :
      C.phase a =
        ((-1 : B.F4) ^ 3) *
          (M.tangentFunctionAtP 1 Z.zeta /
           M.tangentFunctionAtQ 0 0)) :
    a = -1 := by
  rw [M.signed_normalized_flex_ratio] at h
  exact concrete_phase_eq_zeta_sq_implies_neg_one a h

/-- Once an independently geometric pairing supplies the standard additive
laws and its concrete P,Q phase agrees with the Miller evaluation, its entire
F3 exponent pairing is forced to the native Heisenberg orientation. -/
theorem miller_normalized_pairing_equals_existing_native
    (β : E.ActualCurveGroup →+ (E.ActualCurveGroup →+ ZMod 3))
    (hAlt : ∀ p : E.ActualCurveGroup, β p p = 0)
    (hMillerPhase :
      C.phase (β G.P G.Q) =
        ((-1 : B.F4) ^ 3) *
          (M.tangentFunctionAtP 1 Z.zeta /
           M.tangentFunctionAtQ 0 0)) :
    ∀ p q,
      β p q = Native.pairing p q := by
  have hphase : β G.P G.Q = -1 :=
    concrete_phase_eq_miller_ratio_implies_neg_one _ hMillerPhase
  have horient :=
    P.inverted_orientation_pairing_unique β hAlt hphase
  intro p q
  calc
    β p q = -P.ellipticOmega p q := horient p q
    _ = Native.pairing p q :=
      (P.existing_native_elliptic_pairing_eq_neg_normalized p q).symm

/-- In concrete F4 phase language the P,Q native phase is exactly zeta^2,
matching the independent Miller calculation. -/
theorem existing_native_PQ_concrete_phase_is_miller_ratio :
    C.phase (Native.pairing G.P G.Q)
      =
    ((-1 : B.F4) ^ 3) *
      (M.tangentFunctionAtP 1 Z.zeta /
       M.tangentFunctionAtQ 0 0) := by
  have hnative :
      Native.pairing G.P G.Q = (-1 : ZMod 3) := by
    rw [P.existing_native_elliptic_pairing_eq_neg_normalized,
      P.ellipticOmega_P_Q]
  rw [hnative, C.phase_neg_one, M.signed_normalized_flex_ratio]

end Integration.OggSSPP2F4WeilMillerPhaseToNative
