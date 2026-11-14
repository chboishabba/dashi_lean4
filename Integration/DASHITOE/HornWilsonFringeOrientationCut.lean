import Mathlib
import Integration.DASHITOE.HornSelectedWSpectralCubicCut

/-!
# Selected Wilson fringe: reversal-odd versus basing-conjugation-even

SOURCE OWNERSHIP:
Hatcher Algebraic Topology Ex 2B.2 owns the marked commutator source.
Existing Agda neutrino PR #1247 owns SAME exact SU3 W cyclotomic trace
and its illustrative unpolarized two-arm probability at phase zero,
NeutrinoHornedWilsonInterferenceExact.agda. Agda horn #1244 owns
C3 satellite rotation and explicit central basing paths.
Agda #1249 / Lean #84 own source-conditional norm bounds.
This module does NOT construct a new neutrino matrix or interferometer.

For W in SU3, tr(W⁻¹)=conj(tr W), so d(W)=d(W⁻¹) but the
chosen two-path fringe P_W(phi)=1/2 + Re(e^(i phi) tr W)/6
satisfies P_{W⁻¹}(phi)=P_W(-phi). At phi=0 these are
identical, at +/- pi/2 the signed contrast reverses.

The physical phase calibration, connected gauge field and true
Hatcher source meridian are all EXTERNAL. Our rational records below
capture only the exact selected trace's signed coefficient and the
square of the irrational contrast, NOT a synthetic hardware datum.
No Lean/Lake kernel execution is claimed.
-/
namespace DASHIHornWilsonFringeOrientation

def traceDenominator : ℚ := 181846007130841
def sourceTraceRational : ℚ := 176093404722400 / traceDenominator
def sourceZetaMagnitude : ℚ := 19836986431118 / traceDenominator

/-- Re tr(W)=a+b/2 with zeta=-1/2+i sqrt3/2. -/
def selectedRealTrace : ℚ :=
  sourceTraceRational + sourceZetaMagnitude / 2

/-- Existing original PR #1247's zero-phase model port,
recalculated without refitting the original selected W. -/
def phaseZeroPort : ℚ := 1/2 + selectedRealTrace/6

theorem phaseZeroExact :
    phaseZeroPort = 434928608401 / 648677790003 := by
  norm_num [phaseZeroPort, selectedRealTrace, sourceTraceRational,
    sourceZetaMagnitude, traceDenominator]

/-- Squared difference P(+π/2)-P(-π/2) for the selected W:
(Im tr(W))²/9 = (3 b²/4)/9 = b²/12.
This is a conditional model contrast, not real measured fringes. -/
def orientationOddContrastSq : ℚ := sourceZetaMagnitude ^ 2 / 12

theorem nonzeroOddContrast :
    0 < orientationOddContrastSq := by
  norm_num [orientationOddContrastSq, sourceZetaMagnitude,
    traceDenominator]

theorem exactOddContrastSquare :
    orientationOddContrastSq =
      98376507667089911639682481 /
        99203910928289627462680101843 := by
  norm_num [orientationOddContrastSq, sourceZetaMagnitude,
    traceDenominator]

/-- The sign convention is encoded only in the coefficient of the
nonnegative √3/6 multiplier in the phase-odd port contrast. -/
def signedOddCoefficient (invertLoop : Bool) : ℚ :=
  if invertLoop then -sourceZetaMagnitude
  else sourceZetaMagnitude

theorem originalOrientationPositive :
    0 < signedOddCoefficient false := by
  norm_num [signedOddCoefficient, sourceZetaMagnitude, traceDenominator]

theorem inverseOrientationNegative :
    signedOddCoefficient true < 0 := by
  norm_num [signedOddCoefficient, sourceZetaMagnitude, traceDenominator]

theorem orientationInversionFlipsOdd :
    signedOddCoefficient true = -signedOddCoefficient false := by
  simp [signedOddCoefficient]

/-- The two EXACT orientations share the selected real part of
the source trace; reversing only the odd part is not a new independent
C3-sector observation. The original physical two-arm formula remains
external, owned by the neutrino PR #1247. -/
theorem orientationSignsAreOppositeAndNonzero :
    signedOddCoefficient false = -signedOddCoefficient true ∧
      0 < signedOddCoefficient false := by
  constructor
  · simp [signedOddCoefficient]
  · exact originalOrientationPositive

end DASHIHornWilsonFringeOrientation
