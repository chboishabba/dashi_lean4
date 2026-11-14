import Mathlib

/-!
# Selected W: exact SU3 positive spectral cubic and upgraded horn source cut

SOURCE ATTRIBUTION (claim roots rather than citation accumulation):
* Hatcher, Algebraic Topology Example 2B.2 owns the linked-horn
  marked commutator tower and original topology.
* Gotô 1949 owns compact semisimple commutator SURJECTIVITY, not the
  characteristic formula or the quantitative arc bound.
* Existing Agda neutrino PR #1247 owns the EXACT SU3 selected W and
  cyclotomic trace a-b*zeta, with zeta=-1/2+i sqrt(3)/2.
* Existing Agda #1249 / Lean #84 own the earlier sharp direct
  unitary commutator estimate d([A,B])²<=4s²-s⁴ for s<=sqrt(2).

NEW: exact rational scalar spectral cubic, negativity at 517/250,
abstract spectral factor rejection, and conditional child/curved
one-stage consumption. THE ACTUAL MATRIX SU3 characteristic
polynomial identity and analytical direct commutator norm estimate
remain EXTERNAL interfaces until explicitly imported/proved.
SOURCE-WRITTEN ONLY: no Lean kernel receipt or physical measurement.
-/

namespace DASHIHornSelectedWSpectralCubic

def trDenominator : ℚ := 181846007130841
def sourceTraceA : ℚ := 176093404722400 / trDenominator
def sourceTraceB : ℚ := 19836986431118 / trDenominator

/-- Real part of original exact Q(zeta3) selected trace. -/
def trReal : ℚ := sourceTraceA + sourceTraceB / 2

/-- Square of imaginary part, rational despite sqrt(3). -/
def trImagSquared : ℚ := (3 / 4) * sourceTraceB ^ 2

/-- Classical SU3/Newton polynomial for X=(W-I)^*(W-I)
when the 3x3 matrix W has trace t+iu, det W=1, W*W=I.
Its three roots are squared singular gaps (nonnegative real).
The matrix-to-scalar identity is a separate EXTERNAL source step. -/
def spectralCubic (x : ℚ) : ℚ :=
  x ^ 3 - 2 * (3 - trReal) * x ^ 2 +
    ((3 - trReal) ^ 2 + trImagSquared) * x -
    4 * trImagSquared

def selectedRootSqThreshold : ℚ := 517 / 250

theorem exactCubicNegative :
    spectralCubic selectedRootSqThreshold < 0 := by
  norm_num [spectralCubic, selectedRootSqThreshold,
    trReal, trImagSquared, sourceTraceA, sourceTraceB, trDenominator]

/-- If a valid source spectral factorization of the positive Hermitian
X is supplied, negativity of its characteristic at q forces some
eigenvalue >q. This is the exact 3-dimensional root discriminator. -/
theorem someSquaredGapAboveThreshold
    (x y z : ℚ)
    (hCharacteristic :
      (selectedRootSqThreshold - x) *
      (selectedRootSqThreshold - y) *
      (selectedRootSqThreshold - z) =
      spectralCubic selectedRootSqThreshold) :
    selectedRootSqThreshold < x ∨
    selectedRootSqThreshold < y ∨
    selectedRootSqThreshold < z := by
  by_contra h
  push_neg at h
  rcases h with ⟨hx, hy, hz⟩
  have hprod : 0 ≤
      (selectedRootSqThreshold - x) *
      (selectedRootSqThreshold - y) *
      (selectedRootSqThreshold - z) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy))
      (sub_nonneg.mpr hz)
  have hneg := exactCubicNegative
  linarith

/-- The scalar square of the existing DIRECT SU3 commutator arc cap,
valid as the source norm inequality for child gaps <=sqrt(2). -/
def directArcSquared (s : ℚ) : ℚ := 4 * s ^ 2 - s ^ 4

/-- Exact margin: direct child gap <=781/1000 cannot produce
selected W with squared root gap >517/250. -/
theorem directArcAt781BelowRoot :
    directArcSquared (781 / 1000 : ℚ) <
      selectedRootSqThreshold := by
  norm_num [directArcSquared, selectedRootSqThreshold]

/-- Pure rational monotonicity of the direct cap on [0,781/1000],
proved via factorization of a quartic. -/
theorem directArcMonotoneTo781
    (s : ℚ) (hs : 0 ≤ s) (hc : s ≤ 781 / 1000) :
    directArcSquared s ≤ directArcSquared (781 / 1000 : ℚ) := by
  have hsq : s ^ 2 ≤ (781 / 1000 : ℚ) ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ (781 / 1000 : ℚ) - s by linarith)
      (show 0 ≤ (781 / 1000 : ℚ) + s by linarith)
    nlinarith
  have hfactor : 0 ≤
      ((781 / 1000 : ℚ) ^ 2 - s ^ 2) *
      (4 - (781 / 1000 : ℚ) ^ 2 - s ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  unfold directArcSquared
  nlinarith

/-- Source-conditional theorem. hRootSq requires the TRUE original
selected W matrix plus its spectral cubic/matrix eigenvalues;
hDirect is the TRUE analytic unitary commutator bound for an
ACTUALLY Hatcher-marked flat child. This theorem invents neither. -/
theorem selectedWChildGapExceeds781
    (rootSq childGap : ℚ)
    (hRootSq : selectedRootSqThreshold < rootSq)
    (hChildNonneg : 0 ≤ childGap)
    (hDirect : rootSq ≤ directArcSquared childGap) :
    781 / 1000 < childGap := by
  by_contra h
  have hcap : childGap ≤ 781 / 1000 := le_of_not_gt h
  have hbound := directArcMonotoneTo781 childGap hChildNonneg hcap
  have hstrict := directArcAt781BelowRoot
  linarith

theorem curvedChildCap :
    directArcSquared (3 / 4 : ℚ) = 495 / 256 := by
  norm_num [directArcSquared]

theorem curvedChildStrictBound :
    directArcSquared (3 / 4 : ℚ) <
      (1391 / 1000 : ℚ) ^ 2 := by
  norm_num [directArcSquared]

theorem selectedRootStrictBound :
    (1437 / 1000 : ℚ) ^ 2 <
      selectedRootSqThreshold := by
  norm_num [selectedRootSqThreshold]

theorem exactCurvedMargin :
    (1391 / 1000 : ℚ) + 23 / 500 = 1437 / 1000 := by
  norm_num

/-- ONE source-specific curved parent-to-child commutator transport
suffices. Genuine geometric Hatcher marking, analytic SU3 norm cap,
based Stokes homotopy and eta are explicitly required inputs.
The same selected W is not inferred from a merely similar matrix. -/
theorem selectedWCurvedOneStageReject
    (rootGap commGap childGap eta : ℚ)
    (hRootNonneg : 0 ≤ rootGap)
    (hCommNonneg : 0 ≤ commGap)
    (hChildNonneg : 0 ≤ childGap)
    (hChildCap : childGap ≤ 3 / 4)
    (hEtaCap : eta ≤ 23 / 500)
    (hRootSpectral : selectedRootSqThreshold < rootGap ^ 2)
    (hTrueDirectArc : commGap ^ 2 ≤ directArcSquared childGap)
    (hTrueBasedCurvedStep : rootGap ≤ eta + commGap) :
    False := by
  have hChildSq : childGap ^ 2 ≤ (3 / 4 : ℚ) ^ 2 := by
    have hp := mul_nonneg
      (show 0 ≤ (3 / 4 : ℚ) - childGap by linarith)
      (show 0 ≤ (3 / 4 : ℚ) + childGap by linarith)
    nlinarith
  have hfactor : 0 ≤
      ((3 / 4 : ℚ) ^ 2 - childGap ^ 2) *
      (4 - (3 / 4 : ℚ) ^ 2 - childGap ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hArcCap : directArcSquared childGap ≤
      directArcSquared (3 / 4 : ℚ) := by
    unfold directArcSquared
    nlinarith
  have hCommSmall : commGap < (1391 / 1000 : ℚ) := by
    have hscalar := curvedChildStrictBound
    nlinarith
  have hRootSmall : rootGap < (1437 / 1000 : ℚ) := by
    linarith
  have hRootLarge := selectedRootStrictBound
  nlinarith


/-!
## Exact source spectral intervals

The three disjoint real intervals below have opposite endpoint signs
for the EXACT cubic derived from the original Q(zeta3) trace.
A classical intermediate-value/degree-three argument isolates
all three eigenvalue-squared gaps, provided the actual SU3
matrix-to-cubic bridge is supplied. No new physical spectral claim.
-/

theorem lowSquaredGapSignChange :
    spectralCubic (919 / 100000 : ℚ) *
      spectralCubic (920 / 100000 : ℚ) < 0 := by
  norm_num [spectralCubic, trReal, trImagSquared,
    sourceTraceA, sourceTraceB, trDenominator]

theorem middleSquaredGapSignChange :
    spectralCubic (187659 / 100000 : ℚ) *
      spectralCubic (187660 / 100000 : ℚ) < 0 := by
  norm_num [spectralCubic, trReal, trImagSquared,
    sourceTraceA, sourceTraceB, trDenominator]

theorem highSquaredGapSignChange :
    spectralCubic (206838 / 100000 : ℚ) *
      spectralCubic (206839 / 100000 : ℚ) < 0 := by
  norm_num [spectralCubic, trReal, trImagSquared,
    sourceTraceA, sourceTraceB, trDenominator]

theorem spectralIntervalsOrdered :
    (920 / 100000 : ℚ) < 187659 / 100000 ∧
      (187660 / 100000 : ℚ) < 206838 / 100000 := by
  constructor <;> norm_num


end DASHIHornSelectedWSpectralCubic
