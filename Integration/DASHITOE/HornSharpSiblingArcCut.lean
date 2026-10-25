import Mathlib

/-!
# Sharp unitary sibling arc: exact rational coefficient certificates

Original topological source: Hatcher, Algebraic Topology Example 2B.2.
Original compact group commutator: Morikuni Goto (1949).
Previously selected W: Agda neutrino PR #1247; earlier universal 2*d(B)
sibling coefficient: Agda PR #1249 and Lean PR #84.

New ANALYTIC mathematical argument, NOT formalised as matrices here:
For unitary B with delta=||B-I||<=sqrt(2), put lambda=1-delta^2/2.
Then B+B*>=2lambda I implies
||(B-lambda I)||^2<=delta^2-delta^4/4.
Since AB-BA=[A-I,B-lambda I], the sibling multiplier is at most
2*delta*sqrt(1-delta^2/4), sharp for SU3 spectral pair +/-alpha
and infinitesimal transverse A_t. Critical delta=sqrt(2-sqrt(3)).

This source-WRITTEN Lean file kernel-proves only conditional scalar
rational certificates IF compiled. It does not assert an actual
normed matrix, source horn metric, or nonabelian Stokes homotopy.
-/

namespace DASHIHornSharpSiblingArc

/-- Square of the analytic unitary sibling operator-norm coefficient,
for nonnegative delta <= sqrt(2). -/
def arcCoefficientSquared (delta : ℚ) : ℚ :=
  4 * delta ^ 2 * (1 - delta ^ 2 / 4)

/-- Centering the spectral arc has this exact identity. -/
theorem centeredArcIdentity (delta : ℚ) :
    1 - (1 - delta ^ 2 / 2) ^ 2 =
      delta ^ 2 - delta ^ 4 / 4 := by
  ring

theorem halfGapCoefficientSquared :
    arcCoefficientSquared (1 / 2 : ℚ) = 15 / 16 := by
  norm_num [arcCoefficientSquared]

theorem beyondOldHalfGap :
    (1 / 2 : ℚ) < 31 / 60 := by norm_num

theorem rationalArcWitness :
    arcCoefficientSquared (31 / 60 : ℚ) =
      12914879 / 12960000 := by
  norm_num [arcCoefficientSquared]

theorem rationalArcContracts :
    arcCoefficientSquared (31 / 60 : ℚ) < 1 := by
  norm_num [arcCoefficientSquared]

theorem rationalCurvedCap :
    arcCoefficientSquared (31 / 60 : ℚ) <
      (999 / 1000 : ℚ) ^ 2 := by
  norm_num [arcCoefficientSquared]

theorem largerGapFailsContraction :
    1 < arcCoefficientSquared (13 / 25 : ℚ) := by
  norm_num [arcCoefficientSquared]

/-- A finite exact squared-gap budget when 22 genuine source sibling
gaps all obey 1/2: an external SU3 operator-norm theorem supplies
the multiplication of 15/16 at each step. -/
theorem depthTwentyTwoSquaredBudget :
    4 * (15 / 16 : ℚ) ^ 22 <= 1 := by
  norm_num

theorem depthTwentyOneNotYetEnough :
    1 < 4 * (15 / 16 : ℚ) ^ 21 := by
  norm_num

/-- No unconditional SU3 or Hatcher geometry claim:
hsource is the true squared holonomy estimate to be supplied by
the analytic matrix owner and actual marked source loops. -/
theorem selectedRootRejectWithArcReceipt
    (rootGap : ℚ) (hroot : 1 < rootGap)
    (hsource : rootGap ^ 2 <=
      4 * (15 / 16 : ℚ) ^ 22) : False := by
  have hcap := depthTwentyTwoSquaredBudget
  have hr : 0 < rootGap := by linarith
  nlinarith


/-!
## Same selected-W first-generation result (new finite source discriminator)

The original selected W and source rational lower trace/norm belong to
Agda neutrino #1247 and earlier Agda #1249 respectively. If W=[A,B]
as a GENUINE flat Hatcher-marked parent commutator, the direct centered
arc inequality (also valid without any factor d(A)) gives
d(W)<=2*d(B)*sqrt(1-d(B)^2/4), for d(B)<=sqrt(2).
The same applies to the other child by symmetry.
The exact source root certificate is larger than 819/625, the
squared direct cap at delta=3/5, so BOTH children must have d>3/5.
This is an elementary new arithmetic consequence, not a source
meridian/physical gauge-field construction. The analytic matrix
norm-to-rational premise is EXTERNAL here.
-/

def selectedWCertifiedRootGapSqLower : ℚ :=
  854996726408 / 648677790003

theorem sourceRootExceedsThreeFifthsArcCap :
    (819 / 625 : ℚ) < selectedWCertifiedRootGapSqLower := by
  norm_num [selectedWCertifiedRootGapSqLower]

theorem threeFifthsArcCoefficientSquared :
    arcCoefficientSquared (3 / 5 : ℚ) = 819 / 625 := by
  norm_num [arcCoefficientSquared]

/-- Pure rational polynomial monotonicity on the source-relevant
interval, and thus a sound scalar upper cap for any actual unitary
sibling with 0<=d(B)<=3/5. -/
theorem arcMonotoneToThreeFifths
    (delta : ℚ) (hNonneg : 0 <= delta)
    (hCap : delta <= 3 / 5) :
    arcCoefficientSquared delta <= 819 / 625 := by
  have hprod : 0 <= ((3 / 5 : ℚ) - delta) *
      ((3 / 5 : ℚ) + delta) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquared : delta ^ 2 <= (9 / 25 : ℚ) := by
    nlinarith
  have hmonoproduct : 0 <= ((9 / 25 : ℚ) - delta ^ 2) *
      (4 - ((9 / 25 : ℚ) + delta ^ 2)) :=
    mul_nonneg (by linarith) (by nlinarith)
  unfold arcCoefficientSquared
  nlinarith

/-- A physical/source-selected W cannot have a marked child whose
unitary norm gap is at most 3/5, IF the external direct SU3 analytic
commutator inequality supplies hDirect. This must be established for
the SAME Hatcher-based loop and connection; no hypothesis is hidden. -/
theorem selectedWFirstChildGapLower
    (rootSq childGap : ℚ)
    (hRoot : selectedWCertifiedRootGapSqLower <= rootSq)
    (hChildNonneg : 0 <= childGap)
    (hChildSmall : childGap <= 3 / 5)
    (hDirect : rootSq <= arcCoefficientSquared childGap) :
    False := by
  have hCap := arcMonotoneToThreeFifths childGap hChildNonneg hChildSmall
  have hGt := sourceRootExceedsThreeFifthsArcCap
  linarith


end DASHIHornSharpSiblingArc
