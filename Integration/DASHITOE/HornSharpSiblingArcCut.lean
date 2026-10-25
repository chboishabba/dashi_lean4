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

end DASHIHornSharpSiblingArc
