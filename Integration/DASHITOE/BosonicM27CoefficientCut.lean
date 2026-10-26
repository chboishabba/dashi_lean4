import Mathlib

/-!
# Bosonic M 27 → bosonic string 26: selected kinetic coefficient

Mathematical algebra ONLY: the 27D Einstein–Hilbert + one-circle-polarised
4-form reduction is an externally specified physics ansatz. The formulas below
record the result of its conformal Ricci transformation and integration by
parts; their polynomial consequences are theorem-checked by Lean if compiled.

Primary physics roots: Horowitz–Susskind (2000), Lambert–West (2001),
Glennon–West (2024/25), Glennon (2025). See the Agda PR #1249 source ledger.

No 27D Lorentzian manifold, quantum Weyl/BRST, K27-action, Albert product,
Monster representation or physical string theory is constructed here.
-/

namespace DASHIString27

def gravitationalPrefactor (d a b : ℚ) : ℚ := (d - 2) * a + b

def electricThreeFormPrefactor (d a b : ℚ) : ℚ := (d - 6) * a - b

/-- The scalar curvature/volume coefficient before integration by parts:
  -2(b+(d-1)a) Δσ and an explicit |dσ|² term. -/
def curvatureBoxCoefficient (d a b : ℚ) : ℚ :=
  -2 * (b + (d - 1) * a)

def curvatureGradientCoefficient (d a b : ℚ) : ℚ :=
  -2 * b ^ 2 - 2 * (d - 2) * a * b - (d - 1) * (d - 2) * a ^ 2

def reducedEinsteinKinetic (d a b : ℚ) : ℚ :=
  curvatureGradientCoefficient d a b -
    curvatureBoxCoefficient d a b * gravitationalPrefactor d a b

/-- Pure ring identity for the selected (D=d+1)-dimensional metric ansatz. -/
theorem reducedEinsteinKinetic_closed (d a b : ℚ) :
    reducedEinsteinKinetic d a b =
      (d - 1) * a * ((d - 2) * a + 2 * b) := by
  dsimp [reducedEinsteinKinetic, curvatureBoxCoefficient,
    curvatureGradientCoefficient, gravitationalPrefactor]
  ring

/-- Requiring a common string-frame prefactor for R and H^2 forces b=-2a. -/
theorem commonPrefactor_forces_radius (d a b : ℚ)
    (h : gravitationalPrefactor d a b =
      electricThreeFormPrefactor d a b) : b = -2 * a := by
  dsimp [gravitationalPrefactor, electricThreeFormPrefactor] at h
  linarith

/-- Conversely the selected b=-2a makes the two exponents identical. -/
theorem selected_commonPrefactor (d a : ℚ) :
    gravitationalPrefactor d a (-2 * a) =
      electricThreeFormPrefactor d a (-2 * a) := by
  dsimp [gravitationalPrefactor, electricThreeFormPrefactor]
  ring

/-- Normalised actual sigma kinetic vs expected 4(∂Phi)^2 coefficient. -/
def actualStringFrameKinetic (d a : ℚ) : ℚ :=
  reducedEinsteinKinetic d a (-2 * a)

def requiredStringFrameKinetic (d a : ℚ) : ℚ :=
  (d - 4) ^ 2 * a ^ 2

/-- Exact dimension-dependent scalar mismatch; vanishes at d=10. -/
theorem stringKineticGap (d a : ℚ) :
    actualStringFrameKinetic d a - requiredStringFrameKinetic d a =
      (d - 10) * a ^ 2 := by
  dsimp [actualStringFrameKinetic, requiredStringFrameKinetic,
    reducedEinsteinKinetic, curvatureBoxCoefficient,
    curvatureGradientCoefficient, gravitationalPrefactor]
  ring

theorem tenDimensionalCoefficientMatches :
    actualStringFrameKinetic 10 1 = requiredStringFrameKinetic 10 1 := by
  norm_num [actualStringFrameKinetic, requiredStringFrameKinetic,
    reducedEinsteinKinetic, curvatureBoxCoefficient,
    curvatureGradientCoefficient, gravitationalPrefactor]

/-- The original Lambert–West 125/121 obstruction is reproduced as arithmetic. -/
theorem twentySixDimensionalLambertWestRatio :
    actualStringFrameKinetic 26 1 =
      (125 / 121 : ℚ) * requiredStringFrameKinetic 26 1 := by
  norm_num [actualStringFrameKinetic, requiredStringFrameKinetic,
    reducedEinsteinKinetic, curvatureBoxCoefficient,
    curvatureGradientCoefficient, gravitationalPrefactor]

theorem twentySixDimensionalCoefficientNoGo :
    actualStringFrameKinetic 26 1 ≠ requiredStringFrameKinetic 26 1 := by
  norm_num [actualStringFrameKinetic, requiredStringFrameKinetic,
    reducedEinsteinKinetic, curvatureBoxCoefficient,
    curvatureGradientCoefficient, gravitationalPrefactor]

/-- Standard antisymmetric 4-form factorial contraction when one index lies
along an isometric circle, after matching canonical constant-radius B field. -/
theorem fourFormToThreeFormCoefficient :
    (4 : ℚ) / (2 * 24) = 1 / 12 := by
  norm_num

/-- Minimal scalar-repair coefficient determined by source-matched scalar normalization.
    This is a FORMAL off-shell coefficient, not a new 27D action or a
    consistent truncation of a freely propagating scalar. -/
def supplementalScalarSlopeSquared (d a : ℚ) : ℚ :=
  2 * (actualStringFrameKinetic d a - requiredStringFrameKinetic d a)

theorem scalarRepairFormalCoefficient (d a : ℚ) :
    actualStringFrameKinetic d a -
      supplementalScalarSlopeSquared d a / 2 =
      requiredStringFrameKinetic d a := by
  dsimp [supplementalScalarSlopeSquared]
  ring

theorem scalarSlopeSquaredAtTwentySix :
    supplementalScalarSlopeSquared 26 1 = 32 := by
  norm_num [supplementalScalarSlopeSquared, actualStringFrameKinetic,
    requiredStringFrameKinetic, reducedEinsteinKinetic,
    curvatureBoxCoefficient, curvatureGradientCoefficient,
    gravitationalPrefactor]

theorem scalarSlopeSquaredAtTen :
    supplementalScalarSlopeSquared 10 1 = 0 := by
  norm_num [supplementalScalarSlopeSquared, actualStringFrameKinetic,
    requiredStringFrameKinetic, reducedEinsteinKinetic,
    curvatureBoxCoefficient, curvatureGradientCoefficient,
    gravitationalPrefactor]

/-- For sigma=t on a flat 26D Minkowski base, the lifted free scalar wave
    operator acting on chi=k*sigma is -22*a*k*exp(-2*a*sigma).
    The never-vanishing exponential is external geometric input.
    This lemma proves that its algebraic coefficient cannot vanish for
    a nonzero warp slope and a nonzero scalar. -/
theorem freeScalarOffShellResidualNonzero (a k : ℚ)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    -(22 : ℚ) * a * k ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hk

end DASHIString27
