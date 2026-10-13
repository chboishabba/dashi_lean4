import Mathlib

namespace Synthesis.NambuGotoBubbleDynamics

/-- Interior de-Sitter lapse for Λ_in = 21/64. -/
def fIn (R : ℝ) : ℝ := 1 - (7 / 64 : ℝ) * R^2

/-- Exterior Kottler lapse for M=2/9 and Λ_out=19/48. -/
def fOut (R : ℝ) : ℝ := 1 - 4 / (9 * R) - (19 / 144 : ℝ) * R^2

/-- For the constant Nambu-Goto fixture tension 8πσ=1/4,
4πσR = R/8 in the spherical Israel jump equation. -/
def shellJump (R : ℝ) : ℝ := R / 8

/-- Algebraic solution for Rdot^2 obtained from
sqrt(Rdot^2+fIn)-sqrt(Rdot^2+fOut)=shellJump.
The Israel equation itself is the physical authority input; this definition is
its exact selected-fixture algebraic reduction. -/
def radialVelocitySq (R : ℝ) : ℝ :=
  ((fIn R - fOut R - shellJump R ^ 2)^2) / (4 * shellJump R ^ 2) - fOut R

/-- Exact factorization of the selected dynamical shell constraint. -/
theorem radialVelocitySq_factor {R : ℝ} (hR : R ≠ 0) :
    radialVelocitySq R =
      (R - 2)^2 * (43 * R^4 + 172 * R^3 + 192 * R^2 + 256 * R + 256) /
        (324 * R^4) := by
  unfold radialVelocitySq fIn fOut shellJump
  field_simp [hR]
  <;> ring

@[simp] theorem radialVelocitySq_two : radialVelocitySq 2 = 0 := by
  norm_num [radialVelocitySq, fIn, fOut, shellJump]

private theorem positivePolynomial_pos {R : ℝ} (hR : 0 < R) :
    0 < 43 * R^4 + 172 * R^3 + 192 * R^2 + 256 * R + 256 := by
  have h2 : 0 ≤ R^2 := sq_nonneg R
  have h3 : 0 < R^3 := by positivity
  have h4 : 0 < R^4 := by positivity
  positivity

/-- The selected shell's allowed squared velocity is nonnegative at every positive radius. -/
theorem radialVelocitySq_nonneg {R : ℝ} (hR : 0 < R) : 0 ≤ radialVelocitySq R := by
  rw [radialVelocitySq_factor (ne_of_gt hR)]
  positivity

/-- Away from the R=2 turning point, the selected squared velocity is strictly positive. -/
theorem radialVelocitySq_pos {R : ℝ} (hR : 0 < R) (hne : R ≠ 2) :
    0 < radialVelocitySq R := by
  rw [radialVelocitySq_factor (ne_of_gt hR)]
  have hpoly := positivePolynomial_pos hR
  have hsquare : 0 < (R - 2)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hden : 0 < 324 * R^4 := by positivity
  positivity

/-- The exact static fixture is a double algebraic turning point of the velocity-square law. -/
theorem turningPoint_factor :
    ∀ {R : ℝ}, R ≠ 0 →
      radialVelocitySq R =
        (R - 2)^2 * (43 * R^4 + 172 * R^3 + 192 * R^2 + 256 * R + 256) /
          (324 * R^4) :=
  @radialVelocitySq_factor

def selectedBubbleJunctionAlgebraSolved : Bool := true

def movingShellAuthorityStillRequired : Bool := true

def sourceNativeCMP119SelectsShellTrajectoryStillRequired : Bool := true

end Synthesis.NambuGotoBubbleDynamics
