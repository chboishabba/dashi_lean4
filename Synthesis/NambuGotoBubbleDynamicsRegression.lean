import Synthesis.NambuGotoBubbleDynamics

namespace Synthesis.NambuGotoBubbleDynamicsRegression

example : radialVelocitySq 2 = 0 := radialVelocitySq_two
example {R : ℝ} (hR : R ≠ 0) :
    radialVelocitySq R =
      (R - 2)^2 * (43 * R^4 + 172 * R^3 + 192 * R^2 + 256 * R + 256) /
        (324 * R^4) := radialVelocitySq_factor hR
example {R : ℝ} (hR : 0 < R) : 0 ≤ radialVelocitySq R := radialVelocitySq_nonneg hR
example {R : ℝ} (hR : 0 < R) (hne : R ≠ 2) : 0 < radialVelocitySq R :=
  radialVelocitySq_pos hR hne

end Synthesis.NambuGotoBubbleDynamicsRegression
