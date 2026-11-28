import Synthesis.YMCMP99Path13QuaternionTangentExact
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace CMP99Pivot.Path13
open scoped Quaternion
noncomputable section

/-- Actual bond curve in the noncommutative quaternion algebra. Its
one-parameter derivative uses the original exponential, not a formal
operator called dexp. -/
def qBondCurve (q H : Q) (t : ℝ) : Q :=
  q*NormedSpace.exp (t • H)

theorem qBondCurve_derivative (q H : Q) (t : ℝ) :
    HasDerivAt (qBondCurve q H) (qBondCurve q H t*H) t := by
  have h := hasDerivAt_exp_smul_const H t
  have hq := (qLeft q).hasFDerivAt.comp_hasDerivAt h
  simpa [qBondCurve,qLeft,qLeftLinear,mul_assoc] using hq

theorem qBondCurve_zero (q H : Q) : qBondCurve q H 0=q := by
  simp [qBondCurve]

theorem qBondCurve_derivative_zero (q H : Q) :
    HasDerivAt (qBondCurve q H) (qLeft q H) 0 := by
  simpa [qBondCurve_zero,qLeft,qLeftLinear] using qBondCurve_derivative q H 0

/-- Inverted word bond: exp(-tH) * q*, with actual negative sign and
right multiplication order. This is the inverse of the unit bond
curve when H is pure; no general log derivative asserted. -/
def qNegativeBondCurve (q H : Q) (t : ℝ) : Q :=
  NormedSpace.exp (t • (-H))*star q

theorem qNegativeBondCurve_derivative_zero (q H : Q) :
    HasDerivAt (qNegativeBondCurve q H) (-(H*star q)) 0 := by
  have h := hasDerivAt_exp_smul_const (-H) (0:ℝ)
  have hq := (qRight (star q)).hasFDerivAt.comp_hasDerivAt h
  simpa [qNegativeBondCurve,qRight,qRightLinear] using hq

/-- The actual two signed velocities have the same norm on unit bonds. -/
theorem qSignedBond_velocities_norm (q H : Q) (hq : ‖q‖=1) :
    ‖qLeft q H‖=‖H‖ ∧ ‖-(H*star q)‖=‖H‖ := by
  exact ⟨qLeft_isometry_norm q H hq,by rw [norm_neg,norm_mul,norm_star,hq,mul_one]⟩

end
end CMP99Pivot.Path13
