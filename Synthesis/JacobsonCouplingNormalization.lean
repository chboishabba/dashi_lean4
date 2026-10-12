import Mathlib

namespace Synthesis.JacobsonCouplingNormalization

/-- Unruh temperature normalization in units retaining ℏ. -/
def unruhTemperature (ℏ κ : ℝ) : ℝ :=
  ℏ * κ / (2 * Real.pi)

/-- Entropy-per-area coefficient used in the Bekenstein-Hawking normalization
S = A/(4 ℏ G), with k_B=c=1. -/
def bekensteinHawkingAreaDensity (ℏ G : ℝ) : ℝ :=
  1 / (4 * ℏ * G)

/-- The null-contracted curvature/stress coupling obtained after cancelling the
common horizon boost parameter in Jacobson's Clausius comparison. -/
def jacobsonNullCoupling (ℏ η : ℝ) : ℝ :=
  2 * Real.pi / (ℏ * η)

/-- The Jacobson coefficient is the reciprocal of the Clausius-side coefficient
ℏη/(2π), provided the physical normalizations are nonzero. -/
theorem jacobsonCoupling_inverse
    (ℏ η : ℝ) (hℏ : ℏ ≠ 0) (hη : η ≠ 0) :
    jacobsonNullCoupling ℏ η * (ℏ * η / (2 * Real.pi)) = 1 := by
  unfold jacobsonNullCoupling
  field_simp [hℏ, hη, Real.pi_ne_zero]
  <;> ring

/-- Substituting the Bekenstein-Hawking area density collapses the Jacobson
null-contracted coupling exactly to 8πG.  This is normalization algebra only:
it does not prove Unruh, the area law, Raychaudhuri, or the stress-energy weld. -/
theorem jacobsonCoupling_eq_eightPiG
    (ℏ G : ℝ) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) :
    jacobsonNullCoupling ℏ (bekensteinHawkingAreaDensity ℏ G)
      = 8 * Real.pi * G := by
  unfold jacobsonNullCoupling bekensteinHawkingAreaDensity
  field_simp [hℏ, hG]
  <;> ring

/-- Source-level status boundary. -/
def jacobsonCouplingAlgebraOwned : Bool := true

def unruhNormalizationPhysicalReceiptStillRequired : Bool := true

def entropyAreaPhysicalReceiptStillRequired : Bool := true

def raychaudhuriSameCarrierStillRequired : Bool := true

def stressEnergySameObjectStillRequired : Bool := true

end Synthesis.JacobsonCouplingNormalization
