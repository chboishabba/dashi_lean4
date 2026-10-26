import Mathlib
import Synthesis.JacobsonCouplingNormalization

namespace Synthesis.JacobsonClausiusNullAlgebra

open Synthesis.JacobsonCouplingNormalization

/-- Local heat-flux integrand after factoring out the common affine/horizon
measure: -κ T_ab k^a k^b. -/
def heatFluxIntegrand (κ Tkk : ℝ) : ℝ :=
  -κ * Tkk

/-- Linearised local area-variation integrand from the null Raychaudhuri step:
-R_ab k^a k^b. -/
def areaVariationIntegrand (Rkk : ℝ) : ℝ :=
  -Rkk

/-- Entropy variation obtained from the supplied horizon entropy/area density
η. -/
def entropyVariationIntegrand (η Rkk : ℝ) : ℝ :=
  η * areaVariationIntegrand Rkk

/-- Once the same-object heat-flux, Unruh-temperature, entropy/area and
Raychaudhuri integrands are supplied, Clausius equality cancels the common
boost parameter and yields the null-contracted stress/curvature relation. -/
theorem nullRelation_of_clausius
    (ℏ κ η Tkk Rkk : ℝ)
    (hκ : κ ≠ 0)
    (hC : heatFluxIntegrand κ Tkk =
      unruhTemperature ℏ κ * entropyVariationIntegrand η Rkk) :
    Tkk = (ℏ * η / (2 * Real.pi)) * Rkk := by
  apply (mul_left_cancel₀ hκ)
  calc
    κ * Tkk = -(heatFluxIntegrand κ Tkk) := by
      simp [heatFluxIntegrand]
    _ = -(unruhTemperature ℏ κ * entropyVariationIntegrand η Rkk) := by
      rw [hC]
    _ = κ * ((ℏ * η / (2 * Real.pi)) * Rkk) := by
      unfold unruhTemperature entropyVariationIntegrand areaVariationIntegrand
      field_simp [Real.pi_ne_zero]
      <;> ring

/-- Equivalent null-contracted curvature form, obtained by multiplying through
by the reciprocal Jacobson coupling. -/
theorem curvatureNullRelation_of_clausius
    (ℏ κ η Tkk Rkk : ℝ)
    (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) (hη : η ≠ 0)
    (hC : heatFluxIntegrand κ Tkk =
      unruhTemperature ℏ κ * entropyVariationIntegrand η Rkk) :
    Rkk = jacobsonNullCoupling ℏ η * Tkk := by
  have hrel := nullRelation_of_clausius ℏ κ η Tkk Rkk hκ hC
  have hinv := jacobsonCoupling_inverse ℏ η hℏ hη
  calc
    Rkk = 1 * Rkk := by ring
    _ = (jacobsonNullCoupling ℏ η * (ℏ * η / (2 * Real.pi))) * Rkk := by
      rw [hinv]
    _ = jacobsonNullCoupling ℏ η *
        ((ℏ * η / (2 * Real.pi)) * Rkk) := by ring
    _ = jacobsonNullCoupling ℏ η * Tkk := by rw [← hrel]

/-- Bekenstein-Hawking specialization of the same scalar chain.  This yields
the canonical 8πG coefficient on the null-contracted Einstein relation, while
leaving every geometric/QFT same-object premise explicit. -/
theorem einsteinNullRelation_of_clausius_bekensteinHawking
    (ℏ κ G Tkk Rkk : ℝ)
    (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) (hG : G ≠ 0)
    (hC : heatFluxIntegrand κ Tkk =
      unruhTemperature ℏ κ *
        entropyVariationIntegrand (bekensteinHawkingAreaDensity ℏ G) Rkk) :
    Rkk = 8 * Real.pi * G * Tkk := by
  have hden : (4 * ℏ * G : ℝ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hℏ) hG
  have hη : bekensteinHawkingAreaDensity ℏ G ≠ 0 := by
    unfold bekensteinHawkingAreaDensity
    exact one_div_ne_zero hden
  have hrel := curvatureNullRelation_of_clausius
    ℏ κ (bekensteinHawkingAreaDensity ℏ G) Tkk Rkk hℏ hκ hη hC
  rw [jacobsonCoupling_eq_eightPiG ℏ G hℏ hG] at hrel
  exact hrel

/-- Status boundary: the scalar cancellation and normalization algebra are now
owned; the physical/geometric inputs remain independent receipts. -/
def clausiusNullAlgebraOwned : Bool := true

def geometricHeatFluxReceiptStillRequired : Bool := true

def unruhPhysicalReceiptStillRequired : Bool := true

def entropyAreaPhysicalReceiptStillRequired : Bool := true

def raychaudhuriAreaVariationReceiptStillRequired : Bool := true

def sameObjectStressEnergyStillRequired : Bool := true

end Synthesis.JacobsonClausiusNullAlgebra
