import Mathlib
import Synthesis.JacobsonCouplingNormalization

namespace Synthesis.JacobsonUnruhNormalization

open Synthesis.JacobsonCouplingNormalization

/-- Dimensionless KMS period of the boost modular flow in the
Bisognano-Wichmann normalization.  The physical AQFT theorem identifying the
selected wedge modular flow with boosts is a separate premise. -/
def wedgeBoostKMSPeriod : ℝ := 2 * Real.pi

/-- Proper-time energy scale associated with surface gravity / acceleration κ,
in units with c = k_B = 1 while retaining ℏ. -/
def properTimeEnergyScale (ℏ κ : ℝ) : ℝ := ℏ * κ

/-- Once the BW boost parameter is identified with the physical accelerated
observer's proper time, the inverse temperature is the boost KMS period divided
by the proper-time energy scale. -/
def properTimeInverseTemperature (ℏ κ : ℝ) : ℝ :=
  wedgeBoostKMSPeriod / properTimeEnergyScale ℏ κ

/-- Pure normalization algebra: the reciprocal proper-time inverse temperature
is exactly the Unruh temperature already used by the Jacobson scalar chain.
This theorem does not prove the Bisognano-Wichmann property, select a wedge
state, or establish the physical acceleration/proper-time identification. -/
theorem inverseProperTimeBeta_eq_unruhTemperature
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) :
    (properTimeInverseTemperature ℏ κ)⁻¹ = unruhTemperature ℏ κ := by
  unfold properTimeInverseTemperature properTimeEnergyScale wedgeBoostKMSPeriod
  unfold unruhTemperature
  have hscale : ℏ * κ ≠ 0 := mul_ne_zero hℏ hκ
  field_simp [hscale, Real.pi_ne_zero]
  <;> ring

/-- Equivalent temperature-times-inverse-temperature normalization. -/
theorem unruhTemperature_mul_properTimeBeta
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) :
    unruhTemperature ℏ κ * properTimeInverseTemperature ℏ κ = 1 := by
  unfold properTimeInverseTemperature properTimeEnergyScale wedgeBoostKMSPeriod
  unfold unruhTemperature
  field_simp [hℏ, hκ, Real.pi_ne_zero]
  <;> ring

/-- Status boundary: the 2π -> proper-time temperature conversion is paid;
the physical wedge modular theorem and acceleration/proper-time identification
remain independent QFT/geometric receipts. -/
def boostKMSNormalizationOwned : Bool := true

def physicalBisognanoWichmannStillRequired : Bool := true

def physicalWedgeVacuumStateStillRequired : Bool := true

def accelerationProperTimeIdentificationStillRequired : Bool := true

def modularKMSAnalyticStripStillRequired : Bool := true

end Synthesis.JacobsonUnruhNormalization
