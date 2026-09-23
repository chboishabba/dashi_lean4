import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Smith-chart complex reflection core

Electrical-engineering j denotes the imaginary unit; it is not the modular
j-invariant.

For normalized impedance z, define the voltage reflection coordinate

  Gamma(z) = (z - 1) / (z + 1).

This module proves on ordinary Lean complex numbers that:
* complex conjugation commutes with Gamma;
* normalized admittance z^-1 maps to -Gamma(z), away from z = 0.

The latter is the exact half-turn underlying the finite C6 observer
cross-pollination on the Agda side.
-/

namespace Integration.SmithChartComplexReflection

open Complex

noncomputable section

/-- Engineering imaginary unit, named separately from modular j. -/
def engineeringJ : ℂ := Complex.I

theorem engineeringJ_sq :
    engineeringJ ^ 2 = -1 := by
  simp [engineeringJ, pow_two]

/-- Normalized Smith reflection coordinate. -/
def gamma (z : ℂ) : ℂ :=
  (z - 1) / (z + 1)

/-- Conjugation commutes with the Smith fractional-linear transform. -/
theorem gamma_conj (z : ℂ) :
    gamma (conj z) = conj (gamma z) := by
  simp [gamma, map_sub, map_add, map_div]

/-- Normalized admittance is reciprocal normalized impedance. -/
def admittance (z : ℂ) : ℂ := z⁻¹

/-- Impedance/admittance duality is a half-turn in the reflection plane. -/
theorem gamma_admittance
    (z : ℂ)
    (hz : z ≠ 0) :
    gamma (admittance z) = - gamma z := by
  unfold gamma admittance
  by_cases h : z = -1
  · subst z
    norm_num
  · have hzp : z + 1 ≠ 0 := by
      intro hz1
      apply h
      linarith
    field_simp [hz, hzp]
    ring

structure SmithLeanBoundary where
  engineeringJImaginaryUnitOwned : Bool
  gammaFractionalLinearOwned : Bool
  conjugationCompatibilityOwned : Bool
  admittanceHalfTurnOwned : Bool

  engineeringJIsModularJInvariant : Bool

def smithLeanBoundary : SmithLeanBoundary where
  engineeringJImaginaryUnitOwned := true
  gammaFractionalLinearOwned := true
  conjugationCompatibilityOwned := true
  admittanceHalfTurnOwned := true
  engineeringJIsModularJInvariant := false

end

end Integration.SmithChartComplexReflection
