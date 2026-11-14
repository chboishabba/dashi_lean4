import Mathlib
import Synthesis.JacobsonClausiusNullAlgebra
import Synthesis.JacobsonRaychaudhuriEquilibrium

namespace Synthesis.JacobsonHorizonFluxAreaReduction

open Synthesis.JacobsonClausiusNullAlgebra
open Synthesis.JacobsonRaychaudhuriEquilibrium

/-- Scalar coefficient of the approximate boost Killing field along the local
horizon generator, using Jacobson's near-horizon convention

  χ^a = -κ λ k^a.

This is only the coefficient algebra. Identifying an actual vector field and
physical affine parameter with this form is a separate continuum/QFT receipt. -/
def boostKillingCoefficient (κ λ : ℝ) : ℝ := -κ * λ

/-- After supplying the same-object stress contraction `Tkk = T_ab k^a k^b`,
the local horizon heat-flux density is the boost-Killing coefficient times
`Tkk`. The horizon area/affine measure has not yet been integrated. -/
def horizonHeatFluxDensity (κ λ Tkk : ℝ) : ℝ :=
  boostKillingCoefficient κ λ * Tkk

/-- Exact reduction of the local heat-flux density to the affine factor `λ`
and the factored Clausius integrand already owned by
`JacobsonClausiusNullAlgebra`:

  (-κ λ) Tkk = λ (-κ Tkk).
-/
theorem horizonHeatFluxDensity_eq_factored (κ λ Tkk : ℝ) :
    horizonHeatFluxDensity κ λ Tkk = λ * heatFluxIntegrand κ Tkk := by
  unfold horizonHeatFluxDensity boostKillingCoefficient heatFluxIntegrand
  ring

/-- First-order expansion itself after the local-equilibrium Raychaudhuri
specialisation, before multiplying by a horizon area element:

  θ(λ) = -λ Rkk

at the retained linear order. -/
def linearizedExpansion (λ Rkk : ℝ) : ℝ :=
  λ * linearizedExpansionCoefficient Rkk

/-- First-order area-density coefficient `θ dA`, with the actual area measure
left external. -/
def linearizedAreaDensity (λ Rkk : ℝ) : ℝ :=
  linearizedExpansion λ Rkk

/-- Exact weld to the area integrand consumed by the Clausius module:

  -λ Rkk = λ (-Rkk).
-/
theorem linearizedAreaDensity_eq_factored (λ Rkk : ℝ) :
    linearizedAreaDensity λ Rkk = λ * areaVariationIntegrand Rkk := by
  have hcoeff :
      linearizedExpansionCoefficient Rkk = areaVariationIntegrand Rkk := by
    simpa [factoredLinearizedAreaVariation] using
      factoredLinearizedAreaVariation_eq_clausius Rkk
  unfold linearizedAreaDensity linearizedExpansion
  rw [hcoeff]

/-- The common affine factor on the heat and area sides is now explicit. If a
same-object physical construction supplies equality of the two weighted
expressions, no extra horizon-specific scalar algebra remains before the
Clausius null-relation compiler. -/
theorem commonAffineFactorShape
    (κ λ η Tkk Rkk : ℝ) :
    horizonHeatFluxDensity κ λ Tkk
      = λ * heatFluxIntegrand κ Tkk ∧
    η * linearizedAreaDensity λ Rkk
      = λ * (η * areaVariationIntegrand Rkk) := by
  constructor
  · exact horizonHeatFluxDensity_eq_factored κ λ Tkk
  · rw [linearizedAreaDensity_eq_factored]
    ring

/-- Source/theorem status: the near-horizon scalar reduction itself is now
owned. What remains is the physical identification of the approximate boost
Killing field, affine generator, horizon measure, stress tensor, and the
control of the neglected higher-order terms on a selected continuum horizon. -/
def horizonFluxReductionOwned : Bool := true

def linearizedAreaReductionOwned : Bool := true

def physicalBoostKillingIdentificationStillRequired : Bool := true

def physicalAffineGeneratorIdentificationStillRequired : Bool := true

def physicalHorizonMeasureStillRequired : Bool := true

def sameObjectStressTensorStillRequired : Bool := true

def continuumHigherOrderControlStillRequired : Bool := true

end Synthesis.JacobsonHorizonFluxAreaReduction
