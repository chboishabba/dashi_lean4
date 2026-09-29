import Integration.AntigravityFiniteThicknessLapseReconstruction

namespace Integration.AntigravityFiniteThicknessScalarWallNoGo

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravityFiniteThicknessTOVTransition
open Integration.AntigravityFiniteThicknessLapseReconstruction

/-!
Canonical static radial scalar compatibility guardrail.

For a minimally coupled canonical scalar phi(r) in a static spherically
symmetric metric, the radial-gradient contribution enters rho and p_r with the
same sign, while the tangential pressure has

  p_t = - rho.

This file does not assume a scalar equation of motion.  It only records that
necessary algebraic stress identity and tests the two exact finite-thickness
TOV profiles already constructed in this repository.

Result: neither designed profile is a canonical radial scalar wall.  Therefore
a source-native scalar construction must solve a different constrained TOV /
Einstein-scalar profile; it cannot merely reinterpret the existing anisotropy.
-/

def CanonicalStaticRadialScalarStressCompatible
    (state : RationalRadialState) : Prop :=
  state.tangentialPressure = -state.rho

theorem lambda_layer_outer_tangential_pressure :
    (lambdaLayerState transitionOuterRadius).tangentialPressure = 3/4 := by
  norm_num [lambdaLayerState, withDesignedLambdaTangentialPressure,
    designedLambdaTangentialPressure, layerBaseState, layerRadialPressure,
    layerEnergyDensity, transitionOuterRadius, finiteLayerLambda,
    transitionOuterLambda, transitionOuterScaledLambda, scaledLambdaMidpoint,
    lambdaTOVGravityFactor, lambdaTOVGravityNumerator,
    lambdaSchwarzschildDenominator, layerMass, transitionOuterMass]

theorem lambda_layer_outer_not_canonical_scalar :
    ¬ CanonicalStaticRadialScalarStressCompatible
      (lambdaLayerState transitionOuterRadius) := by
  intro h
  unfold CanonicalStaticRadialScalarStressCompatible at h
  rw [lambda_layer_outer_tangential_pressure] at h
  norm_num [lambdaLayerState, withDesignedLambdaTangentialPressure,
    layerBaseState, layerEnergyDensity] at h

theorem affine_lambda_tov_profile_not_canonical_scalar_wall :
    ¬ (∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      CanonicalStaticRadialScalarStressCompatible
        (lambdaLayerState radius)) := by
  intro h
  exact lambda_layer_outer_not_canonical_scalar
    (h transitionOuterRadius
      (by norm_num [transitionInnerRadius, transitionOuterRadius])
      (le_refl _))

theorem lapse_profile_outer_pressure_derivative :
    lapseProfileRadialPressureDerivative transitionOuterRadius
      = 157/475 := by
  norm_num [lapseProfileRadialPressureDerivative, lapseSlopeA, lapseSlopeB,
    lapseGeometryQ, transitionOuterRadius]

theorem explicit_lapse_outer_tangential_pressure :
    (lapseProfileState transitionOuterRadius).tangentialPressure
      = -33/380 := by
  norm_num [lapseProfileState, withDesignedLambdaTangentialPressure,
    designedLambdaTangentialPressure, lapseProfileBaseState,
    lapseProfileRadialPressure, lapseProfileLogSlope,
    lapseProfileRadialPressureDerivative, lapseSlopeA, lapseSlopeB,
    lapseGeometryQ, lapsePressureOffset, layerEnergyDensity,
    transitionOuterRadius, finiteLayerLambda, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint,
    lambdaTOVGravityFactor, lambdaTOVGravityNumerator,
    lambdaSchwarzschildDenominator, layerMass]

theorem explicit_lapse_outer_not_canonical_scalar :
    ¬ CanonicalStaticRadialScalarStressCompatible
      (lapseProfileState transitionOuterRadius) := by
  intro h
  unfold CanonicalStaticRadialScalarStressCompatible at h
  rw [explicit_lapse_outer_tangential_pressure] at h
  norm_num [lapseProfileState, withDesignedLambdaTangentialPressure,
    lapseProfileBaseState, layerEnergyDensity] at h

theorem explicit_lapse_profile_not_canonical_scalar_wall :
    ¬ (∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      CanonicalStaticRadialScalarStressCompatible
        (lapseProfileState radius)) := by
  intro h
  exact explicit_lapse_outer_not_canonical_scalar
    (h transitionOuterRadius
      (by norm_num [transitionInnerRadius, transitionOuterRadius])
      (le_refl _))

def finiteThicknessAffineProfileCanonicalScalarCompatible : Bool := false
def finiteThicknessExplicitLapseProfileCanonicalScalarCompatible : Bool := false
def sourceNativeScalarRequiresNewConstrainedProfile : Bool := true

end Integration.AntigravityFiniteThicknessScalarWallNoGo
