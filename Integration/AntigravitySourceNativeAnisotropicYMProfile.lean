import Integration.AntigravityCorrectedSourceGeometryWeld
import Integration.AntigravityFiniteThicknessMatterCompatibility

namespace Integration.AntigravitySourceNativeAnisotropicYMProfile

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravityFiniteThicknessTOVTransition
open Integration.AntigravityFiniteThicknessLapseReconstruction
open Integration.AntigravityFiniteThicknessMatterCompatibility
open Integration.AntigravityCorrectedSourceGeometryWeld

/-!
AG-G3 / source-native anisotropic YM profile boundary.

A source-native profile must provide the three local orthonormal stress
coordinates on the finite-thickness interval.  For the corrected antigravity
route it must also reproduce the negative active/focusing contraction, not just
a negative trace.
-/

structure SourceNativeAnisotropicYMProfile where
  rho : Rat → Rat
  radialPressure : Rat → Rat
  radialPressureDerivative : Rat → Rat
  tangentialPressure : Rat → Rat

  activeStressNegative :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      rho radius + radialPressure radius + 2 * tangentialPressure radius < 0

def SourceNativeAnisotropicYMProfile.state
    (profile : SourceNativeAnisotropicYMProfile)
    (radius : Rat) : RationalRadialState where
  radius := radius
  mass := layerMass radius
  densityBar := layerDensityBar
  rho := profile.rho radius
  radialPressure := profile.radialPressure radius
  tangentialPressure := profile.tangentialPressure radius

structure MatchesExplicitFiniteThicknessLayer
    (profile : SourceNativeAnisotropicYMProfile) : Prop where
  rhoMatches :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      profile.rho radius = (lapseProfileState radius).rho

  radialPressureMatches :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      profile.radialPressure radius =
        (lapseProfileState radius).radialPressure

  tangentialPressureMatches :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      profile.tangentialPressure radius =
        (lapseProfileState radius).tangentialPressure

theorem explicit_finite_layer_cannot_match_uniform_negative_active_source
    (profile : SourceNativeAnisotropicYMProfile) :
    ¬ MatchesExplicitFiniteThicknessLayer profile := by
  intro h
  have hlo :
      transitionInnerRadius ≤ transitionOuterRadius := by
    norm_num [transitionInnerRadius, transitionOuterRadius]
  have hhi :
      transitionOuterRadius ≤ transitionOuterRadius := le_rfl
  have hneg :=
    profile.activeStressNegative transitionOuterRadius hlo hhi
  have hrho := h.rhoMatches transitionOuterRadius hlo hhi
  have hpr := h.radialPressureMatches transitionOuterRadius hlo hhi
  have hpt := h.tangentialPressureMatches transitionOuterRadius hlo hhi
  have hlayer :
      (lapseProfileState transitionOuterRadius).rho
        + (lapseProfileState transitionOuterRadius).radialPressure
        + 2 * (lapseProfileState transitionOuterRadius).tangentialPressure < 0 := by
    rw [hrho, hpr, hpt] at hneg
    exact hneg
  have hpos := lapse_profile_outer_active_stress_positive
  unfold radialActiveStress at hpos
  linarith

def currentExplicitFiniteLayerIsSourceNativeNegativeActiveYMProfile : Bool := false
def finiteThicknessGeometryMustBeRedesignedOrSourceRouteChanged : Bool := true
def anisotropicYMStressTensorShapeStillRequired : Bool := true

/-!
Preferred G3 target after the no-go: source stress first, geometry second.
-/

structure SourceNativeYMFiniteThicknessTarget
    (profile : SourceNativeAnisotropicYMProfile) : Prop where
  tovSolved :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      anisotropicLambdaTOVRHS
        (profile.state radius) finiteLayerLambda
        =
      profile.radialPressureDerivative radius

  outerRadialPressureZero :
    profile.radialPressure transitionOuterRadius = 0

  correctedActiveSource :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      profile.rho radius
        + profile.radialPressure radius
        + 2 * profile.tangentialPressure radius < 0

def sourceFirstGeometryConstructionRequired : Bool := true


/-!
Sharp outer-boundary redesign condition.

At a boundary where p_r = 0, negative active stress requires

  rho + 2 p_t < 0,

equivalently p_t < -rho/2.
-/

theorem outer_negative_active_requires_tangential_below_minus_half_rho
    (profile : SourceNativeAnisotropicYMProfile)
    (hOuterRadial :
      profile.radialPressure transitionOuterRadius = 0) :
    profile.tangentialPressure transitionOuterRadius
      < -(profile.rho transitionOuterRadius) / 2 := by
  have hlo :
      transitionInnerRadius ≤ transitionOuterRadius := by
    norm_num [transitionInnerRadius, transitionOuterRadius]
  have hhi :
      transitionOuterRadius ≤ transitionOuterRadius := le_rfl
  have hactive :=
    profile.activeStressNegative transitionOuterRadius hlo hhi
  rw [hOuterRadial] at hactive
  linarith

theorem explicit_layer_outer_tangential_pressure_above_negative_half_density :
    -(1 : Rat) / 2
      < (lapseProfileState transitionOuterRadius).tangentialPressure := by
  rw [lapse_profile_outer_tangential_pressure]
  norm_num

theorem explicit_layer_misses_negative_active_outer_threshold :
    ¬ ((lapseProfileState transitionOuterRadius).tangentialPressure
        < -(lapseProfileState transitionOuterRadius).rho / 2) := by
  rw [lapse_profile_outer_tangential_pressure,
    lapse_profile_outer_energy_density]
  norm_num

def sourceNativeOuterTangentialThresholdKnown : Bool := true
def explicitLayerSatisfiesOuterNegativeActiveThreshold : Bool := false

end Integration.AntigravitySourceNativeAnisotropicYMProfile
