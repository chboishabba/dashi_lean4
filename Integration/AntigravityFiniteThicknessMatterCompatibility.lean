import Mathlib
import Integration.AntigravityFiniteThicknessLapseReconstruction

namespace Integration.AntigravityFiniteThicknessMatterCompatibility

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravityFiniteThicknessTOVTransition
open Integration.AntigravityFiniteThicknessLapseReconstruction

/-!
Matter-model audit for the explicit finite-thickness TOV layer.

For a static, radial, canonically normalized minimally-coupled scalar,
write the nonnegative radial kinetic contribution as K and the potential as V.
In the orthonormal static frame the matter stress has

  rho = K + V
  p_r = K - V
  p_t = -K - V = -rho.

The explicit designed Lambda-TOV layer does not satisfy p_t = -rho.  Hence that
specific exact layer cannot be promoted to a canonical single-scalar domain
wall merely by choosing a potential.  A source-native realization must instead
use a genuinely anisotropic effective YM stress, a noncanonical scalar sector,
additional fields, or a redesigned profile.
-/

structure CanonicalStaticRadialScalarStress where
  kinetic : Rat
  potential : Rat

def CanonicalStaticRadialScalarStress.rho
    (s : CanonicalStaticRadialScalarStress) : Rat :=
  s.kinetic + s.potential

def CanonicalStaticRadialScalarStress.radialPressure
    (s : CanonicalStaticRadialScalarStress) : Rat :=
  s.kinetic - s.potential

def CanonicalStaticRadialScalarStress.tangentialPressure
    (s : CanonicalStaticRadialScalarStress) : Rat :=
  -s.kinetic - s.potential

theorem canonical_scalar_tangential_pressure_eq_neg_rho
    (s : CanonicalStaticRadialScalarStress) :
    s.tangentialPressure = -s.rho := by
  unfold CanonicalStaticRadialScalarStress.tangentialPressure
    CanonicalStaticRadialScalarStress.rho
  ring

theorem canonical_scalar_kinetic_from_rho_pr
    (s : CanonicalStaticRadialScalarStress) :
    2 * s.kinetic = s.rho + s.radialPressure := by
  unfold CanonicalStaticRadialScalarStress.rho
    CanonicalStaticRadialScalarStress.radialPressure
  ring

theorem canonical_scalar_potential_from_rho_pr
    (s : CanonicalStaticRadialScalarStress) :
    2 * s.potential = s.rho - s.radialPressure := by
  unfold CanonicalStaticRadialScalarStress.rho
    CanonicalStaticRadialScalarStress.radialPressure
  ring

theorem lapse_profile_outer_tangential_pressure :
    (lapseProfileState transitionOuterRadius).tangentialPressure
      = -33/380 := by
  norm_num [lapseProfileState, withDesignedLambdaTangentialPressure,
    designedLambdaTangentialPressure,
    lapseProfileBaseState, lapseProfileRadialPressureDerivative,
    lapseProfileRadialPressure, lapseProfileLogSlope,
    lapseSlopeA, lapseSlopeB, lapseGeometryQ, lapsePressureOffset,
    lambdaTOVGravityFactor, lambdaTOVGravityNumerator,
    lambdaSchwarzschildDenominator,
    layerMass, layerDensityBar, layerEnergyDensity,
    finiteLayerLambda, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint,
    transitionOuterRadius]

theorem lapse_profile_outer_energy_density :
    (lapseProfileState transitionOuterRadius).rho = 1 := by
  rfl

theorem lapse_profile_outer_not_canonical_scalar_identity :
    (lapseProfileState transitionOuterRadius).tangentialPressure
      ≠ -(lapseProfileState transitionOuterRadius).rho := by
  rw [lapse_profile_outer_tangential_pressure,
    lapse_profile_outer_energy_density]
  norm_num

theorem no_canonical_static_radial_scalar_realizes_outer_layer_stress :
    ¬ ∃ s : CanonicalStaticRadialScalarStress,
      s.rho = (lapseProfileState transitionOuterRadius).rho
      ∧ s.radialPressure =
          (lapseProfileState transitionOuterRadius).radialPressure
      ∧ s.tangentialPressure =
          (lapseProfileState transitionOuterRadius).tangentialPressure := by
  intro h
  rcases h with ⟨s, hrho, hpr, hpt⟩
  have hscalar := canonical_scalar_tangential_pressure_eq_neg_rho s
  have hlayer :
      (lapseProfileState transitionOuterRadius).tangentialPressure
        = -(lapseProfileState transitionOuterRadius).rho := by
    calc
      (lapseProfileState transitionOuterRadius).tangentialPressure
          = s.tangentialPressure := hpt.symm
      _ = -s.rho := hscalar
      _ = -(lapseProfileState transitionOuterRadius).rho := by rw [hrho]
  exact lapse_profile_outer_not_canonical_scalar_identity hlayer

def explicitLayerCanonicalSingleScalarCompatible : Bool := false
def explicitLayerRequiresGenuinelyAnisotropicMatter : Bool := true
def sourceNativeYMTensorProfileStillRequired : Bool := true


/-!
Trace-sign versus active-stress firewall.

The renormalized four-dimensional trace and the static focusing/active-stress
combination are different contractions:

  trace(T)  = -rho + p_r + 2 p_t,
  active(T) =  rho + p_r + 2 p_t.

For the explicit outer finite-layer state, the trace is negative while the
active stress is positive.  Therefore a negative trace-anomaly theorem does not
by itself pay the negative-active-source premise used by the local defocusing
route.
-/

def radialStressTrace (s : RationalRadialState) : Rat :=
  -s.rho + s.radialPressure + 2 * s.tangentialPressure

theorem lapse_profile_outer_active_stress :
    radialActiveStress (lapseProfileState transitionOuterRadius)
      = 157/190 := by
  rw [show radialActiveStress (lapseProfileState transitionOuterRadius)
      =
      (lapseProfileState transitionOuterRadius).rho
        + (lapseProfileState transitionOuterRadius).radialPressure
        + 2 * (lapseProfileState transitionOuterRadius).tangentialPressure by
      rfl]
  rw [lapse_profile_outer_energy_density,
    lapse_profile_outer_pressure,
    lapse_profile_outer_tangential_pressure]
  norm_num

theorem lapse_profile_outer_active_stress_positive :
    0 < radialActiveStress (lapseProfileState transitionOuterRadius) := by
  rw [lapse_profile_outer_active_stress]
  norm_num

theorem lapse_profile_outer_trace :
    radialStressTrace (lapseProfileState transitionOuterRadius)
      = -223/190 := by
  unfold radialStressTrace
  rw [lapse_profile_outer_energy_density,
    lapse_profile_outer_pressure,
    lapse_profile_outer_tangential_pressure]
  norm_num

theorem lapse_profile_outer_trace_negative :
    radialStressTrace (lapseProfileState transitionOuterRadius) < 0 := by
  rw [lapse_profile_outer_trace]
  norm_num

theorem negative_trace_does_not_pay_negative_active_stress_on_explicit_layer :
    radialStressTrace (lapseProfileState transitionOuterRadius) < 0
      ∧
    ¬ (radialActiveStress (lapseProfileState transitionOuterRadius) < 0) := by
  constructor
  · exact lapse_profile_outer_trace_negative
  · linarith [lapse_profile_outer_active_stress_positive]

def negativeTraceImpliesNegativeActiveStress : Bool := false
def explicitFiniteLayerMatchesUniformNegativeActiveSource : Bool := false
def sourceToGeometryNeedsTensorShapeNotTraceSignAlone : Bool := true

end Integration.AntigravityFiniteThicknessMatterCompatibility
