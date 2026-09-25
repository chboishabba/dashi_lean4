import Mathlib
import Integration.AntigravityFiniteThicknessTOVTransition

namespace Integration.AntigravityFiniteThicknessLapseReconstruction

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravityFiniteThicknessTOVTransition

/-!
An explicitly lapse-integrable finite-thickness Lambda-TOV layer.

Keep the already-proved finite-layer mass geometry

  m(r) = (4/225) r^3,
  Lambda = 16/75,

but choose the radial pressure from an affine desired log-lapse slope

  G(r) = (319/190) r - 1747/380.

For the Lambda-TOV gravity factor,

  G_Lambda =
    (m + r^3 p_r - Lambda r^3/3)
    /
    (r (r - 2m - Lambda r^3/3)),

solving algebraically for p_r gives the profile below.  The two coefficients in
G were chosen so that

  p_r(3/2) = -1,
  p_r(5/2) = 0,
  G(5/2)   = -2/5,

where -2/5 is the already-proved Kottler outer log-lapse slope.

Because G is affine, the temporal lapse is explicit:

  L(r) = (1/3) exp[
      (319/190) (r^2 - R^2)
      + 2 (-1747/380) (r-R)
    ],

with R=5/2.  Therefore L'/L = 2 G exactly, L(R)=1/3, and
L'(R)=-4/15, matching the Kottler exterior.

This solves the missing temporal-lapse reconstruction for this designed radial
Einstein-TOV layer.  It does not derive the layer stress profile from CMP119 or
a scalar-field equation.
-/

def lapseSlopeA : Rat := 319/190
def lapseSlopeB : Rat := -1747/380
def lapseGeometryQ : Rat := 8/75
def lapsePressureOffset : Rat := 4/75

def lapseProfileLogSlope (radius : Rat) : Rat :=
  lapseSlopeA * radius + lapseSlopeB

def lapseProfileRadialPressure (radius : Rat) : Rat :=
  lapseProfileLogSlope radius
      * (1 - lapseGeometryQ * radius^2) / radius
    + lapsePressureOffset

def lapseProfileRadialPressureDerivative (radius : Rat) : Rat :=
  -lapseSlopeB / radius^2
    - 2 * lapseSlopeA * lapseGeometryQ * radius
    - lapseSlopeB * lapseGeometryQ

def lapseProfileBaseState (radius : Rat) : RationalRadialState where
  radius := radius
  mass := layerMass radius
  densityBar := layerDensityBar
  rho := layerEnergyDensity
  radialPressure := lapseProfileRadialPressure radius
  tangentialPressure := 0

def lapseProfileState (radius : Rat) : RationalRadialState :=
  withDesignedLambdaTangentialPressure
    (lapseProfileBaseState radius)
    finiteLayerLambda
    (lapseProfileRadialPressureDerivative radius)

theorem lapse_profile_inner_pressure :
    lapseProfileRadialPressure transitionInnerRadius = -1 := by
  norm_num [lapseProfileRadialPressure, lapseProfileLogSlope,
    lapseSlopeA, lapseSlopeB, lapseGeometryQ, lapsePressureOffset,
    transitionInnerRadius]

theorem lapse_profile_outer_pressure :
    lapseProfileRadialPressure transitionOuterRadius = 0 := by
  norm_num [lapseProfileRadialPressure, lapseProfileLogSlope,
    lapseSlopeA, lapseSlopeB, lapseGeometryQ, lapsePressureOffset,
    transitionOuterRadius]

theorem lapse_profile_outer_log_slope :
    lapseProfileLogSlope transitionOuterRadius = -2/5 := by
  norm_num [lapseProfileLogSlope, lapseSlopeA, lapseSlopeB,
    transitionOuterRadius]

theorem lapse_profile_mass_matches_layer (radius : Rat) :
    (lapseProfileBaseState radius).mass = layerMass radius := rfl

theorem lapse_profile_density_matches_layer (radius : Rat) :
    (lapseProfileBaseState radius).densityBar = layerDensityBar := rfl

theorem lapse_profile_gravity_factor
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius)
    (hUpper : radius ≤ transitionOuterRadius) :
    lambdaTOVGravityFactor
      (lapseProfileBaseState radius)
      finiteLayerLambda
      = lapseProfileLogSlope radius := by
  have hr : 0 < radius := layer_radius_positive hLower
  have hden :
      0 <
        radius - 2 * layerMass radius
          - finiteLayerLambda * radius^3 / 3 := by
    simpa [lapseProfileBaseState] using
      (lambda_layer_denominator_positive
        (radius := radius) hLower hUpper)
  have hr0 : radius ≠ 0 := ne_of_gt hr
  have hden0 :
      radius - 2 * layerMass radius
          - finiteLayerLambda * radius^3 / 3 ≠ 0 :=
    ne_of_gt hden
  unfold lambdaTOVGravityFactor lambdaTOVGravityNumerator
    lambdaSchwarzschildDenominator lapseProfileBaseState
    lapseProfileRadialPressure lapseProfileLogSlope
    lapseSlopeA lapseSlopeB lapseGeometryQ lapsePressureOffset
    finiteLayerLambda transitionOuterLambda transitionOuterScaledLambda
    scaledLambdaMidpoint layerMass
  field_simp [hr0, hden0]
  ring

theorem lapse_profile_pressure_derivative_formula
    (radius : Rat) (hr : radius ≠ 0) :
    lapseProfileRadialPressureDerivative radius
      =
    (-lapseSlopeB / radius^2
      - 2 * lapseSlopeA * lapseGeometryQ * radius
      - lapseSlopeB * lapseGeometryQ) := by
  rfl

theorem lapse_profile_lambda_tov_exact
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius) :
    anisotropicLambdaTOVRHS
      (lapseProfileState radius)
      finiteLayerLambda
      = lapseProfileRadialPressureDerivative radius := by
  exact designed_lambda_tangential_pressure_solves_tov
    (lapseProfileBaseState radius)
    finiteLayerLambda
    (lapseProfileRadialPressureDerivative radius)
    (ne_of_gt (layer_radius_positive hLower))

/-! Real temporal-lapse reconstruction. -/

def lapseSlopeAReal : ℝ := (319 : ℝ) / 190
def lapseSlopeBReal : ℝ := -(1747 : ℝ) / 380
def lapseOuterRadiusReal : ℝ := (5 : ℝ) / 2

def lapseProfileLogSlopeReal (radius : ℝ) : ℝ :=
  lapseSlopeAReal * radius + lapseSlopeBReal

def lapseProfileExponent (radius : ℝ) : ℝ :=
  lapseSlopeAReal * (radius^2 - lapseOuterRadiusReal^2)
    + 2 * lapseSlopeBReal * (radius - lapseOuterRadiusReal)

def lapseProfileTemporalLapse (radius : ℝ) : ℝ :=
  (1/3 : ℝ) * Real.exp (lapseProfileExponent radius)

theorem lapse_profile_exponent_hasDerivAt (radius : ℝ) :
    HasDerivAt lapseProfileExponent
      (2 * lapseProfileLogSlopeReal radius) radius := by
  unfold lapseProfileExponent lapseProfileLogSlopeReal
    lapseSlopeAReal lapseSlopeBReal lapseOuterRadiusReal
  convert (by fun_prop :
    HasDerivAt
      (fun x : ℝ =>
        ((319 : ℝ) / 190) * (x^2 - ((5 : ℝ) / 2)^2)
          + 2 * (-(1747 : ℝ) / 380) * (x - (5 : ℝ) / 2))
      (((319 : ℝ) / 190) * (2 * radius)
        + 2 * (-(1747 : ℝ) / 380)) radius) using 1 <;> ring

theorem lapse_profile_temporal_lapse_hasDerivAt (radius : ℝ) :
    HasDerivAt lapseProfileTemporalLapse
      (2 * lapseProfileLogSlopeReal radius
        * lapseProfileTemporalLapse radius) radius := by
  have h :=
    (lapse_profile_exponent_hasDerivAt radius).exp.const_mul (1/3 : ℝ)
  convert h using 1 <;>
    simp [lapseProfileTemporalLapse] <;> ring

theorem lapse_profile_outer_lapse :
    lapseProfileTemporalLapse lapseOuterRadiusReal = 1/3 := by
  simp [lapseProfileTemporalLapse, lapseProfileExponent,
    lapseOuterRadiusReal]

theorem lapse_profile_outer_log_slope_real :
    lapseProfileLogSlopeReal lapseOuterRadiusReal = -2/5 := by
  norm_num [lapseProfileLogSlopeReal, lapseSlopeAReal, lapseSlopeBReal,
    lapseOuterRadiusReal]

theorem lapse_profile_outer_lapse_derivative :
    HasDerivAt lapseProfileTemporalLapse (-4/15)
      lapseOuterRadiusReal := by
  convert lapse_profile_temporal_lapse_hasDerivAt lapseOuterRadiusReal using 1
  · rw [lapse_profile_outer_log_slope_real, lapse_profile_outer_lapse]
    norm_num
  · rfl

theorem lapse_profile_outer_lapse_matches_kottler :
    lapseProfileTemporalLapse lapseOuterRadiusReal
      = (finiteLayerBoundaryLapse : ℝ) := by
  rw [lapse_profile_outer_lapse, finite_layer_boundary_lapse]
  norm_num

theorem lapse_profile_outer_derivative_matches_kottler :
    (-4/15 : ℝ)
      = (fExteriorPrimeJunction
          transitionOuterRadius transitionOuterMass transitionOuterLambda : Rat) := by
  norm_num [fExteriorPrimeJunction, transitionOuterRadius,
    transitionOuterMass, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint]

structure ExplicitFiniteThicknessLapseReconstructionWitness : Prop where
  innerPressure :
    lapseProfileRadialPressure transitionInnerRadius = -1
  outerPressure :
    lapseProfileRadialPressure transitionOuterRadius = 0
  rationalTOV :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      anisotropicLambdaTOVRHS
        (lapseProfileState radius) finiteLayerLambda
        = lapseProfileRadialPressureDerivative radius
  gravitySlope :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      lambdaTOVGravityFactor
        (lapseProfileBaseState radius) finiteLayerLambda
        = lapseProfileLogSlope radius
  temporalLapseDerivative :
    ∀ radius : ℝ,
      HasDerivAt lapseProfileTemporalLapse
        (2 * lapseProfileLogSlopeReal radius
          * lapseProfileTemporalLapse radius) radius
  outerLapse :
    lapseProfileTemporalLapse lapseOuterRadiusReal = 1/3
  outerLapseDerivative :
    HasDerivAt lapseProfileTemporalLapse (-4/15)
      lapseOuterRadiusReal

theorem explicit_finite_thickness_lapse_reconstruction :
    ExplicitFiniteThicknessLapseReconstructionWitness := by
  exact {
    innerPressure := lapse_profile_inner_pressure
    outerPressure := lapse_profile_outer_pressure
    rationalTOV := fun radius hlo _ =>
      lapse_profile_lambda_tov_exact hlo
    gravitySlope := fun radius hlo hhi =>
      lapse_profile_gravity_factor hlo hhi
    temporalLapseDerivative := lapse_profile_temporal_lapse_hasDerivAt
    outerLapse := lapse_profile_outer_lapse
    outerLapseDerivative := lapse_profile_outer_lapse_derivative
  }

def finiteThicknessExplicitTemporalLapseReconstructed : Bool := true
def finiteThicknessDesignedEinsteinTOVRadialSystemSolved : Bool := true
def finiteThicknessSourceNativeCMP119ProfileStillRequired : Bool := true
def finiteThicknessScalarFieldWallEquationStillRequired : Bool := true
def finiteThicknessContinuumEinsteinPromotionStillRequired : Bool := true

end Integration.AntigravityFiniteThicknessLapseReconstruction
