import Integration.AntigravityFiniteThicknessScalarWallNoGo

namespace Integration.AntigravityCanonicalScalarTOVReduction

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravityFiniteThicknessTOVTransition
open Integration.AntigravityFiniteThicknessScalarWallNoGo

/-!
Canonical-scalar reduction of the finite Lambda-TOV wall problem.

Keep the finite-layer mass geometry

  m(r) = (4/225) r^3,
  Lambda = 16/75,

and now make the energy density consistent with the mass equation:

  rho = densityBar = 4/75.

For a canonical static radial scalar, p_t = -rho.  Writing p = p_r, the exact
Lambda-TOV equation becomes

  p' = -(rho+p) *
    [ r (p-4/75)/(1-(8/75)r^2) + 2/r ].

This is Riccati in p.  Set

  y = p + 4/75,
  z = 1/y.

Then the reciprocal slope is linear:

  z' =
    r/(1-(8/75)r^2)
    + z * [2/r - (8/75)r/(1-(8/75)r^2)].

The theorem below is purely algebraic: any pressure slope satisfying the
canonical-scalar TOV equation satisfies this reciprocal linear equation.
A continuum ODE existence/closed-form theorem may now target this scalar
equation directly.
-/

def scalarLayerDensity : Rat := layerDensityBar

def scalarLayerBaseState
    (radius radialPressure : Rat) : RationalRadialState where
  radius := radius
  mass := layerMass radius
  densityBar := scalarLayerDensity
  rho := scalarLayerDensity
  radialPressure := radialPressure
  tangentialPressure := -scalarLayerDensity

theorem scalar_layer_mass_density_consistent (radius : Rat) :
    layerMassDerivative radius
      = radius^2 * scalarLayerDensity := by
  exact layer_mass_slope_equation radius

theorem scalar_layer_canonical_stress_compatible
    (radius pressure : Rat) :
    CanonicalStaticRadialScalarStressCompatible
      (scalarLayerBaseState radius pressure) := by
  rfl

def scalarLayerGeometryFactor (radius : Rat) : Rat :=
  1 - (8/75 : Rat) * radius^2

theorem scalar_layer_lambda_gravity_factor
    {radius pressure : Rat}
    (hRadius : radius ≠ 0)
    (hGeometry : scalarLayerGeometryFactor radius ≠ 0) :
    lambdaTOVGravityFactor
      (scalarLayerBaseState radius pressure)
      finiteLayerLambda
      =
      radius * (pressure - 4/75)
        / scalarLayerGeometryFactor radius := by
  unfold lambdaTOVGravityFactor lambdaTOVGravityNumerator
    lambdaSchwarzschildDenominator scalarLayerBaseState
    scalarLayerDensity scalarLayerGeometryFactor
    layerDensityBar layerMass finiteLayerLambda
    transitionOuterLambda transitionOuterScaledLambda scaledLambdaMidpoint
  field_simp [hRadius, hGeometry]
  ring

def canonicalScalarPressureSlope
    (radius pressure : Rat) : Rat :=
  -(scalarLayerDensity + pressure)
    * (radius * (pressure - 4/75) / scalarLayerGeometryFactor radius
        + 2 / radius)

theorem canonical_scalar_tov_reduction
    {radius pressure : Rat}
    (hRadius : radius ≠ 0)
    (hGeometry : scalarLayerGeometryFactor radius ≠ 0) :
    anisotropicLambdaTOVRHS
      (scalarLayerBaseState radius pressure)
      finiteLayerLambda
      =
      canonicalScalarPressureSlope radius pressure := by
  unfold anisotropicLambdaTOVRHS canonicalScalarPressureSlope
  rw [scalar_layer_lambda_gravity_factor hRadius hGeometry]
  simp [scalarLayerBaseState, scalarLayerDensity]
  ring

def scalarLayerEnthalpy (pressure : Rat) : Rat :=
  pressure + scalarLayerDensity

def scalarLayerReciprocalEnthalpy (pressure : Rat) : Rat :=
  1 / scalarLayerEnthalpy pressure

def scalarLayerReciprocalSlope
    (pressure pressureDerivative : Rat) : Rat :=
  -pressureDerivative / scalarLayerEnthalpy pressure ^ 2

def scalarLayerReciprocalLinearRHS
    (radius pressure : Rat) : Rat :=
  radius / scalarLayerGeometryFactor radius
    + scalarLayerReciprocalEnthalpy pressure
      * (2 / radius
          - (8/75 : Rat) * radius / scalarLayerGeometryFactor radius)

theorem canonical_scalar_tov_reciprocal_linearization
    {radius pressure pressureDerivative : Rat}
    (hRadius : radius ≠ 0)
    (hGeometry : scalarLayerGeometryFactor radius ≠ 0)
    (hEnthalpy : scalarLayerEnthalpy pressure ≠ 0)
    (hSlope :
      pressureDerivative = canonicalScalarPressureSlope radius pressure) :
    scalarLayerReciprocalSlope pressure pressureDerivative
      =
      scalarLayerReciprocalLinearRHS radius pressure := by
  rw [hSlope]
  unfold scalarLayerReciprocalSlope scalarLayerReciprocalLinearRHS
    canonicalScalarPressureSlope scalarLayerReciprocalEnthalpy
    scalarLayerEnthalpy scalarLayerDensity scalarLayerGeometryFactor
    layerDensityBar
  field_simp [hRadius, hGeometry, hEnthalpy]
  ring

theorem scalar_layer_outer_geometry_factor :
    scalarLayerGeometryFactor transitionOuterRadius = 1/3 := by
  norm_num [scalarLayerGeometryFactor, transitionOuterRadius]

theorem scalar_layer_outer_reciprocal_boundary :
    scalarLayerReciprocalEnthalpy 0 = 75/4 := by
  norm_num [scalarLayerReciprocalEnthalpy, scalarLayerEnthalpy,
    scalarLayerDensity, layerDensityBar]

theorem scalar_layer_outer_pressure_slope :
    canonicalScalarPressureSlope transitionOuterRadius 0
      = -16/375 := by
  norm_num [canonicalScalarPressureSlope, scalarLayerDensity,
    scalarLayerGeometryFactor, transitionOuterRadius, layerDensityBar]

structure CanonicalScalarTOVReductionWitness : Prop where
  massDensityConsistent :
    ∀ radius,
      layerMassDerivative radius = radius^2 * scalarLayerDensity
  canonicalStress :
    ∀ radius pressure,
      CanonicalStaticRadialScalarStressCompatible
        (scalarLayerBaseState radius pressure)
  reciprocalBoundary :
    scalarLayerReciprocalEnthalpy 0 = 75/4
  outerPressureSlope :
    canonicalScalarPressureSlope transitionOuterRadius 0 = -16/375
  reciprocalLinearization :
    ∀ {radius pressure pressureDerivative},
      radius ≠ 0 →
      scalarLayerGeometryFactor radius ≠ 0 →
      scalarLayerEnthalpy pressure ≠ 0 →
      pressureDerivative = canonicalScalarPressureSlope radius pressure →
      scalarLayerReciprocalSlope pressure pressureDerivative
        = scalarLayerReciprocalLinearRHS radius pressure

theorem canonical_scalar_tov_reduction_witness :
    CanonicalScalarTOVReductionWitness := by
  exact {
    massDensityConsistent := scalar_layer_mass_density_consistent
    canonicalStress := scalar_layer_canonical_stress_compatible
    reciprocalBoundary := scalar_layer_outer_reciprocal_boundary
    outerPressureSlope := scalar_layer_outer_pressure_slope
    reciprocalLinearization :=
      fun hR hG hE hS =>
        canonical_scalar_tov_reciprocal_linearization hR hG hE hS
  }

def canonicalScalarTOVReducedToLinearReciprocalODE : Bool := true
def canonicalScalarPressureProfileSolved : Bool := false
def canonicalScalarFieldProfileSolved : Bool := false
def canonicalScalarPotentialReconstructed : Bool := false

end Integration.AntigravityCanonicalScalarTOVReduction
