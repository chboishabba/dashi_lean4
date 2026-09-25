import Integration.AntigravityFiniteThicknessWall

namespace Integration.AntigravityFiniteThicknessTOVTransition

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravitySourceGeometryWeld
open Integration.AntigravityFiniteThicknessWall

/-!
Exact finite-thickness anisotropic TOV transition.

The existing literal GRQFT carrier uses rational radial states and the exact
anisotropic TOV right-hand side

  p_r' = -(rho+p_r) G_TOV + 2 (p_t-p_r)/r.

For any nonzero radius and prescribed radial-pressure derivative, the
tangential pressure can be solved algebraically.  This module makes that design
equation explicit and then instantiates a three-node positive-width transition
layer.

This is an exact solution of the repository's finite rational TOV balance at
the three layer nodes, together with exact finite mass updates and positive
Schwarzschild denominators.  It is NOT promoted to a smooth continuum
Einstein-scalar domain-wall solution.
-/

def designedTangentialPressure
    (state : RationalRadialState)
    (radialPressureDerivative : Rat) : Rat :=
  state.radialPressure
    + state.radius / 2
      * (radialPressureDerivative
          + (state.rho + state.radialPressure) * tovGravityFactor state)

def withDesignedTangentialPressure
    (state : RationalRadialState)
    (radialPressureDerivative : Rat) : RationalRadialState :=
  { state with
    tangentialPressure :=
      designedTangentialPressure state radialPressureDerivative }

theorem designed_tangential_pressure_solves_tov
    (state : RationalRadialState)
    (radialPressureDerivative : Rat)
    (hRadius : state.radius ≠ 0) :
    anisotropicTOVRHS
        (withDesignedTangentialPressure state radialPressureDerivative)
      = radialPressureDerivative := by
  unfold anisotropicTOVRHS withDesignedTangentialPressure
    designedTangentialPressure
  simp only
  field_simp [hRadius]
  ring

structure FiniteTOVNode where
  state : RationalRadialState
  radialPressureDerivative : Rat
  radiusNonzero : state.radius ≠ 0
  outsideHorizon : 0 < state.radius - 2 * state.mass
  tovBalance :
    anisotropicTOVRHS state = radialPressureDerivative

def makeDesignedTOVNode
    (base : RationalRadialState)
    (radialPressureDerivative : Rat)
    (hRadius : base.radius ≠ 0)
    (hOutside : 0 < base.radius - 2 * base.mass) :
    FiniteTOVNode where
  state := withDesignedTangentialPressure base radialPressureDerivative
  radialPressureDerivative := radialPressureDerivative
  radiusNonzero := hRadius
  outsideHorizon := hOutside
  tovBalance :=
    designed_tangential_pressure_solves_tov
      base radialPressureDerivative hRadius

/-!
A concrete width-one transition centred on the previous R=2 thin shell.

r = 3/2, 2, 5/2
p_r = -1, -1/2, 0
p_r' = +1

The finite metric mass is advanced by the already-owned literal mass update
m_next = m + r_next^2 rhoBar_next Delta r with Delta r = 1/2.

The chosen rhoBar values are exactly those required for a mass increment 1/18
on each half-step.
-/

def transitionInnerRadius : Rat := 3/2
def transitionMiddleRadius : Rat := 2
def transitionOuterRadius : Rat := 5/2
def transitionHalfStep : Rat := 1/2
def transitionWidth : Rat := transitionOuterRadius - transitionInnerRadius

def transitionInnerMass : Rat := 1/6
def transitionMiddleMass : Rat := 2/9
def transitionOuterMass : Rat := 5/18

def transitionMiddleDensityBar : Rat := 1/36
def transitionOuterDensityBar : Rat := 4/225

def transitionInnerBase : RationalRadialState where
  radius := transitionInnerRadius
  mass := transitionInnerMass
  densityBar := 1/27
  rho := 1
  radialPressure := -1
  tangentialPressure := 0

def transitionMiddleBase : RationalRadialState where
  radius := transitionMiddleRadius
  mass := transitionMiddleMass
  densityBar := transitionMiddleDensityBar
  rho := 1
  radialPressure := -1/2
  tangentialPressure := 0

def transitionOuterBase : RationalRadialState where
  radius := transitionOuterRadius
  mass := transitionOuterMass
  densityBar := transitionOuterDensityBar
  rho := 1
  radialPressure := 0
  tangentialPressure := 0

def transitionPressureDerivative : Rat := 1

def transitionInnerNode : FiniteTOVNode :=
  makeDesignedTOVNode transitionInnerBase transitionPressureDerivative
    (by norm_num [transitionInnerBase, transitionInnerRadius])
    (by norm_num [transitionInnerBase, transitionInnerRadius, transitionInnerMass])

def transitionMiddleNode : FiniteTOVNode :=
  makeDesignedTOVNode transitionMiddleBase transitionPressureDerivative
    (by norm_num [transitionMiddleBase, transitionMiddleRadius])
    (by norm_num [transitionMiddleBase, transitionMiddleRadius, transitionMiddleMass])

def transitionOuterNode : FiniteTOVNode :=
  makeDesignedTOVNode transitionOuterBase transitionPressureDerivative
    (by norm_num [transitionOuterBase, transitionOuterRadius])
    (by norm_num [transitionOuterBase, transitionOuterRadius, transitionOuterMass])

theorem transition_width_positive :
    transitionWidth = 1 := by
  norm_num [transitionWidth, transitionOuterRadius, transitionInnerRadius]

theorem transition_first_mass_step :
    transitionInnerMass
      + massIncrement
          transitionMiddleRadius
          transitionMiddleDensityBar
          transitionHalfStep
      = transitionMiddleMass := by
  norm_num [transitionInnerMass, transitionMiddleMass, massIncrement,
    transitionMiddleRadius, transitionMiddleDensityBar, transitionHalfStep]

theorem transition_second_mass_step :
    transitionMiddleMass
      + massIncrement
          transitionOuterRadius
          transitionOuterDensityBar
          transitionHalfStep
      = transitionOuterMass := by
  norm_num [transitionMiddleMass, transitionOuterMass, massIncrement,
    transitionOuterRadius, transitionOuterDensityBar, transitionHalfStep]

theorem transition_inner_pressure :
    transitionInnerNode.state.radialPressure = -1 := by
  rfl

theorem transition_middle_pressure :
    transitionMiddleNode.state.radialPressure = -1/2 := by
  rfl

theorem transition_outer_pressure :
    transitionOuterNode.state.radialPressure = 0 := by
  rfl

theorem transition_inner_tov_exact :
    anisotropicTOVRHS transitionInnerNode.state = 1 := by
  exact transitionInnerNode.tovBalance

theorem transition_middle_tov_exact :
    anisotropicTOVRHS transitionMiddleNode.state = 1 := by
  exact transitionMiddleNode.tovBalance

theorem transition_outer_tov_exact :
    anisotropicTOVRHS transitionOuterNode.state = 1 := by
  exact transitionOuterNode.tovBalance

theorem transition_inner_outside_horizon :
    0 < transitionInnerNode.state.radius
        - 2 * transitionInnerNode.state.mass :=
  transitionInnerNode.outsideHorizon

theorem transition_middle_outside_horizon :
    0 < transitionMiddleNode.state.radius
        - 2 * transitionMiddleNode.state.mass :=
  transitionMiddleNode.outsideHorizon

theorem transition_outer_outside_horizon :
    0 < transitionOuterNode.state.radius
        - 2 * transitionOuterNode.state.mass :=
  transitionOuterNode.outsideHorizon

structure FiniteThicknessTOVTransitionWitness : Prop where
  positiveWidth : transitionWidth = 1
  firstMassUpdate :
    transitionInnerMass
      + massIncrement
          transitionMiddleRadius transitionMiddleDensityBar transitionHalfStep
      = transitionMiddleMass
  secondMassUpdate :
    transitionMiddleMass
      + massIncrement
          transitionOuterRadius transitionOuterDensityBar transitionHalfStep
      = transitionOuterMass
  innerBalance : anisotropicTOVRHS transitionInnerNode.state = 1
  middleBalance : anisotropicTOVRHS transitionMiddleNode.state = 1
  outerBalance : anisotropicTOVRHS transitionOuterNode.state = 1
  innerOutside : 0 <
    transitionInnerNode.state.radius - 2 * transitionInnerNode.state.mass
  middleOutside : 0 <
    transitionMiddleNode.state.radius - 2 * transitionMiddleNode.state.mass
  outerOutside : 0 <
    transitionOuterNode.state.radius - 2 * transitionOuterNode.state.mass
  pressureStartsAtVacuumTension :
    transitionInnerNode.state.radialPressure = -1
  pressureEndsAtZero :
    transitionOuterNode.state.radialPressure = 0

theorem finite_thickness_tov_transition :
    FiniteThicknessTOVTransitionWitness := by
  exact {
    positiveWidth := transition_width_positive
    firstMassUpdate := transition_first_mass_step
    secondMassUpdate := transition_second_mass_step
    innerBalance := transition_inner_tov_exact
    middleBalance := transition_middle_tov_exact
    outerBalance := transition_outer_tov_exact
    innerOutside := transition_inner_outside_horizon
    middleOutside := transition_middle_outside_horizon
    outerOutside := transition_outer_outside_horizon
    pressureStartsAtVacuumTension := transition_inner_pressure
    pressureEndsAtZero := transition_outer_pressure
  }





/-!
All-rational-radius finite-thickness profile.

This strengthens the three-node fixture to one exact formula on every rational
radius in 3/2 <= r <= 5/2.  The "derivative" fields below are explicit
polynomial slope formulas in the finite rational model; no claim about a
completed real differentiable manifold is made here.
-/

def layerMass (radius : Rat) : Rat :=
  (4/225 : Rat) * radius^3

def layerDensityBar : Rat := 4/75

def layerEnergyDensity : Rat := 1

def layerRadialPressure (radius : Rat) : Rat :=
  radius - 5/2

def layerRadialPressureDerivative : Rat := 1

def layerMassDerivative (radius : Rat) : Rat :=
  (4/75 : Rat) * radius^2

def layerBaseState (radius : Rat) : RationalRadialState where
  radius := radius
  mass := layerMass radius
  densityBar := layerDensityBar
  rho := layerEnergyDensity
  radialPressure := layerRadialPressure radius
  tangentialPressure := 0

def layerState (radius : Rat) : RationalRadialState :=
  withDesignedTangentialPressure
    (layerBaseState radius)
    layerRadialPressureDerivative

theorem layer_mass_slope_equation (radius : Rat) :
    layerMassDerivative radius
      = radius^2 * layerDensityBar := by
  ring

theorem layer_pressure_affine_difference (left right : Rat) :
    layerRadialPressure right - layerRadialPressure left
      = (right - left) * layerRadialPressureDerivative := by
  ring

theorem layer_inner_pressure :
    layerRadialPressure transitionInnerRadius = -1 := by
  norm_num [layerRadialPressure, transitionInnerRadius]

theorem layer_outer_pressure :
    layerRadialPressure transitionOuterRadius = 0 := by
  norm_num [layerRadialPressure, transitionOuterRadius]

theorem layer_outer_mass_matches :
    layerMass transitionOuterRadius = transitionOuterMass := by
  norm_num [layerMass, transitionOuterRadius, transitionOuterMass]

theorem layer_radius_positive
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius) :
    0 < radius := by
  norm_num [transitionInnerRadius] at hLower
  linarith

theorem layer_radius_square_upper
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius)
    (hUpper : radius ≤ transitionOuterRadius) :
    radius^2 ≤ (25/4 : Rat) := by
  have hr : 0 < radius := layer_radius_positive hLower
  have hsum : 0 ≤ (5/2 : Rat) + radius := by
    linarith
  have hdiff : 0 ≤ (5/2 : Rat) - radius := by
    norm_num [transitionOuterRadius] at hUpper
    linarith
  have hprod :
      0 ≤ ((5/2 : Rat) - radius) * ((5/2 : Rat) + radius) :=
    mul_nonneg hdiff hsum
  nlinarith

theorem layer_outside_horizon
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius)
    (hUpper : radius ≤ transitionOuterRadius) :
    0 < radius - 2 * layerMass radius := by
  have hr : 0 < radius := layer_radius_positive hLower
  have hsq : radius^2 ≤ (25/4 : Rat) :=
    layer_radius_square_upper hLower hUpper
  have hfactor : (7/9 : Rat) ≤ 1 - (8/225 : Rat) * radius^2 := by
    nlinarith
  have hfactorPos : 0 < 1 - (8/225 : Rat) * radius^2 := by
    linarith
  have hprod :
      0 < radius * (1 - (8/225 : Rat) * radius^2) :=
    mul_pos hr hfactorPos
  convert hprod using 1 <;> ring

theorem layer_tov_exact
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius) :
    anisotropicTOVRHS (layerState radius)
      = layerRadialPressureDerivative := by
  exact designed_tangential_pressure_solves_tov
    (layerBaseState radius)
    layerRadialPressureDerivative
    (ne_of_gt (layer_radius_positive hLower))

structure RationalFiniteThicknessTOVProfileWitness : Prop where
  innerPressure :
    layerRadialPressure transitionInnerRadius = -1
  outerPressure :
    layerRadialPressure transitionOuterRadius = 0
  outerMass :
    layerMass transitionOuterRadius = transitionOuterMass
  massEquation :
    ∀ radius,
      layerMassDerivative radius = radius^2 * layerDensityBar
  pressureAffine :
    ∀ left right,
      layerRadialPressure right - layerRadialPressure left
        = (right - left) * layerRadialPressureDerivative
  horizonSafe :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      0 < radius - 2 * layerMass radius
  tovExact :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      anisotropicTOVRHS (layerState radius)
        = layerRadialPressureDerivative

theorem rational_finite_thickness_tov_profile :
    RationalFiniteThicknessTOVProfileWitness := by
  exact {
    innerPressure := layer_inner_pressure
    outerPressure := layer_outer_pressure
    outerMass := layer_outer_mass_matches
    massEquation := layer_mass_slope_equation
    pressureAffine := layer_pressure_affine_difference
    horizonSafe := fun radius hlo hhi =>
      layer_outside_horizon hlo hhi
    tovExact := fun radius hlo _ =>
      layer_tov_exact hlo
  }

def finiteThicknessAllRationalRadiiTOVSolved : Bool := true


/-!
Exact Kottler exterior parameter compatibility for the outer finite-thickness
node.

M = 5/18, R = 5/2 satisfies R > 3M.  Choose the midpoint of the Kottler
repulsion/static window in scaled-Lambda coordinates.

Important boundary: `fInteriorJunction` below is the repository's de Sitter
helper, NOT the lapse reconstructed from `layerState`.  The equal-lapse and
derivative-jump calculations therefore certify a de-Sitter/Kottler comparison
at the same (M,R), not a Darmois match of the finite TOV layer itself.
-/

def transitionOuterScaledLambda : Rat :=
  scaledLambdaMidpoint transitionOuterMass transitionOuterRadius

def transitionOuterLambda : Rat :=
  transitionOuterScaledLambda / transitionOuterRadius^3

def transitionInnerMatchedLambda : Rat :=
  transitionOuterLambda
    + 6 * transitionOuterMass / transitionOuterRadius^3

theorem transition_outer_scaled_lambda :
    transitionOuterScaledLambda = 10/3 := by
  norm_num [transitionOuterScaledLambda, scaledLambdaMidpoint,
    transitionOuterMass, transitionOuterRadius]

theorem transition_outer_lambda :
    transitionOuterLambda = 16/75 := by
  norm_num [transitionOuterLambda, transitionOuterScaledLambda,
    scaledLambdaMidpoint, transitionOuterMass, transitionOuterRadius]

theorem transition_inner_matched_lambda :
    transitionInnerMatchedLambda = 8/25 := by
  norm_num [transitionInnerMatchedLambda, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint,
    transitionOuterMass, transitionOuterRadius]

theorem transition_outer_kottler_lapse :
    fExteriorJunction
      transitionOuterRadius transitionOuterMass transitionOuterLambda
      = 1/3 := by
  norm_num [fExteriorJunction, transitionOuterRadius, transitionOuterMass,
    transitionOuterLambda, transitionOuterScaledLambda, scaledLambdaMidpoint]

theorem transition_inner_de_sitter_lapse :
    fInteriorJunction
      transitionOuterRadius transitionInnerMatchedLambda
      = 1/3 := by
  norm_num [fInteriorJunction, transitionOuterRadius,
    transitionInnerMatchedLambda, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint,
    transitionOuterMass]

theorem transition_outer_lapse_matches :
    fInteriorJunction transitionOuterRadius transitionInnerMatchedLambda
      =
    fExteriorJunction
      transitionOuterRadius transitionOuterMass transitionOuterLambda := by
  rw [transition_inner_de_sitter_lapse, transition_outer_kottler_lapse]

theorem transition_outer_acceleration_positive :
    kottlerRadialAcceleration
      transitionOuterMass transitionOuterRadius transitionOuterLambda
      = 2/15 := by
  norm_num [kottlerRadialAcceleration, transitionOuterMass,
    transitionOuterRadius, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint]

theorem transition_outer_derivative_jump :
    fExteriorPrimeJunction
        transitionOuterRadius transitionOuterMass transitionOuterLambda
      -
      fInteriorPrimeJunction
        transitionOuterRadius transitionInnerMatchedLambda
      = 4/15 := by
  norm_num [fExteriorPrimeJunction, fInteriorPrimeJunction,
    transitionOuterRadius, transitionOuterMass,
    transitionOuterLambda, transitionInnerMatchedLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint]

structure FiniteThicknessExteriorParameterWitness : Prop where
  outerLambda : transitionOuterLambda = 16/75
  innerLambda : transitionInnerMatchedLambda = 8/25
  lapseMatched :
    fInteriorJunction transitionOuterRadius transitionInnerMatchedLambda
      =
    fExteriorJunction
      transitionOuterRadius transitionOuterMass transitionOuterLambda
  staticPositive :
    fExteriorJunction
      transitionOuterRadius transitionOuterMass transitionOuterLambda
      = 1/3
  outwardAcceleration :
    kottlerRadialAcceleration
      transitionOuterMass transitionOuterRadius transitionOuterLambda
      = 2/15
  derivativeJump :
    fExteriorPrimeJunction
        transitionOuterRadius transitionOuterMass transitionOuterLambda
      -
      fInteriorPrimeJunction
        transitionOuterRadius transitionInnerMatchedLambda
      = 4/15

theorem finite_thickness_exterior_parameters :
    FiniteThicknessExteriorParameterWitness := by
  exact {
    outerLambda := transition_outer_lambda
    innerLambda := transition_inner_matched_lambda
    lapseMatched := transition_outer_lapse_matches
    staticPositive := transition_outer_kottler_lapse
    outwardAcceleration := transition_outer_acceleration_positive
    derivativeJump := transition_outer_derivative_jump
  }




/-!
Source-calibrated finite-thickness capstone.

Unlike the older thin-wall bubble calibration, this uses the actual finite-layer
Kottler target Lambda_out = 16/75.
-/

def finiteThicknessKottlerTarget : Rat := transitionOuterLambda

theorem finite_thickness_kottler_target_exact :
    finiteThicknessKottlerTarget = 16/75 :=
  transition_outer_lambda

theorem finite_thickness_kottler_target_positive :
    0 < finiteThicknessKottlerTarget := by
  rw [finite_thickness_kottler_target_exact]
  norm_num

def finiteThicknessRequiredStressLengthSquaredLower
    (source : AgdaTraceSourceReceipt) : Rat :=
  requiredStressLengthSquaredLowerFor finiteThicknessKottlerTarget source

def finiteThicknessRequiredStressLengthSquaredUpper
    (source : AgdaTraceSourceReceipt) : Rat :=
  requiredStressLengthSquaredUpperFor finiteThicknessKottlerTarget source

theorem finite_thickness_required_scale_interval_ordered
    (source : AgdaTraceSourceReceipt) :
    finiteThicknessRequiredStressLengthSquaredLower source
      ≤ finiteThicknessRequiredStressLengthSquaredUpper source := by
  exact required_stress_length_squared_for_interval_ordered
    finiteThicknessKottlerTarget source
    (le_of_lt finite_thickness_kottler_target_positive)

structure FiniteThicknessSourceGeometryWitness
    (source : AgdaTraceSourceReceipt)
    (calibration :
      NormalizedSourceToKottlerTargetCalibration
        source finiteThicknessKottlerTarget) : Prop where
  sourceActiveNegative :
    source.activeConnectedNumerator < 0
  sourceMagnitudePositive :
    0 < source.sourceMagnitude
  sourceCalibratesToFiniteThicknessLambda :
    calibration.dimensionlessAmplitude = finiteThicknessKottlerTarget
  tovTransition :
    FiniteThicknessTOVTransitionWitness
  exteriorParameters :
    FiniteThicknessExteriorParameterWitness
  exteriorAcceleration :
    kottlerRadialAcceleration
      transitionOuterMass transitionOuterRadius transitionOuterLambda
      = 2/15

theorem compile_finite_thickness_source_geometry
    (source : AgdaTraceSourceReceipt)
    (calibration :
      NormalizedSourceToKottlerTargetCalibration
        source finiteThicknessKottlerTarget) :
    FiniteThicknessSourceGeometryWitness source calibration := by
  exact {
    sourceActiveNegative := source.activeConnectedNumerator_negative
    sourceMagnitudePositive := source.sourceMagnitude_positive
    sourceCalibratesToFiniteThicknessLambda :=
      normalized_target_calibration_exact
        source finiteThicknessKottlerTarget calibration
    tovTransition := finite_thickness_tov_transition
    exteriorParameters := finite_thickness_exterior_parameters
    exteriorAcceleration := transition_outer_acceleration_positive
  }

def finiteThicknessSourceToGeometryCompilerClosed : Bool := true
def finiteThicknessMeasuredScaleProductIntervalCompiled : Bool := true


/-!
Actual TOV-layer -> Kottler Darmois boundary.

The rational TOV state determines mass, density and pressures, but the current
carrier does not yet reconstruct the temporal lapse Phi(r).  A shell-free
Darmois theorem therefore needs an explicit lapse/normal-derivative
reconstruction on the TOV side.
-/

structure TOVLayerExteriorDarmoisData where
  interiorLapseAtOuter : Rat
  interiorLapsePrimeAtOuter : Rat
  exteriorLapseAtOuter : Rat
  exteriorLapsePrimeAtOuter : Rat
  lapseContinuity :
    interiorLapseAtOuter = exteriorLapseAtOuter
  derivativeContinuity :
    interiorLapsePrimeAtOuter = exteriorLapsePrimeAtOuter

structure TOVLayerMetricReconstructionBoundary : Prop where
  outerRadialPressureZero :
    layerRadialPressure transitionOuterRadius = 0
  outerMassKnown :
    layerMass transitionOuterRadius = transitionOuterMass
  temporalLapseReconstructionStillRequired : True
  secondFundamentalFormMatchStillRequired : True

theorem current_tov_layer_metric_reconstruction_boundary :
    TOVLayerMetricReconstructionBoundary := by
  exact {
    outerRadialPressureZero := layer_outer_pressure
    outerMassKnown := layer_outer_mass_matches
    temporalLapseReconstructionStillRequired := trivial
    secondFundamentalFormMatchStillRequired := trivial
  }

def finiteThicknessFullInteriorLapseReconstructed : Bool := false
def finiteThicknessOuterDarmoisBoundarySolved : Bool := true
def finiteThicknessFullDarmoisMetricReconstructionSolved : Bool := false

/-!
Lambda-aware finite-thickness TOV profile and shell-free outer boundary.

The repulsive exterior uses a positive cosmological term.  The correct interior
comparison therefore uses the SAME lambda in the finite TOV gravity factor:

  G_Lambda =
    (m + r^3 p_r - Lambda r^3/3)
    /
    (r (r - 2m - Lambda r^3/3)).

At p_r(R)=0 this is exactly f'_Kottler(R)/(2 f_Kottler(R)).  Hence once the
boundary time normalization is chosen so that e^(2 Phi(R)) = f_Kottler(R),
the first radial derivative of g_tt matches as well; no residual Israel shell is
required at the outer boundary.
-/

def lambdaSchwarzschildDenominator
    (state : RationalRadialState)
    (lambda : Rat) : Rat :=
  state.radius
    * (state.radius - 2 * state.mass - lambda * state.radius^3 / 3)

def lambdaTOVGravityNumerator
    (state : RationalRadialState)
    (lambda : Rat) : Rat :=
  state.mass + state.radius^3 * state.radialPressure
    - lambda * state.radius^3 / 3

def lambdaTOVGravityFactor
    (state : RationalRadialState)
    (lambda : Rat) : Rat :=
  lambdaTOVGravityNumerator state lambda
    / lambdaSchwarzschildDenominator state lambda

def anisotropicLambdaTOVRHS
    (state : RationalRadialState)
    (lambda : Rat) : Rat :=
  -((state.rho + state.radialPressure)
      * lambdaTOVGravityFactor state lambda)
    + 2 * (state.tangentialPressure - state.radialPressure) / state.radius

def designedLambdaTangentialPressure
    (state : RationalRadialState)
    (lambda radialPressureDerivative : Rat) : Rat :=
  state.radialPressure
    + state.radius / 2
      * (radialPressureDerivative
          + (state.rho + state.radialPressure)
            * lambdaTOVGravityFactor state lambda)

def withDesignedLambdaTangentialPressure
    (state : RationalRadialState)
    (lambda radialPressureDerivative : Rat) : RationalRadialState :=
  { state with
    tangentialPressure :=
      designedLambdaTangentialPressure
        state lambda radialPressureDerivative }

theorem designed_lambda_tangential_pressure_solves_tov
    (state : RationalRadialState)
    (lambda radialPressureDerivative : Rat)
    (hRadius : state.radius ≠ 0) :
    anisotropicLambdaTOVRHS
        (withDesignedLambdaTangentialPressure
          state lambda radialPressureDerivative)
        lambda
      = radialPressureDerivative := by
  unfold anisotropicLambdaTOVRHS
    withDesignedLambdaTangentialPressure
    designedLambdaTangentialPressure
  simp only
  field_simp [hRadius]
  ring

def finiteLayerLambda : Rat := transitionOuterLambda

def lambdaLayerState (radius : Rat) : RationalRadialState :=
  withDesignedLambdaTangentialPressure
    (layerBaseState radius)
    finiteLayerLambda
    layerRadialPressureDerivative

theorem lambda_layer_denominator_positive
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius)
    (hUpper : radius ≤ transitionOuterRadius) :
    0 <
      layerBaseState radius |>.radius
        - 2 * (layerBaseState radius |>.mass)
        - finiteLayerLambda * (layerBaseState radius |>.radius)^3 / 3 := by
  have hr : 0 < radius := layer_radius_positive hLower
  have hsq : radius^2 ≤ (25/4 : Rat) :=
    layer_radius_square_upper hLower hUpper
  rw [finite_thickness_kottler_target_exact]
  dsimp [layerBaseState, layerMass]
  have hfactor : (1/3 : Rat) ≤ 1 - (8/75 : Rat) * radius^2 := by
    nlinarith
  have hfactorPos : 0 < 1 - (8/75 : Rat) * radius^2 := by
    linarith
  have hprod :
      0 < radius * (1 - (8/75 : Rat) * radius^2) :=
    mul_pos hr hfactorPos
  convert hprod using 1 <;> ring

theorem lambda_layer_tov_exact
    {radius : Rat}
    (hLower : transitionInnerRadius ≤ radius) :
    anisotropicLambdaTOVRHS
        (lambdaLayerState radius)
        finiteLayerLambda
      = layerRadialPressureDerivative := by
  exact designed_lambda_tangential_pressure_solves_tov
    (layerBaseState radius)
    finiteLayerLambda
    layerRadialPressureDerivative
    (ne_of_gt (layer_radius_positive hLower))

theorem lambda_layer_outer_gravity_factor :
    lambdaTOVGravityFactor
      (layerBaseState transitionOuterRadius)
      finiteLayerLambda
      = -2/5 := by
  norm_num [lambdaTOVGravityFactor, lambdaTOVGravityNumerator,
    lambdaSchwarzschildDenominator, layerBaseState, layerMass,
    layerRadialPressure, layerEnergyDensity, layerDensityBar,
    transitionOuterRadius, transitionOuterMass,
    finiteLayerLambda, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint]

def kottlerLogLapseSlope
    (radius mass lambda : Rat) : Rat :=
  fExteriorPrimeJunction radius mass lambda
    / (2 * fExteriorJunction radius mass lambda)

theorem finite_layer_outer_log_lapse_matches :
    lambdaTOVGravityFactor
      (layerBaseState transitionOuterRadius)
      finiteLayerLambda
    =
    kottlerLogLapseSlope
      transitionOuterRadius transitionOuterMass transitionOuterLambda := by
  rw [lambda_layer_outer_gravity_factor]
  norm_num [kottlerLogLapseSlope, fExteriorPrimeJunction,
    fExteriorJunction, transitionOuterRadius, transitionOuterMass,
    transitionOuterLambda, transitionOuterScaledLambda,
    scaledLambdaMidpoint]

def finiteLayerBoundaryLapse : Rat :=
  fExteriorJunction
    transitionOuterRadius transitionOuterMass transitionOuterLambda

def finiteLayerBoundaryLapsePrime : Rat :=
  2 * finiteLayerBoundaryLapse
    * lambdaTOVGravityFactor
        (layerBaseState transitionOuterRadius)
        finiteLayerLambda

theorem finite_layer_boundary_lapse :
    finiteLayerBoundaryLapse = 1/3 := by
  exact transition_outer_kottler_lapse

theorem finite_layer_boundary_lapse_prime :
    finiteLayerBoundaryLapsePrime = -4/15 := by
  rw [finite_layer_boundary_lapse, lambda_layer_outer_gravity_factor]
  norm_num [finiteLayerBoundaryLapsePrime]

theorem finite_layer_boundary_lapse_prime_matches_kottler :
    finiteLayerBoundaryLapsePrime
      =
    fExteriorPrimeJunction
      transitionOuterRadius transitionOuterMass transitionOuterLambda := by
  rw [finite_layer_boundary_lapse_prime]
  norm_num [fExteriorPrimeJunction, transitionOuterRadius,
    transitionOuterMass, transitionOuterLambda,
    transitionOuterScaledLambda, scaledLambdaMidpoint]

structure LambdaAwareFiniteThicknessBoundaryWitness : Prop where
  sameLambda :
    finiteLayerLambda = transitionOuterLambda
  radialPressureZero :
    layerRadialPressure transitionOuterRadius = 0
  outerMassMatched :
    layerMass transitionOuterRadius = transitionOuterMass
  boundaryLapsePositive :
    finiteLayerBoundaryLapse = 1/3
  logLapseSlopeMatched :
    lambdaTOVGravityFactor
      (layerBaseState transitionOuterRadius)
      finiteLayerLambda
    =
    kottlerLogLapseSlope
      transitionOuterRadius transitionOuterMass transitionOuterLambda
  lapseDerivativeMatched :
    finiteLayerBoundaryLapsePrime
      =
    fExteriorPrimeJunction
      transitionOuterRadius transitionOuterMass transitionOuterLambda

theorem lambda_aware_finite_thickness_boundary :
    LambdaAwareFiniteThicknessBoundaryWitness := by
  exact {
    sameLambda := rfl
    radialPressureZero := layer_outer_pressure
    outerMassMatched := layer_outer_mass_matches
    boundaryLapsePositive := finite_layer_boundary_lapse
    logLapseSlopeMatched := finite_layer_outer_log_lapse_matches
    lapseDerivativeMatched :=
      finite_layer_boundary_lapse_prime_matches_kottler
  }

structure LambdaAwareRationalFiniteThicknessTOVProfileWitness : Prop where
  baseProfile : RationalFiniteThicknessTOVProfileWitness
  lambdaTOVExact :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      anisotropicLambdaTOVRHS
        (lambdaLayerState radius)
        finiteLayerLambda
        = layerRadialPressureDerivative
  lambdaRadialDenominatorPositive :
    ∀ radius,
      transitionInnerRadius ≤ radius →
      radius ≤ transitionOuterRadius →
      0 <
        layerBaseState radius |>.radius
          - 2 * (layerBaseState radius |>.mass)
          - finiteLayerLambda * (layerBaseState radius |>.radius)^3 / 3
  outerBoundary : LambdaAwareFiniteThicknessBoundaryWitness

theorem lambda_aware_rational_finite_thickness_tov_profile :
    LambdaAwareRationalFiniteThicknessTOVProfileWitness := by
  exact {
    baseProfile := rational_finite_thickness_tov_profile
    lambdaTOVExact := fun radius hlo _ =>
      lambda_layer_tov_exact hlo
    lambdaRadialDenominatorPositive := fun radius hlo hhi =>
      lambda_layer_denominator_positive hlo hhi
    outerBoundary := lambda_aware_finite_thickness_boundary
  }

def finiteThicknessLambdaAwareTOVSolved : Bool := true
def finiteThicknessOuterDarmoisBoundaryDataSolved : Bool := true
def finiteThicknessFullInteriorLapseReconstructionStillRequired : Bool := true

def finiteThicknessLiteralTOVTransitionSolved : Bool := true
def finiteThicknessContinuumEinsteinPDESolved : Bool := false
def finiteThicknessScalarFieldEquationSolved : Bool := false
def finiteThicknessSourceNativeCMP119ProfileDerived : Bool := false
def finiteThicknessExteriorParameterWindowCompiled : Bool := true
def finiteThicknessTOVToKottlerOuterBoundaryMatchingStillRequired : Bool := false
def finiteThicknessFullMetricMatchingStillRequired : Bool := true
def finiteThicknessExteriorParameterMatchingStillRequired : Bool := false
def finiteThicknessOuterBoundaryMatchingCompiled : Bool := true

end Integration.AntigravityFiniteThicknessTOVTransition
