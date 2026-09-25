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

def finiteThicknessLiteralTOVTransitionSolved : Bool := true
def finiteThicknessContinuumEinsteinPDESolved : Bool := false
def finiteThicknessScalarFieldEquationSolved : Bool := false
def finiteThicknessSourceNativeCMP119ProfileDerived : Bool := false
def finiteThicknessExteriorMatchingStillRequired : Bool := true

end Integration.AntigravityFiniteThicknessTOVTransition
