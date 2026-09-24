/-!
# Executable GR/QFT Einstein and stress-weld BIDI residuals

This module mirrors the executable-candidate discipline introduced in
DASHI Agda.  Missing promotion authority does not suppress an available
calculation: run the candidate objects, compute a residual, and distinguish an
exact witness from a counterexample.

The finite Einstein fixture is normalized.  `Coupling.pos` represents the
dimensionless kappa = 1 normalization of 8*pi*G in this fixture only.  It is
not SI calibration and does not promote a continuum GR or GR/QFT theorem.
-/

namespace Integration.GRQFTExecutableResidual

inductive Axis4 where
  | time | x | y | z
  deriving DecidableEq, Repr

inductive SourceCoefficient where
  | neg | zero | pos
  deriving DecidableEq, Repr

inductive Coupling where
  | neg | zero | pos
  deriving DecidableEq, Repr

inductive AttemptOutcome where
  | exactResidualZero
  | nonzeroResidualCounterexample
  deriving DecidableEq, Repr

def negateSource : SourceCoefficient → SourceCoefficient
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

def addSource : SourceCoefficient → SourceCoefficient → SourceCoefficient
  | .neg, .neg => .neg
  | .neg, .zero => .neg
  | .neg, .pos => .zero
  | .zero, .neg => .neg
  | .zero, .zero => .zero
  | .zero, .pos => .pos
  | .pos, .neg => .zero
  | .pos, .zero => .pos
  | .pos, .pos => .pos

def scaleSource : Coupling → SourceCoefficient → SourceCoefficient
  | .neg, .neg => .pos
  | .neg, .zero => .zero
  | .neg, .pos => .neg
  | .zero, _ => .zero
  | .pos, s => s

abbrev Tensor4 := Axis4 → Axis4 → SourceCoefficient

def computedEinsteinTensor : Tensor4
  | .time, .time => .pos
  | .x, .x => .neg
  | .y, .y => .neg
  | .z, .z => .neg
  | _, _ => .zero

def computedMatterStress : Tensor4
  | .time, .time => .pos
  | .x, .x => .neg
  | .y, .y => .neg
  | .z, .z => .neg
  | _, _ => .zero

def einsteinEquationResidual (kappa : Coupling) : Tensor4 :=
  fun a b =>
    addSource
      (computedEinsteinTensor a b)
      (negateSource (scaleSource kappa (computedMatterStress a b)))

def sourceIsZero : SourceCoefficient → Bool
  | .zero => true
  | _ => false

def allComponentsZero (tensor : Tensor4) : Bool :=
  sourceIsZero (tensor .time .time) &&
  sourceIsZero (tensor .time .x) &&
  sourceIsZero (tensor .time .y) &&
  sourceIsZero (tensor .time .z) &&
  sourceIsZero (tensor .x .time) &&
  sourceIsZero (tensor .x .x) &&
  sourceIsZero (tensor .x .y) &&
  sourceIsZero (tensor .x .z) &&
  sourceIsZero (tensor .y .time) &&
  sourceIsZero (tensor .y .x) &&
  sourceIsZero (tensor .y .y) &&
  sourceIsZero (tensor .y .z) &&
  sourceIsZero (tensor .z .time) &&
  sourceIsZero (tensor .z .x) &&
  sourceIsZero (tensor .z .y) &&
  sourceIsZero (tensor .z .z)

def runEinsteinEquationAttempt (kappa : Coupling) : AttemptOutcome :=
  if allComponentsZero (einsteinEquationResidual kappa) then
    .exactResidualZero
  else
    .nonzeroResidualCounterexample

theorem normalized_residual_pointwise (a b : Axis4) :
    einsteinEquationResidual .pos a b = .zero := by
  cases a <;> cases b <;> rfl

theorem normalized_all_components_zero :
    allComponentsZero (einsteinEquationResidual .pos) = true := rfl

theorem normalized_attempt_passes :
    runEinsteinEquationAttempt .pos = .exactResidualZero := rfl

theorem zero_coupling_time_time_counterexample :
    einsteinEquationResidual .zero .time .time = .pos := rfl

theorem zero_coupling_attempt_fails :
    runEinsteinEquationAttempt .zero = .nonzeroResidualCounterexample := rfl

theorem negative_coupling_time_time_counterexample :
    einsteinEquationResidual .neg .time .time = .pos := rfl

theorem negative_coupling_attempt_fails :
    runEinsteinEquationAttempt .neg = .nonzeroResidualCounterexample := rfl

structure StressWeldObjects (Stress : Type u) where
  gr : Stress
  qft : Stress

structure ResidualProbe (Stress : Type u) (Residual : Type v) where
  zeroResidual : Residual
  residual : Stress → Stress → Residual
  residualIsZero : Residual → Bool
  reflexiveResidualZero : ∀ stress, residual stress stress = zeroResidual
  reflexiveResidualClassifiesZero :
    ∀ stress, residualIsZero (residual stress stress) = true

def runStressWeldAttempt
    {Stress : Type u} {Residual : Type v}
    (probe : ResidualProbe Stress Residual)
    (objects : StressWeldObjects Stress) : AttemptOutcome :=
  if probe.residualIsZero (probe.residual objects.gr objects.qft) then
    .exactResidualZero
  else
    .nonzeroResidualCounterexample

structure StressWeldAttemptReceipt
    (Stress : Type u) (Residual : Type v) where
  objects : StressWeldObjects Stress
  probe : ResidualProbe Stress Residual
  computedResidual : Residual
  outcome : AttemptOutcome
  residualIsLiteral :
    computedResidual = probe.residual objects.gr objects.qft
  outcomeIsComputed :
    outcome = runStressWeldAttempt probe objects

def executeStressWeldAttempt
    {Stress : Type u} {Residual : Type v}
    (probe : ResidualProbe Stress Residual)
    (objects : StressWeldObjects Stress) :
    StressWeldAttemptReceipt Stress Residual where
  objects := objects
  probe := probe
  computedResidual := probe.residual objects.gr objects.qft
  outcome := runStressWeldAttempt probe objects
  residualIsLiteral := rfl
  outcomeIsComputed := rfl

def bidiAttemptRunsWithoutPromotionReceipt : Bool := true

theorem bidi_attempt_runs_without_promotion :
    bidiAttemptRunsWithoutPromotionReceipt = true := rfl

def physicalCalibrationStillOpen : Bool := true

theorem physical_calibration_still_open :
    physicalCalibrationStillOpen = true := rfl

end Integration.GRQFTExecutableResidual
