/-!
# Lean mirror of `DASHI/Analysis/FiniteOperatorReductionCore.agda`

This file provides the domain-neutral finite-operator surface re-exported by
the Agda module.  The upstream Agda records are interfaces: their analytic
claims remain structure fields and therefore explicit inputs in Lean.  The
short projection and assembly results below only expose or compose those
fields; they do not manufacture finite-dimensional coercivity assumptions.
-/

namespace AgdaMirror.FiniteOperatorReductionCore

universe u v w

/-- Data for the constrained covariance minimizer. -/
structure ConstrainedMinimizerData (Fine : Type u) (Coarse : Type v) where
  covariance : Fine → Fine
  average : Fine → Coarse
  averageStar : Coarse → Fine
  middleInverse : Coarse → Coarse
  middleInverseLeft : ∀ coarse,
    average (covariance (averageStar (middleInverse coarse))) = coarse

/-- The constrained minimizer represented by the supplied covariance data. -/
def constrainedMinimizer {Fine : Type u} {Coarse : Type v}
    (bundle : ConstrainedMinimizerData Fine Coarse) : Coarse → Fine :=
  fun coarse => bundle.covariance (bundle.averageStar (bundle.middleInverse coarse))

/-- Its average is the prescribed coarse value, by the explicit inverse field. -/
theorem constrainedMinimizerHasAverage {Fine : Type u} {Coarse : Type v}
    (bundle : ConstrainedMinimizerData Fine Coarse) (coarse : Coarse) :
    bundle.average (constrainedMinimizer bundle coarse) = coarse :=
  bundle.middleInverseLeft coarse

/-- Data needed to subtract a constrained minimizer and project to the kernel. -/
structure KernelProjectionData (Fine : Type u) (Coarse : Type v) where
  minimizerData : ConstrainedMinimizerData Fine Coarse
  fineSubtract : Fine → Fine → Fine
  coarseSubtract : Coarse → Coarse → Coarse
  coarseZero : Coarse
  averageSubtract : ∀ left right,
    minimizerData.average (fineSubtract left right) =
      coarseSubtract (minimizerData.average left) (minimizerData.average right)
  coarseSubtractSelf : ∀ coarse, coarseSubtract coarse coarse = coarseZero

/-- Subtract the constrained lift of a fine vector's average. -/
def kernelProjection {Fine : Type u} {Coarse : Type v}
    (bundle : KernelProjectionData Fine Coarse) : Fine → Fine :=
  fun fine => bundle.fineSubtract fine
    (constrainedMinimizer bundle.minimizerData (bundle.minimizerData.average fine))

/-- The supplied subtraction laws imply that the kernel projection has zero
average. -/
theorem kernelProjectionHasZeroAverage {Fine : Type u} {Coarse : Type v}
    (bundle : KernelProjectionData Fine Coarse) (fine : Fine) :
    bundle.minimizerData.average (kernelProjection bundle fine) = bundle.coarseZero := by
  rw [kernelProjection, bundle.averageSubtract,
    constrainedMinimizerHasAverage, bundle.coarseSubtractSelf]

/-- Finite Hessian symmetry and positivity certificate.  Positivity is an
explicit, proof-relevant predicate supplied by an instance. -/
structure FiniteHessianCertificate (Vector : Type u) (Scalar : Type v) where
  hessian : Vector → Vector
  inner : Vector → Vector → Scalar
  symmetric : ∀ left right, inner left (hessian right) = inner (hessian left) right
  Positive : Scalar → Type v
  positive : ∀ vector, Positive (inner vector (hessian vector))

/-- Explicit two-sided inverse certificate for a finite Hessian. -/
structure FiniteCovarianceCertificate {Vector : Type u} {Scalar : Type v}
    (hessianData : FiniteHessianCertificate Vector Scalar) where
  covariance : Vector → Vector
  covarianceLeft : ∀ x, covariance (hessianData.hessian x) = x
  covarianceRight : ∀ x, hessianData.hessian (covariance x) = x

/-- Algebraic block/Schur data.  The determinant factorization is retained as
an imported structure field, not claimed as a derived Lean theorem. -/
structure BlockSchurData (A : Type u) (Scalar : Type v) where
  aBlock : A → A
  bBlock : A → A
  cBlock : A → A
  dBlock : A → A
  aInverse : A → A
  add : (A → A) → (A → A) → A → A
  subtract : (A → A) → (A → A) → A → A
  compose : (A → A) → (A → A) → A → A
  schurComplement : A → A
  schurDefinition :
    schurComplement = subtract dBlock (compose cBlock (compose aInverse bBlock))
  determinant : (A → A) → Scalar
  scalarMultiply : Scalar → Scalar → Scalar
  determinantFactorization :
    determinant (add aBlock (add bBlock (add cBlock dBlock))) =
      scalarMultiply (determinant aBlock) (determinant schurComplement)

/-- Finite contraction data; contractivity and fixedness remain explicit
fields. -/
structure FiniteContractionCertificate (State : Type u) (Distance : Type v) where
  step : State → State
  distance : State → State → Distance
  StrictlySmaller : Distance → Distance → Type v
  fixedPoint : State
  fixed : step fixedPoint = fixedPoint
  contractive : ∀ left right,
    StrictlySmaller (distance (step left) (step right)) (distance left right)

/-! ## Domain-neutral quantitative Schur coercivity -/

/-- Ordered subtraction socket used by the quantitative Schur result. -/
structure SchurOrderLaws (Scalar : Type u) where
  le : Scalar → Scalar → Type u
  subtract : Scalar → Scalar → Scalar
  subtractLowerBound : ∀ {δ d correction η},
    le δ d → le correction η → le η δ →
      le (subtract δ η) (subtract d correction)

/-- Quantitative block-Schur hypotheses. -/
structure QuantitativeBlockSchur (Vector : Type u) (Scalar : Type v)
    (O : SchurOrderLaws Scalar) where
  dBlock : Vector → Vector
  crossCorrection : Vector → Vector
  schurComplement : Vector → Vector
  inner : Vector → Vector → Scalar
  highGap : Scalar
  crossBudget : Scalar
  schurQuadraticIdentity : ∀ x,
    inner x (schurComplement x) =
      O.subtract (inner x (dBlock x)) (inner x (crossCorrection x))
  highBlockCoercive : ∀ x, O.le highGap (inner x (dBlock x))
  crossCorrectionBounded : ∀ x, O.le (inner x (crossCorrection x)) crossBudget
  crossBelowHighGap : O.le crossBudget highGap

/-- The quantitative Schur lower bound follows directly from the supplied
ordered-subtraction law and block estimates. -/
def schurCoercive {Vector : Type u} {Scalar : Type v}
    (O : SchurOrderLaws Scalar) (Q : QuantitativeBlockSchur Vector Scalar O)
    (x : Vector) :
    O.le (O.subtract Q.highGap Q.crossBudget)
      (Q.inner x (Q.schurComplement x)) := by
  rw [Q.schurQuadraticIdentity]
  exact O.subtractLowerBound (Q.highBlockCoercive x)
    (Q.crossCorrectionBounded x) Q.crossBelowHighGap

/-- Explicit strictness receipt for the residual Schur gap. -/
structure StrictSchurGap {Vector : Type u} {Scalar : Type v}
    (O : SchurOrderLaws Scalar) (Q : QuantitativeBlockSchur Vector Scalar O) where
  StrictlyPositive : Scalar → Type v
  residualGapPositive : StrictlyPositive (O.subtract Q.highGap Q.crossBudget)

/-- Bundled strict gap and proved lower bound. -/
structure QuantitativeSchurCertificate {Vector : Type u} {Scalar : Type v}
    (O : SchurOrderLaws Scalar) (Q : QuantitativeBlockSchur Vector Scalar O) where
  strictGap : StrictSchurGap O Q
  lowerBound : ∀ x, O.le (O.subtract Q.highGap Q.crossBudget)
    (Q.inner x (Q.schurComplement x))

/-- Package the structural Schur proof with a separately supplied strict gap. -/
def certifyQuantitativeSchur {Vector : Type u} {Scalar : Type v}
    (O : SchurOrderLaws Scalar) (Q : QuantitativeBlockSchur Vector Scalar O)
    (gap : StrictSchurGap O Q) : QuantitativeSchurCertificate O Q where
  strictGap := gap
  lowerBound := schurCoercive O Q

/-! ## Hodge–Poincaré coercivity surface -/

/-- Abstract ordered additive energy socket. -/
structure OrderedEnergy (Scalar : Type u) where
  le : Scalar → Scalar → Type u
  add : Scalar → Scalar → Scalar
  reflexive : ∀ value, le value value
  transitive : ∀ {a b c}, le a b → le b c → le a c
  addMonotoneRight : ∀ fixed {a b}, le a b → le (add fixed a) (add fixed b)

/-- Curl, divergence, and average contributions to gauge-fixed energy. -/
def gaugeFixedEnergy {Scalar : Type u} (order : OrderedEnergy Scalar)
    (curlEnergy divergenceEnergy averageEnergy : Scalar) : Scalar :=
  order.add curlEnergy (order.add divergenceEnergy averageEnergy)

/-- Replace the locally controlled mean energy by its average-energy bound. -/
def blockHodgePoincareFromLocal {Scalar : Type u}
    (order : OrderedEnergy Scalar)
    (normEnergy differentialEnergy meanEnergy averageEnergy : Scalar)
    (localOscillation : order.le normEnergy (order.add differentialEnergy meanEnergy))
    (meanControlled : order.le meanEnergy averageEnergy) :
    order.le normEnergy (order.add differentialEnergy averageEnergy) :=
  order.transitive localOscillation
    (order.addMonotoneRight differentialEnergy meanControlled)

/-- Gauge-fixed block Hodge–Poincaré data.  The inequality is an explicit
field supplied by the finite analysis. -/
structure GaugeFixedBlockHodgePoincare (Vector : Type u) (Scalar : Type v)
    (order : OrderedEnergy Scalar) where
  normSquared : Vector → Scalar
  curlEnergy : Vector → Scalar
  divergenceEnergy : Vector → Scalar
  averageEnergy : Vector → Scalar
  constantWeightedEnergy : Vector → Scalar
  weightedEnergyDefinition : ∀ vector,
    constantWeightedEnergy vector = gaugeFixedEnergy order
      (curlEnergy vector) (divergenceEnergy vector) (averageEnergy vector)
  hodgePoincare : ∀ vector, order.le (normSquared vector) (constantWeightedEnergy vector)

/-- Zero-background coercivity interface. -/
structure ZeroBackgroundCoercivity (Vector : Type u) (Scalar : Type v)
    (order : OrderedEnergy Scalar) where
  normSquared : Vector → Scalar
  hessianEnergy : Vector → Scalar
  coercive : ∀ vector, order.le (normSquared vector) (hessianEnergy vector)

/-- Transport a Hodge–Poincaré bound across an explicitly supplied energy
identity. -/
def hodgePoincareGivesZeroBackgroundCoercivity
    {Vector : Type u} {Scalar : Type v} (order : OrderedEnergy Scalar)
    (hodge : GaugeFixedBlockHodgePoincare Vector Scalar order)
    (hessianEnergy : Vector → Scalar)
    (energyIdentity : ∀ vector,
      hessianEnergy vector = hodge.constantWeightedEnergy vector) :
    ZeroBackgroundCoercivity Vector Scalar order where
  normSquared := hodge.normSquared
  hessianEnergy := hessianEnergy
  coercive := fun vector => order.transitive (hodge.hodgePoincare vector) (by
    rw [energyIdentity vector]
    exact order.reflexive _)

/-- Compose base coercivity, perturbative comparison, and loss absorption. -/
def backgroundCoercivityFromPerturbation {Scalar : Type u}
    (order : OrderedEnergy Scalar)
    (norm baseEnergy backgroundEnergy loss absorbedEnergy : Scalar)
    (baseCoercive : order.le norm baseEnergy)
    (perturbationComparison : order.le baseEnergy (order.add backgroundEnergy loss))
    (lossAbsorbed : order.le (order.add backgroundEnergy loss) absorbedEnergy) :
    order.le norm absorbedEnergy :=
  order.transitive baseCoercive (order.transitive perturbationComparison lossAbsorbed)

/-! ## Stable projection names -/

/-- Stable name for the constraint average. -/
def constraintAverage {Fine : Type u} {Coarse : Type v}
    (data : ConstrainedMinimizerData Fine Coarse) : Fine → Coarse := data.average

/-- Stable name for the ordered-energy relation. -/
def orderedEnergyLeq {Scalar : Type u} (order : OrderedEnergy Scalar) :
    Scalar → Scalar → Type u := order.le

/-- Stable name for the Hodge norm square. -/
def hodgeNormSquared {Vector : Type u} {Scalar : Type v}
    {order : OrderedEnergy Scalar}
    (H : GaugeFixedBlockHodgePoincare Vector Scalar order) : Vector → Scalar :=
  H.normSquared

/-- Stable name for the constant-weighted Hodge energy. -/
def hodgeWeightedEnergy {Vector : Type u} {Scalar : Type v}
    {order : OrderedEnergy Scalar}
    (H : GaugeFixedBlockHodgePoincare Vector Scalar order) : Vector → Scalar :=
  H.constantWeightedEnergy

/-- Stable projection of the Hodge–Poincaré inequality field. -/
def hodgeControlsNorm {Vector : Type u} {Scalar : Type v}
    {order : OrderedEnergy Scalar}
    (H : GaugeFixedBlockHodgePoincare Vector Scalar order) (vector : Vector) :
    orderedEnergyLeq order (hodgeNormSquared H vector) (hodgeWeightedEnergy H vector) :=
  H.hodgePoincare vector

end AgdaMirror.FiniteOperatorReductionCore
