namespace Synthesis.JacobsonNullConeRecovery

universe u v w

/-- A field-equation defect whose quadratic contraction vanishes on every
selected null direction.  The carrier remains abstract: physical stress tensor,
continuum geometry, and Jacobson thermodynamics are separate payments. -/
structure NullContractedFieldRelation
    (Tensor : Type u) (NullDirection : Type v) (Scalar : Type w) where
  zero : Scalar
  defect : Tensor
  nullContraction : Tensor → NullDirection → Scalar
  allNullDirections : ∀ k, nullContraction defect k = zero

/-- Geometric rigidity payment: tensors invisible on every null direction are
metric multiples.  A concrete Lorentzian carrier must prove this theorem. -/
structure NullConeTensorRigidity
    {Tensor : Type u} {NullDirection : Type v} {Scalar : Type w}
    (R : NullContractedFieldRelation Tensor NullDirection Scalar) where
  MetricCoefficient : Type u
  metricMultiple : MetricCoefficient → Tensor
  rigidity : ∀ candidate : Tensor,
    (∀ k : NullDirection, R.nullContraction candidate k = R.zero) →
    ∃ coefficient : MetricCoefficient, candidate = metricMultiple coefficient

/-- The tensor equation recovered from the null-contracted relation is only
fixed modulo a pure metric term, i.e. the cosmological coefficient. -/
structure TensorEquationModuloMetric
    {Tensor : Type u} {NullDirection : Type v} {Scalar : Type w}
    (R : NullContractedFieldRelation Tensor NullDirection Scalar)
    (G : NullConeTensorRigidity R) where
  cosmologicalCoefficient : G.MetricCoefficient
  tensorEquation : R.defect = G.metricMultiple cosmologicalCoefficient

/-- Exact compiler: once null-cone rigidity is paid, the all-null relation
recovers the tensor equation modulo the metric term. -/
theorem recoverTensorEquationModuloMetric
    {Tensor : Type u} {NullDirection : Type v} {Scalar : Type w}
    (R : NullContractedFieldRelation Tensor NullDirection Scalar)
    (G : NullConeTensorRigidity R) :
    TensorEquationModuloMetric R G := by
  rcases G.rigidity R.defect R.allNullDirections with ⟨coefficient, h⟩
  exact ⟨coefficient, h⟩

/-- A concrete null metric makes the metric-multiple term invisible to the
preceding null-contracted equation. -/
structure MetricNullInvisibility
    {Tensor : Type u} {NullDirection : Type v} {Scalar : Type w}
    (R : NullContractedFieldRelation Tensor NullDirection Scalar)
    (G : NullConeTensorRigidity R) where
  metricMultipleNull : ∀ coefficient : G.MetricCoefficient,
    ∀ k : NullDirection,
      R.nullContraction (G.metricMultiple coefficient) k = R.zero

-- Promotion/status boundary.  These are intentionally boring Booleans so
-- downstream status surfaces cannot confuse the compiler with its premises.
def tensorRecoveryCompilerOwned : Bool := true
def nullConeRigidityStillRequired : Bool := true
def stressEnergySameObjectStillRequired : Bool := true
def unruhClausiusStillRequired : Bool := true
def continuumRaychaudhuriStillRequired : Bool := true
def nullRelationAloneDoesNotFixCosmologicalTerm : Bool := true

end Synthesis.JacobsonNullConeRecovery
