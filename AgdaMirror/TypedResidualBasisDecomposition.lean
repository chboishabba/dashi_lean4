import Mathlib

/-!
# Lean mirror of `DASHI/Core/TypedResidualBasisDecomposition.agda`
(faithful protocol + genuine decision lemmas)

The Typed Residual Basis Decomposition (TRBD) protocol: typed basis provenance,
frozen numeric receipt strings, obstruction status, and a promotion boundary.
The genuine content is the *decision logic*: which obstruction statuses are
promotion-eligible (`TRBDPromotionEligible`) and which basis sources are
non-fitted (`NotFittedBasisSource`).  We prove that a `PromotableTRBDReceipt`
can never carry a partial or untyped obstruction, and that a derived (promotable)
receipt's basis is never the fitted basis.
-/

namespace AgdaMirror.TypedResidualBasisDecomposition

/-- The provenance of a typed basis. -/
inductive BasisSourceType where
  | causalBasis | structuralBasis | symmetryBasis | mdlBasis | fittedBasis
deriving DecidableEq

/-- A basis source is "not fitted" unless it is the fitted basis. -/
def NotFittedBasisSource : BasisSourceType → Prop
  | .fittedBasis => False
  | _ => True

abbrev BasisName := String

/-- A typed basis with provenance. -/
structure TypedBasis (X : Type) where
  basisName : BasisName
  basisVectors : List X
  basisSource : BasisSourceType
  notFitted : NotFittedBasisSource basisSource
  basisSourceDescription : String
  basisPromotionBoundary : List String

/-- The obstruction status of a residual diagnostic. -/
inductive ObstructionStatus where
  | pass
  | obstructionTypedClean (name : BasisName)
  | obstructionTypedPartial (name : BasisName)
  | obstructionUntyped

/-- Which obstruction statuses are promotion-eligible. -/
def TRBDPromotionEligible : ObstructionStatus → Prop
  | .pass => True
  | .obstructionTypedClean _ => True
  | .obstructionTypedPartial _ => False
  | .obstructionUntyped => False

/-- Frozen protocol thresholds. -/
structure TRBDProtocolThresholds where
  coverageThresholdName : String
  coverageThreshold : String
  perpendicularThresholdName : String
  perpendicularThreshold : String
  thresholdFrozen : Bool
  thresholdFrozenIsTrue : thresholdFrozen = true

/-- A full TRBD receipt. -/
structure TRBDReceipt (X : Type) where
  observed : X
  predicted : X
  residualConvention : String
  metricOrCovariance : String
  basis : TypedBasis X
  basisCoefficients : List String
  rawChi2PerDof : String
  perpendicularChi2PerDof : String
  basisCoverage : String
  basisCoverageFormula : String
  coverageHonest : basisCoverageFormula = "rho_B = 1 - (perpendicular chi2 / raw chi2)"
  thresholds : TRBDProtocolThresholds
  obstructionStatus : ObstructionStatus
  projectionArtifact : String
  diagnosticOnly : Bool
  promotionBoundary : List String

/-- A promotable TRBD receipt: promotion-eligible status, derived basis, and not
diagnostic-only. -/
structure PromotableTRBDReceipt (X : Type) where
  receipt : TRBDReceipt X
  statusPromotable : TRBDPromotionEligible receipt.obstructionStatus
  derivedBasis : NotFittedBasisSource receipt.basis.basisSource
  diagnosticOnlyIsFalse : receipt.diagnosticOnly = false

/-! ### Genuine decision lemmas -/

/-- A promotable receipt never carries a partial obstruction. -/
theorem promotable_not_partial {X : Type} (r : PromotableTRBDReceipt X) (n : BasisName) :
    r.receipt.obstructionStatus ≠ ObstructionStatus.obstructionTypedPartial n := by
  intro h
  have := r.statusPromotable
  rw [h] at this
  exact this

/-- A promotable receipt never carries an untyped obstruction. -/
theorem promotable_not_untyped {X : Type} (r : PromotableTRBDReceipt X) :
    r.receipt.obstructionStatus ≠ ObstructionStatus.obstructionUntyped := by
  intro h
  have := r.statusPromotable
  rw [h] at this
  exact this

/-- A promotable receipt's basis is never the fitted basis. -/
theorem promotable_basis_not_fitted {X : Type} (r : PromotableTRBDReceipt X) :
    r.receipt.basis.basisSource ≠ BasisSourceType.fittedBasis := by
  intro h
  have := r.derivedBasis
  rw [h] at this
  exact this

/-- `pass` is always promotion-eligible. -/
theorem pass_promotable : TRBDPromotionEligible ObstructionStatus.pass := trivial

end AgdaMirror.TypedResidualBasisDecomposition
