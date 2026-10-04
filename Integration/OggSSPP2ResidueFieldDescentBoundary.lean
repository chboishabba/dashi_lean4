import Mathlib
import Integration.OggSSPP2ExplicitF2CurveCandidate
import Integration.OggSSPP2ConcreteF2UniversalDeformationRecognition

/-!
# p=2 residue-field descent boundary

The current Lean branch has no theorem-bearing explicit supersingular elliptic
curve model over F2 and no base-change/descent theorem identifying the generic
source universal deformation over W(k)[[t]] with the concrete F2-specialized
carrier already constructed in this branch.

Accordingly, the F2 Witt base is retained as a candidate specialization only.
-/

namespace Integration.OggSSPP2ResidueFieldDescentBoundary

inductive Residual
  | missingExplicitSupersingularCurveModelOverF2
  | missingGeometricSupersingularityIdentification
  | missingUniversalDeformationBaseChangeDescent
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingGeometricSupersingularityIdentification

structure Boundary where
  explicitSupersingularCurveModelOverF2Owned : Bool
  geometricSupersingularityIdentificationOwned : Bool
  universalDeformationDescentToF2Owned : Bool
  combinedConcreteF2SourceRecognitionContractOwned : Bool
  f2WittBaseRemainsSpecializationOnly : Bool
  firstResidualIsGeometricSupersingularityIdentification : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitSupersingularCurveModelOverF2Owned := true
  geometricSupersingularityIdentificationOwned := false
  universalDeformationDescentToF2Owned := false
  combinedConcreteF2SourceRecognitionContractOwned := true
  f2WittBaseRemainsSpecializationOnly := true
  firstResidualIsGeometricSupersingularityIdentification := true

end Integration.OggSSPP2ResidueFieldDescentBoundary
