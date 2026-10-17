import Mathlib
import AgdaMirror.SeaMeInItPhysicalSuitClosure

/-!
# Lean parity mirror for adaptive-suit deployment authority

This mirrors the authority-bearing part of
`DASHI.Interop.SeaMeInItAdaptiveSuitClosure`: physical ROM validation may
license testing of adaptive hardware; adaptive hardware tests may license
controller validation; controller validation still does not synthesize external
field-deployment authority.
-/

namespace AgdaMirror.SeaMeInItAdaptiveSuitClosure

open AgdaMirror.SeaMeInItPhysicalSuitClosure

structure AdaptiveModuleBoundary where
  physicalROMPromoted : Bool
  moduleInventoryGate : TriGate
  commandEnvelopeGate : TriGate
  failSafeGate : TriGate
  powerBudgetGate : TriGate
  evidenceGate : TriGate

/-- Adaptive hardware authority requires the upstream physical receipt and all
module-specific empirical gates. -/
def AdaptiveModuleBoundary.promotable (r : AdaptiveModuleBoundary) : Prop :=
  r.physicalROMPromoted = true ∧
  r.moduleInventoryGate = .admissible ∧
  r.commandEnvelopeGate = .admissible ∧
  r.failSafeGate = .admissible ∧
  r.powerBudgetGate = .admissible ∧
  r.evidenceGate = .admissible

structure ControllerSafetyBoundary where
  adaptiveModulePromoted : Bool
  scenarioCoverageGate : TriGate
  hardViolationGate : TriGate
  latencyGate : TriGate
  emergencyStopGate : TriGate
  controllerEvidenceGate : TriGate

/-- Controller authority is a distinct empirical boundary. -/
def ControllerSafetyBoundary.promotable (r : ControllerSafetyBoundary) : Prop :=
  r.adaptiveModulePromoted = true ∧
  r.scenarioCoverageGate = .admissible ∧
  r.hardViolationGate = .admissible ∧
  r.latencyGate = .admissible ∧
  r.emergencyStopGate = .admissible ∧
  r.controllerEvidenceGate = .admissible

structure SuitDeploymentBoundary where
  controllerPromoted : Bool
  deploymentProfileGate : TriGate
  deploymentEvidenceGate : TriGate
  /-- Deliberately supplied from outside the proof/test chain. -/
  externalAuthorityReviewGate : TriGate
  claimBoundaryGate : TriGate

/-- Field deployment requires a separate external authority gate. -/
def SuitDeploymentBoundary.promotable (r : SuitDeploymentBoundary) : Prop :=
  r.controllerPromoted = true ∧
  r.deploymentProfileGate = .admissible ∧
  r.deploymentEvidenceGate = .admissible ∧
  r.externalAuthorityReviewGate = .admissible ∧
  r.claimBoundaryGate = .admissible

/-- Even a controller-promoted boundary with all local deployment evidence
cannot promote while external review remains diagnostic. -/
theorem diagnostic_external_review_blocks_deployment
    (r : SuitDeploymentBoundary)
    (_hcontroller : r.controllerPromoted = true)
    (_hprofile : r.deploymentProfileGate = .admissible)
    (_hevidence : r.deploymentEvidenceGate = .admissible)
    (hreview : r.externalAuthorityReviewGate = .diagnostic)
    (_hclaim : r.claimBoundaryGate = .admissible) :
    ¬ r.promotable := by
  intro h
  rcases h with ⟨_, _, _, hreviewAdmissible, _⟩
  rw [hreview] at hreviewAdmissible
  cases hreviewAdmissible

/-- A constructor with diagnostic external review makes the non-derivability
of field authority explicit even when every local value is caller-selected. -/
def diagnosticReviewBoundary
    (controllerPromoted : Bool)
    (profileGate evidenceGate claimGate : TriGate) : SuitDeploymentBoundary :=
  { controllerPromoted := controllerPromoted
    deploymentProfileGate := profileGate
    deploymentEvidenceGate := evidenceGate
    externalAuthorityReviewGate := .diagnostic
    claimBoundaryGate := claimGate }

/-- Local controller/profile/evidence choices cannot synthesize an admissible
external review gate. -/
theorem local_success_cannot_synthesize_external_review
    (controllerPromoted : Bool)
    (profileGate evidenceGate claimGate : TriGate) :
    ¬ (diagnosticReviewBoundary
        controllerPromoted profileGate evidenceGate claimGate).promotable := by
  intro h
  rcases h with ⟨_, _, _, hreview, _⟩
  cases hreview

end AgdaMirror.SeaMeInItAdaptiveSuitClosure
