import YMSourceAuthoritySurface

/-! Lean mirror of the Yang–Mills proof-target inventory surface. -/
namespace AgdaMirror.Physics.YangMills.ProofTargetSurface

open YMSourceAuthoritySurface

abbrev ProofStatus := VerificationStatus

def proofStatusLabel : ProofStatus → String
  | .proved => "proved"
  | .standardWrapper => "standard-wrapper"
  | .paperImport => "paper-import"
  | .auditTested => "audit-tested"
  | .openTarget => "open"
  | .mixedReducer => "mixed-reducer"
  | .provedConditionalReducer => "proved-conditional-reducer"

def surfaceClosed : ProofStatus → Bool
  | .openTarget => false
  | _ => true

/-- Descriptive inventory record; no theorem is proved merely by constructing it. -/
structure ProofTargetSurface where
  lemmaName : String
  sourceReference : String
  exactStatement : String
  assumptions : String
  outputConclusion : String
  consumingGate : String
  failureConsequence : String
  status : ProofStatus
  sourceAuthorityId : SourceAuthorityId
  theoremLocator : String
  claimRole : ClaimRole
  verificationStatus : VerificationStatus
  noClayPromotion : clayYangMillsPromoted = false

def proofTargetIsClosed (target : ProofTargetSurface) : Bool :=
  surfaceClosed target.status

def mkProofTargetSurfaceWithAuthority
    (lemmaName sourceReference exactStatement assumptions outputConclusion
      consumingGate failureConsequence : String)
    (status : ProofStatus) (sourceId : SourceAuthorityId) (locator : String)
    (role : ClaimRole) (vStatus : VerificationStatus) : ProofTargetSurface :=
  { lemmaName, sourceReference, exactStatement, assumptions, outputConclusion,
    consumingGate, failureConsequence, status, sourceAuthorityId := sourceId,
    theoremLocator := locator, claimRole := role, verificationStatus := vStatus,
    noClayPromotion := rfl }

def mkProofTargetSurface
    (lemmaName sourceReference exactStatement assumptions outputConclusion
      consumingGate failureConsequence : String) (status : ProofStatus) :
    ProofTargetSurface :=
  mkProofTargetSurfaceWithAuthority lemmaName sourceReference exactStatement
    assumptions outputConclusion consumingGate failureConsequence status
    .unknownAuthority "" .postulateImport status

end AgdaMirror.Physics.YangMills.ProofTargetSurface
