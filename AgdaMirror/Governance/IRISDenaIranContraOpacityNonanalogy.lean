import AgdaMirror.Governance.IranContraCovertFlowHistoricalMechanism
import AgdaMirror.Governance.IRISDenaPublicRecordCeilingAndFOI

namespace AgdaMirror.Governance.IRISDenaIranContraOpacityNonanalogy

open AgdaMirror.Governance.IranContraCovertFlowHistoricalMechanism
open AgdaMirror.Governance.IRISDenaPublicRecordCeilingAndFOI

inductive OperationalKnowledgeState
  | documentedPolicyOperationalDivergence
  | publicRecordIncomplete
  | exactOperationalRecordPaid
  deriving DecidableEq, Repr

structure CurrentOpacityWitness where
  state : OperationalKnowledgeState
  ceiling : PublicRecordCeiling
  missingObjectRef : String
  publicRecordIncompletePaid : Bool := true
  policyOperationalDivergencePaid : Bool := false
  covertRoutingPaid : Bool := false

def irisOpacityWitness : CurrentOpacityWitness :=
  ⟨.publicRecordIncomplete,canonicalPublicRecordCeiling,
   "proof Hansard / watchbill / embedding protocol / action log"⟩

theorem opacity_is_not_covert_divergence :
    irisOpacityWitness.policyOperationalDivergencePaid = false ∧
    irisOpacityWitness.covertRoutingPaid = false := by
  decide

end AgdaMirror.Governance.IRISDenaIranContraOpacityNonanalogy
