import AgdaMirror.Cognition.PNF.SensibLawITIRNarrativeComparisonTransport
import AgdaMirror.Governance.FriendlyjordiesNarrativeGovernanceTransport

namespace AgdaMirror.Interop.SLRGWBNarrativeGovernancePacketBridge

open AgdaMirror.Cognition.PNF.SensibLawITIRNarrativeComparisonTransport
open AgdaMirror.Governance.FriendlyjordiesNarrativeGovernanceTransport

structure WorldNarrativeGovernancePacket where
  candidateWorldPaid : Bool
  sourceRolesPaid : Bool
  reviewedEventJoinPaid : Bool
  chronologyPaid : Bool
  causalLinkProvenancePaid : Bool
  missingnessRetained : Bool
  governanceTrajectoryClosed : Bool
  worldTruthPromoted : Bool
  sourceNarrativesMerged : Bool
  narrativeComparison : NarrativeComparison
  governanceWitness : GovernanceWitness

def friendlyjordiesGWBPacket : WorldNarrativeGovernancePacket :=
  ⟨true, true, false, false, true, true, false, false, false,
   canonicalFriendlyjordiesComparison, friendlyjordiesGovernanceWitness⟩

theorem packet_is_fail_closed :
    friendlyjordiesGWBPacket.reviewedEventJoinPaid = false ∧
    friendlyjordiesGWBPacket.chronologyPaid = false ∧
    friendlyjordiesGWBPacket.governanceTrajectoryClosed = false ∧
    friendlyjordiesGWBPacket.worldTruthPromoted = false ∧
    friendlyjordiesGWBPacket.sourceNarrativesMerged = false := by
  decide

end AgdaMirror.Interop.SLRGWBNarrativeGovernancePacketBridge
