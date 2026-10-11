import Dashi.Biology.QuailEggIBSTransferLadderExact

namespace Dashi.Biology.QuailEggIBSTransferLadderRegression
open Dashi.Biology.QuailEggIBSTransferLadderExact

example : QuailEggIBSTransferLadder := canonicalQuailEggIBSTransferLadder
example : canonicalHumanIBSQuailTerminalReceipt.terminalClosed = false := by rfl
example : humanIBSQuailStageReceipt.status = .openTerminal := by rfl
example : canonicalQuailEggIBSTransferLadder.ibsQuailStage.status = .openTerminal := by rfl
example : canonicalQuailEggIBSTransferLadderBoundary.quailSpecificHumanIBSTerminalClosed = false := by rfl
example : AdjacentEvidenceClosesHumanIBSPermission → False := adjacentEvidenceDoesNotCloseHumanIBS

end Dashi.Biology.QuailEggIBSTransferLadderRegression
