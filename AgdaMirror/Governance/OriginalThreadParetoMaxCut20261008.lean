import AgdaMirror.Governance.IRISDenaSameObjectAcquisitionMaxCut
import AgdaMirror.Governance.AUKUSEmbeddedAuthorityCommandNoncollapse
import AgdaMirror.Governance.AUKUSPersonnelExchangeMOUExistence
import AgdaMirror.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelope
import AgdaMirror.Governance.IRISDenaMinisterialBriefingFOIBoundary
import AgdaMirror.Governance.IRISDenaBunkClaimRevisionConflict
import AgdaMirror.Governance.IRISDenaPublicRecordConsumerNonDescent
import AgdaMirror.Governance.IRISDenaCorrectionAwareReviewGate

namespace AgdaMirror.Governance.OriginalThreadParetoMaxCut20261008

inductive LiveRequirement
  | irisCorrectionAwareHansardContent
  | irisEmbeddingProtocolOperativeText
  | irisExactOperationalRecord
  | iranMarginalRepressionIncrement
  | broadHistoricalExpansion
  deriving DecidableEq, Repr

structure ParetoCell where
  requirement : LiveRequirement
  requiredForConsumer : Bool
  admissible : Bool
  splitsLiveFibre : Bool
  cost : Nat
  certifiedGain : Nat
  onFrontier : Bool
  reference : String


def hansardContentCell : ParetoCell :=
  ⟨.irisCorrectionAwareHansardContent, true, true, true, 1, 5, true,
   "Acquire transcript 29619 pp. 49-52 plus applicable Chief-of-Navy correction, resolve correction applicability, and bind exact review to the same duty-class proposition before promotion."⟩

def embeddingProtocolCell : ParetoCell :=
  ⟨.irisEmbeddingProtocolOperativeText, true, true, true, 2, 6, true,
   "Acquire complete 2024 Chief-of-Navy directive plus operative bilateral MOU text/annexes. Generic US PEP statutory/program authority, Australia-partner status and MOU existence/purpose are already paid at their own source roles."⟩

def exactOperationalCell : ParetoCell :=
  ⟨.irisExactOperationalRecord, true, true, true, 5, 8, true,
   "Acquire watchbill/duty assignment, action log, debrief or equivalent same-episode record; public, duty-class and protocol observers do not determine exact task."⟩

def iranMarginalCell : ParetoCell :=
  ⟨.iranMarginalRepressionIncrement, true, true, true, 5, 5, false,
   "Required but currently dominated by the three IRIS same-object acquisition cells."⟩

def broadExpansionCell : ParetoCell :=
  ⟨.broadHistoricalExpansion, false, true, false, 5, 2, false,
   "Deferred until live same-object IRIS acquisition is paid or acquisition-blocked."⟩

theorem live_frontier_is_three_stage_iris :
    hansardContentCell.onFrontier = true ∧
    embeddingProtocolCell.onFrontier = true ∧
    exactOperationalCell.onFrontier = true ∧
    iranMarginalCell.onFrontier = false ∧
    broadExpansionCell.onFrontier = false := by
  decide

-- Paid substructure does not replace the live frontier.
def usPEPAuthorityEnvelope :=
  AgdaMirror.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelope.canonicalEnvelope

def bunkClaimRevision :=
  AgdaMirror.Governance.IRISDenaBunkClaimRevisionConflict.canonicalRevision

def correctionAwareReviewDemand :=
  AgdaMirror.Governance.IRISDenaCorrectionAwareReviewGate.canonicalReviewDemand

theorem paid_substructure_does_not_close_live_cells :
    usPEPAuthorityEnvelope.bilateralMOUOperativeTextPaid = false ∧
    usPEPAuthorityEnvelope.irisSameEpisodeDutyPaid = false ∧
    bunkClaimRevision.exactDutyDisclosedByDenial = false ∧
    correctionAwareReviewDemand.exactReviewBindingPaid = false ∧
    correctionAwareReviewDemand.dutyClassPromotionPaid = false := by
  decide

end AgdaMirror.Governance.OriginalThreadParetoMaxCut20261008
