import AgdaMirror.Governance.IRISDenaSameObjectAcquisitionMaxCut

namespace AgdaMirror.Governance.OriginalThreadParetoMaxCut20261008

inductive LiveRequirement
  | irisCorrectionAwareHansardContent
  | irisEmbeddingProtocolText
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
   "Read transcript 29619 pp. 49-52 plus applicable Chief-of-Navy correction before promoting duty-class content."⟩

def embeddingProtocolCell : ParetoCell :=
  ⟨.irisEmbeddingProtocolText, true, true, true, 3, 6, true,
   "Acquire the actual Australian-US embedding protocol for third-party hostilities."⟩

def exactOperationalCell : ParetoCell :=
  ⟨.irisExactOperationalRecord, true, true, true, 5, 8, true,
   "Acquire watchbill/duty assignment, action log, debrief or equivalent same-episode record."⟩

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

end AgdaMirror.Governance.OriginalThreadParetoMaxCut20261008
