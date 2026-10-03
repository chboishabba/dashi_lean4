namespace AgdaMirror.Governance.MostazafinRepresentedConstituencyDivergence

inductive RepresentedLayer
  | revolutionarySubject
  | constitutionalForeignPolicySubject
  | charitableInstitutionName
  | securityInstitutionName
  | empiricalLabourCohort
  | empiricalProtestCohort
  deriving DecidableEq, Repr

inductive OverlapStatus
  | noIdentityClaim
  | candidateOverlapRequiresCaseEvidence
  | caseSpecificOverlapPaid
  deriving DecidableEq, Repr

structure RepresentedConstituencyReceipt where
  layer : RepresentedLayer
  sourceRef : String
  boundedReading : String
  sourcePaid : Bool := true
  equalsEveryWorker : Bool := false
  equalsEveryProtester : Bool := false

structure StateActionDivergenceCandidate where
  representedReceipt : RepresentedConstituencyReceipt
  empiricalCohortRef : String
  stateActionRef : String
  overlapStatus : OverlapStatus
  institutionalVocabularyPersists : Bool := true
  repressionDocumented : Bool := true
  samePersonsProved : Bool := false
  semanticParadoxClosed : Bool := false

def ideologicalMostazafin : RepresentedConstituencyReceipt :=
  ⟨.revolutionarySubject,
   "Glombitza 2026",
   "Shariati globalised mostazafin and Khomeini institutionalised oppressed-versus-oppressor grammar."⟩

def labourDivergenceCandidate : StateActionDivergenceCandidate :=
  ⟨ideologicalMostazafin,
   "HRW 2022 labor activists/workers",
   "HRW 2022 repression/prosecution of labor activists",
   .candidateOverlapRequiresCaseEvidence⟩

theorem divergence_is_not_identity :
    labourDivergenceCandidate.samePersonsProved = false ∧
    labourDivergenceCandidate.semanticParadoxClosed = false := by
  decide

end AgdaMirror.Governance.MostazafinRepresentedConstituencyDivergence
