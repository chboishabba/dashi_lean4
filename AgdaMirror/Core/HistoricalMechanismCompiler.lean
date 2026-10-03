namespace AgdaMirror.Core.HistoricalMechanismCompiler

structure SourceTotalReceipt where
  packetRef : String
  allConsumedClaimsDisposed : Bool := true
  orphanClaimsAdmitted : Bool := false

structure ReviewedJoinReceipt where
  joinRef : String
  leftClaimRef : String
  rightClaimRef : String
  joinBasisRef : String
  reviewed : Bool := true
  mergesNarratives : Bool := false

structure DualChronologyReceipt where
  chronologyRef : String
  eventTimeRef : String
  knowledgeTimeRef : String
  eventAndKnowledgeTimeCollapsed : Bool := false

structure CausalMechanismReceipt where
  mechanismRef : String
  causeClaimRef : String
  effectClaimRef : String
  counterHypothesisRef : String
  provenanceRef : String
  reviewed : Bool := true
  sourceAdjacencyUsedAsCausation : Bool := false

structure HistoricalMechanismWitness where
  witnessRef : String
  sourceTotal : SourceTotalReceipt
  reviewedJoin : ReviewedJoinReceipt
  chronology : DualChronologyReceipt
  causalMechanism : CausalMechanismReceipt
  createsPoliticalVerdict : Bool := false
  createsUniversalRanking : Bool := false

inductive MechanismResidualKind
  | sourceTotalityResidual | reviewedJoinResidual | chronologyResidual | causalMechanismResidual
  deriving DecidableEq, Repr

structure MechanismResidual where
  kind : MechanismResidualKind
  residualRef : String
  requiredEvidence : String
  acquisitionHint : String
  mayPromoteTruth : Bool := false

inductive MechanismCompilation
  | closed (witness : HistoricalMechanismWitness)
  | abstain (residuals : List MechanismResidual)

def compileHistoricalMechanism
    (ref : String)
    (s : SourceTotalReceipt)
    (j : ReviewedJoinReceipt)
    (t : DualChronologyReceipt)
    (c : CausalMechanismReceipt) : HistoricalMechanismWitness :=
  ⟨ref,s,j,t,c⟩

end AgdaMirror.Core.HistoricalMechanismCompiler
