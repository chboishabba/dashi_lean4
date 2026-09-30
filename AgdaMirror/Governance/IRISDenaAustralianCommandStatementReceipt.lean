namespace AgdaMirror.Governance.IRISDenaAustralianCommandStatementReceipt

inductive CommandClaimKind
  | personnelPresent
  | noOffensiveParticipation
  | notOrderedToBunks
  | dutiesUnderEmbeddingAgreement
  | exactDutyReconstruction
  deriving DecidableEq, Repr

structure CommandStatementReceipt where
  claimKind : CommandClaimKind
  sourceRef : String
  boundedReading : String
  commandLevelPrimarySource : Bool := true
  independentlyReconstructsOperationalLog : Bool := false

def presenceReceipt : CommandStatementReceipt :=
  ⟨.personnelPresent,
   "Prime Minister of Australia, Sky Newsday, 2026-03-06",
   "Albanese confirms three Australian personnel were aboard the U.S. submarine."⟩

def nonParticipationReceipt : CommandStatementReceipt :=
  ⟨.noOffensiveParticipation,
   "Prime Minister of Australia, Sky Newsday, 2026-03-06",
   "Albanese states no Australian personnel participated in offensive action against Iran."⟩

def notBunksReceipt : CommandStatementReceipt :=
  ⟨.notOrderedToBunks,
   "Defence Ministers press conference, 2026-03-21",
   "Chief of Navy rejects the claim that the Australian submariners were ordered to their bunks."⟩

def embeddingProtocolReceipt : CommandStatementReceipt :=
  ⟨.dutiesUnderEmbeddingAgreement,
   "Defence Ministers press conference, 2026-03-21",
   "Chief of Navy and Defence Minister say the sailors operated under embedding protocols aligned with Australian policy."⟩

structure OperationalResidual where
  residualRef : String
  requiredObject : String
  reason : String
  publicCommandStatementsInsufficient : Bool := true

def exactDutyResidual : OperationalResidual :=
  ⟨"residual:iris-dena:exact-duty-reconstruction",
   "operational action log, watch/duty record, embedding protocol text, or another independently reviewable same-object record",
   "public command statements narrow presence/participation but explicitly withhold operational detail"⟩

end AgdaMirror.Governance.IRISDenaAustralianCommandStatementReceipt
