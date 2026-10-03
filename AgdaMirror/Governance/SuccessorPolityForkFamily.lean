namespace AgdaMirror.Governance.SuccessorPolityForkFamily

inductive ForkMechanism
  | civilWarRivalGovernmentFork
  | foreignOccupationColdWarFork
  | ceasefireProvisionalPartitionFork
  | negotiatedConstitutionalPartitionFork
  | ideologicalBlocDivisionFork
  deriving DecidableEq, Repr

inductive ResolutionMode
  | unresolvedDualPolity
  | reunifiedByMilitaryPoliticalVictory
  | reunifiedByNegotiatedAccession
  | partitionPersistsWithAgreementFramework
  deriving DecidableEq, Repr

structure SuccessorPolityCase where
  label : String
  mechanism : ForkMechanism
  laterResolution : ResolutionMode
  sourceReceipt : String
  sharedHistoricalSurface : Bool := true
  samePresentPolity : Bool := false
  sharedOriginDeterminesPresentIdentity : Bool := false
  oneSideAutomaticallyInheritsLegitimacy : Bool := false

def chinaTaiwanCase : SuccessorPolityCase :=
  ⟨"PRC / ROC-on-Taiwan", .civilWarRivalGovernmentFork, .unresolvedDualPolity, "Taiwan NHRM history"⟩

def koreaCase : SuccessorPolityCase :=
  ⟨"DPRK / ROK", .foreignOccupationColdWarFork, .unresolvedDualPolity, "US State Department historical source"⟩

def vietnamCase : SuccessorPolityCase :=
  ⟨"North / South Vietnam", .ceasefireProvisionalPartitionFork, .reunifiedByMilitaryPoliticalVictory, "1954 Geneva history"⟩

def germanyCase : SuccessorPolityCase :=
  ⟨"FRG / GDR", .ideologicalBlocDivisionFork, .reunifiedByNegotiatedAccession, "German Federal Government unity history"⟩

def irelandCase : SuccessorPolityCase :=
  ⟨"Ireland / Northern Ireland", .negotiatedConstitutionalPartitionFork, .partitionPersistsWithAgreementFramework, "UK House of Commons Library"⟩

def canonicalCases : List SuccessorPolityCase :=
  [chinaTaiwanCase, koreaCase, vietnamCase, germanyCase, irelandCase]

theorem shared_origin_never_auto_settles_identity_or_legitimacy :
    ∀ c ∈ canonicalCases,
      c.samePresentPolity = false ∧
      c.sharedOriginDeterminesPresentIdentity = false ∧
      c.oneSideAutomaticallyInheritsLegitimacy = false := by
  intro c h
  simp [canonicalCases] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

end AgdaMirror.Governance.SuccessorPolityForkFamily
