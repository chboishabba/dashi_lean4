namespace AgdaMirror.Governance.IRISDenaSenateEstimatesDutyNarrowing

structure DutyNarrowingReceipt where
  parliamentaryTopicSourceRef : String
  contentSourceRef : String
  boundedReading : String
  defensiveDutyAttributed : Bool := true
  platformMaintenanceAttributed : Bool := true
  primaryHansardContentVerified : Bool := false
  exactWatchstationKnown : Bool := false
  offensiveWeaponEmploymentAttributed : Bool := false

def senateDutyNarrowing : DutyNarrowingReceipt :=
  ⟨"Parliament of Australia 2026-27 Budget Estimates key-issues index",
   "Liberal Party of Australia Senate Estimates Week Two summary",
   "Primary index confirms topic/pages; partisan secondary summary attributes defensive and platform-maintenance duties."⟩

theorem secondary_attribution_not_primary :
    senateDutyNarrowing.primaryHansardContentVerified = false ∧
    senateDutyNarrowing.exactWatchstationKnown = false ∧
    senateDutyNarrowing.offensiveWeaponEmploymentAttributed = false := by
  decide

end AgdaMirror.Governance.IRISDenaSenateEstimatesDutyNarrowing
