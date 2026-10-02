namespace AgdaMirror.Governance.MostazafinWorkerCategoryOverlapReviewedJoin

structure CategoryOverlapReceipt where
  representedCategoryRef : String
  currentCohortRef : String
  historicalSourceRef : String
  currentSourceRef : String
  historicalMembershipRelationPaid : Bool := true
  currentCohortPresencePaid : Bool := true
  categoryOverlapPaid : Bool := true
  everyCurrentProtesterInsideCategory : Bool := false
  sameHistoricalPersonsPersist : Bool := false

def workerMostazafinCategoryOverlap : CategoryOverlapReceipt :=
  ⟨"historical Khomeinist mostazafin category includes workers",
   "2026 Iranian labour protest / strike cohort",
   "Middle Eastern Studies 2018 factory discourse study",
   "Worker Rights Watch Jan-June 2026"⟩

theorem category_overlap_is_bounded :
    workerMostazafinCategoryOverlap.categoryOverlapPaid = true ∧
    workerMostazafinCategoryOverlap.everyCurrentProtesterInsideCategory = false ∧
    workerMostazafinCategoryOverlap.sameHistoricalPersonsPersist = false := by
  decide

end AgdaMirror.Governance.MostazafinWorkerCategoryOverlapReviewedJoin
