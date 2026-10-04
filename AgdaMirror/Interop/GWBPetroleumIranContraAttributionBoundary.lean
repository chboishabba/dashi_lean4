namespace AgdaMirror.Interop.GWBPetroleumIranContraAttributionBoundary

structure GWBCorpusAllegation where
  corpusRef : String
  retainedSourceRef : String
  propositionRef : String
  boundedReading : String
  corpusContainsClaim : Bool := true
  claimIndependentlyVerified : Bool := false
  candidateOnly : Bool := true

def bushIranContraAllegation : GWBCorpusAllegation :=
  ⟨"SensibLaw GWB corpus",
   "retained local-book lane",
   "claim:book-alleges-bush-connection-to-iran-contra",
   "Corpus contains an allegation; GWB candidate-world/audit boundaries prohibit promotion without reviewed evidence."⟩

structure VerifiedBackground where
  oilBiographyPaid : Bool := true
  archivalIranContraSeriesPaid : Bool := true
  historicalIranContraMechanismPaid : Bool := true
  oilBiographyProvesIranContraParticipation : Bool := false
  archiveSeriesProvesAllegation : Bool := false

def canonicalBackground : VerifiedBackground := {}

theorem corpus_allegation_remains_candidate :
    bushIranContraAllegation.claimIndependentlyVerified = false ∧
    bushIranContraAllegation.candidateOnly = true ∧
    canonicalBackground.oilBiographyProvesIranContraParticipation = false ∧
    canonicalBackground.archiveSeriesProvesAllegation = false := by
  decide

end AgdaMirror.Interop.GWBPetroleumIranContraAttributionBoundary
