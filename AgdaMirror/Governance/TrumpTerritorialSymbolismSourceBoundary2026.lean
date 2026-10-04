namespace AgdaMirror.Governance.TrumpTerritorialSymbolismSourceBoundary2026

inductive TerritorialSpeechAct
  | mapPost | annexationRhetoric | acquisitionProposal | enactedTreaty | enactedStatute | militaryOrder
  deriving DecidableEq, Repr

structure TerritorialSymbolicArtifact where
  act : TerritorialSpeechAct
  carrier : String
  representedTerritory : String
  sourceReceipt : String
  officialLegalInstrument : Bool := false
  formalAnnexationPolicy : Bool := false
  evidencesTerritorialImaginary : Bool := true
  provesImplementationIntent : Bool := false

def septemberMap : TerritorialSymbolicArtifact :=
  ⟨.mapPost,
   "Trump Truth Social post as reported by Reuters",
   "Canada, Greenland, Iceland, Mexico, Central America and Caribbean areas under U.S. flag",
   "Reuters 2026-09-08"⟩

theorem map_is_symbolic_not_legal_instrument :
    septemberMap.evidencesTerritorialImaginary = true ∧
    septemberMap.officialLegalInstrument = false ∧
    septemberMap.formalAnnexationPolicy = false ∧
    septemberMap.provesImplementationIntent = false := by
  decide

end AgdaMirror.Governance.TrumpTerritorialSymbolismSourceBoundary2026
